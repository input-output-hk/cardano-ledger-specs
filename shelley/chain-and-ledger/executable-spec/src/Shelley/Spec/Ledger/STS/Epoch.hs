{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Shelley.Spec.Ledger.STS.Epoch
  ( EPOCH,
    EpochPredicateFailure (..),
    PredicateFailure,
  )
where

import Cardano.Ledger.BaseTypes (ShelleyBase)
import Cardano.Ledger.Coin (Coin (..))
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Era (Era)
import Cardano.Ledger.Shelley.Constraints (UsesTxOut, UsesValue)
import Cardano.Ledger.Slot (EpochNo)
import Control.SetAlgebra (eval, (⨃))
import Control.State.Transition
  ( Embed (..),
    STS (..),
    TRC (..),
    TransitionRule,
    judgmentContext,
    trans,
  )
import Data.Default.Class (Default)
import qualified Data.Map.Strict as Map
import GHC.Generics (Generic)
import GHC.Records
import NoThunks.Class (NoThunks (..))
import Shelley.Spec.Ledger.EpochBoundary (SnapShots, obligation)
import Shelley.Spec.Ledger.LedgerState
  ( EpochState,
    LedgerState,
    PState (..),
    UpecState (..),
    esAccountState,
    esLState,
    esNonMyopic,
    esPp,
    esPrevPp,
    esSnapshots,
    _delegationState,
    _deposited,
    _ppups,
    _reserves,
    _rewards,
    _utxoState,
    pattern DPState,
    pattern EpochState,
  )
import Shelley.Spec.Ledger.Rewards ()
import Shelley.Spec.Ledger.STS.PoolReap (POOLREAP, PoolreapPredicateFailure, PoolreapState (..))
import Shelley.Spec.Ledger.STS.Snap (SNAP, SnapPredicateFailure)
import Shelley.Spec.Ledger.STS.Upec (UPEC, UpecPredicateFailure)

data EPOCH era

data EpochPredicateFailure era
  = PoolReapFailure (PredicateFailure (Core.EraRule "POOLREAP" era)) -- Subtransition Failures
  | SnapFailure (PredicateFailure (Core.EraRule "SNAP" era)) -- Subtransition Failures
  | UpecFailure (PredicateFailure (Core.EraRule "UPEC" era)) -- Subtransition Failures
  deriving (Generic)

deriving stock instance
  ( Eq (PredicateFailure (Core.EraRule "POOLREAP" era)),
    Eq (PredicateFailure (Core.EraRule "SNAP" era)),
    Eq (PredicateFailure (Core.EraRule "UPEC" era))
  ) =>
  Eq (EpochPredicateFailure era)

deriving stock instance
  ( Show (PredicateFailure (Core.EraRule "POOLREAP" era)),
    Show (PredicateFailure (Core.EraRule "SNAP" era)),
    Show (PredicateFailure (Core.EraRule "UPEC" era))
  ) =>
  Show (EpochPredicateFailure era)

instance
  ( UsesTxOut era,
    UsesValue era,
    Embed (Core.EraRule "SNAP" era) (EPOCH era),
    Environment (Core.EraRule "SNAP" era) ~ LedgerState era,
    State (Core.EraRule "SNAP" era) ~ SnapShots era,
    Signal (Core.EraRule "SNAP" era) ~ EpochNo,
    Embed (Core.EraRule "POOLREAP" era) (EPOCH era),
    Environment (Core.EraRule "POOLREAP" era) ~ Core.PParams era,
    State (Core.EraRule "POOLREAP" era) ~ PoolreapState era,
    Signal (Core.EraRule "POOLREAP" era) ~ EpochNo,
    Embed (Core.EraRule "UPEC" era) (EPOCH era),
    Environment (Core.EraRule "UPEC" era) ~ EpochState era,
    State (Core.EraRule "UPEC" era) ~ UpecState era,
    Signal (Core.EraRule "UPEC" era) ~ (),
    Default (State (Core.EraRule "PPUP" era)),
    Default (Core.PParams era),
    HasField "_keyDeposit" (Core.PParams era) Coin,
    HasField "_poolDeposit" (Core.PParams era) Coin
  ) =>
  STS (EPOCH era)
  where
  type State (EPOCH era) = EpochState era
  type Signal (EPOCH era) = EpochNo
  type Environment (EPOCH era) = ()
  type BaseM (EPOCH era) = ShelleyBase
  type PredicateFailure (EPOCH era) = EpochPredicateFailure era
  transitionRules = [epochTransition]

instance
  ( NoThunks (PredicateFailure (Core.EraRule "POOLREAP" era)),
    NoThunks (PredicateFailure (Core.EraRule "SNAP" era)),
    NoThunks (PredicateFailure (Core.EraRule "UPEC" era))
  ) =>
  NoThunks (EpochPredicateFailure era)

epochTransition ::
  forall era.
  ( Embed (Core.EraRule "SNAP" era) (EPOCH era),
    Environment (Core.EraRule "SNAP" era) ~ LedgerState era,
    State (Core.EraRule "SNAP" era) ~ SnapShots era,
    Signal (Core.EraRule "SNAP" era) ~ EpochNo,
    Embed (Core.EraRule "POOLREAP" era) (EPOCH era),
    Environment (Core.EraRule "POOLREAP" era) ~ Core.PParams era,
    State (Core.EraRule "POOLREAP" era) ~ PoolreapState era,
    Signal (Core.EraRule "POOLREAP" era) ~ EpochNo,
    Embed (Core.EraRule "UPEC" era) (EPOCH era),
    Environment (Core.EraRule "UPEC" era) ~ EpochState era,
    State (Core.EraRule "UPEC" era) ~ UpecState era,
    Signal (Core.EraRule "UPEC" era) ~ (),
    HasField "_keyDeposit" (Core.PParams era) Coin,
    HasField "_poolDeposit" (Core.PParams era) Coin
  ) =>
  TransitionRule (EPOCH era)
epochTransition = do
  TRC
    ( (),
      EpochState
        { esAccountState = acnt,
          esSnapshots = ss,
          esLState = ls,
          esPrevPp = pr,
          esPp = pp,
          esNonMyopic = nm
        },
      e
      ) <-
    judgmentContext
  let utxoSt = _utxoState ls
  let DPState dstate pstate = _delegationState ls
  ss' <-
    trans @(Core.EraRule "SNAP" era) $ TRC (ls, ss, e)

  let PState pParams fPParams _ = pstate
      ppp = eval (pParams ⨃ fPParams)
      pstate' =
        pstate
          { _pParams = ppp,
            _fPParams = Map.empty
          }
  PoolreapState utxoSt' acnt' dstate' pstate'' <-
    trans @(Core.EraRule "POOLREAP" era) $
      TRC (pp, PoolreapState utxoSt acnt dstate pstate', e)

  let epochState' =
        EpochState
          acnt'
          ss'
          (ls {_utxoState = utxoSt', _delegationState = DPState dstate' pstate''})
          pr
          pp
          nm

  UpecState pp' ppupSt' <-
    trans @(Core.EraRule "UPEC" era) $
      TRC (epochState', UpecState pp (_ppups utxoSt'), ())
  let utxoSt'' = utxoSt' {_ppups = ppupSt'}

  let Coin oblgCurr = obligation pp (_rewards dstate') (_pParams pstate'')
      Coin oblgNew = obligation pp' (_rewards dstate') (_pParams pstate'')
      Coin reserves = _reserves acnt'
      utxoSt''' = utxoSt'' {_deposited = Coin oblgNew}
      acnt'' = acnt' {_reserves = Coin $ reserves + oblgCurr - oblgNew}
  pure $
    epochState'
      { esAccountState = acnt'',
        esLState = (esLState epochState') {_utxoState = utxoSt'''},
        esPrevPp = pp,
        esPp = pp'
      }

instance
  ( UsesTxOut era,
    UsesValue era,
    PredicateFailure (Core.EraRule "SNAP" era) ~ SnapPredicateFailure era
  ) =>
  Embed (SNAP era) (EPOCH era)
  where
  wrapFailed = SnapFailure

instance
  ( Era era,
    STS (POOLREAP era),
    PredicateFailure (Core.EraRule "POOLREAP" era) ~ PoolreapPredicateFailure era
  ) =>
  Embed (POOLREAP era) (EPOCH era)
  where
  wrapFailed = PoolReapFailure

instance
  ( Era era,
    STS (UPEC era),
    PredicateFailure (Core.EraRule "UPEC" era) ~ UpecPredicateFailure era
  ) =>
  Embed (UPEC era) (EPOCH era)
  where
  wrapFailed = UpecFailure
