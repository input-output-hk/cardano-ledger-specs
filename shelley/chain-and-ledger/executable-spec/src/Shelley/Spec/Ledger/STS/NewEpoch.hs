{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Shelley.Spec.Ledger.STS.NewEpoch
  ( NEWEPOCH,
    NewEpochPredicateFailure (..),
    PredicateFailure,
    calculatePoolDistr,
  )
where

import Cardano.Ledger.BaseTypes
import Cardano.Ledger.Coin
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Era (Crypto, Era)
import Cardano.Ledger.Shelley.Constraints (UsesTxOut, UsesValue)
import Cardano.Ledger.Slot
import qualified Cardano.Ledger.Val as Val
import Control.Provenance (runProvM)
import Control.State.Transition
import Data.Default.Class (Default, def)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes)
import GHC.Generics (Generic)
import GHC.Records
import NoThunks.Class (NoThunks (..))
import Shelley.Spec.Ledger.Delegation.Certificates
import Shelley.Spec.Ledger.EpochBoundary
import Shelley.Spec.Ledger.LedgerState
import Shelley.Spec.Ledger.PParams (ProtVer)
import Shelley.Spec.Ledger.Rewards (sumRewards)
import Shelley.Spec.Ledger.STS.Epoch
import Shelley.Spec.Ledger.STS.Mir
import Shelley.Spec.Ledger.TxBody

data NEWEPOCH era

data NewEpochPredicateFailure era
  = EpochFailure (PredicateFailure (Core.EraRule "EPOCH" era)) -- Subtransition Failures
  | CorruptRewardUpdate
      !(RewardUpdate (Crypto era)) -- The reward update which violates an invariant
  | MirFailure (PredicateFailure (Core.EraRule "MIR" era)) -- Subtransition Failures
  deriving (Generic)

deriving stock instance
  ( Show (PredicateFailure (Core.EraRule "EPOCH" era)),
    Show (PredicateFailure (Core.EraRule "MIR" era))
  ) =>
  Show (NewEpochPredicateFailure era)

deriving stock instance
  ( Eq (PredicateFailure (Core.EraRule "EPOCH" era)),
    Eq (PredicateFailure (Core.EraRule "MIR" era))
  ) =>
  Eq (NewEpochPredicateFailure era)

instance
  ( NoThunks (PredicateFailure (Core.EraRule "EPOCH" era)),
    NoThunks (PredicateFailure (Core.EraRule "MIR" era))
  ) =>
  NoThunks (NewEpochPredicateFailure era)

instance
  ( UsesTxOut era,
    UsesValue era,
    Embed (Core.EraRule "MIR" era) (NEWEPOCH era),
    Embed (Core.EraRule "EPOCH" era) (NEWEPOCH era),
    Environment (Core.EraRule "MIR" era) ~ (),
    State (Core.EraRule "MIR" era) ~ EpochState era,
    Signal (Core.EraRule "MIR" era) ~ (),
    Environment (Core.EraRule "EPOCH" era) ~ (),
    State (Core.EraRule "EPOCH" era) ~ EpochState era,
    Signal (Core.EraRule "EPOCH" era) ~ EpochNo,
    Default (EpochState era),
    HasField "_protocolVersion" (Core.PParams era) ProtVer,
    Default (State (Core.EraRule "PPUP" era)),
    Default (Core.PParams era)
  ) =>
  STS (NEWEPOCH era)
  where
  type State (NEWEPOCH era) = NewEpochState era

  type Signal (NEWEPOCH era) = EpochNo

  type Environment (NEWEPOCH era) = ()

  type BaseM (NEWEPOCH era) = ShelleyBase
  type PredicateFailure (NEWEPOCH era) = NewEpochPredicateFailure era

  initialRules =
    [ pure $
        NewEpochState
          (EpochNo 0)
          (BlocksMade Map.empty)
          (BlocksMade Map.empty)
          def
          SNothing
          (PoolDistr Map.empty)
    ]

  transitionRules = [newEpochTransition]

newEpochTransition ::
  forall era.
  ( Embed (Core.EraRule "MIR" era) (NEWEPOCH era),
    Embed (Core.EraRule "EPOCH" era) (NEWEPOCH era),
    Environment (Core.EraRule "MIR" era) ~ (),
    State (Core.EraRule "MIR" era) ~ EpochState era,
    Signal (Core.EraRule "MIR" era) ~ (),
    Environment (Core.EraRule "EPOCH" era) ~ (),
    State (Core.EraRule "EPOCH" era) ~ EpochState era,
    Signal (Core.EraRule "EPOCH" era) ~ EpochNo,
    HasField "_protocolVersion" (Core.PParams era) ProtVer,
    UsesTxOut era,
    UsesValue era,
    Default (State (Core.EraRule "PPUP" era)),
    Default (Core.PParams era)
  ) =>
  TransitionRule (NEWEPOCH era)
newEpochTransition = do
  TRC
    ( (),
      src@(NewEpochState (EpochNo eL) _ bcur es ru _pd),
      epochno@(EpochNo e_)
      ) <-
    judgmentContext
  if e_ /= eL + 1
    then pure src
    else do
      es' <- case ru of
        SNothing -> pure es
        SJust (p@(Pulsing _ _)) -> do
          ru'@(RewardUpdate dt dr rs_ df _) <- liftSTS $ runProvM $ completeRupd p
          let totRs = sumRewards (esPrevPp es) rs_
          Val.isZero (dt <> (dr <> (toDeltaCoin totRs) <> df)) ?! CorruptRewardUpdate ru'
          pure $ applyRUpd ru' es
        SJust (Complete ru') -> do
          let RewardUpdate dt dr rs_ df _ = ru'
              totRs = sumRewards (esPrevPp es) rs_
          Val.isZero (dt <> (dr <> (toDeltaCoin totRs) <> df)) ?! CorruptRewardUpdate ru'
          pure $ applyRUpd ru' es

      es'' <- trans @(Core.EraRule "MIR" era) $ TRC ((), es', ())
      es''' <- trans @(Core.EraRule "EPOCH" era) $ TRC ((), es'', epochno)
      let EpochState _acnt ss _ls _pr _ _ = es'''
          pd' = calculatePoolDistr (_pstakeSet ss)
      pure $
        NewEpochState
          epochno
          bcur
          (BlocksMade Map.empty)
          es'''
          SNothing
          pd'

calculatePoolDistr :: SnapShot crypto -> PoolDistr crypto
calculatePoolDistr (SnapShot (Stake stake) delegs poolParams) =
  let Coin total = Map.foldl' (<>) mempty stake
      sd =
        Map.fromListWith (+) $
          catMaybes
            [ (,fromIntegral c / fromIntegral (if total == 0 then 1 else total))
                <$> Map.lookup hk delegs -- TODO mgudemann total could be zero (in
                -- particular when shrinking)
              | (hk, Coin c) <- Map.toList stake
            ]
   in PoolDistr $ Map.intersectionWith IndividualPoolStake sd (Map.map _poolVrf poolParams)

instance
  ( UsesTxOut era,
    UsesValue era,
    STS (EPOCH era),
    PredicateFailure (Core.EraRule "EPOCH" era) ~ EpochPredicateFailure era
  ) =>
  Embed (EPOCH era) (NEWEPOCH era)
  where
  wrapFailed = EpochFailure

instance
  ( Era era,
    Default (EpochState era),
    PredicateFailure (Core.EraRule "MIR" era) ~ MirPredicateFailure era
  ) =>
  Embed (MIR era) (NEWEPOCH era)
  where
  wrapFailed = MirFailure
