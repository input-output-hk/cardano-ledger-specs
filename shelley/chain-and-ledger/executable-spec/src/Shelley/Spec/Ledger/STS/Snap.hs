{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Shelley.Spec.Ledger.STS.Snap
  ( SNAP,
    PredicateFailure,
    SnapPredicateFailure,
  )
where

import Cardano.Ledger.BaseTypes
import Cardano.Ledger.Shelley.Constraints (UsesTxOut, UsesValue)
import Cardano.Ledger.Slot (EpochNo, EpochSize (..), epochInfoSize)
import Control.Monad.Trans.Reader (asks)
import Control.State.Transition
  ( STS (..),
    TRC (..),
    TransitionRule,
    judgmentContext,
    liftSTS,
  )
import qualified Data.Map as Map
import Data.Ratio
import Data.Word (Word64)
import GHC.Generics (Generic)
import NoThunks.Class (NoThunks (..))
import Shelley.Spec.Ledger.EpochBoundary
import Shelley.Spec.Ledger.LedgerState
  ( DPState (..),
    LedgerState (..),
    UTxOState (..),
    makePulsingStakeDistr,
  )
import Shelley.Spec.Ledger.UTxO (UTxO (..))

-- ===============================================

data SNAP era

data SnapPredicateFailure era -- No predicate failures
  deriving (Show, Generic, Eq)

instance NoThunks (SnapPredicateFailure era)

instance (UsesTxOut era, UsesValue era) => STS (SNAP era) where
  type State (SNAP era) = SnapShots era
  type Signal (SNAP era) = EpochNo
  type Environment (SNAP era) = LedgerState era
  type BaseM (SNAP era) = ShelleyBase
  type PredicateFailure (SNAP era) = SnapPredicateFailure era
  initialRules = [pure emptySnapShots]
  transitionRules = [snapTransition]

snapTransition ::
  (UsesValue era, UsesTxOut era) =>
  TransitionRule (SNAP era)
snapTransition = do
  TRC (lstate, s, epochno) <- judgmentContext
  let LedgerState (UTxOState (utxo@(UTxO u)) _ fees _) (DPState dstate pstate) = lstate
  num_blocks_estimate <- liftSTS $ approxBlocksPerEpoch epochno
  let pulseSize = (div (Map.size u) (fromIntegral num_blocks_estimate)) + 1
      stake = makePulsingStakeDistr pulseSize utxo dstate pstate
  pure $
    s
      { _pstakeMark = stake,
        _pstakeSet = runToCompletion (_pstakeMark s),
        _pstakeGo = _pstakeSet s,
        _feeSS = fees
      }

-- | Compute an (under) estimate of the number of blocks in the current Epoch, from the current EpochNo.
--   We want the estimate to be a little too small, as this increases the probability that the
--   pulsing will be Completed before the end of the Epoch. When we divide this 'too small' number into
--   the UTxO size, we will get a slighty 'too large' pulseSize, so we should finish early.
approxBlocksPerEpoch :: EpochNo -> BaseM (SNAP era) Word64
approxBlocksPerEpoch epochno = do
  active <- asks activeSlotCoeff
  let asc = (realToFrac . unboundRational . activeSlotVal $ active) :: Ratio Word64
  ei <- asks epochInfo
  (EpochSize slots) <- epochInfoSize ei epochno
  let total = ((slots % 1) * asc * (10 % 11)) :: Ratio Word64
  pure ((floor total) + 1) -- We never want this to zero, because if it is, we will never finish pulsing.
