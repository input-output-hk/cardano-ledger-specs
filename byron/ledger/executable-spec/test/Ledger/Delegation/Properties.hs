{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

-- | Properties of the delegation traces induced by the transition systems
-- associated with this aspect of the ledger.
module Ledger.Delegation.Properties
  ( dcertsAreTriggered
  , rejectDupSchedDelegs
  , tracesAreClassified
  , dblockTracesAreClassified
  , DBLOCK
  )
where

import Control.Arrow ((&&&), first)
import Control.Lens ((^.), makeLenses, (&), (.~), view, to)
import Data.Bimap (Bimap)
import qualified Data.Bimap as Bimap
import Data.List (last)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Hedgehog
  ( MonadTest
  , Property
  , (===)
  , assert
  , classify
  , forAll
  , property
  , success
  , withTests
  )
import Hedgehog.Gen (integral)
import Hedgehog.Range (constant, linear)

import Control.State.Transition
  ( Environment
  , PredicateFailure
  , STS
  , Signal
  , State
  , initialRules
  , transitionRules
  , TRC (TRC)
  , IRC (IRC)
  , judgmentContext
  , (?!)
  , trans
  , Embed
  , wrapFailed
  , applySTS
  )
import Control.State.Transition.Generator
  ( HasSizeInfo
  , HasTrace
  , classifyTraceLength
  , initEnvGen
  , isTrivial
  , nonTrivialTrace
  , sigGen
  , suchThatLastState
  , trace
  )
import Control.State.Transition.Trace
  ( Trace
  , TraceOrder(OldestFirst)
  , lastState
  , preStatesAndSignals
  , traceEnv
  , traceSignals
  )
import Ledger.Core
  ( Epoch(Epoch)
  , Owner(Owner)
  , Sig(Sig)
  , Slot
  , SlotCount(SlotCount)
  , VKey(VKey)
  , VKeyGenesis
  , VKeyGenesis(VKeyGenesis)
  , addSlot
  , owner
  , unSlot
  , unSlotCount
  )
import Ledger.Delegation
  ( DCert
  , DCert(DCert)
  , DELEG
  , DIState(DIState)
  , DSEnv(DSEnv, _dSEnvK)
  , DSEnv
  , DSState(DSState)
  , DState(DState, _dStateDelegationMap, _dStateLastDelegation)
  , PredicateFailure(IsAlreadyScheduled, SDelegFailure, SDelegSFailure)
  , _dIStateDelegationMap
  , _dIStateKeyEpochDelegations
  , _dIStateLastDelegation
  , _dIStateScheduledDelegations
  , _dSStateKeyEpochDelegations
  , _dSStateScheduledDelegations
  , _dbody
  , _depoch
  , _dwho
  , _dwit
  , delegate
  , delegationMap
  , delegator
  , liveAfter
  , scheduledDelegations
  , slot
  )

import Ledger.Core.Generators (blockCountGen, epochGen, slotGen, vkGen)

--------------------------------------------------------------------------------
-- Delegation certification triggering tests
--------------------------------------------------------------------------------

-- | Initial state for the ADELEG and ADELEGS systems
initADelegsState :: DState
initADelegsState = DState
  { _dStateDelegationMap  = Bimap.empty
  , _dStateLastDelegation = Map.empty
  }

-- | Initial state for the ADELEG and ADELEGS systems
initSDelegsState :: DSState
initSDelegsState = DSState
  { _dSStateScheduledDelegations = []
  , _dSStateKeyEpochDelegations  = Set.empty
  }

-- | Initial state for the DELEG system
initialDIState :: DIState
initialDIState = DIState
  { _dIStateDelegationMap  = _dStateDelegationMap initADelegsState
  , _dIStateLastDelegation = _dStateLastDelegation initADelegsState
  , _dIStateScheduledDelegations = initSDelegsState ^. scheduledDelegations
  , _dIStateKeyEpochDelegations  = _dSStateKeyEpochDelegations initSDelegsState
  }

-- | Delegation blocks. Simple blockchain to test delegation.
data DBLOCK

-- | A delegation block.
data DBlock
  = DBlock
    { _blockSlot  :: Slot
    , _blockCerts :: [DCert]
    }
  deriving (Show, Eq)

makeLenses ''DBlock

-- | This corresponds to a state-transition rule where blocks with increasing
-- slot-numbers are produced.
instance STS DBLOCK where
  type Environment DBLOCK = DSEnv -- The initial environment is only used to bootstrap the initial state.
  type State DBLOCK = (DSEnv, DIState)
  type Signal DBLOCK = DBlock

  data PredicateFailure DBLOCK
    = DPF (PredicateFailure DELEG)
    | NotIncreasingBlockSlot
    deriving (Eq, Show)

  initialRules
    = [ do
          IRC env <- judgmentContext
          pure (env, initialDIState)
      ]

  transitionRules
    = [ do
          TRC (_, (env, st), dblock) <- judgmentContext
          env ^. slot < dblock ^. blockSlot ?! NotIncreasingBlockSlot
          stNext <- trans @DELEG $ TRC (env, st, dblock ^. blockCerts)
          return (env & slot .~ dblock ^. blockSlot, stNext)
      ]

instance Embed DELEG DBLOCK where
  wrapFailed = DPF

-- | Check that all the delegation certificates in the trace were correctly
-- applied.
dcertsAreTriggeredInTrace :: MonadTest m => Trace DBLOCK -> m ()
dcertsAreTriggeredInTrace tr
  = lastDms === trExpectedDms
  where
    -- | Delegation map at the final state.
    lastDms = st ^. delegationMap

    -- | Delegation map what we'd expect to see judging by the delegation
    -- certificates in the trace' signals.
    trExpectedDms
      = expectedDms lastSlot
                    ((fromIntegral . unSlotCount . liveAfter) (_dSEnvK env))
                    slotsAndDcerts

    (env, st) = lastState tr

    -- | Last slot that was considered for an activation.
    lastSlot :: Int
    lastSlot = fst . last $ slotsAndDcerts

    -- | Slots in which each block was applied. This is simply the result of
    -- pairing the slot number in the pre-state of a signal, with the signal
    -- itself.
    --
    -- We make use of integers, since negative numbers are quite handy when
    -- computing the slot at which a given certificate should have been
    -- activated (see 'expectedDms' and 'activationSlot').
    slotsAndDcerts :: [(Int, DBlock)]
    slotsAndDcerts
      = first (view (to fst . slot . to unSlot . to fromIntegral))
      <$> preStatesAndSignals OldestFirst tr

-- | Compute the expected delegation map after applying the sequence of
-- delegation certificates contained in the given blocks.
--
-- Delegation certificates are applied in the order they appear in the within a
-- block, and blocks are considered in the order they appear on the list passed
-- as parameter.
expectedDms
  :: Int
  -- ^ Last slot that should have been considered for certificate activation.
  -> Int
  -- ^ Delegation certificate liveness parameter.
  -> [(Int, DBlock)]
  -- ^ Delegation certificates to apply, and the slot at which these
  -- certificates where scheduled.
  -> Bimap VKeyGenesis VKey
expectedDms s d sbs = Bimap.fromList (fmap (delegator &&& delegate) activeCerts)
  where
    -- | We keep all the blocks whose certificates should be active given the
    -- current slot.
    activeBlocks :: [DBlock]
    activeBlocks
      =  snd
     <$> filter ((<= activationSlot) . fst) sbs

    -- | Slot at which the certificates should have become active. If this
    -- number is negative that means that no certificate can be activated.
    activationSlot :: Int
    activationSlot = s - d

    -- | Get the active certificates from each block, and concatenate them all
    -- together.
    activeCerts :: [DCert]
    activeCerts = concatMap _blockCerts activeBlocks

instance HasTrace DBLOCK where

  initEnvGen
    = DSEnv
    <$> allowedDelegators
    -- We do not expect the current epoch to have an influence on the tests, so
    -- we chose a small value here.
    <*> epochGen 0 10
    -- As with epochs, the current slot should not have influence in the tests.
    <*> slotGen 0 100
    -- 2160 the value of @k@ used in production. However, delegation
    -- certificates are activated @2*k@ slots from the slot in which they are
    -- issued. This means that if we want to see delegation activations, we
    -- need to choose a small value for @k@ since we do not want to blow up the
    -- testing time by using large trace lengths.
    <*> blockCountGen 0 100
    where
      -- We scale the number of delegators linearly up to twice the number of
      -- genesis keys we use in production. Factor 2 is chosen ad-hoc here.
      allowedDelegators = do
        n <- integral (linear 1 14)
        pure $! Set.fromAscList $ gk <$> [1 .. n]
      gk = VKeyGenesis . VKey . Owner

  sigGen _ (env, st) = do
    c <- integral (constant 1 10)
    let newSlot = (env ^.slot) `addSlot` SlotCount c
    delegs <- sigGen @DELEG env st
    return $ DBlock newSlot delegs

instance HasSizeInfo DBlock where
  isTrivial = null . view blockCerts

dcertsAreTriggered :: Property
dcertsAreTriggered = withTests 300 $ property $
  -- The number of tests was determined ad-hoc, since the default failed to
  -- uncover the presence of errors.
  forAll (nonTrivialTrace 1000) >>= dcertsAreTriggeredInTrace

dblockTracesAreClassified :: Property
dblockTracesAreClassified = property $ do
  let (tl, step) = (1000, 100)
  tr <- forAll (trace @DBLOCK tl)
  classifyTraceLength tr tl step
  -- Let's see what happens if we filter the empty signals.
  let
    -- Total number of delegation certificates found in the trace
    totalDCerts :: [DCert]
    totalDCerts = concat $ _blockCerts <$> traceSignals OldestFirst tr
  -- TODO: generalize this as classifyListLength (or foldableLength) (and
  -- classifyTraceLength can use this function)
  classify "total dcerts [0, 3)" $ length totalDCerts < 3
  classify "total dcerts [3, 5)" $ 3 <= length totalDCerts && length totalDCerts <= 5
  classify "total dcerts [5, 10)" $ 5 <= length totalDCerts && length totalDCerts < 10
  classify "total dcerts [10, 15)" $ 10 <= length totalDCerts && length totalDCerts < 15
  classify "total dcerts [15, 20)" $ 15 <= length totalDCerts && length totalDCerts < 20
  classify "total dcerts [20, 30)" $ 20 <= length totalDCerts && length totalDCerts < 30
  classify "total dcerts [30, 50)" $ 30 <= length totalDCerts && length totalDCerts < 50
  classify "total dcerts [50, 100)" $ 30 <= length totalDCerts && length totalDCerts < 100
  classify "total dcerts [100, 200)" $ 100 <= length totalDCerts && length totalDCerts < 200
  success

--------------------------------------------------------------------------------
-- Properties related to the transition rules
--------------------------------------------------------------------------------

-- | Reject delegation certificates where a genesis key tries to delegate in
-- the same slot.
--
-- This property tries to generate a trace where the last state contains a
-- non-empty sequence of scheduled delegations. If such trace cannot be
-- generated, then the test will fail when the heap limit is reached, or
-- hedgehog gives up.
rejectDupSchedDelegs :: Property
rejectDupSchedDelegs = property $ do
  (tr, dcert) <- forAll $ do
    tr <- trace @DELEG 1000
          `suchThatLastState` (not . null . view scheduledDelegations)
    let vkS =
          case lastState tr ^. scheduledDelegations of
            (_, (res, _)):_ -> res
            _ -> error $  "This should not happen: "
                       ++ "tr is guaranteed to contain a non-empty sequence of scheduled delegations"
    vkD <- vkGen
    epo <- Epoch <$> integral (linear 0 100)
    let dcert
          = DCert
          { _dbody = (vkD, epo)
          , _dwit = Sig vkS (owner vkS)
          , _dwho = (vkS, vkD)
          , _depoch = epo
          }
    return (tr, dcert)
  let pfs = case applySTS (TRC (tr ^. traceEnv, lastState tr, [dcert])) of
        Left res -> res
        Right _ -> []
  assert $ SDelegSFailure (SDelegFailure IsAlreadyScheduled) `elem` pfs

-- | Classify the traces.
tracesAreClassified :: Property
tracesAreClassified = property $ do
  let (tl, step) = (1000, 100)
  tr <- forAll (trace @DELEG tl)
  classifyTraceLength tr tl step
  success
