{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Rules.TestLedger
  ( rewardZeroAfterReg
  , credentialRemovedAfterDereg
  , consumedEqualsProduced
  , registeredPoolIsAdded
  )
where

import           Data.Word (Word64)
import           Lens.Micro ((^.))

import           Hedgehog (Property, forAll, property, withTests)

import           Control.State.Transition.Generator (ofLengthAtLeast, trace,
                     traceOfLengthWithInitState)
import           Control.State.Transition.Trace (SourceSignalTarget (..), source,
                     sourceSignalTargets, target, traceEnv)
import           Generator.Core (mkGenesisLedgerState)
import           Generator.LedgerTrace ()

import           Coin (pattern Coin)
import           LedgerState (pattern DPState, pattern DState, pattern UTxOState, _deposited,
                     _dstate, _fees, _rewards, _utxo)
import           MockTypes (LEDGER)
import qualified Rules.TestDeleg as TestDeleg
import qualified Rules.TestPool as TestPool
import           UTxO (balance)

import           Test.Utils (assertAll)

------------------------------
-- Constants for Properties --
------------------------------

numberOfTests :: Word64
numberOfTests = 300

traceLen :: Word64
traceLen = 100

---------------------------
-- Properties for LEDGER --
---------------------------

-- | Check that a newly registered key has a reward of 0.
rewardZeroAfterReg :: Property
rewardZeroAfterReg = withTests (fromIntegral numberOfTests) . property $ do
  t <- forAll
       (traceOfLengthWithInitState @LEDGER
                                   (fromIntegral traceLen)
                                   mkGenesisLedgerState
        `ofLengthAtLeast` 1)

  TestDeleg.rewardZeroAfterReg
    ((concatMap TestDeleg.ledgerToDelegSsts . sourceSignalTargets) t)


credentialRemovedAfterDereg :: Property
credentialRemovedAfterDereg =
  withTests (fromIntegral numberOfTests) . property $ do
    tr <- fmap sourceSignalTargets
          $ forAll
          $ traceOfLengthWithInitState @LEDGER
                                     (fromIntegral traceLen)
                                     mkGenesisLedgerState
            `ofLengthAtLeast` 1
    TestDeleg.credentialRemovedAfterDereg
      (concatMap TestDeleg.ledgerToDelegSsts tr)


-- | Check that the value consumed by UTXO is equal to the value produced in
-- DELEGS
consumedEqualsProduced :: Property
consumedEqualsProduced = withTests (fromIntegral numberOfTests) . property $ do
  tr <- fmap sourceSignalTargets
        $ forAll
        $ trace @LEDGER traceLen `ofLengthAtLeast` 1

  assertAll consumedSameAsGained tr

  where consumedSameAsGained (SourceSignalTarget
                               { source = (UTxOState
                                           { _utxo = u
                                           , _deposited = d
                                           , _fees = fees
                                           }
                                          , DPState
                                            { _dstate = DState { _rewards = rewards }
                                            }
                                          )
                               , target = (UTxOState
                                            { _utxo = u'
                                            , _deposited = d'
                                            , _fees = fees'
                                            }
                                         , DPState
                                           { _dstate = DState { _rewards = rewards' }})}) =

          (balance u  + d  + fees  + foldl (+) (Coin 0) rewards ) ==
          (balance u' + d' + fees' + foldl (+) (Coin 0) rewards')


-- | Check that a `RegPool` certificate properly adds a stake pool.
registeredPoolIsAdded :: Property
registeredPoolIsAdded = do
  withTests (fromIntegral numberOfTests) . property $ do
    tr <- forAll
          $ traceOfLengthWithInitState @LEDGER
                                     (fromIntegral traceLen)
                                     mkGenesisLedgerState
            `ofLengthAtLeast` 1
    TestPool.registeredPoolIsAdded
      (tr ^. traceEnv)
      (concatMap TestPool.ledgerToPoolSsts (sourceSignalTargets tr))
