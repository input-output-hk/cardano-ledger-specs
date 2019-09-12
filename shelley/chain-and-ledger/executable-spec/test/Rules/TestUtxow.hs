{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Rules.TestUtxow where

import           Control.Monad (when)
import           Data.Foldable (toList)

import           Hedgehog (Property, forAll, property, withTests, (===))

import           Control.State.Transition.Generator (trace)
import           Control.State.Transition.Trace (sourceSignalTargets, traceLength, _traceEnv)

import           LedgerState (pattern UTxOState, decayedTx, keyRefunds)
import           MockTypes (UTXOW)
import           STS.Utxo (UtxoEnv (..))
import           TxData (_body, _certs, _inputs, _txfee)
import           UTxO (balance, deposits, txouts)

import           Ledger.Core ((<|))

------------------------------
-- Constants for Properties --
------------------------------

numberOfTests :: Int
numberOfTests = 300

traceLen :: Int
traceLen = 100

--------------------------
-- Properties for UTXOW --
--------------------------

-- | Preserve the balance in a transaction, i.e., the sum of the consumed value
-- equals the sum of the created value.
preserveBalance :: Property
preserveBalance = withTests (fromIntegral numberOfTests) . property $ do
  t <- forAll (trace @UTXOW $ fromIntegral traceLen)
  let
    n :: Integer
    n = fromIntegral $ traceLength t
    tr = sourceSignalTargets t
    UtxoEnv _ pp stk stp _ = _traceEnv t

  when (n > 1) $
    [] === filter (not . (createdIsConsumed pp stk stp)) tr

  where createdIsConsumed pp stk stp (UTxOState u _ _ _, tx, UTxOState u' _ _ _) =
          created u' tx pp stp == consumed u tx pp stk
        created u tx pp stp =
            balance u
          + _txfee (_body tx)
          + (deposits pp stp (toList $ _certs $ _body tx))
        consumed u tx pp stk =
            balance u
          + keyRefunds pp stk (_body tx)
