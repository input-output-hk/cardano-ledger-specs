{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
-- Embed instances for (AlonzoEra TestCrypto)
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | This benchmark file is for profiling Property tests. It appears as a benchmark
--     but we do not use any of the criterion stuff. We just run main, which is profiled.
-- First set up the cabal.project.local (in the root of the cardano-ledger-specs directory) as follows.
-- ----
-- ignore-project: False
-- profiling: True
-- profiling-detail: all-functions
-- package plutus-core
--  ghc-options: -fexternal-interpreter
-- ---
-- In the cardano-ledger-test directory (where the cardano-ledger-test.cabal file resides)
-- This cabal file defines the benchProperty benchmark. Now build with profiling enabled
--    cabal build benchProperty --enable-profiling
-- Now run the build with the -- +RTS -p   flags
--    cabal run benchProperty -- +RTS -p
--
-- When you are done be sure an reset the  cabal.project.local, and rebuild things
-- without profiling enabled. One way to do this is
-- Reset the cabal.project.local file
--  cabal configure
-- Rebuild everything in the current project
--  cabal build
module Main where

import Cardano.Ledger.Alonzo (AlonzoEra)
import Cardano.Ledger.Alonzo.PParams (PParams' (..))
import Cardano.Ledger.Alonzo.Rules.Bbody (AlonzoBBODY)
import Cardano.Ledger.Alonzo.Rules.Utxow (AlonzoUTXOW)
import Control.State.Transition.Extended (Embed (..))
import Shelley.Spec.Ledger.STS.Chain (CHAIN, ChainPredicateFailure (..))
import Shelley.Spec.Ledger.STS.Ledger (LEDGER, LedgerPredicateFailure (UtxowFailure))
import Test.Cardano.Ledger.Alonzo.AlonzoEraGen ()
import Test.Cardano.Ledger.EraBuffet (TestCrypto)
import Test.Shelley.Spec.Ledger.Rules.ClassifyTraces (relevantCasesAreCovered)
import qualified Test.Tasty as T
import Test.Tasty.QuickCheck

instance Embed (AlonzoBBODY (AlonzoEra TestCrypto)) (CHAIN (AlonzoEra TestCrypto)) where
  wrapFailed = BbodyFailure

instance Embed (AlonzoUTXOW (AlonzoEra TestCrypto)) (LEDGER (AlonzoEra TestCrypto)) where
  wrapFailed = UtxowFailure

profileCover :: IO ()
profileCover =
  T.defaultMain $
    testProperty
      "Chain and Ledger traces cover the relevant cases"
      (withMaxSuccess 1 (relevantCasesAreCovered @(AlonzoEra TestCrypto)))

main :: IO ()
main = profileCover
