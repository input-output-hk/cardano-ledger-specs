{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Test.Cardano.Ledger.BaseTypes (baseTypesTests)
import Test.Cardano.Ledger.Examples.TwoPhaseValidation
  ( alonzoBBODYexamples,
    alonzoUTXOWexamples,
    collectOrderingAlonzo,
  )
import Test.Cardano.Ledger.ModelChain.Properties (modelUnitTests_)
import Test.Tasty
import Test.TestScenario (TestScenario (..), mainWithTestScenario)

-- ====================================================================================

tests :: TestTree
tests = askOption $ \case
  Nightly -> mainTests
  Fast -> mainTests
  _ -> mainTests

mainTests :: TestTree
mainTests =
  testGroup
    "cardano-core"
    [ baseTypesTests,
      testGroup
        "STS Tests"
        [ alonzoUTXOWexamples,
          alonzoBBODYexamples,
          collectOrderingAlonzo,
          modelUnitTests_
        ]
    ]

-- main entry point
main :: IO ()
main = mainWithTestScenario tests
