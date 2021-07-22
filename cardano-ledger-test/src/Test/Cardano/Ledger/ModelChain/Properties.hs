{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Test.Cardano.Ledger.ModelChain.Properties where

import Cardano.Ledger.Alonzo (AlonzoEra)
import Cardano.Ledger.BaseTypes (boundRational)
import Cardano.Ledger.Coin
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Mary.Value (AssetName (..))
import Cardano.Ledger.Shelley (ShelleyEra)
import Control.State.Transition.Extended
import qualified Data.ByteString.Char8 as BS
import Data.Default.Class
import Data.Foldable
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Data.Ratio ((%))
import qualified Data.Set as Set
import Data.String (IsString (..))
import Data.Typeable
import GHC.Natural
import qualified PlutusTx
import Shelley.Spec.Ledger.API.Genesis
import Test.Cardano.Ledger.Elaborators
import Test.Cardano.Ledger.Elaborators.Alonzo ()
import Test.Cardano.Ledger.Elaborators.Shelley ()
import Test.Cardano.Ledger.ModelChain
import Test.Cardano.Ledger.ModelChain.Address
import Test.Cardano.Ledger.ModelChain.FeatureSet
import Test.Cardano.Ledger.ModelChain.Script
import Test.Cardano.Ledger.ModelChain.Utils
import Test.Cardano.Ledger.ModelChain.Value
import Test.Shelley.Spec.Ledger.ConcreteCryptoTypes (C_Crypto)
import Test.Tasty
import Test.Tasty.QuickCheck

modelMACoin ::
  (ValueFeature era ~ 'ExpectAnyOutput) =>
  ModelScript (ScriptFeature era) ->
  [(AssetName, Integer)] ->
  ModelValue 'ExpectAnyOutput era
modelMACoin script assets =
  ModelValue $
    ModelValue_Var $
      ModelValue_MA mempty $ Map.singleton script $ Map.fromList assets

modelCoin :: Integer -> ModelValue era k
modelCoin = ModelValue . ModelValue_Inject . Coin

modelReward :: ModelAddress (ScriptFeature era) -> ModelValue k era
modelReward = ModelValue . ModelValue_Var . ModelValue_Reward

modelRewards :: [ModelAddress (ScriptFeature era)] -> Map.Map (ModelAddress (ScriptFeature era)) (ModelValue k era)
modelRewards = foldMap $ \maddr -> Map.singleton maddr $ modelReward maddr

infixl 6 $+

infixl 6 $-

infixl 7 $*

($*) :: Natural -> ModelValue era k -> ModelValue era k
x $* ModelValue y = ModelValue (ModelValue_Scale x y)

($+) :: ModelValue era k -> ModelValue era k -> ModelValue era k
ModelValue x $+ ModelValue y = ModelValue (ModelValue_Add x y)

($-) :: ModelValue era k -> ModelValue era k -> ModelValue era k
ModelValue x $- ModelValue y = ModelValue (ModelValue_Sub x y)

purpleModelScript :: ModelScript ('TyScriptFeature 'True x)
purpleModelScript = ModelScript_Timelock $ ModelTimelock_AllOf []

bobCoinScript :: ModelScript ('TyScriptFeature 'True x)
bobCoinScript = ModelScript_Timelock $ ModelTimelock_Signature "BobCoin"

modelPlutusScript :: Natural -> ModelScript ('TyScriptFeature x 'True)
modelPlutusScript = ModelScript_PlutusV1 . ModelPlutusScript_AlwaysSucceeds

instance IsString AssetName where
  fromString = AssetName . BS.pack

modelTestDelegations ::
  ( ElaborateEraModel era,
    Default (AdditionalGenesisConfig era),
    -- Eq (PredicateFailure (Core.EraRule "LEDGER" era)),
    Show (PredicateFailure (Core.EraRule "LEDGER" era)),
    Show (Core.Value era)
  ) =>
  proxy era ->
  Bool ->
  ModelAddress AllScriptFeatures ->
  [TestTree]
modelTestDelegations proxy needsCollateral stakeAddr =
  let modelPool = ModelPoolParams "pool1" (Coin 0) (Coin 0) (fromJust $ boundRational $ 0 % 1) "rewardAcct" ["poolOwner"]
      allAtOnce =
        [ ModelBlock
            0
            [ (modelTx 1)
                { _mtxInputs = Set.fromList [0],
                  _mtxCollateral = SupportsPlutus $ Set.fromList [x | x <- [0], needsCollateral],
                  _mtxOutputs =
                    [ (100, modelTxOut "unstaked" (modelCoin 9_800_000_000_000)),
                      (200, modelTxOut stakeAddr (modelCoin 100_000_000_000))
                    ],
                  _mtxFee = modelCoin 100_000_000_000,
                  _mtxDCert =
                    [ ModelRegisterStake stakeAddr,
                      ModelRegisterPool modelPool,
                      ModelDelegate (ModelDelegation stakeAddr "pool1")
                    ]
                }
            ]
        ]
      oneAtATime =
        [ ModelBlock
            0
            [ (modelTx 0)
                { _mtxInputs = Set.fromList [0],
                  _mtxOutputs =
                    [ (1, modelTxOut "unstaked" (modelCoin 9_875_000_000_000)),
                      (2, modelTxOut stakeAddr (modelCoin 100_000_000_000))
                    ],
                  _mtxFee = modelCoin 25_000_000_000
                }
            ],
          ModelBlock
            1
            [ (modelTx 1)
                { _mtxInputs = Set.fromList [1],
                  _mtxOutputs =
                    [ (2, modelTxOut "unstaked" (modelCoin 9_850_000_000_000))
                    ],
                  _mtxFee = modelCoin 25_000_000_000,
                  _mtxDCert = [ModelRegisterStake stakeAddr]
                }
            ],
          ModelBlock
            2
            [ (modelTx 2)
                { _mtxInputs = Set.fromList [2],
                  _mtxOutputs =
                    [ (3, modelTxOut "unstaked" (modelCoin 9_825_000_000_000))
                    ],
                  _mtxFee = modelCoin 25_000_000_000,
                  _mtxDCert = [ModelRegisterPool modelPool]
                }
            ],
          ModelBlock
            3
            [ (modelTx 3)
                { _mtxInputs = Set.fromList [3],
                  _mtxCollateral = SupportsPlutus $ Set.fromList [x | x <- [3], needsCollateral],
                  _mtxOutputs =
                    [ (100, modelTxOut "unstaked" (modelCoin 9_800_000_000_000))
                    ],
                  _mtxFee = modelCoin 25_000_000_000,
                  _mtxDCert =
                    [ ModelDelegate (ModelDelegation stakeAddr "pool1")
                    ]
                }
            ]
        ]
      genAct =
        [ (0, "unstaked", Coin 10_000_000_000_000)
        ]
      checkAllWithdrawnRewards nes ems =
        let rewards = observeRewards (nes, ems)
         in counterexample (show rewards) $ Coin 0 === fold rewards
      go reg =
        testChainModelInteractionWith
          proxy
          checkAllWithdrawnRewards
          genAct
          [ ModelEpoch reg (ModelBlocksMade $ Map.fromList []),
            ModelEpoch [] (ModelBlocksMade $ Map.fromList []),
            ModelEpoch [] (ModelBlocksMade $ Map.fromList [("pool1", 1 % 1)]),
            ModelEpoch [] (ModelBlocksMade $ Map.fromList []),
            ModelEpoch
              [ ModelBlock
                  0
                  [ (modelTx 100)
                      { _mtxInputs = Set.fromList [100],
                        _mtxCollateral = SupportsPlutus $ Set.fromList [x | x <- [100], needsCollateral],
                        _mtxOutputs =
                          [ (103, modelTxOut "unstaked" (modelCoin 9_700_000_000_000)),
                            (104, modelTxOut "reward-less-minimum" (modelReward stakeAddr $- modelCoin 100_000_000)),
                            (105, modelTxOut "minimum" (modelCoin 100_000_000))
                          ],
                        _mtxFee = modelCoin 100_000_000_000,
                        _mtxWdrl = modelRewards [stakeAddr]
                      }
                  ]
              ]
              (ModelBlocksMade $ Map.fromList [])
          ]
   in [ testProperty "allAtOnce" $ go allAtOnce,
        testProperty "oneAtATime" $ go oneAtATime
      ]

-- | some hand-written model based unit tests
modelUnitTests ::
  forall era proxy.
  ( ElaborateEraModel era,
    Default (AdditionalGenesisConfig era),
    Eq (PredicateFailure (Core.EraRule "LEDGER" era)),
    Show (PredicateFailure (Core.EraRule "LEDGER" era)),
    Show (Core.Value era)
  ) =>
  proxy era ->
  TestTree
modelUnitTests proxy =
  testGroup
    (show $ typeRep proxy)
    [ testProperty "noop" $ testChainModelInteraction proxy [] [],
      testProperty "noop-2" $
        testChainModelInteraction
          proxy
          ( [ (0, "alice", Coin 1_000_000),
              (1, "bob", Coin 1_000_000)
            ]
          )
          [ModelEpoch [] mempty],
      testGroup "deleg-keyHash" $ modelTestDelegations proxy False "keyHashStake",
      testGroup "deleg-plutus" $ modelTestDelegations proxy True (ModelScriptAddress $ ModelPlutusScript_AlwaysSucceeds 4),
      testProperty "xfer" $
        testChainModelInteraction
          proxy
          ( [ (0, "alice", Coin 1_000_000_000)
            ]
          )
          [ ModelEpoch
              [ ModelBlock
                  1
                  [ (modelTx 1)
                      { _mtxInputs = Set.fromList [0],
                        _mtxOutputs =
                          [ (1, modelTxOut "bob" (modelCoin 100_000_000)),
                            (2, modelTxOut "alice" (modelCoin 1_000_000_000 $- (modelCoin 100_000_000 $+ modelCoin 1_000_000)))
                          ],
                        _mtxFee = modelCoin 1_000_000
                      }
                  ]
              ]
              mempty
          ],
      testProperty "unbalanced" $
        testChainModelInteractionRejection
          proxy
          (ModelValueNotConservedUTxO (modelCoin 1_000_000_000) (modelCoin 101_000_000))
          ( [ (0, "alice", Coin 1_000_000_000)
            ]
          )
          [ ModelEpoch
              [ ModelBlock
                  1
                  [ (modelTx 1)
                      { _mtxInputs = (Set.fromList [0]),
                        _mtxOutputs = [(1, modelTxOut "bob" $ modelCoin 100_000_000)],
                        _mtxFee = modelCoin 1_000_000
                      }
                  ]
              ]
              mempty
          ],
      testProperty "xfer-2" $
        testChainModelInteraction
          proxy
          ( [ (0, "alice", Coin 1_000_000_000)
            ]
          )
          [ ModelEpoch
              [ ModelBlock
                  1
                  [ (modelTx 1)
                      { _mtxInputs = Set.fromList [0],
                        _mtxOutputs =
                          [ (1, modelTxOut "bob" (modelCoin 100_000_000)),
                            (2, modelTxOut "alice" (modelCoin 1_000_000_000 $- (modelCoin 100_000_000 $+ modelCoin 1_000_000)))
                          ],
                        _mtxFee = modelCoin 1_000_000
                      }
                  ],
                ModelBlock
                  2
                  [ (modelTx 2)
                      { _mtxInputs = Set.fromList [2],
                        _mtxOutputs =
                          [ (3, modelTxOut "bob" (modelCoin 100_000_000)),
                            (4, modelTxOut "alice" (modelCoin 1_000_000_000 $- 2 $* (modelCoin 100_000_000 $+ modelCoin 1_000_000)))
                          ],
                        _mtxFee = modelCoin 1_000_000
                      }
                  ]
              ]
              mempty
          ],
      testProperty "mint" $
        ( testChainModelInteraction
            proxy
            ( [ (0, "alice", Coin 1_000_000_000)
              ]
            )
        )
          [ ModelEpoch
              [ ModelBlock
                  1
                  [ (modelTx 1)
                      { _mtxInputs = Set.fromList [0],
                        _mtxOutputs =
                          [ ( 1,
                              modelTxOut
                                "alice"
                                ( modelCoin 1_000_000_000 $- (modelCoin 1_000_000)
                                    $+ modelMACoin purpleModelScript [("purp", 1234)]
                                )
                            )
                          ],
                        _mtxFee = modelCoin 1_000_000,
                        _mtxMint = SupportsMint (modelMACoin purpleModelScript [("purp", 1234)])
                      }
                  ]
              ]
              mempty
          ],
      testProperty "mint-2" $
        ( testChainModelInteraction
            proxy
            ( [ (0, "alice", Coin 1_000_000_000)
              ]
            )
        )
          [ ModelEpoch
              [ ModelBlock
                  1
                  [ (modelTx 1)
                      { _mtxInputs = Set.fromList [0],
                        _mtxOutputs =
                          [ ( 1,
                              modelTxOut
                                "alice"
                                ( modelCoin 1_000_000_000 $- (modelCoin 1_000_000)
                                    $+ modelMACoin bobCoinScript [("BOB", 1234)]
                                )
                            )
                          ],
                        _mtxFee = modelCoin 1_000_000,
                        _mtxMint = SupportsMint (modelMACoin bobCoinScript [("BOB", 1234)])
                      }
                  ]
              ]
              mempty
          ],
      testProperty "mint-3" $
        ( testChainModelInteraction
            proxy
            ( [ (0, "alice", Coin 1_000_000_000)
              ]
            )
        )
          [ ModelEpoch
              [ ModelBlock
                  1
                  [ (modelTx 1)
                      { _mtxInputs = Set.fromList [0],
                        _mtxOutputs =
                          [ ( 1,
                              modelTxOut
                                "alice"
                                ( modelCoin 1_000_000_000 $- (modelCoin 1_000_000)
                                    $+ modelMACoin purpleModelScript [("BOB", 1234)]
                                )
                            )
                          ],
                        _mtxFee = modelCoin 1_000_000,
                        _mtxMint = SupportsMint (modelMACoin purpleModelScript [("BOB", 1234)])
                      },
                    (modelTx 2)
                      { _mtxInputs = Set.fromList [1],
                        _mtxOutputs =
                          [ ( 2,
                              modelTxOut
                                "alice"
                                ( modelCoin 1_000_000_000 $- (3 $* modelCoin 1_000_000)
                                    $+ modelMACoin purpleModelScript [("BOB", 1134)]
                                )
                            ),
                            ( 3,
                              modelTxOut
                                "carol"
                                ( modelCoin 1_000_000
                                    $+ modelMACoin purpleModelScript [("BOB", 100)]
                                )
                            )
                          ],
                        _mtxFee = modelCoin 1_000_000
                      }
                  ]
              ]
              mempty
          ],
      testProperty "mint-4" $
        ( testChainModelInteraction
            proxy
            ( [ (0, "alice", Coin 1_000_000_000)
              ]
            )
        )
          [ ModelEpoch
              [ ModelBlock
                  1
                  [ (modelTx 1)
                      { _mtxInputs = Set.fromList [0],
                        _mtxOutputs =
                          [ ( 1,
                              modelTxOut
                                "alice"
                                ( modelCoin 1_000_000_000 $- (modelCoin 1_000_000)
                                    $+ modelMACoin bobCoinScript [("BOB", 1234)]
                                )
                            )
                          ],
                        _mtxFee = modelCoin 1_000_000,
                        _mtxMint = SupportsMint (modelMACoin bobCoinScript [("BOB", 1234)])
                      },
                    (modelTx 2)
                      { _mtxInputs = Set.fromList [1],
                        _mtxOutputs =
                          [ ( 2,
                              modelTxOut
                                "alice"
                                ( modelCoin 1_000_000_000 $- (3 $* modelCoin 1_000_000)
                                    $+ modelMACoin bobCoinScript [("BOB", 1134)]
                                )
                            ),
                            ( 3,
                              modelTxOut
                                "carol"
                                ( modelCoin 1_000_000
                                    $+ modelMACoin bobCoinScript [("BOB", 100)]
                                )
                            )
                          ],
                        _mtxFee = modelCoin 1_000_000
                      }
                  ]
              ]
              mempty
          ],
      testProperty "mint-plutus" $
        testChainModelInteraction
          proxy
          ( [ (0, "alice", Coin 1_000_000_000)
            ]
          )
          [ ModelEpoch
              [ ModelBlock
                  1
                  [ (modelTx 1)
                      { _mtxInputs = Set.fromList [0],
                        _mtxCollateral = SupportsPlutus (Set.fromList [0]),
                        _mtxOutputs =
                          [ ( 1,
                              modelTxOut
                                "alice"
                                ( modelCoin 1_000_000_000 $- (modelCoin 1_000_000)
                                    $+ modelMACoin (modelPlutusScript 3) [("purp", 1234)]
                                )
                            )
                          ],
                        _mtxFee = modelCoin 1_000_000,
                        _mtxMint = SupportsMint (modelMACoin (modelPlutusScript 3) [("purp", 1234)])
                      }
                  ]
              ]
              mempty
          ],
      testProperty "tx-plutus" $
        testChainModelInteraction
          proxy
          ( [ (0, "alice", Coin 1_000_000_000)
            ]
          )
          [ ModelEpoch
              [ ModelBlock
                  1
                  [ (modelTx 1)
                      { _mtxInputs = Set.fromList [0],
                        _mtxOutputs =
                          [ (1, modelTxOut "bob" (modelCoin 100_000_000)),
                            ( 2,
                              (modelTxOut (ModelScriptAddress $ ModelPlutusScript_AlwaysSucceeds 2) (modelCoin 1_000_000_000 $- (modelCoin 100_000_000 $+ modelCoin 1_000_000)))
                                { _mtxo_data = SupportsPlutus $ Just $ PlutusTx.I 7
                                }
                            )
                          ],
                        _mtxFee = modelCoin 1_000_000
                      }
                  ],
                ModelBlock
                  2
                  [ (modelTx 2)
                      { _mtxInputs = Set.fromList [2],
                        _mtxCollateral = SupportsPlutus (Set.fromList [1]),
                        _mtxOutputs =
                          [ (3, modelTxOut "bob" (modelCoin 100_000_000)),
                            (4, modelTxOut "alice" (modelCoin 1_000_000_000 $- 2 $* (modelCoin 100_000_000 $+ modelCoin 1_000_000)))
                          ],
                        _mtxFee = modelCoin 1_000_000
                      }
                  ]
              ]
              mempty
          ]
    ]

modelUnitTests_ :: TestTree
modelUnitTests_ =
  testGroup
    "model-unit-tests"
    [ modelUnitTests (Proxy :: Proxy (ShelleyEra C_Crypto)),
      modelUnitTests (Proxy :: Proxy (AlonzoEra C_Crypto))
    ]

modelTxOut :: ModelAddress AllScriptFeatures -> ModelValue 'ExpectAnyOutput AllModelFeatures -> ModelTxOut AllModelFeatures
modelTxOut a v = ModelTxOut a v (SupportsPlutus Nothing)

defaultTestMain :: IO ()
defaultTestMain = defaultMain modelUnitTests_
