{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

module Test.Cardano.Ledger.ModelChain.Utils where

import Cardano.Ledger.BaseTypes (Globals (..), activeSlotVal, boundRational, epochInfo)
import Cardano.Ledger.Coin
import qualified Cardano.Ledger.Core as Core
import Cardano.Slotting.EpochInfo.API (epochInfoSize)
import Cardano.Slotting.Slot (EpochNo (..))
import Control.State.Transition.Extended
import Data.Default.Class
import Data.Functor.Identity
import Data.List (nub, (\\))
import qualified Data.Map as Map
import Data.Proxy
import qualified Data.Set as Set
import Data.Time.Clock (secondsToNominalDiffTime)
import Data.Time.Clock.POSIX (posixSecondsToUTCTime)
import Shelley.Spec.Ledger.API.Genesis
import Shelley.Spec.Ledger.API.Mempool (ApplyTxError (..))
import Shelley.Spec.Ledger.Genesis
import Shelley.Spec.Ledger.LedgerState (NewEpochState)
import Shelley.Spec.Ledger.PParams (emptyPParams)
import qualified Shelley.Spec.Ledger.PParams as PParams
import Test.Cardano.Ledger.Elaborators
import Test.Cardano.Ledger.ModelChain
import Test.Cardano.Ledger.ModelChain.Address
import Test.Cardano.Ledger.ModelChain.FeatureSet
import Test.Cardano.Ledger.ModelChain.Value
import Test.Shelley.Spec.Ledger.Utils (testGlobals)
import Test.Tasty.QuickCheck

-- type ApplyBlockError era = (ApplyBlockTransitionError era)

type ModelAddress' = ModelAddress ('TyScriptFeature 'False 'False)

-- | apply a list of ModelEpoch to an empty ledger and return the resulting
-- state, or the error if one occured
chainModelInteractionWith ::
  forall era proxy.
  ( Default (AdditionalGenesisConfig era),
    ElaborateEraModel era
  ) =>
  proxy era ->
  [(ModelUTxOId, ModelAddress', Coin)] ->
  [ModelEpoch (EraFeatureSet era)] ->
  (Either (ElaborateBlockError era) (), (NewEpochState era, EraElaboratorState era))
chainModelInteractionWith _ genesisAccounts0 modelBlocks =
  let -- TODO, pass this in as a generator.

      globals = testGlobals
      genesisAccounts = (\(a, b, c) -> (a, liftModelAddress b, c)) <$> genesisAccounts0

      sg :: ShelleyGenesis era
      sg =
        ShelleyGenesis
          { sgSystemStart = (posixSecondsToUTCTime 0),
            sgNetworkMagic = 1, -- genNetworkMagic
            sgNetworkId = networkId globals,
            sgActiveSlotsCoeff = activeSlotVal $ activeSlotCoeff globals,
            sgSecurityParam = securityParameter globals,
            sgEpochLength = runIdentity $ flip epochInfoSize (EpochNo 1) $ epochInfo globals,
            sgSlotsPerKESPeriod = slotsPerKESPeriod globals,
            sgMaxKESEvolutions = maxKESEvo globals,
            sgSlotLength = (secondsToNominalDiffTime 1),
            sgUpdateQuorum = quorum globals,
            sgMaxLovelaceSupply = maxLovelaceSupply globals,
            sgProtocolParams =
              emptyPParams
                { PParams._rho = case boundRational 0.02 of
                    Just rho -> rho
                    Nothing -> error "boundRational 0.02 out of bounds"
                }, -- genPParams
            sgGenDelegs = mempty, --  genGenesisDelegationList
            sgInitialFunds = mempty, -- genFundsList
            sgStaking = emptyGenesisStaking -- genStaking
          }

      elabState = elaborateInitialState sg def genesisAccounts def
   in elaborateBlocks_ globals modelBlocks elabState

-- | Apply a list of ModelEpoch's to an empty ledger, then check the resulting
-- ledger against a user supplied predicate.
testChainModelInteractionWith ::
  ( Testable prop,
    ElaborateEraModel era,
    Default (AdditionalGenesisConfig era),
    Show (PredicateFailure (Core.EraRule "LEDGER" era)),
    Show (Core.Value era)
  ) =>
  proxy era ->
  (NewEpochState era -> EraElaboratorState era -> prop) ->
  [(ModelUTxOId, ModelAddress', Coin)] ->
  [ModelEpoch AllModelFeatures] ->
  Property
testChainModelInteractionWith proxy p a = filterChainModelProp proxy $ \b ->
  let (result, (nes, ees)) = chainModelInteractionWith proxy a b
   in case result of
        Right () -> property $! p nes ees
        Left bad -> counterexample (show bad) False

compareLists :: forall a. (Show a, Eq a) => [a] -> [a] -> Property
compareLists a b = case nub a \\ nub b of
  [] -> property True
  _ -> a === b

-- | Apply a list of ModelEpoch's to an empty ledger, then check the resulting
-- error is the one predicted by the model.
testChainModelInteractionRejection ::
  forall era proxy.
  ( ElaborateEraModel era,
    Default (AdditionalGenesisConfig era),
    Eq (PredicateFailure (Core.EraRule "LEDGER" era)),
    Show (PredicateFailure (Core.EraRule "LEDGER" era)),
    Show (Core.Value era)
  ) =>
  proxy era ->
  ModelPredicateFailure (EraFeatureSet era) ->
  [(ModelUTxOId, ModelAddress', Coin)] ->
  [ModelEpoch AllModelFeatures] ->
  Property
testChainModelInteractionRejection proxy e a = filterChainModelProp proxy $ \b ->
  let (result, (nes, ees)) = chainModelInteractionWith proxy a b
   in case result of
        Left e' ->
          let elaboratedError' = toEraPredicateFailure @era e (nes, ees)
           in case elaboratedError' of
                Left bad -> counterexample ("couldn't elaborate expected error:" <> show bad) False
                Right elaboratedError -> case (e', elaboratedError) of
                  (bad@(ElaborateBlockError_Fee {}), _) -> counterexample (show bad) False
                  (bad@(ElaborateBlockError_TxValue {}), _) -> counterexample (show bad) False
                  (ElaborateBlockError_ApplyTx (ApplyTxError te), ApplyBlockTransitionError_Tx (ApplyTxError te')) ->
                    compareLists te te'
        -- fallthrough if/when more error types are added
        -- (te, te') -> te === te'

        Right _ -> counterexample "no error encountered" False

-- | Apply a list of ModelEpoch's to an empty ledger, and fail if there was an
-- error
testChainModelInteraction ::
  ( Show (PredicateFailure (Core.EraRule "LEDGER" era)),
    ElaborateEraModel era,
    Default (AdditionalGenesisConfig era),
    Show (Core.Value era)
  ) =>
  proxy era ->
  [(ModelUTxOId, ModelAddress', Coin)] ->
  [ModelEpoch AllModelFeatures] ->
  Property
testChainModelInteraction proxy = testChainModelInteractionWith proxy $ (\x y -> x `seq` y `seq` True)

type AllScriptFeatures = ('TyScriptFeature 'True 'True)

type AllModelFeatures = 'FeatureSet 'ExpectAnyOutput AllScriptFeatures

filterChainModelProp ::
  forall era proxy.
  (ElaborateEraModel era) =>
  proxy era ->
  ([ModelEpoch (EraFeatureSet era)] -> Property) ->
  [ModelEpoch AllModelFeatures] ->
  Property
filterChainModelProp proxy f xs =
  case traverse (filterFeatures (eraFeatureSet proxy)) xs of
    Nothing -> cover 0 True "feature absent in era" True -- todo, is there a nice way to report these?
    Just xs' -> f xs'

-- | helper to produce a "blank" ModelTx with most fields set to a reasonable
-- "default"
modelTx :: forall (era :: FeatureSet). KnownRequiredFeatures era => ModelTxId -> ModelTx era
modelTx txId =
  ModelTx
    { _mtxId = txId,
      _mtxInputs = Set.empty,
      _mtxOutputs = [],
      _mtxFee = ModelValue $ ModelValue_Inject $ Coin 0,
      _mtxDCert = [],
      _mtxWdrl = Map.empty,
      _mtxMint = case reifyRequiredFeatures (Proxy :: Proxy era) of
        FeatureTag v _ -> case v of
          ValueFeatureTag_AdaOnly -> NoMintSupport ()
          ValueFeatureTag_AnyOutput -> SupportsMint $ ModelValue $ ModelValue_Inject $ Coin 0,
      _mtxCollateral = mapSupportsPlutus (const $ Set.empty) $ reifySupportsPlutus (Proxy :: Proxy (ScriptFeature era))
    }
