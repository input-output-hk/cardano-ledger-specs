{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fmax-relevant-binds=0 #-}

module Test.Cardano.Ledger.Elaborators.Alonzo where

import qualified Cardano.Crypto.DSIGN.Class as DSIGN
import qualified Cardano.Crypto.KES.Class as KES
import Cardano.Crypto.Util (SignableRepresentation)
import Cardano.Ledger.Alonzo (AlonzoEra)
import Cardano.Ledger.Alonzo.Genesis (AlonzoGenesis (..))
import Cardano.Ledger.Alonzo.Language (Language (..))
import Cardano.Ledger.Alonzo.Rules.Utxo
import Cardano.Ledger.Alonzo.Rules.Utxow
import Cardano.Ledger.Alonzo.Scripts (ExUnits (..), Prices (..))
import qualified Cardano.Ledger.Alonzo.Scripts as Alonzo
import Cardano.Ledger.Alonzo.Translation ()
import qualified Cardano.Ledger.Alonzo.Tx as Alonzo
import qualified Cardano.Ledger.Alonzo.TxBody as Alonzo
import qualified Cardano.Ledger.Alonzo.TxWitness as Alonzo
import Cardano.Ledger.BaseTypes (boundRational)
import Cardano.Ledger.Coin
import Cardano.Ledger.Crypto (DSIGN, KES)
import Cardano.Ledger.ShelleyMA.Timelocks (ValidityInterval (..))
import qualified Control.Monad.Except as Except
import qualified Control.Monad.Trans.State as State hiding (state)
import Data.Default.Class
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Data.Maybe.Strict (StrictMaybe (..))
import qualified Data.Set as Set
import Shelley.Spec.Ledger.API.Mempool (ApplyTxError (..))
import Shelley.Spec.Ledger.API.Protocol (PraosCrypto)
import qualified Shelley.Spec.Ledger.LedgerState as LedgerState
import Shelley.Spec.Ledger.STS.Ledger
import Shelley.Spec.Ledger.STS.Utxow
import Test.Cardano.Ledger.Elaborators
import Test.Cardano.Ledger.Examples.TwoPhaseValidation (freeCostModel)
import Test.Cardano.Ledger.ModelChain
import Test.Cardano.Ledger.ModelChain.FeatureSet
import Test.Cardano.Ledger.ModelChain.Value

instance Default AlonzoGenesis where
  def =
    AlonzoGenesis
      { coinsPerUTxOWord = Coin 10000,
        costmdls = Map.fromSet (const freeCostModel) $ Set.fromList [minBound ..],
        prices = Prices (fromJust $ boundRational 1000) (fromJust $ boundRational 1000),
        maxTxExUnits = ExUnits 100 100,
        maxBlockExUnits = ExUnits 100 100,
        maxValSize = 100000,
        collateralPercentage = 100,
        maxCollateralInputs = 100
      }

instance
  ( PraosCrypto crypto,
    KES.Signable (KES crypto) ~ SignableRepresentation,
    DSIGN.Signable (DSIGN crypto) ~ SignableRepresentation
  ) =>
  ElaborateEraModel (AlonzoEra crypto)
  where
  type EraFeatureSet (AlonzoEra crypto) = 'FeatureSet 'ExpectAnyOutput ('TyScriptFeature 'True 'True)
  eraFeatureSet _ = FeatureTag ValueFeatureTag_AnyOutput ScriptFeatureTag_PlutusV1

  reifyValueConstraint = ExpectedValueTypeC_MA

  toEraPredicateFailure = \case
    ModelValueNotConservedUTxO (ModelValue x) (ModelValue y) -> State.evalState $
      Except.runExceptT $ do
        x' <- Except.ExceptT $ evalModelValue (lookupModelValue noScriptAction) x
        y' <- Except.ExceptT $ evalModelValue (lookupModelValue noScriptAction) y
        pure $
          ApplyBlockTransitionError_Tx $
            ApplyTxError
              [ UtxowFailure
                  ( WrappedShelleyEraFailure
                      (UtxoFailure (ValueNotConservedUTxO x' y'))
                  )
              ]

  makeTimelockScript _ (SupportsTimelock x) = Alonzo.TimelockScript x
  makePlutusScript _ (SupportsPlutus x) = x -- Alonzo.PlutusScript
  makeExtendedTxOut _ (Alonzo.TxOut a v _) (SupportsPlutus dh) = Alonzo.TxOut a v (SJust dh)

  makeTxBody nes (TxBodyArguments maxTTL fee ins outs dcerts wdrl (SupportsMint mint) (SupportsPlutus redeemers) (SupportsPlutus cins)) =
    Alonzo.TxBody
      { Alonzo.inputs = ins,
        Alonzo.collateral = cins,
        Alonzo.outputs = outs,
        Alonzo.txcerts = dcerts,
        Alonzo.txwdrls = wdrl,
        Alonzo.txfee = fee,
        Alonzo.txvldt = ValidityInterval SNothing $ SJust (1 + maxTTL),
        Alonzo.txUpdates = SNothing,
        Alonzo.reqSignerHashes = Set.empty,
        Alonzo.mint = mint,
        Alonzo.wppHash = redeemers >>= uncurry (Alonzo.hashWitnessPPData (LedgerState.esPp . LedgerState.nesEs $ nes) (Set.singleton PlutusV1)),
        Alonzo.adHash = SNothing,
        Alonzo.txnetworkid = SNothing -- SJust Testnet
      }

  makeTx _ realTxBody (TxWitnessArguments wits (SupportsScript ScriptFeatureTag_PlutusV1 scripts) (SupportsPlutus (rdmr, dats))) =
    let witSet =
          Alonzo.TxWitness
            { Alonzo.txwitsVKey = wits,
              Alonzo.txwitsBoot = Set.empty,
              Alonzo.txscripts = scripts,
              Alonzo.txdats = dats,
              Alonzo.txrdmrs = rdmr
            }
     in (Alonzo.ValidatedTx realTxBody witSet (Alonzo.IsValidating True) SNothing)
