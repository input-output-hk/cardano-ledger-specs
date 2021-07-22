{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Test.Cardano.Ledger.Elaborators.Shelley where

import qualified Cardano.Crypto.DSIGN.Class as DSIGN
import qualified Cardano.Crypto.KES.Class as KES
import Cardano.Crypto.Util (SignableRepresentation)
import Cardano.Ledger.Crypto (DSIGN, KES)
import Cardano.Ledger.Shelley (ShelleyEra)
import qualified Control.Monad.Except as Except
import qualified Control.Monad.Trans.State as State hiding (state)
import Data.Maybe.Strict (StrictMaybe (..))
import Data.Void
import Shelley.Spec.Ledger.API.Mempool (ApplyTxError (..))
import Shelley.Spec.Ledger.API.Protocol (PraosCrypto)
import Shelley.Spec.Ledger.STS.EraMapping ()
import Shelley.Spec.Ledger.STS.Ledger (LedgerPredicateFailure (..))
import Shelley.Spec.Ledger.STS.Utxo (UtxoPredicateFailure (..))
import Shelley.Spec.Ledger.STS.Utxow (UtxowPredicateFailure (..))
import qualified Shelley.Spec.Ledger.Tx as Shelley
import Test.Cardano.Ledger.Elaborators
import Test.Cardano.Ledger.ModelChain
import Test.Cardano.Ledger.ModelChain.FeatureSet
import Test.Cardano.Ledger.ModelChain.Value

instance
  ( PraosCrypto crypto,
    KES.Signable (KES crypto) ~ SignableRepresentation,
    DSIGN.Signable (DSIGN crypto) ~ SignableRepresentation
  ) =>
  ElaborateEraModel (ShelleyEra crypto)
  where
  type EraFeatureSet (ShelleyEra crypto) = 'FeatureSet 'ExpectAdaOnly ('TyScriptFeature 'False 'False)
  eraFeatureSet _ = FeatureTag ValueFeatureTag_AdaOnly ScriptFeatureTag_None

  reifyValueConstraint = ExpectedValueTypeC_Simple

  makeTimelockScript _ (NoTimelockSupport x) = absurd x
  makePlutusScript _ (NoPlutusSupport x) = absurd x
  makeExtendedTxOut _ _ (NoPlutusSupport x) = absurd x

  toEraPredicateFailure = \case
    ModelValueNotConservedUTxO (ModelValue x) (ModelValue y) -> State.evalState $
      Except.runExceptT $ do
        x' <- Except.ExceptT $ evalModelValue (lookupModelValue noScriptAction) x
        y' <- Except.ExceptT $ evalModelValue (lookupModelValue noScriptAction) y
        pure $
          ApplyBlockTransitionError_Tx $
            ApplyTxError
              [UtxowFailure (UtxoFailure (ValueNotConservedUTxO x' y'))]

  makeTxBody _ (TxBodyArguments maxTTL fee ins outs dcerts wdrl (NoMintSupport ()) (NoPlutusSupport ()) (NoPlutusSupport ())) =
    Shelley.TxBody
      { Shelley._inputs = ins,
        Shelley._outputs = outs,
        Shelley._certs = dcerts,
        Shelley._wdrls = wdrl,
        Shelley._txfee = fee,
        Shelley._ttl = maxTTL,
        Shelley._txUpdate = SNothing,
        Shelley._mdHash = SNothing
      }

  makeTx _ realTxBody (TxWitnessArguments wits (NoScriptSupport ()) (NoPlutusSupport ())) =
    Shelley.Tx realTxBody (mempty {Shelley.addrWits = wits}) SNothing
