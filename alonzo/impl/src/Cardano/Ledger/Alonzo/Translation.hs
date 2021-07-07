{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Cardano.Ledger.Alonzo.Translation where

import Cardano.Binary
  ( DecoderError,
    FromCBOR (..),
    ToCBOR (..),
    decodeAnnotator,
    serialize,
  )
import Cardano.Ledger.Alonzo (AlonzoEra)
import Cardano.Ledger.Alonzo.Genesis (AlonzoGenesis (..), extendPPWithGenesis)
import Cardano.Ledger.Alonzo.PParams (PParams, PParamsUpdate, extendPP)
import Cardano.Ledger.Alonzo.Tx (IsValidating (..), ValidatedTx (..))
import Cardano.Ledger.Alonzo.TxBody (TxOut (..))
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Crypto (Crypto)
import Cardano.Ledger.Era
  ( PreviousEra,
    TranslateEra (..),
    TranslationContext,
    translateEra',
  )
import qualified Cardano.Ledger.Era as Era
import Cardano.Ledger.Mary (MaryEra)
import qualified Cardano.Ledger.Tx as LTX
import Control.Monad.Except (Except, throwError)
import Data.Coders
import Data.Text (Text)
import Shelley.Spec.Ledger.API
  ( EpochState (..),
    NewEpochState (..),
    ShelleyGenesis,
    StrictMaybe (..),
  )
import qualified Shelley.Spec.Ledger.API as API
import Shelley.Spec.Ledger.EpochBoundary (translateSnapShots)
import qualified Shelley.Spec.Ledger.PParams as Shelley
import qualified Shelley.Spec.Ledger.TxBody as Shelley

--------------------------------------------------------------------------------
-- Translation from Mary to Alonzo
--
-- The instances below are needed by the consensus layer. Do not remove any of
-- them without coordinating with consensus.
--
-- Please add auxiliary instances and other declarations at the bottom of this
-- module, not in the list below so that it remains clear which instances the
-- consensus layer needs.
--
-- WARNING: when a translation instance currently uses the default
-- 'TranslationError', i.e., 'Void', it means the consensus layer relies on it
-- being total. Do not change it!
--------------------------------------------------------------------------------

type instance PreviousEra (AlonzoEra c) = MaryEra c

type instance TranslationContext (AlonzoEra c) = AlonzoGenesis

instance
  (Crypto c) =>
  TranslateEra (AlonzoEra c) NewEpochState
  where
  translateEra ctxt nes =
    return $
      NewEpochState
        { nesEL = nesEL nes,
          nesBprev = nesBprev nes,
          nesBcur = nesBcur nes,
          nesEs = translateEra' ctxt $ nesEs nes,
          nesRu = nesRu nes,
          nesPd = nesPd nes
        }

instance Crypto c => TranslateEra (AlonzoEra c) Core.Tx where
  type TranslationError (AlonzoEra c) Core.Tx = DecoderError
  translateEra _ctx tx =
    case decodeAnnotator "tx" fromCBOR (serialize tx) of
      Right newTx -> pure newTx
      Left decoderError -> throwError decoderError

instance Crypto c => TranslateEra (AlonzoEra c) ShelleyGenesis where
  translateEra ctxt genesis =
    return
      API.ShelleyGenesis
        { API.sgSystemStart = API.sgSystemStart genesis,
          API.sgNetworkMagic = API.sgNetworkMagic genesis,
          API.sgNetworkId = API.sgNetworkId genesis,
          API.sgActiveSlotsCoeff = API.sgActiveSlotsCoeff genesis,
          API.sgSecurityParam = API.sgSecurityParam genesis,
          API.sgEpochLength = API.sgEpochLength genesis,
          API.sgSlotsPerKESPeriod = API.sgSlotsPerKESPeriod genesis,
          API.sgMaxKESEvolutions = API.sgMaxKESEvolutions genesis,
          API.sgSlotLength = API.sgSlotLength genesis,
          API.sgUpdateQuorum = API.sgUpdateQuorum genesis,
          API.sgMaxLovelaceSupply = API.sgMaxLovelaceSupply genesis,
          API.sgProtocolParams = translateEra' ctxt (API.sgProtocolParams genesis),
          API.sgGenDelegs = API.sgGenDelegs genesis,
          API.sgInitialFunds = API.sgInitialFunds genesis,
          API.sgStaking = API.sgStaking genesis
        }

newtype TxInBlock era = TxInBlock {unTxInBlock :: (Era.TxInBlock era)}

instance
  ( Crypto c,
    Era.TxInBlock (AlonzoEra c) ~ ValidatedTx (AlonzoEra c)
  ) =>
  TranslateEra (AlonzoEra c) TxInBlock
  where
  type TranslationError (AlonzoEra c) TxInBlock = DecoderError
  translateEra _ctxt (TxInBlock tx) = do
    -- Note that this does not preserve the hidden bytes field of the transaction.
    -- This is under the premise that this is irrelevant for TxInBlocks, which are
    -- not transmitted as contiguous chunks.
    bdy <- translateViaCBORAnn "txbody" $ LTX.body tx
    txwits <- translateViaCBORAnn "txwitness" $ LTX.wits tx
    -- transactions from Mary era always pass script ("phase 2") validation
    aux <- case LTX.auxiliaryData tx of
      SNothing -> pure SNothing
      SJust axd -> SJust <$> translateViaCBORAnn "auxiliarydata" axd
    let validating = IsValidating True
    pure $ TxInBlock $ ValidatedTx bdy txwits validating aux

--------------------------------------------------------------------------------
-- Auxiliary instances and functions
--------------------------------------------------------------------------------

translateViaCBORAnn :: (ToCBOR a, FromCBOR (Annotator b)) => Text -> a -> Except DecoderError b
translateViaCBORAnn name x =
  case decodeAnnotator name fromCBOR (serialize x) of
    Right newx -> pure newx
    Left decoderError -> throwError decoderError

instance (Crypto c, Functor f) => TranslateEra (AlonzoEra c) (API.PParams' f)

instance Crypto c => TranslateEra (AlonzoEra c) EpochState where
  translateEra ctxt es =
    return
      EpochState
        { esAccountState = esAccountState es,
          esSnapshots = translateSnapShots (esSnapshots es),
          esLState = translateEra' ctxt $ esLState es,
          esPrevPp = translatePParams ctxt $ esPrevPp es,
          esPp = translatePParams ctxt $ esPp es,
          esNonMyopic = esNonMyopic es
        }

instance Crypto c => TranslateEra (AlonzoEra c) API.LedgerState where
  translateEra ctxt ls =
    return
      API.LedgerState
        { API._utxoState = translateEra' ctxt $ API._utxoState ls,
          API._delegationState = API._delegationState ls
        }

instance Crypto c => TranslateEra (AlonzoEra c) API.UTxOState where
  translateEra ctxt us =
    return
      API.UTxOState
        { API._utxo = translateEra' ctxt $ API._utxo us,
          API._deposited = API._deposited us,
          API._fees = API._fees us,
          API._ppups = translateEra' ctxt $ API._ppups us
        }

instance Crypto c => TranslateEra (AlonzoEra c) API.UTxO where
  translateEra _ctxt utxo =
    return $ API.UTxO $ fmap translateTxOut $ API.unUTxO utxo

instance Crypto c => TranslateEra (AlonzoEra c) API.PPUPState where
  translateEra ctxt ps =
    return
      API.PPUPState
        { API.proposals = translateEra' ctxt $ API.proposals ps,
          API.futureProposals = translateEra' ctxt $ API.futureProposals ps
        }

instance Crypto c => TranslateEra (AlonzoEra c) API.ProposedPPUpdates where
  translateEra _ctxt (API.ProposedPPUpdates ppup) =
    return $ API.ProposedPPUpdates $ fmap translatePParamsUpdate ppup

translateTxOut ::
  Core.TxOut (MaryEra c) -> Core.TxOut (AlonzoEra c)
translateTxOut (Shelley.TxOutCompact addr value) =
  TxOutCompact addr value SNothing

-- extendPP with type: extendPP :: Shelley.PParams' f era1 -> ... -> PParams' f era2
-- Is general enough to work for both
-- (PParams era)       = (PParams' Identity era)    and
-- (PParamsUpdate era) = (PParams' StrictMaybe era)

translatePParams ::
  AlonzoGenesis -> Shelley.PParams (MaryEra c) -> PParams (AlonzoEra c)
translatePParams = flip extendPPWithGenesis

translatePParamsUpdate ::
  Shelley.PParamsUpdate (MaryEra c) -> PParamsUpdate (AlonzoEra c)
translatePParamsUpdate pp =
  extendPP pp SNothing SNothing SNothing SNothing SNothing SNothing SNothing SNothing
