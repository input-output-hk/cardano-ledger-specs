{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{- We disable warnings for name shadowing because of
https://gitlab.haskell.org/ghc/ghc/-/issues/14630, which means that we get
shadowing warnings for the named field puns when used with a pattern synonym.
-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Cardano.Ledger.Mary.Translation where

import Cardano.Binary
  ( DecoderError,
    decodeAnnotator,
    fromCBOR,
    serialize,
  )
import Cardano.Ledger.Allegra (AllegraEra)
import Cardano.Ledger.Compactible (Compactible (..))
import Cardano.Ledger.Crypto (Crypto)
import Cardano.Ledger.Era hiding (Crypto)
import Cardano.Ledger.Mary (MaryEra)
import Cardano.Ledger.Mary.Value (Value (..))
import Cardano.Ledger.ShelleyMA.AuxiliaryData
  ( AuxiliaryData (..),
    pattern AuxiliaryData,
  )
import qualified Cardano.Ledger.Val as Val
import Control.Monad.Except (throwError)
import Data.Coerce (coerce)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Shelley.Spec.Ledger.API hiding (Metadata, TxBody)
import Shelley.Spec.Ledger.EpochBoundary (translateSnapShots)
import Shelley.Spec.Ledger.Tx (decodeWits)

--------------------------------------------------------------------------------
-- Translation from Allegra to Mary
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

type instance PreviousEra (MaryEra c) = AllegraEra c

-- | Currently no context is needed to translate from Allegra to Mary.
--
-- Note: if context is needed, please coordinate with consensus, who will have
-- to provide the context in the right place.
type instance TranslationContext (MaryEra c) = ()

instance Crypto c => TranslateEra (MaryEra c) NewEpochState where
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

instance Crypto c => TranslateEra (MaryEra c) Tx where
  type TranslationError (MaryEra c) Tx = DecoderError
  translateEra _ctx tx =
    case decodeAnnotator "tx" fromCBOR (serialize tx) of
      Right newTx -> pure newTx
      Left decoderError -> throwError decoderError

-- TODO when a genesis has been introduced for Mary, this instance can be
-- removed.
instance Crypto c => TranslateEra (MaryEra c) ShelleyGenesis where
  translateEra ctxt genesis =
    return
      ShelleyGenesis
        { sgSystemStart = sgSystemStart genesis,
          sgNetworkMagic = sgNetworkMagic genesis,
          sgNetworkId = sgNetworkId genesis,
          sgActiveSlotsCoeff = sgActiveSlotsCoeff genesis,
          sgSecurityParam = sgSecurityParam genesis,
          sgEpochLength = sgEpochLength genesis,
          sgSlotsPerKESPeriod = sgSlotsPerKESPeriod genesis,
          sgMaxKESEvolutions = sgMaxKESEvolutions genesis,
          sgSlotLength = sgSlotLength genesis,
          sgUpdateQuorum = sgUpdateQuorum genesis,
          sgMaxLovelaceSupply = sgMaxLovelaceSupply genesis,
          sgProtocolParams = translateEra' ctxt (sgProtocolParams genesis),
          sgGenDelegs = sgGenDelegs genesis,
          sgInitialFunds = sgInitialFunds genesis,
          sgStaking = sgStaking genesis
        }

--------------------------------------------------------------------------------
-- Auxiliary instances and functions
--------------------------------------------------------------------------------

instance (Crypto c, Functor f) => TranslateEra (MaryEra c) (PParams' f)

instance Crypto c => TranslateEra (MaryEra c) EpochState where
  translateEra ctxt es =
    return
      EpochState
        { esAccountState = esAccountState es,
          esSnapshots = translateSnapShots (esSnapshots es),
          esLState = translateEra' ctxt $ esLState es,
          esPrevPp = translateEra' ctxt $ esPrevPp es,
          esPp = translateEra' ctxt $ esPp es,
          esNonMyopic = esNonMyopic es
        }

instance Crypto c => TranslateEra (MaryEra c) LedgerState where
  translateEra ctxt ls =
    return
      LedgerState
        { _utxoState = translateEra' ctxt $ _utxoState ls,
          _delegationState = _delegationState ls
        }

instance Crypto c => TranslateEra (MaryEra c) ProposedPPUpdates where
  translateEra ctxt (ProposedPPUpdates ppup) =
    return $ ProposedPPUpdates $ Map.map (translateEra' ctxt) ppup

instance Crypto c => TranslateEra (MaryEra c) PPUPState where
  translateEra ctxt ps =
    return
      PPUPState
        { proposals = translateEra' ctxt $ proposals ps,
          futureProposals = translateEra' ctxt $ futureProposals ps
        }

instance Crypto c => TranslateEra (MaryEra c) UTxOState where
  translateEra ctxt us =
    return
      UTxOState
        { _utxo = translateEra' ctxt $ _utxo us,
          _deposited = _deposited us,
          _fees = _fees us,
          _ppups = translateEra' ctxt $ _ppups us
        }

instance Crypto c => TranslateEra (MaryEra c) TxOut where
  translateEra () (TxOutCompact addr cfval) =
    pure $ TxOutCompact (coerce addr) (translateCompactValue cfval)

instance Crypto c => TranslateEra (MaryEra c) UTxO where
  translateEra ctxt utxo =
    return $ UTxO $ Map.map (translateEra' ctxt) $ unUTxO utxo

instance Crypto c => TranslateEra (MaryEra c) WitnessSet where
  type TranslationError (MaryEra c) WitnessSet = DecoderError
  translateEra _ctx ws =
    case decodeAnnotator "witnessSet" decodeWits (serialize ws) of
      Right new -> pure new
      Left decoderError -> throwError decoderError

instance Crypto c => TranslateEra (MaryEra c) Update where
  translateEra _ (Update pp en) = pure $ Update (coerce pp) en

instance Crypto c => TranslateEra (MaryEra c) AuxiliaryData where
  translateEra _ (AuxiliaryData md as) =
    pure $ AuxiliaryData md as

translateValue :: Crypto c => Coin -> Value c
translateValue = Val.inject

translateCompactValue :: Crypto c => CompactForm Coin -> CompactForm (Value c)
translateCompactValue =
  fromMaybe (error msg) . toCompact . translateValue . fromCompact
  where
    msg = "impossible error: compact coin is out of range"
