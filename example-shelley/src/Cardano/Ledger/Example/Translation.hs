{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{- We disable warnings for name shadowing because of
https://gitlab.haskell.org/ghc/ghc/-/issues/14630, which means that we get
shadowing warnings for the named field puns when used with a pattern synonym.
-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Cardano.Ledger.Example.Translation where

import Cardano.Binary
  ( DecoderError,
    decodeAnnotator,
    fromCBOR,
    serialize,
  )
import Cardano.Ledger.Crypto (Crypto)
import Cardano.Ledger.Era hiding (Crypto)
import Cardano.Ledger.Example (ExampleEra)
import Cardano.Ledger.Shelley (ShelleyEra)
import Control.Monad.Except (throwError)
import Data.Coerce (coerce)
import qualified Data.Map.Strict as Map
import Shelley.Spec.Ledger.API
import Shelley.Spec.Ledger.EpochBoundary (translateSnapShots)
import Shelley.Spec.Ledger.PParams ()
import Shelley.Spec.Ledger.Tx (decodeWits)

--------------------------------------------------------------------------------
-- Translation from Shelley to Example
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

type instance PreviousEra (ExampleEra c) = ShelleyEra c

-- | Currently no context is needed to translate from Shelley to Example.

-- Note: if context is needed, please coordinate with consensus, who will have
-- to provide the context in the right place.
type instance TranslationContext (ExampleEra c) = ()

instance Crypto c => TranslateEra (ExampleEra c) NewEpochState where
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

instance forall c. Crypto c => TranslateEra (ExampleEra c) Tx where
  type TranslationError (ExampleEra c) Tx = DecoderError
  translateEra _ctx tx =
    case decodeAnnotator "tx" fromCBOR (serialize tx) of
      Right newTx -> pure newTx
      Left decoderError -> throwError decoderError

instance Crypto c => TranslateEra (ExampleEra c) ShelleyGenesis where
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

instance Crypto c => TranslateEra (ExampleEra c) (PParams' f) where
  translateEra _ pp =
    return $
      PParams
        { _minfeeA = _minfeeA pp,
          _minfeeB = _minfeeB pp,
          _maxBBSize = _maxBBSize pp,
          _maxTxSize = _maxTxSize pp,
          _maxBHSize = _maxBHSize pp,
          _keyDeposit = _keyDeposit pp,
          _poolDeposit = _poolDeposit pp,
          _eMax = _eMax pp,
          _nOpt = _nOpt pp,
          _a0 = _a0 pp,
          _rho = _rho pp,
          _tau = _tau pp,
          _d = _d pp,
          _extraEntropy = _extraEntropy pp,
          _protocolVersion = _protocolVersion pp,
          _minUTxOValue = _minUTxOValue pp,
          _minPoolCost = _minPoolCost pp
        }

instance Crypto c => TranslateEra (ExampleEra c) ProposedPPUpdates where
  translateEra ctxt (ProposedPPUpdates ppup) =
    return $ ProposedPPUpdates $ Map.map (translateEra' ctxt) ppup

instance Crypto c => TranslateEra (ExampleEra c) PPUPState where
  translateEra ctxt ps =
    return
      PPUPState
        { proposals = translateEra' ctxt $ proposals ps,
          futureProposals = translateEra' ctxt $ futureProposals ps
        }

instance Crypto c => TranslateEra (ExampleEra c) TxOut where
  translateEra () (TxOutCompact addr cfval) =
    pure $ TxOutCompact (coerce addr) cfval

instance Crypto c => TranslateEra (ExampleEra c) UTxO where
  translateEra ctxt utxo =
    return $ UTxO $ Map.map (translateEra' ctxt) $ unUTxO utxo

instance Crypto c => TranslateEra (ExampleEra c) UTxOState where
  translateEra ctxt us =
    return
      UTxOState
        { _utxo = translateEra' ctxt $ _utxo us,
          _deposited = _deposited us,
          _fees = _fees us,
          _ppups = translateEra' ctxt $ _ppups us
        }

instance Crypto c => TranslateEra (ExampleEra c) LedgerState where
  translateEra ctxt ls =
    return
      LedgerState
        { _utxoState = translateEra' ctxt $ _utxoState ls,
          _delegationState = _delegationState ls
        }

instance Crypto c => TranslateEra (ExampleEra c) EpochState where
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

instance Crypto c => TranslateEra (ExampleEra c) WitnessSet where
  type TranslationError (ExampleEra c) WitnessSet = DecoderError
  translateEra _ctx ws =
    case decodeAnnotator "witnessSet" decodeWits (serialize ws) of
      Right new -> pure new
      Left decoderError -> throwError decoderError

instance Crypto c => TranslateEra (ExampleEra c) Update where
  translateEra _ (Update pp en) = pure $ Update (coerce pp) en
