{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

-- | Pre-generated items to use in traces.
--
--   Functions in this module make specific assumptions about the sets of keys
--   involved, and thus cannot be used as generic generators.
module Test.Shelley.Spec.Ledger.Generator.Presets
  ( coreNodeKeys,
    keySpace,
    genEnv,
    genesisDelegs0,
    someKeyPairs,
    keyPairs,
    scriptSpace,
  )
where

import qualified Cardano.Ledger.Crypto as CC (Crypto)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Word (Word64)
import Cardano.Ledger.Keys
  ( GenDelegPair (..),
    KeyHash,
    KeyPair (..),
    KeyRole (..),
    coerceKeyRole,
    hashKey,
    hashVerKeyVRF,
  )
import Shelley.Spec.Ledger.OCert (KESPeriod (..))
import Test.Shelley.Spec.Ledger.Generator.Constants
  ( Constants (..),
    defaultConstants,
  )
import Test.Shelley.Spec.Ledger.Generator.Core
import Test.Shelley.Spec.Ledger.Generator.ScriptClass(keyPairs)
import Test.Shelley.Spec.Ledger.Utils
  ( maxKESIterations,
    mkKESKeyPair,
    mkVRFKeyPair,
    slotsPerKESIteration,
  )

import Test.Shelley.Spec.Ledger.Generator.EraGen(EraGen(..),allScripts,someKeyPairs)
import Data.Proxy(Proxy(..))
import Cardano.Ledger.Era (ValidateScript(hashScript))

-- =================================================================

-- | Example generator environment, consisting of default constants and an
-- corresponding keyspace.
genEnv :: forall era.
  (EraGen era) =>
  Proxy era ->
  GenEnv era
genEnv _ =
  GenEnv
    (keySpace defaultConstants)
    (scriptSpace @era (genEraTwoPhase3Arg @era)  (genEraTwoPhase2Arg @era))
    defaultConstants

-- | An Example Script space for use in Trace generators
scriptSpace :: forall era. ValidateScript era => [TwoPhase3ArgInfo era] -> [TwoPhase2ArgInfo era] -> ScriptSpace era
scriptSpace scripts3 scripts2  =
   ScriptSpace scripts3
               scripts2
               (Map.fromList [(hashScript @era (getScript3 s),s) | s <- scripts3])
               (Map.fromList [(hashScript @era (getScript2 s),s) | s <- scripts2])

-- | Example keyspace for use in generators
keySpace ::
  forall era.
  EraGen era =>
  Constants ->
  KeySpace era
keySpace c =
  KeySpace
    (coreNodeKeys c)
    (genesisDelegates c)
    (stakePoolKeys c)
    (keyPairs c)
    (allScripts @era c)

-- Pairs of (genesis key, node keys)
--
-- NOTE: we use a seed range in the [1000...] range
-- to create keys that don't overlap with any of the other generated keys
coreNodeKeys ::
  CC.Crypto crypto =>
  Constants ->
  [(KeyPair 'Genesis crypto, AllIssuerKeys crypto 'GenesisDelegate)]
coreNodeKeys c@Constants {numCoreNodes} =
  [ ( (toKeyPair . mkGenKey) (RawSeed x 0 0 0 0),
      issuerKeys c 0 x
    )
    | x <- [1001 .. 1000 + numCoreNodes]
  ]
  where
    toKeyPair (sk, vk) = KeyPair vk sk

-- Pre-generate a set of keys to use for genesis delegates.
genesisDelegates :: CC.Crypto crypto => Constants -> [AllIssuerKeys crypto 'GenesisDelegate]
genesisDelegates c =
  [ issuerKeys c 20 x
    | x <- [0 .. 50]
  ]

-- Pre-generate a set of keys to use for stake pools.
stakePoolKeys :: CC.Crypto crypto => Constants -> [AllIssuerKeys crypto 'StakePool]
stakePoolKeys c =
  [ issuerKeys c 10 x
    | x <- [0 .. 50]
  ]

-- | Generate all keys for any entity which will be issuing blocks.
issuerKeys ::
  (CC.Crypto crypto) =>
  Constants ->
  -- | Namespace parameter. Can be used to differentiate between different
  --   "types" of issuer.
  Word64 ->
  Word64 ->
  AllIssuerKeys crypto r
issuerKeys Constants {maxSlotTrace} ns x =
  let (skCold, vkCold) = mkKeyPair (RawSeed x 0 0 0 (ns + 1))
   in AllIssuerKeys
        { cold = KeyPair vkCold skCold,
          hot =
            [ ( KESPeriod (fromIntegral (iter * fromIntegral maxKESIterations)),
                mkKESKeyPair (RawSeed x 0 0 (fromIntegral iter) (ns + 3))
              )
              | iter <-
                  [ 0
                    .. ( 1
                           + div
                             maxSlotTrace
                             ( fromIntegral
                                 (maxKESIterations * slotsPerKESIteration)
                             )
                       )
                  ]
            ],
          vrf = mkVRFKeyPair (RawSeed x 0 0 0 (ns + 2)),
          hk = hashKey vkCold
        }

genesisDelegs0 ::
  CC.Crypto crypto =>
  Constants ->
  Map (KeyHash 'Genesis crypto) (GenDelegPair crypto)
genesisDelegs0 c =
  Map.fromList
    [ ( hashVKey gkey,
        GenDelegPair
          (coerceKeyRole $ hashVKey (cold pkeys))
          (hashVerKeyVRF . snd . vrf $ pkeys)
      )
      | (gkey, pkeys) <- coreNodeKeys c
    ]
  where
    hashVKey = hashKey . vKey
