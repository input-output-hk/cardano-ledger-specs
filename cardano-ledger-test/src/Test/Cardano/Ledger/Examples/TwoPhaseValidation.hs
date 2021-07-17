{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Test.Cardano.Ledger.Examples.TwoPhaseValidation where

import Cardano.Crypto.DSIGN.Class (Signable)
import qualified Cardano.Crypto.Hash as CH
import Cardano.Crypto.Hash.Class (sizeHash)
import qualified Cardano.Crypto.KES.Class as KES
import Cardano.Crypto.VRF (evalCertified)
import qualified Cardano.Crypto.VRF.Class as VRF
import Cardano.Ledger.Address (Addr (..))
import Cardano.Ledger.Alonzo (AlonzoEra)
import Cardano.Ledger.Alonzo.Data (Data (..), hashData)
import Cardano.Ledger.Alonzo.Language (Language (..))
import Cardano.Ledger.Alonzo.PParams (PParams' (..))
import Cardano.Ledger.Alonzo.PlutusScriptApi (CollectError (..), collectTwoPhaseScriptInputs)
import Cardano.Ledger.Alonzo.Rules.Bbody (AlonzoBBODY, AlonzoBbodyPredFail (..))
import Cardano.Ledger.Alonzo.Rules.Utxo (UtxoPredicateFailure (..))
import Cardano.Ledger.Alonzo.Rules.Utxos (UtxosPredicateFailure (..))
import Cardano.Ledger.Alonzo.Rules.Utxow (AlonzoPredFail (..), AlonzoUTXOW)
import Cardano.Ledger.Alonzo.Scripts
  ( CostModel (..),
    ExUnits (..),
  )
import qualified Cardano.Ledger.Alonzo.Scripts as Tag (Tag (..))
import Cardano.Ledger.Alonzo.Tx
  ( IsValidating (..),
    ScriptPurpose (..),
    ValidatedTx (..),
    hashWitnessPPData,
  )
import Cardano.Ledger.Alonzo.TxInfo (txInfo, valContext)
import Cardano.Ledger.Alonzo.TxWitness (RdmrPtr (..), Redeemers (..), TxDats (..))
import Cardano.Ledger.BaseTypes (Network (..), Seed, StrictMaybe (..), textToUrl)
import Cardano.Ledger.Coin (Coin (..))
import Cardano.Ledger.Core (EraRule)
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Credential
  ( Credential (..),
    StakeCredential,
    StakeReference (..),
  )
import qualified Cardano.Ledger.Crypto as CC
import Cardano.Ledger.Era (Era (..), SupportsSegWit (..), ValidateScript (hashScript))
import Cardano.Ledger.Hashes (EraIndependentTxBody, ScriptHash)
import Cardano.Ledger.Keys
  ( GenDelegs (..),
    KeyHash,
    KeyPair (..),
    KeyRole (..),
    asWitness,
    coerceKeyRole,
    hashKey,
    hashVerKeyVRF,
    signedDSIGN,
    signedKES,
  )
import Cardano.Ledger.Mary.Value (PolicyID (..))
import Cardano.Ledger.SafeHash (hashAnnotated)
import Cardano.Ledger.Serialization (ToCBORGroup)
import Cardano.Ledger.ShelleyMA.Timelocks (ValidityInterval (..))
import Cardano.Ledger.Slot (BlockNo (..))
import qualified Cardano.Ledger.Tx as Core (Tx (..))
import Cardano.Ledger.Val (inject, (<+>))
import Cardano.Slotting.EpochInfo (EpochInfo, fixedEpochInfo)
import Cardano.Slotting.Slot (EpochSize (..), SlotNo (..))
import Cardano.Slotting.Time (SystemStart (..), mkSlotLength)
import Control.State.Transition.Extended hiding (Assertion)
import Control.State.Transition.Trace (checkTrace, (.-), (.->))
import qualified Data.ByteString as BS (replicate)
import Data.Coerce (coerce)
import Data.Default.Class (Default (..))
import Data.Functor.Identity (Identity, runIdentity)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import qualified Data.Sequence.Strict as StrictSeq
import qualified Data.Set as Set
import Data.Time.Clock.POSIX (posixSecondsToUTCTime)
import Numeric.Natural (Natural)
import Plutus.V1.Ledger.Api (defaultCostModelParams)
import qualified Plutus.V1.Ledger.Api as Plutus
import Shelley.Spec.Ledger.API
  ( BHBody (..),
    BHeader (..),
    Block (..),
    DPState (..),
    DState (..),
    KESPeriod (..),
    LedgerState (..),
    Nonce (NeutralNonce),
    OCert (..),
    PoolParams (..),
    PrevHash (GenesisHash),
    ProtVer (..),
    UTxO (..),
  )
import Shelley.Spec.Ledger.BlockChain (bBodySize, mkSeed, seedEta, seedL)
import Shelley.Spec.Ledger.EpochBoundary (BlocksMade (..))
import Shelley.Spec.Ledger.LedgerState (UTxOState (..), WitHashes (..))
import Shelley.Spec.Ledger.OCert (OCertSignable (..))
import Shelley.Spec.Ledger.STS.Bbody (BbodyEnv (..), BbodyPredicateFailure (..), BbodyState (..))
import Shelley.Spec.Ledger.STS.Delegs (DelegsPredicateFailure (..))
import Shelley.Spec.Ledger.STS.Delpl (DelplPredicateFailure (..))
import Shelley.Spec.Ledger.STS.Ledger (LedgerPredicateFailure (..))
import Shelley.Spec.Ledger.STS.Ledgers (LedgersPredicateFailure (..))
import Shelley.Spec.Ledger.STS.Pool (PoolPredicateFailure (..))
import Shelley.Spec.Ledger.STS.Utxo (UtxoEnv (..))
import Shelley.Spec.Ledger.STS.Utxow (UtxowPredicateFailure (..))
import Shelley.Spec.Ledger.TxBody
  ( DCert (..),
    DelegCert (..),
    PoolCert (..),
    PoolMetadata (..),
    RewardAcnt (..),
    TxIn (..),
    Wdrl (..),
  )
import Shelley.Spec.Ledger.UTxO (makeWitnessVKey, txid)
import Test.Cardano.Ledger.Generic.Indexed (theKeyPair)
import Test.Cardano.Ledger.Generic.Proof
import Test.Cardano.Ledger.Generic.Updaters
import Test.Shelley.Spec.Ledger.ConcreteCryptoTypes (C_Crypto)
import Test.Shelley.Spec.Ledger.Generator.EraGen (genesisId)
import Test.Shelley.Spec.Ledger.Utils
  ( RawSeed (..),
    applySTSTest,
    mkKESKeyPair,
    mkKeyPair,
    mkVRFKeyPair,
    runShelleyBase,
    unsafeBoundRational,
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, testCase, (@?=))

-- =======================
-- Setup the initial state
-- =======================

testEpochInfo :: EpochInfo Identity
testEpochInfo = fixedEpochInfo (EpochSize 100) (mkSlotLength 1)

testSystemStart :: SystemStart
testSystemStart = SystemStart $ posixSecondsToUTCTime 0

-- | A cost model that sets everything as being free
freeCostModel :: CostModel
freeCostModel = CostModel $ 0 <$ fromJust defaultCostModelParams

pp :: Proof era -> Core.PParams era
pp pf =
  newPParams
    pf
    [ Costmdls $ Map.singleton PlutusV1 freeCostModel,
      MaxValSize 1000000000,
      MaxTxExUnits $ ExUnits 1000000 1000000,
      MaxBlockExUnits $ ExUnits 1000000 1000000,
      ProtocolVersion $ ProtVer 5 0
    ]

utxoEnv :: Proof era -> UtxoEnv era
utxoEnv pf =
  UtxoEnv
    (SlotNo 0)
    (pp pf)
    mempty
    (GenDelegs mempty)

-- | Create an address with a given payment script.
-- The proof here is used only as a Proxy.
scriptAddr :: forall era. (Scriptic era) => Core.Script era -> Proof era -> Addr (Crypto era)
scriptAddr s _pf = Addr Testnet pCred sCred
  where
    pCred = ScriptHashObj . hashScript @era $ s
    (_ssk, svk) = mkKeyPair @(Crypto era) (RawSeed 0 0 0 0 0)
    sCred = StakeRefBase . KeyHashObj . hashKey $ svk

someKeys :: forall era. Era era => Proof era -> KeyPair 'Payment (Crypto era)
someKeys _pf = KeyPair vk sk
  where
    (sk, vk) = mkKeyPair @(Crypto era) (RawSeed 1 1 1 1 1)

someAddr :: forall era. Era era => Proof era -> Addr (Crypto era)
someAddr pf = Addr Testnet pCred sCred
  where
    (_ssk, svk) = mkKeyPair @(Crypto era) (RawSeed 0 0 0 0 2)
    pCred = KeyHashObj . hashKey . vKey $ someKeys pf
    sCred = StakeRefBase . KeyHashObj . hashKey $ svk

someOutput :: Scriptic era => Proof era -> Core.TxOut era
someOutput pf =
  newTxOut Override pf [Address $ someAddr pf, Amount (inject $ Coin 1000)]

collateralOutput :: Scriptic era => Proof era -> Core.TxOut era
collateralOutput pf =
  newTxOut Override pf [Address $ someAddr pf, Amount (inject $ Coin 1000)]

alwaysSucceedsHash ::
  forall era.
  Scriptic era =>
  Natural ->
  Proof era ->
  ScriptHash (Crypto era)
alwaysSucceedsHash n pf = hashScript @era $ (always n pf)

alwaysFailsHash :: forall era. Scriptic era => Natural -> Proof era -> ScriptHash (Crypto era)
alwaysFailsHash n pf = hashScript @era $ (never n pf)

timelockScript :: PostShelley era => Int -> Proof era -> Core.Script era
timelockScript s pf = allOf [matchkey 1, after (100 + s)] $ pf

timelockHash ::
  forall era.
  PostShelley era =>
  Int ->
  Proof era ->
  ScriptHash (Crypto era)
timelockHash n pf = hashScript @era $ (timelockScript n pf)

timelockAddr :: forall era. PostShelley era => Proof era -> Addr (Crypto era)
timelockAddr pf = Addr Testnet pCred sCred
  where
    (_ssk, svk) = mkKeyPair @(Crypto era) (RawSeed 0 0 0 0 2)
    pCred = ScriptHashObj (timelockHash 0 pf)
    sCred = StakeRefBase . KeyHashObj . hashKey $ svk

timelockOut :: PostShelley era => Proof era -> Core.TxOut era
timelockOut pf =
  newTxOut Override pf [Address $ timelockAddr pf, Amount (inject $ Coin 1)]

-- | This output is unspendable since it is locked by a plutus script,
--  but has no datum hash.
unspendableOut :: forall era. (Scriptic era) => Proof era -> Core.TxOut era
unspendableOut pf =
  newTxOut
    Override
    pf
    [ Address (scriptAddr (always 3 pf) pf),
      Amount (inject $ Coin 5000)
    ]

initUTxO :: PostShelley era => Proof era -> UTxO era
initUTxO pf =
  UTxO $
    Map.fromList $
      [ (TxIn genesisId 1, alwaysSucceedsOutput pf),
        (TxIn genesisId 2, alwaysFailsOutput pf)
      ]
        ++ map (\i -> (TxIn genesisId i, someOutput pf)) [3 .. 8]
        ++ map (\i -> (TxIn genesisId i, collateralOutput pf)) [11 .. 18]
        ++ [ (TxIn genesisId 100, timelockOut pf),
             (TxIn genesisId 101, unspendableOut pf)
           ]

initialUtxoSt ::
  ( Default (State (EraRule "PPUP" era)),
    PostShelley era
  ) =>
  Proof era ->
  UTxOState era
initialUtxoSt pf = UTxOState (initUTxO pf) (Coin 0) (Coin 0) def

-- | This is a helper type for the expectedUTxO function.
--  ExpectSuccess indicates that we created a valid transaction
--  where the IsValidating flag is true.
data Expect era = ExpectSuccess (Core.TxBody era) (Core.TxOut era) | ExpectFailure

-- | In each of our main eight examples, the UTxO map obtained
-- by applying the transaction is straightforward. This function
-- captures the logic.
--
-- Each example transaction (given a number i) will use
-- (TxIn genesisId (10+i), someOutput) for its' single input,
-- and (TxIn genesisId i, collateralOutput) for its' single collateral output.
--
-- If we expect the transaction script to validate, then
-- the UTxO for (TxIn genesisId i) will be consumed and a UTxO will be created.
-- Otherwise, the UTxO for (TxIn genesisId (10+i)) will be consumed.
expectedUTxO :: forall era. (PostShelley era) => Proof era -> Expect era -> Natural -> UTxO era
expectedUTxO pf ex idx = UTxO utxo
  where
    utxo = case ex of
      ExpectSuccess txb newOut ->
        Map.insert (TxIn (txid @era txb) 0) newOut (filteredUTxO idx)
      ExpectFailure -> filteredUTxO (10 + idx)
    filteredUTxO :: Natural -> Map.Map (TxIn (Crypto era)) (Core.TxOut era)
    filteredUTxO x = Map.filterWithKey (\(TxIn _ i) _ -> i /= x) (unUTxO . initUTxO $ pf)

keyBy :: Ord k => (a -> k) -> [a] -> Map k a
keyBy f xs = Map.fromList $ (\x -> (f x, x)) <$> xs

-- =========================================================================
--  Example 1: Process a SPEND transaction with a succeeding Plutus script.
-- =========================================================================

datumExample1 :: Data era
datumExample1 = Data (Plutus.I 123)

redeemerExample1 :: Data era
redeemerExample1 = Data (Plutus.I 42)

txDatsExample1 :: Era era => TxDats era
txDatsExample1 = TxDats $ keyBy hashData $ [datumExample1]

alwaysSucceedsOutput :: forall era. (Scriptic era) => Proof era -> Core.TxOut era
alwaysSucceedsOutput pf =
  newTxOut
    Override
    pf
    [ Address (scriptAddr (always 3 pf) pf),
      Amount (inject $ Coin 5000),
      DHash [hashData $ datumExample1 @era]
    ]

validatingRedeemersEx1 :: Era era => Redeemers era
validatingRedeemersEx1 =
  Redeemers $
    Map.singleton (RdmrPtr Tag.Spend 0) (redeemerExample1, ExUnits 5000 5000)

outEx1 :: Scriptic era => Proof era -> Core.TxOut era
outEx1 pf = newTxOut Override pf [Address (someAddr pf), Amount (inject $ Coin 4995)]

validatingBody :: Scriptic era => Proof era -> Core.TxBody era
validatingBody pf =
  newTxBody
    Override
    pf
    [ Inputs [TxIn genesisId 1],
      Collateral [TxIn genesisId 11],
      Outputs [outEx1 pf],
      Txfee (Coin 5),
      WppHash (newWppHash pf (pp pf) [PlutusV1] validatingRedeemersEx1 txDatsExample1)
    ]

type SignBody era =
  ( Signable
      (CC.DSIGN (Crypto era))
      (CH.Hash (CC.HASH (Crypto era)) EraIndependentTxBody)
  )

validatingTx ::
  forall era.
  ( Scriptic era,
    SignBody era
  ) =>
  Proof era ->
  Core.Tx era
validatingTx pf =
  newTx
    Override
    pf
    [ Body (validatingBody pf),
      Witnesses'
        [ AddrWits [makeWitnessVKey (hashAnnotated (validatingBody pf)) (someKeys pf)],
          ScriptWits [always 3 pf],
          DataWits [datumExample1],
          RdmrWits validatingRedeemersEx1
        ]
    ]

utxoEx1 :: forall era. PostShelley era => Proof era -> UTxO era
utxoEx1 pf = expectedUTxO pf (ExpectSuccess (validatingBody pf) (outEx1 pf)) 1

utxoStEx1 ::
  forall era.
  (Default (State (EraRule "PPUP" era)), PostShelley era) =>
  Proof era ->
  UTxOState era
utxoStEx1 pf = UTxOState (utxoEx1 pf) (Coin 0) (Coin 5) def

-- ======================================================================
--  Example 2: Process a SPEND transaction with a failing Plutus script.
-- ======================================================================

datumExample2 :: Data era
datumExample2 = Data (Plutus.I 0)

redeemerExample2 :: Data era
redeemerExample2 = Data (Plutus.I 1)

txDatsExample2 :: Era era => TxDats era
txDatsExample2 = TxDats $ keyBy hashData $ [datumExample2]

notValidatingRedeemers :: Era era => Redeemers era
notValidatingRedeemers =
  Redeemers
    ( Map.fromList
        [ ( RdmrPtr Tag.Spend 0,
            (redeemerExample2, ExUnits 5000 5000)
          )
        ]
    )

alwaysFailsOutput :: forall era. (Scriptic era) => Proof era -> Core.TxOut era
alwaysFailsOutput pf =
  newTxOut
    Override
    pf
    [ Address (scriptAddr (never 0 pf) pf),
      Amount (inject $ Coin 3000),
      DHash [hashData $ datumExample2 @era]
    ]

outEx2 :: (Scriptic era) => Proof era -> Core.TxOut era
outEx2 pf = newTxOut Override pf [Address (someAddr pf), Amount (inject $ Coin 2995)]

notValidatingBody :: Scriptic era => Proof era -> Core.TxBody era
notValidatingBody pf =
  newTxBody
    Override
    pf
    [ Inputs [TxIn genesisId 2],
      Collateral [TxIn genesisId 12],
      Outputs [outEx2 pf],
      Txfee (Coin 5),
      WppHash (newWppHash pf (pp pf) [PlutusV1] notValidatingRedeemers txDatsExample2)
    ]

notValidatingTx ::
  ( Scriptic era,
    SignBody era
  ) =>
  Proof era ->
  Core.Tx era
notValidatingTx pf =
  newTx
    Override
    pf
    [ Body (notValidatingBody pf),
      Witnesses'
        [ AddrWits [makeWitnessVKey (hashAnnotated (notValidatingBody pf)) (someKeys pf)],
          ScriptWits [never 0 pf],
          DataWits [datumExample2],
          RdmrWits notValidatingRedeemers
        ]
    ]

utxoEx2 :: PostShelley era => Proof era -> UTxO era
utxoEx2 pf = expectedUTxO pf ExpectFailure 2

utxoStEx2 ::
  (Default (State (EraRule "PPUP" era)), PostShelley era) =>
  Proof era ->
  UTxOState era
utxoStEx2 pf = UTxOState (utxoEx2 pf) (Coin 0) (Coin 1000) def

-- =========================================================================
--  Example 3: Process a CERT transaction with a succeeding Plutus script.
-- =========================================================================

outEx3 :: Era era => Proof era -> Core.TxOut era
outEx3 pf = newTxOut Override pf [Address (someAddr pf), Amount (inject $ Coin 995)]

redeemerExample3 :: Data era
redeemerExample3 = Data (Plutus.I 42)

validatingRedeemersEx3 :: Era era => Redeemers era
validatingRedeemersEx3 =
  Redeemers $
    Map.singleton (RdmrPtr Tag.Cert 0) (redeemerExample3, ExUnits 5000 5000)

scriptStakeCredSuceed :: Scriptic era => Proof era -> StakeCredential (Crypto era)
scriptStakeCredSuceed pf = ScriptHashObj (alwaysSucceedsHash 2 pf)

validatingBodyWithCert :: Scriptic era => Proof era -> Core.TxBody era
validatingBodyWithCert pf =
  newTxBody
    Override
    pf
    [ Inputs [TxIn genesisId 3],
      Collateral [TxIn genesisId 13],
      Outputs [outEx3 pf],
      Certs [DCertDeleg (DeRegKey $ scriptStakeCredSuceed pf)],
      Txfee (Coin 5),
      WppHash (newWppHash pf (pp pf) [PlutusV1] validatingRedeemersEx3 mempty)
    ]

validatingTxWithCert ::
  forall era.
  ( Scriptic era,
    SignBody era
  ) =>
  Proof era ->
  Core.Tx era
validatingTxWithCert pf =
  newTx
    Override
    pf
    [ Body (validatingBodyWithCert pf),
      Witnesses'
        [ AddrWits [makeWitnessVKey (hashAnnotated (validatingBodyWithCert pf)) (someKeys pf)],
          ScriptWits [always 2 pf],
          RdmrWits validatingRedeemersEx3
        ]
    ]

utxoEx3 :: PostShelley era => Proof era -> UTxO era
utxoEx3 pf = expectedUTxO pf (ExpectSuccess (validatingBodyWithCert pf) (outEx3 pf)) 3

utxoStEx3 ::
  (Default (State (EraRule "PPUP" era)), PostShelley era) =>
  Proof era ->
  UTxOState era
utxoStEx3 pf = UTxOState (utxoEx3 pf) (Coin 0) (Coin 5) def

-- =====================================================================
--  Example 4: Process a CERT transaction with a failing Plutus script.
-- =====================================================================

outEx4 :: (Scriptic era) => Proof era -> Core.TxOut era
outEx4 pf = newTxOut Override pf [Address (someAddr pf), Amount (inject $ Coin 995)]

redeemerExample4 :: Data era
redeemerExample4 = Data (Plutus.I 0)

notValidatingRedeemersEx4 :: Era era => Redeemers era
notValidatingRedeemersEx4 =
  Redeemers $
    Map.singleton (RdmrPtr Tag.Cert 0) (redeemerExample4, ExUnits 5000 5000)

scriptStakeCredFail :: Scriptic era => Proof era -> StakeCredential (Crypto era)
scriptStakeCredFail pf = ScriptHashObj (alwaysFailsHash 1 pf)

notValidatingBodyWithCert :: Scriptic era => Proof era -> Core.TxBody era
notValidatingBodyWithCert pf =
  newTxBody
    Override
    pf
    [ Inputs [TxIn genesisId 4],
      Collateral [TxIn genesisId 14],
      Outputs [outEx4 pf],
      Certs [DCertDeleg (DeRegKey $ scriptStakeCredFail pf)],
      Txfee (Coin 5),
      WppHash (newWppHash pf (pp pf) [PlutusV1] notValidatingRedeemersEx4 mempty)
    ]

notValidatingTxWithCert ::
  forall era.
  ( Scriptic era,
    SignBody era
  ) =>
  Proof era ->
  Core.Tx era
notValidatingTxWithCert pf =
  newTx
    Override
    pf
    [ Body (notValidatingBodyWithCert pf),
      Witnesses'
        [ AddrWits [makeWitnessVKey (hashAnnotated (notValidatingBodyWithCert pf)) (someKeys pf)],
          ScriptWits [never 1 pf],
          RdmrWits notValidatingRedeemersEx4
        ]
    ]

utxoEx4 :: PostShelley era => Proof era -> UTxO era
utxoEx4 pf = expectedUTxO pf ExpectFailure 4

utxoStEx4 ::
  (Default (State (EraRule "PPUP" era)), PostShelley era) =>
  Proof era ->
  UTxOState era
utxoStEx4 pf = UTxOState (utxoEx4 pf) (Coin 0) (Coin 1000) def

-- ==============================================================================
--  Example 5: Process a WITHDRAWAL transaction with a succeeding Plutus script.
-- ==============================================================================

outEx5 :: (Scriptic era) => Proof era -> Core.TxOut era
outEx5 pf = newTxOut Override pf [Address (someAddr pf), Amount (inject $ Coin 1995)]

redeemerExample5 :: Data era
redeemerExample5 = Data (Plutus.I 42)

validatingRedeemersEx5 :: Era era => Redeemers era
validatingRedeemersEx5 =
  Redeemers $
    Map.singleton (RdmrPtr Tag.Rewrd 0) (redeemerExample5, ExUnits 5000 5000)

validatingBodyWithWithdrawal :: Scriptic era => Proof era -> Core.TxBody era
validatingBodyWithWithdrawal pf =
  newTxBody
    Override
    pf
    [ Inputs [TxIn genesisId 5],
      Collateral [TxIn genesisId 15],
      Outputs [outEx5 pf],
      Txfee (Coin 5),
      Wdrls
        ( Wdrl $
            Map.singleton
              (RewardAcnt Testnet (scriptStakeCredSuceed pf))
              (Coin 1000)
        ),
      WppHash (newWppHash pf (pp pf) [PlutusV1] validatingRedeemersEx5 mempty)
    ]

validatingTxWithWithdrawal ::
  forall era.
  ( Scriptic era,
    SignBody era
  ) =>
  Proof era ->
  Core.Tx era
validatingTxWithWithdrawal pf =
  newTx
    Override
    pf
    [ Body (validatingBodyWithWithdrawal pf),
      Witnesses'
        [ AddrWits [makeWitnessVKey (hashAnnotated (validatingBodyWithWithdrawal pf)) (someKeys pf)],
          ScriptWits [always 2 pf],
          RdmrWits validatingRedeemersEx5
        ]
    ]

utxoEx5 :: PostShelley era => Proof era -> UTxO era
utxoEx5 pf = expectedUTxO pf (ExpectSuccess (validatingBodyWithWithdrawal pf) (outEx5 pf)) 5

utxoStEx5 ::
  (Default (State (EraRule "PPUP" era)), PostShelley era) =>
  Proof era ->
  UTxOState era
utxoStEx5 pf = UTxOState (utxoEx5 pf) (Coin 0) (Coin 5) def

-- ===========================================================================
--  Example 6: Process a WITHDRAWAL transaction with a failing Plutus script.
-- ===========================================================================

outEx6 :: (Scriptic era) => Proof era -> Core.TxOut era
outEx6 pf = newTxOut Override pf [Address (someAddr pf), Amount (inject $ Coin 1995)]

redeemerExample6 :: Data era
redeemerExample6 = Data (Plutus.I 0)

notValidatingRedeemersEx6 :: Era era => Redeemers era
notValidatingRedeemersEx6 =
  Redeemers $
    Map.singleton (RdmrPtr Tag.Rewrd 0) (redeemerExample6, ExUnits 5000 5000)

notValidatingBodyWithWithdrawal :: Scriptic era => Proof era -> Core.TxBody era
notValidatingBodyWithWithdrawal pf =
  newTxBody
    Override
    pf
    [ Inputs [TxIn genesisId 6],
      Collateral [TxIn genesisId 16],
      Outputs [outEx6 pf],
      Txfee (Coin 5),
      Wdrls
        ( Wdrl $
            Map.singleton
              (RewardAcnt Testnet (scriptStakeCredFail pf))
              (Coin 1000)
        ),
      WppHash (newWppHash pf (pp pf) [PlutusV1] notValidatingRedeemersEx6 mempty)
    ]

notValidatingTxWithWithdrawal ::
  forall era.
  ( Scriptic era,
    SignBody era
  ) =>
  Proof era ->
  Core.Tx era
notValidatingTxWithWithdrawal pf =
  newTx
    Override
    pf
    [ Body (notValidatingBodyWithWithdrawal pf),
      Witnesses'
        [ AddrWits [makeWitnessVKey (hashAnnotated (notValidatingBodyWithWithdrawal pf)) (someKeys pf)],
          ScriptWits [never 1 pf],
          RdmrWits notValidatingRedeemersEx6
        ]
    ]

utxoEx6 :: PostShelley era => Proof era -> UTxO era
utxoEx6 pf = expectedUTxO pf ExpectFailure 6

utxoStEx6 ::
  (Default (State (EraRule "PPUP" era)), PostShelley era) =>
  Proof era ->
  UTxOState era
utxoStEx6 pf = UTxOState (utxoEx6 pf) (Coin 0) (Coin 1000) def

-- =============================================================================
--  Example 7: Process a MINT transaction with a succeeding Plutus script.
-- =============================================================================

mintEx7 :: forall era. (Scriptic era, HasTokens era) => Proof era -> Core.Value era
mintEx7 pf = forge @era 1 (always 2 pf)

outEx7 :: (HasTokens era, Scriptic era) => Proof era -> Core.TxOut era
outEx7 pf = newTxOut Override pf [Address (someAddr pf), Amount (mintEx7 pf <+> inject (Coin 995))]

redeemerExample7 :: Data era
redeemerExample7 = Data (Plutus.I 42)

validatingRedeemersEx7 :: Era era => Redeemers era
validatingRedeemersEx7 =
  Redeemers $
    Map.singleton (RdmrPtr Tag.Mint 0) (redeemerExample7, ExUnits 5000 5000)

validatingBodyWithMint :: (HasTokens era, Scriptic era) => Proof era -> Core.TxBody era
validatingBodyWithMint pf =
  newTxBody
    Override
    pf
    [ Inputs [TxIn genesisId 7],
      Collateral [TxIn genesisId 17],
      Outputs [outEx7 pf],
      Txfee (Coin 5),
      Mint (mintEx7 pf),
      WppHash (newWppHash pf (pp pf) [PlutusV1] validatingRedeemersEx7 mempty)
    ]

validatingTxWithMint ::
  forall era.
  ( Scriptic era,
    HasTokens era,
    SignBody era
  ) =>
  Proof era ->
  Core.Tx era
validatingTxWithMint pf =
  newTx
    Override
    pf
    [ Body (validatingBodyWithMint pf),
      Witnesses'
        [ AddrWits [makeWitnessVKey (hashAnnotated (validatingBodyWithMint pf)) (someKeys pf)],
          ScriptWits [always 2 pf],
          RdmrWits validatingRedeemersEx7
        ]
    ]

utxoEx7 :: forall era. (HasTokens era, PostShelley era) => Proof era -> UTxO era
utxoEx7 pf = expectedUTxO pf (ExpectSuccess (validatingBodyWithMint pf) (outEx7 pf)) 7

utxoStEx7 ::
  forall era.
  (Default (State (EraRule "PPUP" era)), PostShelley era, HasTokens era) =>
  Proof era ->
  UTxOState era
utxoStEx7 pf = UTxOState (utxoEx7 pf) (Coin 0) (Coin 5) def

-- ==============================================================================
--  Example 8: Process a MINT transaction with a failing Plutus script.
-- ==============================================================================

mintEx8 :: forall era. (Scriptic era, HasTokens era) => Proof era -> Core.Value era
mintEx8 pf = forge @era 1 (never 1 pf)

outEx8 :: (HasTokens era, Scriptic era) => Proof era -> Core.TxOut era
outEx8 pf = newTxOut Override pf [Address (someAddr pf), Amount (mintEx8 pf <+> inject (Coin 995))]

redeemerExample8 :: Data era
redeemerExample8 = Data (Plutus.I 0)

notValidatingRedeemersEx8 :: Era era => Redeemers era
notValidatingRedeemersEx8 =
  Redeemers $
    Map.singleton (RdmrPtr Tag.Mint 0) (redeemerExample8, ExUnits 5000 5000)

notValidatingBodyWithMint :: (HasTokens era, Scriptic era) => Proof era -> Core.TxBody era
notValidatingBodyWithMint pf =
  newTxBody
    Override
    pf
    [ Inputs [TxIn genesisId 8],
      Collateral [TxIn genesisId 18],
      Outputs [outEx8 pf],
      Txfee (Coin 5),
      Mint (mintEx8 pf),
      WppHash (newWppHash pf (pp pf) [PlutusV1] notValidatingRedeemersEx8 mempty)
    ]

notValidatingTxWithMint ::
  forall era.
  ( Scriptic era,
    HasTokens era,
    SignBody era
  ) =>
  Proof era ->
  Core.Tx era
notValidatingTxWithMint pf =
  newTx
    Override
    pf
    [ Body (notValidatingBodyWithMint pf),
      Witnesses'
        [ AddrWits [makeWitnessVKey (hashAnnotated (notValidatingBodyWithMint pf)) (someKeys pf)],
          ScriptWits [never 1 pf],
          RdmrWits notValidatingRedeemersEx8
        ]
    ]

utxoEx8 :: PostShelley era => Proof era -> UTxO era
utxoEx8 pf = expectedUTxO pf ExpectFailure 8

utxoStEx8 ::
  (Default (State (EraRule "PPUP" era)), PostShelley era) =>
  Proof era ->
  UTxOState era
utxoStEx8 pf = UTxOState (utxoEx8 pf) (Coin 0) (Coin 1000) def

-- ====================================================================================
--  Example 9: Process a transaction with a succeeding script in every place possible,
--  and also with succeeding timelock scripts.
-- ====================================================================================

validatingRedeemersEx9 :: Era era => Redeemers era
validatingRedeemersEx9 =
  Redeemers . Map.fromList $
    [ (RdmrPtr Tag.Spend 0, (Data (Plutus.I 101), ExUnits 5000 5000)),
      (RdmrPtr Tag.Cert 1, (Data (Plutus.I 102), ExUnits 5000 5000)),
      (RdmrPtr Tag.Rewrd 0, (Data (Plutus.I 103), ExUnits 5000 5000)),
      (RdmrPtr Tag.Mint 1, (Data (Plutus.I 104), ExUnits 5000 5000))
    ]

mintEx9 :: forall era. (PostShelley era, HasTokens era) => Proof era -> Core.Value era
mintEx9 pf = forge @era 1 (always 2 pf) <+> forge @era 1 (timelockScript 1 pf)

outEx9 :: (HasTokens era, PostShelley era) => Proof era -> Core.TxOut era
outEx9 pf =
  newTxOut
    Override
    pf
    [ Address (someAddr pf),
      Amount (mintEx9 pf <+> inject (Coin 4996))
    ]

timelockStakeCred :: PostShelley era => Proof era -> StakeCredential (Crypto era)
timelockStakeCred pf = ScriptHashObj (timelockHash 2 pf)

validatingBodyManyScripts ::
  (HasTokens era, PostShelley era) =>
  Proof era ->
  Core.TxBody era
validatingBodyManyScripts pf =
  newTxBody
    Override
    pf
    [ Inputs [TxIn genesisId 1, TxIn genesisId 100],
      Collateral [TxIn genesisId 11],
      Outputs [outEx9 pf],
      Txfee (Coin 5),
      Certs
        [ DCertDeleg (DeRegKey $ timelockStakeCred pf),
          DCertDeleg (DeRegKey $ scriptStakeCredSuceed pf)
        ],
      Wdrls
        ( Wdrl $
            Map.fromList
              [ (RewardAcnt Testnet (scriptStakeCredSuceed pf), Coin 0),
                (RewardAcnt Testnet (timelockStakeCred pf), Coin 0)
              ]
        ),
      Mint (mintEx9 pf),
      WppHash (newWppHash pf (pp pf) [PlutusV1] validatingRedeemersEx9 txDatsExample1),
      Vldt (ValidityInterval SNothing (SJust $ SlotNo 1))
    ]

validatingTxManyScripts ::
  forall era.
  ( PostShelley era,
    HasTokens era,
    SignBody era
  ) =>
  Proof era ->
  Core.Tx era
validatingTxManyScripts pf =
  newTx
    Override
    pf
    [ Body (validatingBodyManyScripts pf),
      Witnesses'
        [ AddrWits $
            map
              (makeWitnessVKey . hashAnnotated . validatingBodyManyScripts $ pf)
              [someKeys pf, theKeyPair 1],
          ScriptWits
            [ always 2 pf,
              always 3 pf,
              timelockScript 0 pf,
              timelockScript 1 pf,
              timelockScript 2 pf
            ],
          DataWits [datumExample1],
          RdmrWits validatingRedeemersEx9
        ]
    ]

utxoEx9 :: forall era. (PostShelley era, HasTokens era) => Proof era -> UTxO era
utxoEx9 pf = UTxO utxo
  where
    utxo =
      Map.insert (TxIn (txid @era (validatingBodyManyScripts pf)) 0) (outEx9 pf) $
        Map.filterWithKey
          (\k _ -> k /= (TxIn genesisId 1) && k /= (TxIn genesisId 100))
          (unUTxO $ initUTxO pf)

utxoStEx9 ::
  forall era.
  (Default (State (EraRule "PPUP" era)), PostShelley era, HasTokens era) =>
  Proof era ->
  UTxOState era
utxoStEx9 pf = UTxOState (utxoEx9 pf) (Coin 0) (Coin 5) def

-- ====================================================================================
--  Example 10: A transaction with an acceptable supplimentary datum
-- ====================================================================================

outEx10 :: forall era. (Scriptic era) => Proof era -> Core.TxOut era
outEx10 pf =
  newTxOut
    Override
    pf
    [ Address (scriptAddr (always 3 pf) pf),
      Amount (inject $ Coin 995),
      DHash [hashData $ datumExample1 @era]
    ]

okSupplimentaryDatumTxBody :: Scriptic era => Proof era -> Core.TxBody era
okSupplimentaryDatumTxBody pf =
  newTxBody
    Override
    pf
    [ Inputs [TxIn genesisId 3],
      Outputs [outEx10 pf],
      Txfee (Coin 5),
      WppHash (newWppHash pf (pp pf) [] (Redeemers mempty) txDatsExample1)
    ]

okSupplimentaryDatumTx ::
  forall era.
  ( Scriptic era,
    SignBody era
  ) =>
  Proof era ->
  Core.Tx era
okSupplimentaryDatumTx pf =
  newTx
    Override
    pf
    [ Body (okSupplimentaryDatumTxBody pf),
      Witnesses'
        [ AddrWits [makeWitnessVKey (hashAnnotated (okSupplimentaryDatumTxBody pf)) (someKeys pf)],
          DataWits [datumExample1]
        ]
    ]

utxoEx10 :: forall era. PostShelley era => Proof era -> UTxO era
utxoEx10 pf = expectedUTxO pf (ExpectSuccess (okSupplimentaryDatumTxBody pf) (outEx10 pf)) 3

utxoStEx10 ::
  forall era.
  (Default (State (EraRule "PPUP" era)), PostShelley era) =>
  Proof era ->
  UTxOState era
utxoStEx10 pf = UTxOState (utxoEx10 pf) (Coin 0) (Coin 5) def

-- =======================
-- Invalid Transactions
-- =======================

incorrectNetworkIDTxBody :: Era era => Proof era -> Core.TxBody era
incorrectNetworkIDTxBody pf =
  newTxBody
    Override
    pf
    [ Inputs [TxIn genesisId 3],
      Outputs [outEx3 pf],
      Txfee (Coin 5),
      Txnetworkid (SJust Mainnet)
    ]

incorrectNetworkIDTx :: (Era era, SignBody era) => Proof era -> Core.Tx era
incorrectNetworkIDTx pf =
  newTx
    Override
    pf
    [ Body (incorrectNetworkIDTxBody pf),
      Witnesses'
        [ AddrWits [makeWitnessVKey (hashAnnotated (incorrectNetworkIDTxBody pf)) (someKeys pf)]
        ]
    ]

extraneousKeyHash :: CC.Crypto c => KeyHash 'Witness c
extraneousKeyHash = hashKey . snd . mkKeyPair $ (RawSeed 0 0 0 0 99)

missingRequiredWitnessTxBody :: Era era => Proof era -> Core.TxBody era
missingRequiredWitnessTxBody pf =
  newTxBody
    Override
    pf
    [ Inputs [TxIn genesisId 3],
      Outputs [outEx3 pf],
      Txfee (Coin 5),
      ReqSignerHashes [extraneousKeyHash]
    ]

missingRequiredWitnessTx :: (Era era, SignBody era) => Proof era -> Core.Tx era
missingRequiredWitnessTx pf =
  newTx
    Override
    pf
    [ Body (missingRequiredWitnessTxBody pf),
      Witnesses'
        [ AddrWits [makeWitnessVKey (hashAnnotated (missingRequiredWitnessTxBody pf)) (someKeys pf)]
        ]
    ]

missingRedeemerTxBody :: Scriptic era => Proof era -> Core.TxBody era
missingRedeemerTxBody pf =
  newTxBody
    Override
    pf
    [ Inputs [TxIn genesisId 1],
      Collateral [TxIn genesisId 11],
      Outputs [outEx1 pf],
      Txfee (Coin 5),
      WppHash (newWppHash pf (pp pf) [PlutusV1] (Redeemers mempty) txDatsExample1)
    ]

missingRedeemerTx ::
  (Scriptic era, SignBody era) =>
  Proof era ->
  Core.Tx era
missingRedeemerTx pf =
  newTx
    Override
    pf
    [ Body (missingRedeemerTxBody pf),
      Witnesses'
        [ AddrWits [makeWitnessVKey (hashAnnotated (missingRedeemerTxBody pf)) (someKeys pf)],
          ScriptWits [always 3 pf],
          DataWits [datumExample1]
        ]
    ]

wrongWppHashTx ::
  (Scriptic era, SignBody era) =>
  Proof era ->
  Core.Tx era
wrongWppHashTx pf =
  newTx
    Override
    pf
    [ Body (missingRedeemerTxBody pf),
      Witnesses'
        [ AddrWits [makeWitnessVKey (hashAnnotated (missingRedeemerTxBody pf)) (someKeys pf)],
          ScriptWits [always 3 pf],
          DataWits [datumExample1],
          RdmrWits validatingRedeemersEx1
        ]
    ]

missing1phaseScriptWitnessTx ::
  forall era.
  ( PostShelley era,
    HasTokens era,
    SignBody era
  ) =>
  Proof era ->
  Core.Tx era
missing1phaseScriptWitnessTx pf =
  newTx
    Override
    pf
    [ Body (validatingBodyManyScripts pf),
      Witnesses'
        [ AddrWits $
            map
              (makeWitnessVKey . hashAnnotated . validatingBodyManyScripts $ pf)
              [someKeys pf, theKeyPair 1],
          ScriptWits
            [ always 2 pf,
              always 3 pf,
              -- intentionally missing -> timelockScript 0 pf,
              timelockScript 1 pf,
              timelockScript 2 pf
            ],
          DataWits [datumExample1],
          RdmrWits validatingRedeemersEx9
        ]
    ]

missing2phaseScriptWitnessTx ::
  forall era.
  ( PostShelley era,
    HasTokens era,
    SignBody era
  ) =>
  Proof era ->
  Core.Tx era
missing2phaseScriptWitnessTx pf =
  newTx
    Override
    pf
    [ Body (validatingBodyManyScripts pf),
      Witnesses'
        [ AddrWits $
            map
              (makeWitnessVKey . hashAnnotated . validatingBodyManyScripts $ pf)
              [someKeys pf, theKeyPair 1],
          ScriptWits
            [ -- intentionally missing -> always 2 pf,
              always 3 pf,
              timelockScript 0 pf,
              timelockScript 1 pf,
              timelockScript 2 pf
            ],
          DataWits [datumExample1],
          RdmrWits validatingRedeemersEx9
        ]
    ]

misPurposedRedeemer :: Era era => Redeemers era
misPurposedRedeemer =
  Redeemers $
    -- The label *should* be Spend, not Mint
    Map.singleton (RdmrPtr Tag.Mint 0) (redeemerExample1, ExUnits 5000 5000)

wrongRedeemerLabelTxBody :: Scriptic era => Proof era -> Core.TxBody era
wrongRedeemerLabelTxBody pf =
  newTxBody
    Override
    pf
    [ Inputs [TxIn genesisId 1],
      Collateral [TxIn genesisId 11],
      Outputs [outEx1 pf],
      Txfee (Coin 5),
      WppHash (newWppHash pf (pp pf) [PlutusV1] misPurposedRedeemer txDatsExample1)
    ]

wrongRedeemerLabelTx ::
  forall era.
  ( Scriptic era,
    SignBody era
  ) =>
  Proof era ->
  Core.Tx era
wrongRedeemerLabelTx pf =
  newTx
    Override
    pf
    [ Body (wrongRedeemerLabelTxBody pf),
      Witnesses'
        [ AddrWits [makeWitnessVKey (hashAnnotated (wrongRedeemerLabelTxBody pf)) (someKeys pf)],
          ScriptWits [always 3 pf],
          DataWits [datumExample1],
          RdmrWits misPurposedRedeemer
        ]
    ]

missingDatumTxBody :: Scriptic era => Proof era -> Core.TxBody era
missingDatumTxBody pf =
  newTxBody
    Override
    pf
    [ Inputs [TxIn genesisId 1],
      Collateral [TxIn genesisId 11],
      Outputs [outEx1 pf],
      Txfee (Coin 5),
      WppHash (newWppHash pf (pp pf) [PlutusV1] validatingRedeemersEx1 mempty)
    ]

missingDatumTx ::
  forall era.
  ( Scriptic era,
    SignBody era
  ) =>
  Proof era ->
  Core.Tx era
missingDatumTx pf =
  newTx
    Override
    pf
    [ Body (missingDatumTxBody pf),
      Witnesses'
        [ AddrWits [makeWitnessVKey (hashAnnotated (missingDatumTxBody pf)) (someKeys pf)],
          ScriptWits [always 3 pf],
          RdmrWits validatingRedeemersEx1
        ]
    ]

phase1FailureTx ::
  forall era.
  ( PostShelley era,
    HasTokens era,
    SignBody era
  ) =>
  Proof era ->
  Core.Tx era
phase1FailureTx pf =
  newTx
    Override
    pf
    [ Body (validatingBodyManyScripts pf),
      Witnesses'
        [ AddrWits
            [ makeWitnessVKey
                (hashAnnotated $ validatingBodyManyScripts pf)
                (someKeys pf)
            ],
          ScriptWits
            [ always 2 pf,
              always 3 pf,
              timelockScript 0 pf,
              timelockScript 1 pf,
              timelockScript 2 pf
            ],
          DataWits [datumExample1],
          RdmrWits validatingRedeemersEx9
        ]
    ]

validatingRedeemersTooManyExUnits :: Era era => Redeemers era
validatingRedeemersTooManyExUnits =
  Redeemers $
    Map.singleton (RdmrPtr Tag.Spend 0) (redeemerExample1, ExUnits 1000001 5000)

tooManyExUnitsTxBody :: Scriptic era => Proof era -> Core.TxBody era
tooManyExUnitsTxBody pf =
  newTxBody
    Override
    pf
    [ Inputs [TxIn genesisId 1],
      Collateral [TxIn genesisId 11],
      Outputs [outEx1 pf],
      Txfee (Coin 5),
      WppHash (newWppHash pf (pp pf) [PlutusV1] validatingRedeemersTooManyExUnits txDatsExample1)
    ]

tooManyExUnitsTx ::
  forall era.
  ( Scriptic era,
    SignBody era
  ) =>
  Proof era ->
  Core.Tx era
tooManyExUnitsTx pf =
  newTx
    Override
    pf
    [ Body (tooManyExUnitsTxBody pf),
      Witnesses'
        [ AddrWits [makeWitnessVKey (hashAnnotated (tooManyExUnitsTxBody pf)) (someKeys pf)],
          ScriptWits [always 3 pf],
          DataWits [datumExample1],
          RdmrWits validatingRedeemersTooManyExUnits
        ]
    ]

missingCollateralSig ::
  forall era.
  Scriptic era =>
  Proof era ->
  Core.Tx era
missingCollateralSig pf =
  newTx
    Override
    pf
    [ Body (validatingBody pf),
      Witnesses'
        [ ScriptWits [always 3 pf],
          DataWits [datumExample1],
          RdmrWits validatingRedeemersEx1
        ]
    ]

plutusOutputWithNoDataTxBody :: Scriptic era => Proof era -> Core.TxBody era
plutusOutputWithNoDataTxBody pf =
  newTxBody
    Override
    pf
    [ Inputs [TxIn genesisId 101],
      Collateral [TxIn genesisId 11],
      Outputs [outEx1 pf],
      Txfee (Coin 5),
      WppHash (newWppHash pf (pp pf) [PlutusV1] validatingRedeemersEx1 mempty)
    ]

plutusOutputWithNoDataTx ::
  forall era.
  ( Scriptic era,
    SignBody era
  ) =>
  Proof era ->
  Core.Tx era
plutusOutputWithNoDataTx pf =
  newTx
    Override
    pf
    [ Body (plutusOutputWithNoDataTxBody pf),
      Witnesses'
        [ AddrWits [makeWitnessVKey (hashAnnotated (plutusOutputWithNoDataTxBody pf)) (someKeys pf)],
          ScriptWits [always 3 pf],
          RdmrWits validatingRedeemersEx1
        ]
    ]

totallyIrrelevantDatum :: Data era
totallyIrrelevantDatum = Data (Plutus.I 1729)

outputWithNoDatum :: forall era. Era era => Proof era -> Core.TxOut era
outputWithNoDatum pf = newTxOut Override pf [Address $ someAddr pf, Amount (inject $ Coin 995)]

notOkSupplimentaryDatumTxBody :: Scriptic era => Proof era -> Core.TxBody era
notOkSupplimentaryDatumTxBody pf =
  newTxBody
    Override
    pf
    [ Inputs [TxIn genesisId 3],
      Outputs [outputWithNoDatum pf],
      Txfee (Coin 5),
      WppHash (newWppHash pf (pp pf) [] (Redeemers mempty) totallyIrrelevantTxDats)
    ]
  where
    totallyIrrelevantTxDats = TxDats $ keyBy hashData [totallyIrrelevantDatum]

notOkSupplimentaryDatumTx ::
  forall era.
  ( Scriptic era,
    SignBody era
  ) =>
  Proof era ->
  Core.Tx era
notOkSupplimentaryDatumTx pf =
  newTx
    Override
    pf
    [ Body (notOkSupplimentaryDatumTxBody pf),
      Witnesses'
        [ AddrWits [makeWitnessVKey (hashAnnotated (notOkSupplimentaryDatumTxBody pf)) (someKeys pf)],
          DataWits [totallyIrrelevantDatum]
        ]
    ]

hashsize :: forall c. CC.Crypto c => Int
hashsize = fromIntegral $ sizeHash ([] @(CC.HASH c))

poolMDHTooBigTxBody :: forall era. Scriptic era => Proof era -> Core.TxBody era
poolMDHTooBigTxBody pf =
  newTxBody
    Override
    pf
    [ Inputs [TxIn genesisId 3],
      Outputs [newTxOut Override pf [Address $ someAddr pf, Amount (inject $ Coin 995)]],
      Certs [DCertPool (RegPool poolParams)],
      Txfee (Coin 5)
    ]
  where
    tooManyBytes = BS.replicate (hashsize @(Crypto era) + 1) 0
    poolParams =
      PoolParams
        { _poolId = coerceKeyRole . hashKey . vKey $ someKeys pf,
          _poolVrf = hashVerKeyVRF . snd . mkVRFKeyPair $ RawSeed 0 0 0 0 0,
          _poolPledge = Coin 0,
          _poolCost = Coin 0,
          _poolMargin = unsafeBoundRational 0,
          _poolRAcnt = RewardAcnt Testnet (scriptStakeCredSuceed pf),
          _poolOwners = mempty,
          _poolRelays = mempty,
          _poolMD = SJust $ PoolMetadata (fromJust $ textToUrl "") tooManyBytes
        }

poolMDHTooBigTx ::
  forall era.
  ( Scriptic era,
    SignBody era
  ) =>
  Proof era ->
  Core.Tx era
poolMDHTooBigTx pf =
  -- Note that the UTXOW rule will no trigger the expected predicate failure,
  -- since it is checked in the POOL rule. BBODY will trigger it, however.
  newTx
    Override
    pf
    [ Body (poolMDHTooBigTxBody pf),
      Witnesses'
        [ AddrWits [makeWitnessVKey (hashAnnotated (poolMDHTooBigTxBody pf)) (someKeys pf)]
        ]
    ]

-- =======================
-- Alonzo UTXOW Tests
-- =======================

type A = AlonzoEra C_Crypto

testUTXOW ::
  ValidatedTx A ->
  Either [PredicateFailure (Core.EraRule "UTXOW" A)] (UTxOState A) ->
  Assertion
testUTXOW tx (Right expectedSt) =
  checkTrace @(AlonzoUTXOW A) runShelleyBase (utxoEnv (Alonzo Mock)) $
    pure (initialUtxoSt $ Alonzo Mock) .- tx .-> expectedSt
testUTXOW tx predicateFailure@(Left _) = do
  let st =
        runShelleyBase $
          applySTSTest @(AlonzoUTXOW A)
            (TRC (utxoEnv (Alonzo Mock), (initialUtxoSt $ Alonzo Mock), tx))
  st @?= predicateFailure

trustMe :: Bool -> Core.Tx A -> ValidatedTx A
trustMe v (Core.Tx b w a) = ValidatedTx b w (IsValidating v) a

alonzoUTXOWexamples :: TestTree
alonzoUTXOWexamples =
  testGroup
    "Alonzo UTXOW examples"
    [ testGroup
        "valid transactions"
        [ testCase "validating SPEND script" $
            testUTXOW
              (trustMe True $ validatingTx pf)
              (Right . utxoStEx1 $ pf),
          testCase "not validating SPEND script" $
            testUTXOW
              (trustMe False $ notValidatingTx pf)
              (Right . utxoStEx2 $ pf),
          testCase "validating CERT script" $
            testUTXOW
              (trustMe True $ validatingTxWithCert pf)
              (Right . utxoStEx3 $ pf),
          testCase "not validating CERT script" $
            testUTXOW
              (trustMe False $ notValidatingTxWithCert pf)
              (Right . utxoStEx4 $ pf),
          testCase "validating WITHDRAWAL script" $
            testUTXOW
              (trustMe True $ validatingTxWithWithdrawal pf)
              (Right . utxoStEx5 $ pf),
          testCase "not validating WITHDRAWAL script" $
            testUTXOW
              (trustMe False $ notValidatingTxWithWithdrawal pf)
              (Right . utxoStEx6 $ pf),
          testCase "validating MINT script" $
            testUTXOW
              (trustMe True $ validatingTxWithMint pf)
              (Right . utxoStEx7 $ pf),
          testCase "not validating MINT script" $
            testUTXOW
              (trustMe False $ notValidatingTxWithMint pf)
              (Right . utxoStEx8 $ pf),
          testCase "validating scripts everywhere" $
            testUTXOW
              (trustMe True $ validatingTxManyScripts pf)
              (Right . utxoStEx9 $ pf),
          testCase "acceptable supplimentary datum" $
            testUTXOW
              (trustMe True $ okSupplimentaryDatumTx pf)
              (Right . utxoStEx10 $ pf)
        ],
      testGroup
        "invalid transactions"
        [ testCase "wrong network ID" $
            testUTXOW
              (trustMe True $ incorrectNetworkIDTx pf)
              ( Left
                  [ WrappedShelleyEraFailure
                      (UtxoFailure (WrongNetworkInTxBody Testnet Mainnet))
                  ]
              ),
          testCase "missing required key witness" $
            testUTXOW
              (trustMe True $ missingRequiredWitnessTx pf)
              ( Left [(MissingRequiredSigners . Set.singleton) extraneousKeyHash]
              ),
          testCase "missing redeemer" $
            testUTXOW
              (trustMe True $ missingRedeemerTx pf)
              ( Left
                  [ WrappedShelleyEraFailure . UtxoFailure
                      . UtxosFailure
                      . CollectErrors
                      $ [NoRedeemer (Spending (TxIn genesisId 1))],
                    UnRedeemableScripts
                      [ ( Spending (TxIn genesisId 1),
                          (alwaysSucceedsHash 3 pf)
                        )
                      ]
                  ]
              ),
          testCase "wrong wpp hash" $
            testUTXOW
              (trustMe True $ wrongWppHashTx pf)
              ( Left
                  [ PPViewHashesDontMatch
                      ( hashWitnessPPData
                          (pp pf)
                          (Set.singleton PlutusV1)
                          (Redeemers mempty)
                          txDatsExample1
                      )
                      ( hashWitnessPPData
                          (pp pf)
                          (Set.singleton PlutusV1)
                          validatingRedeemersEx1
                          txDatsExample1
                      )
                  ]
              ),
          testCase "missing 1-phase script witness" $
            testUTXOW
              (trustMe True $ missing1phaseScriptWitnessTx pf)
              ( Left
                  [ WrappedShelleyEraFailure . UtxoFailure . UtxosFailure . CollectErrors $
                      [ NoRedeemer (Spending (TxIn genesisId 100)),
                        NoWitness (timelockHash 0 pf)
                      ],
                    WrappedShelleyEraFailure . MissingScriptWitnessesUTXOW . Set.singleton $
                      (timelockHash 0 pf),
                    UnRedeemableScripts [(Spending $ TxIn genesisId 100, timelockHash 0 pf)]
                  ]
              ),
          testCase "missing 2-phase script witness" $
            testUTXOW
              (trustMe True $ missing2phaseScriptWitnessTx pf)
              ( Left
                  [ WrappedShelleyEraFailure . UtxoFailure . UtxosFailure . CollectErrors $
                      [ NoWitness (alwaysSucceedsHash 2 pf),
                        NoWitness (alwaysSucceedsHash 2 pf),
                        NoWitness (alwaysSucceedsHash 2 pf)
                      ],
                    WrappedShelleyEraFailure . MissingScriptWitnessesUTXOW . Set.singleton $
                      (alwaysSucceedsHash 2 pf),
                    UnRedeemableScripts
                      [ ( Rewarding
                            ( RewardAcnt
                                { getRwdNetwork = Testnet,
                                  getRwdCred = ScriptHashObj (alwaysSucceedsHash 2 pf)
                                }
                            ),
                          (alwaysSucceedsHash 2 pf)
                        ),
                        ( Certifying . DCertDeleg . DeRegKey . ScriptHashObj $
                            (alwaysSucceedsHash 2 pf),
                          (alwaysSucceedsHash 2 pf)
                        ),
                        ( Minting (PolicyID {policyID = (alwaysSucceedsHash 2 pf)}),
                          (alwaysSucceedsHash 2 pf)
                        )
                      ]
                  ]
              ),
          testCase "redeemer with incorrect label" $
            testUTXOW
              (trustMe True $ wrongRedeemerLabelTx pf)
              ( Left
                  [ WrappedShelleyEraFailure . UtxoFailure
                      . UtxosFailure
                      . CollectErrors
                      $ [NoRedeemer (Spending (TxIn genesisId 1))],
                    UnRedeemableScripts
                      [ ( Spending (TxIn genesisId 1),
                          (alwaysSucceedsHash 3 pf)
                        )
                      ]
                  ]
              ),
          testCase "missing datum" $
            testUTXOW
              (trustMe True $ missingDatumTx pf)
              ( Left
                  [ MissingRequiredDatums
                      (Set.singleton $ hashData @A datumExample1)
                      mempty
                  ]
              ),
          testCase "phase 1 script failure" $
            testUTXOW
              (trustMe True $ phase1FailureTx pf)
              ( Left
                  [ WrappedShelleyEraFailure . ScriptWitnessNotValidatingUTXOW $
                      Set.fromList
                        [ timelockHash 0 pf,
                          timelockHash 1 pf,
                          timelockHash 2 pf
                        ]
                  ]
              ),
          testCase "valid transaction marked as invalid" $
            testUTXOW
              (trustMe False $ validatingTx pf)
              ( Left
                  [ WrappedShelleyEraFailure
                      ( UtxoFailure
                          (UtxosFailure (ValidationTagMismatch (IsValidating False) ("Script expected to fail, passes.")))
                      )
                  ]
              ),
          testCase "invalid transaction marked as valid" $
            testUTXOW
              (trustMe True $ notValidatingTx pf)
              ( Left
                  [ WrappedShelleyEraFailure
                      (UtxoFailure (UtxosFailure (ValidationTagMismatch (IsValidating True) (""))))
                  ]
              ),
          testCase "too many execution units for tx" $
            testUTXOW
              (trustMe True $ tooManyExUnitsTx pf)
              ( Left
                  [ WrappedShelleyEraFailure . UtxoFailure $
                      ExUnitsTooBigUTxO
                        (ExUnits {exUnitsMem = 1000000, exUnitsSteps = 1000000})
                        (ExUnits {exUnitsMem = 1000001, exUnitsSteps = 5000})
                  ]
              ),
          testCase "missing signature for collateral input" $
            testUTXOW
              (trustMe True $ missingCollateralSig pf)
              ( Left
                  [ WrappedShelleyEraFailure
                      ( MissingVKeyWitnessesUTXOW
                          ( WitHashes
                              ( Set.fromList
                                  [ asWitness $
                                      hashKey (vKey $ someKeys pf)
                                  ]
                              )
                          )
                      )
                  ]
              ),
          testCase "two-phase UTxO with no datum hash" $
            testUTXOW
              (trustMe True $ plutusOutputWithNoDataTx pf)
              ( Left [UnspendableUTxONoDatumHash . Set.singleton $ TxIn genesisId 101]
              ),
          testCase "unacceptable supplimentary datum" $
            testUTXOW
              (trustMe True $ notOkSupplimentaryDatumTx pf)
              ( Left
                  [ NonOutputSupplimentaryDatums
                      (Set.singleton $ hashData @A totallyIrrelevantDatum)
                      mempty
                  ]
              )
        ]
    ]
  where
    pf = Alonzo Mock

-- Test for Plutus Data Ordering

collectTwoPhaseScriptInputsOutputOrdering :: Assertion
collectTwoPhaseScriptInputsOutputOrdering =
  collectTwoPhaseScriptInputs testEpochInfo testSystemStart (pp apf) (validatingTx apf) (initUTxO apf)
    @?= Right
      [ ( always 3 apf,
          [datumExample1, redeemerExample1, context],
          ExUnits 5000 5000,
          freeCostModel
        )
      ]
  where
    apf = Alonzo Mock
    context =
      valContext
        (runIdentity $ txInfo testEpochInfo testSystemStart (initUTxO apf) (validatingTx apf))
        (Spending $ TxIn genesisId 1)

collectOrderingAlonzo :: TestTree
collectOrderingAlonzo =
  testCase
    "collectTwoPhaseScriptInputs output order"
    $ collectTwoPhaseScriptInputsOutputOrdering

-- =======================
-- Alonzo BBODY Tests
-- =======================

bbodyEnv :: Proof era -> BbodyEnv era
bbodyEnv pf = BbodyEnv (pp pf) def

dpstate :: Scriptic era => Proof era -> DPState (Crypto era)
dpstate pf =
  def
    { _dstate =
        def {_rewards = Map.singleton (scriptStakeCredSuceed pf) (Coin 1000)}
    }

initialBBodyState ::
  ( Default (State (EraRule "PPUP" era)),
    PostShelley era
  ) =>
  Proof era ->
  BbodyState era
initialBBodyState pf =
  BbodyState (LedgerState (initialUtxoSt pf) (dpstate pf)) (BlocksMade mempty)

coldKeys :: CC.Crypto c => KeyPair 'BlockIssuer c
coldKeys = KeyPair vk sk
  where
    (sk, vk) = mkKeyPair (RawSeed 1 2 3 2 1)

makeNaiveBlock ::
  forall era.
  ( Era era,
    ToCBORGroup (TxSeq era),
    VRF.Signable (CC.VRF (Crypto era)) Seed,
    Signable (CC.DSIGN (Crypto era)) (OCertSignable (Crypto era)),
    KES.Signable (CC.KES (Crypto era)) (BHBody (Crypto era))
  ) =>
  [TxInBlock era] ->
  Block era
makeNaiveBlock txs = Block (BHeader bhb sig) txs'
  where
    bhb =
      BHBody
        { bheaderBlockNo = BlockNo 0,
          bheaderSlotNo = SlotNo 0,
          bheaderPrev = GenesisHash,
          bheaderVk = vKey coldKeys,
          bheaderVrfVk = vvrf,
          bheaderEta = coerce $ evalCertified () nonceNonce svrf,
          bheaderL = coerce $ evalCertified () leaderNonce svrf,
          bsize = fromIntegral $ bBodySize txs',
          bhash = hashTxSeq @era txs',
          bheaderOCert =
            OCert
              vkes
              0
              (KESPeriod 0)
              ( signedDSIGN @(Crypto era)
                  (sKey $ coldKeys @(Crypto era))
                  (OCertSignable vkes 0 (KESPeriod 0))
              ),
          bprotver = ProtVer 5 0
        }
    sig = signedKES @(CC.KES (Crypto era)) () 0 bhb skes
    nonceNonce = mkSeed seedEta (SlotNo 0) NeutralNonce
    leaderNonce = mkSeed seedL (SlotNo 0) NeutralNonce
    txs' = (toTxSeq @era) . StrictSeq.fromList $ txs
    (svrf, vvrf) = mkVRFKeyPair (RawSeed 0 0 0 0 2)
    (skes, vkes) = mkKESKeyPair (RawSeed 0 0 0 0 3)

testAlonzoBlock :: Block A
testAlonzoBlock =
  makeNaiveBlock
    [ trustMe True $ validatingTx pf,
      trustMe False $ notValidatingTx pf,
      trustMe True $ validatingTxWithWithdrawal pf,
      trustMe False $ notValidatingTxWithWithdrawal pf,
      trustMe True $ validatingTxWithCert pf,
      trustMe False $ notValidatingTxWithCert pf,
      trustMe True $ validatingTxWithMint pf,
      trustMe False $ notValidatingTxWithMint pf
    ]
  where
    pf = Alonzo Mock

testAlonzoBadPMDHBlock :: Block A
testAlonzoBadPMDHBlock = makeNaiveBlock [trustMe True $ poolMDHTooBigTx pf]
  where
    pf = Alonzo Mock

example1UTxO :: UTxO A
example1UTxO =
  UTxO $
    Map.fromList
      [ (TxIn (txid @A (validatingBody pf)) 0, outEx1 pf),
        (TxIn (txid @A (validatingBodyWithCert pf)) 0, outEx3 pf),
        (TxIn (txid @A (validatingBodyWithWithdrawal pf)) 0, outEx5 pf),
        (TxIn (txid @A (validatingBodyWithMint pf)) 0, outEx7 pf),
        (TxIn genesisId 11, collateralOutput pf),
        (TxIn genesisId 2, alwaysFailsOutput pf),
        (TxIn genesisId 13, collateralOutput pf),
        (TxIn genesisId 4, someOutput pf),
        (TxIn genesisId 15, collateralOutput pf),
        (TxIn genesisId 6, someOutput pf),
        (TxIn genesisId 17, collateralOutput pf),
        (TxIn genesisId 8, someOutput pf),
        (TxIn genesisId 100, timelockOut pf),
        (TxIn genesisId 101, unspendableOut pf)
      ]
  where
    pf = Alonzo Mock

example1UtxoSt :: UTxOState A
example1UtxoSt = UTxOState example1UTxO (Coin 0) (Coin 4020) def

example1BBodyState :: BbodyState A
example1BBodyState =
  BbodyState (LedgerState example1UtxoSt def) (BlocksMade $ Map.singleton poolID 1)
  where
    poolID = hashKey . vKey . coerceKeyRole $ coldKeys

testBBODY ::
  BbodyState A ->
  Block A ->
  Either [PredicateFailure (AlonzoBBODY A)] (BbodyState A) ->
  Assertion
testBBODY initialSt block (Right expectedSt) =
  checkTrace @(AlonzoBBODY A) runShelleyBase (bbodyEnv $ Alonzo Mock) $
    pure initialSt .- block .-> expectedSt
testBBODY initialSt block predicateFailure@(Left _) = do
  let st =
        runShelleyBase $
          applySTSTest @(AlonzoBBODY A)
            (TRC (bbodyEnv (Alonzo Mock), initialSt, block))
  st @?= predicateFailure

alonzoBBODYexamples :: TestTree
alonzoBBODYexamples =
  testGroup
    "Alonzo BBODY examples"
    [ testCase "eight plutus scripts cases" $
        testBBODY (initialBBodyState pf) testAlonzoBlock (Right example1BBodyState),
      testCase "block with bad pool md hash in tx" $
        testBBODY
          (initialBBodyState pf)
          testAlonzoBadPMDHBlock
          ( Left
              [ ShelleyInAlonzoPredFail . LedgersFailure . LedgerFailure . DelegsFailure . DelplFailure . PoolFailure $
                  PoolMedataHashTooBig (coerceKeyRole . hashKey . vKey $ someKeys pf) (hashsize @Mock + 1)
              ]
          )
    ]
  where
    pf = Alonzo Mock
