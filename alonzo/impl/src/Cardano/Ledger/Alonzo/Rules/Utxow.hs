{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Cardano.Ledger.Alonzo.Rules.Utxow where

import Cardano.Binary (FromCBOR (..), ToCBOR (..))
import Cardano.Ledger.Address (Addr (..), bootstrapKeyHash, getRwdCred)
import Cardano.Ledger.Alonzo.Data (DataHash)
import Cardano.Ledger.Alonzo.Language (Language (..))
import Cardano.Ledger.Alonzo.PParams (PParams)
import Cardano.Ledger.Alonzo.PlutusScriptApi
  ( checkScriptData,
    language,
    scriptsNeeded,
  )
import Cardano.Ledger.Alonzo.Rules.Utxo (AlonzoUTXO)
import qualified Cardano.Ledger.Alonzo.Rules.Utxo as Alonzo (UtxoPredicateFailure)
import Cardano.Ledger.Alonzo.Scripts (Script (..))
import Cardano.Ledger.Alonzo.Tx
  ( ScriptPurpose,
    ValidatedTx (..),
    hashWitnessPPData,
    isTwoPhaseScriptAddress,
    rdptr,
  )
import Cardano.Ledger.Alonzo.TxBody (WitnessPPDataHash)
import Cardano.Ledger.Alonzo.TxWitness
  ( RdmrPtr,
    TxWitness (..),
    unRedeemers,
    unTxDats,
  )
import Cardano.Ledger.BaseTypes
  ( ShelleyBase,
    StrictMaybe (..),
    strictMaybeToMaybe,
  )
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Credential (Credential (KeyHashObj))
import Cardano.Ledger.Era (Crypto, Era, ValidateScript (..))
import Cardano.Ledger.Keys (GenDelegs, KeyHash, KeyRole (..), asWitness)
import Cardano.Ledger.Rules.ValidationMode ((?!#))
import Control.DeepSeq (NFData (..))
import Control.Iterate.SetAlgebra (domain, eval, (⊆), (◁), (➖))
import Control.State.Transition.Extended
import Data.Coders
import Data.Foldable (toList)
import qualified Data.Map.Strict as Map
import Data.Sequence.Strict (StrictSeq)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import GHC.Records
import NoThunks.Class
import Shelley.Spec.Ledger.Delegation.Certificates
  ( delegCWitness,
    genesisCWitness,
    poolCWitness,
    requiresVKeyWitness,
  )
import Shelley.Spec.Ledger.LedgerState
  ( UTxOState (..),
    WitHashes (..),
    propWits,
    unWitHashes,
    witsFromTxWitnesses,
  )
import Shelley.Spec.Ledger.PParams (Update)
import Shelley.Spec.Ledger.STS.Utxo (UtxoEnv (..))
import Shelley.Spec.Ledger.STS.Utxow
  ( ShelleyStyleWitnessNeeds,
    UtxowPredicateFailure (..),
    shelleyStyleWitness,
  )
import Shelley.Spec.Ledger.Scripts (ScriptHash (..))
import Shelley.Spec.Ledger.Tx (TxIn (..), extractKeyHashWitnessSet)
import Shelley.Spec.Ledger.TxBody
  ( DCert (DCertDeleg, DCertGenesis, DCertPool),
    PoolCert (RegPool),
    PoolParams (..),
    Wdrl,
    unWdrl,
  )
import Shelley.Spec.Ledger.UTxO (UTxO (..), txinLookup)

-- =================================================

-- | The Predicate failure type in the Alonzo Era. It embeds the Predicate
--   failure type of the Shelley Era, as they share some failure modes.
data AlonzoPredFail era
  = WrappedShelleyEraFailure !(UtxowPredicateFailure era)
  | UnRedeemableScripts ![(ScriptPurpose (Crypto era), ScriptHash (Crypto era))]
  | MissingRequiredDatums
      !(Set (DataHash (Crypto era))) -- Set of missing data hashes
      !(Set (DataHash (Crypto era))) -- Set of received data hashes
  | NonOutputSupplimentaryDatums
      !(Set (DataHash (Crypto era))) -- Set of unallowed data hashes
      !(Set (DataHash (Crypto era))) -- Set of acceptable supplimental data hashes
  | PPViewHashesDontMatch
      !(StrictMaybe (WitnessPPDataHash (Crypto era)))
      -- ^ The PPHash in the TxBody
      !(StrictMaybe (WitnessPPDataHash (Crypto era)))
      -- ^ Computed from the current Protocol Parameters
  | MissingRequiredSigners (Set (KeyHash 'Witness (Crypto era)))
  | UnspendableUTxONoDatumHash (Set (TxIn (Crypto era)))
  | ExtraRedeemers ![RdmrPtr]
  deriving (Generic)

deriving instance
  ( Era era,
    Show (PredicateFailure (Core.EraRule "UTXO" era)), -- The Shelley UtxowPredicateFailure needs this to Show
    Show (Core.Script era)
  ) =>
  Show (AlonzoPredFail era)

deriving instance
  ( Era era,
    Eq (PredicateFailure (Core.EraRule "UTXO" era)), -- The Shelley UtxowPredicateFailure needs this to Eq
    Eq (Core.Script era)
  ) =>
  Eq (AlonzoPredFail era)

instance
  ( Era era,
    NoThunks (Core.Script era),
    NoThunks (PredicateFailure (Core.EraRule "UTXO" era))
  ) =>
  NoThunks (AlonzoPredFail era)

instance
  ( Era era,
    ToCBOR (PredicateFailure (Core.EraRule "UTXO" era)),
    Typeable (Core.AuxiliaryData era),
    Typeable (Core.Script era),
    ToCBOR (Core.Script era)
  ) =>
  ToCBOR (AlonzoPredFail era)
  where
  toCBOR x = encode (encodePredFail x)

encodePredFail ::
  ( Era era,
    ToCBOR (PredicateFailure (Core.EraRule "UTXO" era)),
    Typeable (Core.Script era),
    Typeable (Core.AuxiliaryData era)
  ) =>
  AlonzoPredFail era ->
  Encode 'Open (AlonzoPredFail era)
encodePredFail (WrappedShelleyEraFailure x) = Sum WrappedShelleyEraFailure 0 !> E toCBOR x
encodePredFail (UnRedeemableScripts x) = Sum UnRedeemableScripts 1 !> To x
encodePredFail (MissingRequiredDatums x y) = Sum MissingRequiredDatums 2 !> To x !> To y
encodePredFail (NonOutputSupplimentaryDatums x y) = Sum NonOutputSupplimentaryDatums 3 !> To x !> To y
encodePredFail (PPViewHashesDontMatch x y) = Sum PPViewHashesDontMatch 4 !> To x !> To y
encodePredFail (MissingRequiredSigners x) = Sum MissingRequiredSigners 5 !> To x
encodePredFail (UnspendableUTxONoDatumHash x) = Sum UnspendableUTxONoDatumHash 6 !> To x
encodePredFail (ExtraRedeemers x) = Sum ExtraRedeemers 7 !> To x

instance
  ( Era era,
    FromCBOR (PredicateFailure (Core.EraRule "UTXO" era)),
    Typeable (Core.Script era),
    Typeable (Core.AuxiliaryData era)
  ) =>
  FromCBOR (AlonzoPredFail era)
  where
  fromCBOR = decode (Summands "(AlonzoPredFail" decodePredFail)

decodePredFail ::
  ( Era era,
    FromCBOR (PredicateFailure (Core.EraRule "UTXO" era)), -- TODO, we should be able to get rid of this constraint
    Typeable (Core.Script era),
    Typeable (Core.AuxiliaryData era)
  ) =>
  Word ->
  Decode 'Open (AlonzoPredFail era)
decodePredFail 0 = SumD WrappedShelleyEraFailure <! D fromCBOR
decodePredFail 1 = SumD UnRedeemableScripts <! From
decodePredFail 2 = SumD MissingRequiredDatums <! From <! From
decodePredFail 3 = SumD NonOutputSupplimentaryDatums <! From <! From
decodePredFail 4 = SumD PPViewHashesDontMatch <! From <! From
decodePredFail 5 = SumD MissingRequiredSigners <! From
decodePredFail 6 = SumD UnspendableUTxONoDatumHash <! From
decodePredFail 7 = SumD ExtraRedeemers <! From
decodePredFail n = Invalid n

-- =============================================

-- | given the "txscripts" field of the Witnesses, compute the set of languages used in a transaction
langsUsed :: forall era. (Core.Script era ~ Script era, ValidateScript era) => Map.Map (ScriptHash (Crypto era)) (Script era) -> Set Language
langsUsed hashScriptMap =
  Set.fromList
    [ l | (_hash, script) <- Map.toList hashScriptMap, (not . isNativeScript @era) script, Just l <- [language @era script]
    ]

{- Defined in the Shelley Utxow rule.
type ShelleyStyleWitnessNeeds era =
  ( HasField "certs" (Core.TxBody era) (StrictSeq (DCert (Crypto era))),
    HasField "inputs" (Core.TxBody era) (Set (TxIn (Crypto era))),
    HasField "wdrls" (Core.TxBody era) (Wdrl (Crypto era)),
    HasField "addrWits" (Core.Tx era) (Set (WitVKey 'Witness (Crypto era))),
    HasField "update" (Core.TxBody era) (StrictMaybe (Update era)),
    HasField "_protocolVersion" (Core.PParams era) ProtVer,
    ValidateAuxiliaryData era (Crypto era),
    ValidateScript era,
    DSignable (Crypto era) (Hash (Crypto era) EraIndependentTxBody)
  )
-}

-- | Constraints to make an Alonzo Utxow STS instance
--   (in addition to ShelleyStyleWitnessNeeds)
type AlonzoStyleAdditions era =
  ( HasField "datahash" (Core.TxOut era) (StrictMaybe (DataHash (Crypto era))), -- BE SURE AND ADD THESE INSTANCES
    HasField "wppHash" (Core.TxBody era) (StrictMaybe (WitnessPPDataHash (Crypto era)))
  )

-- | A somewhat generic STS transitionRule function for the Alonzo Era.
alonzoStyleWitness ::
  forall era utxow.
  ( Era era,
    -- Fix some Core types to the Alonzo Era
    Core.Tx era ~ ValidatedTx era, -- scriptsNeeded, checkScriptData etc. are fixed at Alonzo.Tx
    Core.PParams era ~ PParams era,
    Core.Script era ~ Script era,
    -- Allow UTXOW to call UTXO
    Embed (Core.EraRule "UTXO" era) (utxow era),
    Environment (Core.EraRule "UTXO" era) ~ UtxoEnv era,
    State (Core.EraRule "UTXO" era) ~ UTxOState era,
    Signal (Core.EraRule "UTXO" era) ~ ValidatedTx era,
    -- Asumptions needed since we are going to fix utxow when we use this in an STS Era
    BaseM (utxow era) ~ ShelleyBase,
    Environment (utxow era) ~ UtxoEnv era,
    State (utxow era) ~ UTxOState era,
    Signal (utxow era) ~ ValidatedTx era,
    PredicateFailure (utxow era) ~ AlonzoPredFail era,
    STS (utxow era),
    -- Supply the HasField and Validate instances for Alonzo
    ShelleyStyleWitnessNeeds era,
    AlonzoStyleAdditions era,
    -- New transaction body fields needed for Alonzo
    HasField "reqSignerHashes" (Core.TxBody era) (Set (KeyHash 'Witness (Crypto era))),
    HasField "collateral" (Core.TxBody era) (Set (TxIn (Crypto era)))
  ) =>
  TransitionRule (utxow era)
alonzoStyleWitness = do
  (TRC (UtxoEnv _slot pp _stakepools _genDelegs, u', tx)) <- judgmentContext

  {-  (utxo,_,_,_ ) := utxoSt  -}
  {-  txb := txbody tx  -}
  {-  txw := txwits tx  -}
  {-  witsKeyHashes := { hashKey vk | vk ∈ dom(txwitsVKey txw) }  -}
  let utxo = _utxo u'
      txbody = getField @"body" (tx :: Core.Tx era)
      witsKeyHashes = unWitHashes $ witsFromTxWitnesses @era tx

  {-  { h | (_ → (a,_,h)) ∈ txins tx ◁ utxo, isNonNativeScriptAddress tx a} = dom(txdats txw)   -}
  let inputs = getField @"inputs" txbody :: (Set (TxIn (Crypto era)))
      smallUtxo = eval (inputs ◁ utxo) :: Map.Map (TxIn (Crypto era)) (Core.TxOut era)
      twoPhaseOuts =
        [ output
          | (_input, output) <- Map.toList smallUtxo,
            isTwoPhaseScriptAddress @era tx (getField @"address" output)
        ]
      utxoHashes' = mapM (getField @"datahash") twoPhaseOuts
  case utxoHashes' of
    SNothing ->
      -- In the spec, the Nothing value can end up on the left hand side
      -- of the equality check, but we must explicitly rule it out.
      failBecause . UnspendableUTxONoDatumHash . Set.fromList $
        [ input
          | (input, output) <- Map.toList smallUtxo,
            SNothing <- [getField @"datahash" output],
            isTwoPhaseScriptAddress @era tx (getField @"address" output)
        ]
    SJust utxoHashes -> do
      let txHashes = domain (unTxDats . txdats . wits $ tx)
          inputHashes = Set.fromList utxoHashes
          unmatchedDatumHashes = eval (inputHashes ➖ txHashes)
      Set.null unmatchedDatumHashes ?! MissingRequiredDatums unmatchedDatumHashes txHashes

      -- Check that all supplimental datums contained in the witness set appear in the outputs.
      let outputDatumHashes =
            Set.fromList
              [ dh
                | out <- toList $ getField @"outputs" txbody,
                  SJust dh <- [getField @"datahash" out]
              ]
          supplimentalDatumHashes = eval (txHashes ➖ inputHashes)
          (okSupplimentalDHs, notOkSupplimentalDHs) =
            Set.partition (`Set.member` outputDatumHashes) supplimentalDatumHashes
      Set.null notOkSupplimentalDHs
        ?! NonOutputSupplimentaryDatums notOkSupplimentalDHs okSupplimentalDHs

  {-  ∀ sph ∈ scriptsNeeded utxo tx, checkScriptData tx utxo  ph  -}
  let sphs :: [(ScriptPurpose (Crypto era), ScriptHash (Crypto era))]
      sphs = scriptsNeeded utxo tx
      unredeemed =
        -- A script is unredeemed, is we can't find the Data that it requires to execute.
        let ans = (filter (not . checkScriptData tx) sphs)
         in seq (rnf ans) ans
  null unredeemed ?! UnRedeemableScripts unredeemed

  {-  || { (sp, h) ∈ \fun{scriptsNeeded} utxo tx | h\mapsto s ∈ txscripts txw, s ∈ ScriptPhTwo } || = || fun{txrdmrs} tx ||  -}
  let rdptrs = Set.fromList [el | (sp, _) <- sphs, SJust el <- [rdptr @era txbody sp]]
      extraRdmrs :: [RdmrPtr]
      extraRdmrs = Map.keys $ Map.withoutKeys (unRedeemers $ txrdmrs $ wits tx) rdptrs
  null extraRdmrs ?! ExtraRedeemers extraRdmrs

  {-  THIS DOES NOT APPPEAR IN THE SPEC as a separate check, but
      witsVKeyNeeded includes the reqSignerHashes in the union   -}
  let reqSignerHashes' = getField @"reqSignerHashes" txbody
  eval (reqSignerHashes' ⊆ witsKeyHashes)
    ?!# MissingRequiredSigners (eval $ reqSignerHashes' ➖ witsKeyHashes)

  {-  wppHash txb = hashWitnessPPData pp (languages txw) (txrdmrs txw)  -}
  let languages =
        [ l
          | (_hash, script) <- Map.toList (getField @"scriptWits" tx),
            (not . isNativeScript @era) script,
            Just l <- [language @era script]
        ]
      computedPPhash = hashWitnessPPData pp (Set.fromList languages) (txrdmrs . wits $ tx) (txdats . wits $ tx)
      bodyPPhash = getField @"wppHash" txbody
  bodyPPhash == computedPPhash ?! PPViewHashesDontMatch bodyPPhash computedPPhash

  {- The shelleyStyleWitness calls the UTXO rule which applies all these rules -}
  {-  ∀ s ∈ range(txscripts txw) ∩ Scriptnative), runNativeScript s tx   -}
  {-  { s | (_,s) ∈ scriptsNeeded utxo tx} = dom(txscripts txw)          -}
  {-  ∀ (vk ↦ σ) ∈ (txwitsVKey txw), V_vk⟦ txbodyHash ⟧_σ                -}
  {-  witsVKeyNeeded utxo tx genDelegs ⊆ witsKeyHashes                   -}
  {-  genSig := { hashKey gkey | gkey ∈ dom(genDelegs)} ∩ witsKeyHashes  -}
  {-  { c ∈ txcerts txb ∩ DCert_mir} ≠ ∅  ⇒ (|genSig| ≥ Quorum) ∧ (d pp > 0)  -}
  {-   adh := txADhash txb;  ad := auxiliaryData tx                      -}
  {-  ((adh = ◇) ∧ (ad= ◇)) ∨ (adh = hashAD ad)                          -}
  shelleyStyleWitness witsVKeyNeeded WrappedShelleyEraFailure

-- | Collect the set of hashes of keys that needs to sign a given transaction.
--  This set consists of the txin owners, certificate authors, and withdrawal
--  reward accounts.
--
--  Compared to pre-Alonzo eras, we additionally gather the certificates
--  required to authenticate collateral witnesses.
witsVKeyNeeded ::
  forall era tx.
  ( Era era,
    HasField "body" tx (Core.TxBody era),
    HasField "wdrls" (Core.TxBody era) (Wdrl (Crypto era)),
    HasField "certs" (Core.TxBody era) (StrictSeq (DCert (Crypto era))),
    HasField "inputs" (Core.TxBody era) (Set (TxIn (Crypto era))),
    HasField "collateral" (Core.TxBody era) (Set (TxIn (Crypto era))),
    HasField "update" (Core.TxBody era) (StrictMaybe (Update era))
  ) =>
  UTxO era ->
  tx ->
  GenDelegs (Crypto era) ->
  WitHashes (Crypto era)
witsVKeyNeeded utxo' tx genDelegs =
  WitHashes $
    certAuthors
      `Set.union` inputAuthors
      `Set.union` owners
      `Set.union` wdrlAuthors
      `Set.union` updateKeys
  where
    txbody = getField @"body" tx
    inputAuthors :: Set (KeyHash 'Witness (Crypto era))
    inputAuthors =
      foldr
        accum
        Set.empty
        ( getField @"inputs" txbody
            `Set.union` getField @"collateral" txbody
        )
      where
        accum txin ans =
          case txinLookup txin utxo' of
            Just out ->
              case getField @"address" out of
                Addr _ (KeyHashObj pay) _ -> Set.insert (asWitness pay) ans
                AddrBootstrap bootAddr ->
                  Set.insert (asWitness (bootstrapKeyHash bootAddr)) ans
                _ -> ans
            Nothing -> ans

    wdrlAuthors :: Set (KeyHash 'Witness (Crypto era))
    wdrlAuthors = Map.foldrWithKey accum Set.empty (unWdrl (getField @"wdrls" txbody))
      where
        accum key _ ans = Set.union (extractKeyHashWitnessSet [getRwdCred key]) ans
    owners :: Set (KeyHash 'Witness (Crypto era))
    owners = foldr accum Set.empty (getField @"certs" txbody)
      where
        accum (DCertPool (RegPool pool)) ans =
          Set.union
            (Set.map asWitness (_poolOwners pool))
            ans
        accum _cert ans = ans
    cwitness (DCertDeleg dc) = extractKeyHashWitnessSet [delegCWitness dc]
    cwitness (DCertPool pc) = extractKeyHashWitnessSet [poolCWitness pc]
    cwitness (DCertGenesis gc) = Set.singleton (asWitness $ genesisCWitness gc)
    cwitness c = error $ show c ++ " does not have a witness"
    -- key reg requires no witness but this is already filtered outby requiresVKeyWitness
    -- before the call to `cwitness`, so this error should never be reached.

    certAuthors :: Set (KeyHash 'Witness (Crypto era))
    certAuthors = foldr accum Set.empty (getField @"certs" txbody)
      where
        accum cert ans | requiresVKeyWitness cert = Set.union (cwitness cert) ans
        accum _cert ans = ans
    updateKeys :: Set (KeyHash 'Witness (Crypto era))
    updateKeys =
      asWitness
        `Set.map` propWits
          ( strictMaybeToMaybe $
              getField @"update" txbody
          )
          genDelegs

-- ====================================
-- Make the STS instance

data AlonzoUTXOW era

instance
  forall era.
  ( -- Fix some Core types to the Alonzo Era
    Core.Tx era ~ ValidatedTx era,
    Core.PParams era ~ PParams era,
    Core.Script era ~ Script era,
    -- Allow UTXOW to call UTXO
    Embed (Core.EraRule "UTXO" era) (AlonzoUTXOW era),
    Environment (Core.EraRule "UTXO" era) ~ UtxoEnv era,
    State (Core.EraRule "UTXO" era) ~ UTxOState era,
    Signal (Core.EraRule "UTXO" era) ~ ValidatedTx era,
    -- New transaction body fields needed for Alonzo
    HasField "reqSignerHashes" (Core.TxBody era) (Set (KeyHash 'Witness (Crypto era))),
    HasField "collateral" (Core.TxBody era) (Set (TxIn (Crypto era))),
    -- Supply the HasField and Validate instances for Alonzo
    ShelleyStyleWitnessNeeds era, -- supplies a subset of those needed. All the old Shelley Needs still apply.
    Show (Core.TxOut era),
    AlonzoStyleAdditions era
  ) =>
  STS (AlonzoUTXOW era)
  where
  type State (AlonzoUTXOW era) = UTxOState era
  type Signal (AlonzoUTXOW era) = ValidatedTx era
  type Environment (AlonzoUTXOW era) = UtxoEnv era
  type BaseM (AlonzoUTXOW era) = ShelleyBase
  type
    PredicateFailure (AlonzoUTXOW era) =
      AlonzoPredFail era
  transitionRules = [alonzoStyleWitness]
  initialRules = []

instance
  ( Era era,
    STS (AlonzoUTXO era),
    PredicateFailure (Core.EraRule "UTXO" era) ~ Alonzo.UtxoPredicateFailure era,
    BaseM (AlonzoUTXOW era) ~ ShelleyBase,
    PredicateFailure (AlonzoUTXOW era) ~ AlonzoPredFail era
  ) =>
  Embed (AlonzoUTXO era) (AlonzoUTXOW era)
  where
  wrapFailed = WrappedShelleyEraFailure . UtxoFailure
