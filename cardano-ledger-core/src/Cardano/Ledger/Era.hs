{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

-- | Support for multiple (Shelley-based) eras in the ledger.
module Cardano.Ledger.Era
  ( Era,
    Crypto,
    PreviousEra,
    TranslationContext,
    TranslateEra (..),
    translateEra',
    translateEraMaybe,
    WellFormed,
    ValidateScript (..),
    -- $segWit
    SupportsSegWit (..),
    TxInBlock,
  )
where

import qualified Cardano.Crypto.Hash as Hash
import Cardano.Ledger.Address (Addr)
import Cardano.Ledger.AuxiliaryData (AuxiliaryDataHash)
import Cardano.Ledger.Coin (Coin)
import Cardano.Ledger.Compactible (Compactible)
import qualified Cardano.Ledger.Core as Core
import qualified Cardano.Ledger.Crypto as CryptoClass
import Cardano.Ledger.Hashes
  ( EraIndependentAuxiliaryData,
    EraIndependentBlockBody,
    EraIndependentTxBody,
    ScriptHash (..),
  )
import Cardano.Ledger.SafeHash
  ( HashAnnotated (..),
    SafeToHash (..),
  )
import Cardano.Ledger.Val (Val)
import Control.Monad.Except (Except, runExcept)
import qualified Data.ByteString as BS
import Data.Coerce (Coercible, coerce)
import Data.Kind (Type)
import Data.Map (Map)
import Data.Maybe.Strict (StrictMaybe)
import Data.Sequence.Strict (StrictSeq)
import Data.Set (Set)
import Data.Typeable (Typeable)
import Data.Void (Void, absurd)
import Data.Word (Word64)
import GHC.Records (HasField (..))

--------------------------------------------------------------------------------
-- Era
--------------------------------------------------------------------------------

class
  ( CryptoClass.Crypto (Crypto e),
    Typeable e,
    WellFormed e
  ) =>
  Era e
  where
  type Crypto e :: Type

-----------------------------------------------------------------------------
-- Script Validation
-----------------------------------------------------------------------------

-- HasField "scriptWits" (ValidatedTx era) (Map.Map (ScriptHash c) script)

-- | Typeclass for script data types. Allows for script validation and hashing.
--   You must understand the role of SafeToHash and scriptPrefixTag to make new
--   instances. 'scriptPrefixTag' is a magic number representing the tag of the
--   script language. For each new script language defined, a new tag is chosen
--   and the tag is included in the script hash for a script. The safeToHash
--   constraint ensures that Scripts are never reserialised.
class
  ( Era era,
    SafeToHash (Core.Script era),
    HasField "body" (Core.Tx era) (Core.TxBody era)
  ) =>
  ValidateScript era
  where
  scriptPrefixTag :: Core.Script era -> BS.ByteString
  validateScript :: Core.Script era -> Core.Tx era -> Bool
  hashScript :: Core.Script era -> ScriptHash (Crypto era)
  -- ONE SHOULD NOT OVERIDE THE hashScript DEFAULT METHOD
  -- UNLESS YOU UNDERSTAND THE SafeToHash class, AND THE ROLE OF THE scriptPrefixTag
  hashScript =
    ScriptHash . Hash.castHash
      . Hash.hashWith
        (\x -> scriptPrefixTag @era x <> originalBytes x)
  isNativeScript :: Core.Script era -> Bool
  isNativeScript _ = True

--------------------------------------------------------------------------------
-- Segregated Witness
--------------------------------------------------------------------------------

-- $segWit
-- * Segregated Witness
--
-- The idea of segretated witnessing is to alter the encoding of transactions in
-- a block such that the witnesses (the information needed to verify the
-- validity of the transactions) can be stored separately from the body (the
-- information needed to update the ledger state). In this way, a node which
-- only cares about replaying transactions need not even decode the witness
-- information.
--
-- In order to do this, we introduce two concepts:
-- - A 'TxSeq`, which represents the decoded structure of a sequence of
--   transactions as represented in the encoded block; that is, with witnessing,
--   metadata and other non-body parts split separately.

-- | Indicates that an era supports segregated witnessing.
--
--   This class is embodies an isomorphism between 'TxSeq era' and 'StrictSeq
--   (Tx era)', witnessed by 'fromTxSeq' and 'toTxSeq'.
class SupportsSegWit era where
  type TxSeq era :: Type

  fromTxSeq :: TxSeq era -> StrictSeq (Core.Tx era)
  toTxSeq :: StrictSeq (Core.Tx era) -> TxSeq era

  -- | Get the block body hash from the TxSeq. Note that this is not a regular
  -- "hash the stored bytes" function since the block body hash forms a small
  -- Merkle tree.
  hashTxSeq ::
    TxSeq era ->
    Hash.Hash (CryptoClass.HASH (Crypto era)) EraIndependentBlockBody

  -- | The number of segregated components
  numSegComponents :: Word64

{-# DEPRECATED TxInBlock "Please use Cardano.Ledger.Core.Tx instead." #-}

-- | Deprecated alias for Tx.
--
--   TODO Remove this once downstream projects have been updated.
type TxInBlock era = Core.Tx era

--------------------------------------------------------------------------------
-- Era translation
--------------------------------------------------------------------------------

-- | Map an era to its predecessor.
--
-- For example:
--
-- > type instance PreviousEra (AllegraEra c) = ShelleyEra c
type family PreviousEra era :: Type

-- | Per-era context used for 'TranslateEra'.
--
-- This context will be passed to the translation instances of /all/ types of
-- that particular era. In practice, most instances won't need the context, but
-- this approach makes the translation composable (as opposed to having a
-- separate context per type).
type family TranslationContext era :: Type

-- | Translation of types between eras, e.g., from Shelley to Allegra.
--
-- When @era@ is just a phantom type parameter, an empty standalone deriving can be used:
--
-- > newtype Foo era = Foo Int
-- >
-- > instance TranslateEra (Allegra c) Foo
--
-- Note that one could use @DerivingAnyClass@ (@deriving (TranslateEra (Allegra
-- c))@), but this would introduce an undesired coupling between the
-- era-parametric type and (a) particular era(s). The intention is to have a
-- module with orphan instances per era.
--
-- In most cases, the @era@ parameter won't be phantom, and a manual instance
-- will have to be written:
--
-- > newtype Bar era = Bar (TxBody era)
-- >
-- > instance CryptoClass.Crypto c => TranslateEra (Allegra c) Bar where
-- >     translateEra ctxt = Bar <$> translateEra ctxt
-- >
-- > -- With the following instance being in scope:
-- > instance CryptoClass.Crypto c => TranslatEra (Allegra c) TxBody
--
-- Note: we use 'PreviousEra' instead of @NextEra@ as an era definitely knows
-- its predecessor, but not necessarily its successor. Moreover, one could argue
-- that it makes more sense to define the translation from era A to era B where
-- era B is defined, than where era A is defined.
class (Era era, Era (PreviousEra era)) => TranslateEra era f where
  -- | Most translations should be infallible (default instance), but we leave
  -- the door open for partial translations.
  --
  -- For a partial translation, override the default type to be '()' or a
  -- concrete error type.
  type TranslationError era f :: Type

  type TranslationError era f = Void

  -- | Translate a type @f@ parameterised by the era from an era to the era
  -- after it.
  --
  -- The translation is a given the translation context of @era@.
  --
  -- A default instance is provided for when the two types are 'Coercible'.
  translateEra :: TranslationContext era -> f (PreviousEra era) -> Except (TranslationError era f) (f era)
  default translateEra ::
    Coercible (f (PreviousEra era)) (f era) =>
    TranslationContext era ->
    f (PreviousEra era) ->
    Except (TranslationError era f) (f era)
  translateEra _ = return . coerce

-- | Variant of 'translateEra' for when 'TranslationError' is 'Void' and the
-- translation thus cannot fail.
translateEra' ::
  (TranslateEra era f, TranslationError era f ~ Void) =>
  TranslationContext era ->
  f (PreviousEra era) ->
  f era
translateEra' ctxt = either absurd id . runExcept . translateEra ctxt

-- | Variant of 'translateEra' for when 'TranslationError' is '()', converting
-- the result to a 'Maybe'.
translateEraMaybe ::
  (TranslateEra era f, TranslationError era f ~ ()) =>
  TranslationContext era ->
  f (PreviousEra era) ->
  Maybe (f era)
translateEraMaybe ctxt =
  either (const Nothing) Just . runExcept . translateEra ctxt

-- ==========================================================
-- WellFormed-ness
-- ==========================================================

-- | All Well Formed Eras have this minimal structure.
type WellFormed era =
  ( -- TxBody
    HasField "outputs" (Core.TxBody era) (StrictSeq (Core.TxOut era)),
    HasField "txfee" (Core.TxBody era) Coin,
    HasField "minted" (Core.TxBody era) (Set (ScriptHash (Crypto era))),
    HasField "adHash" (Core.TxBody era) (StrictMaybe (AuxiliaryDataHash (Crypto era))),
    -- Tx
    HasField "body" (Core.Tx era) (Core.TxBody era),
    HasField "wits" (Core.Tx era) (Core.Witnesses era),
    HasField "auxiliaryData" (Core.Tx era) (StrictMaybe (Core.AuxiliaryData era)),
    HasField "txsize" (Core.Tx era) Integer,
    HasField "scriptWits" (Core.Tx era) (Map (ScriptHash (Crypto era)) (Core.Script era)),
    -- TxOut
    HasField "value" (Core.TxOut era) (Core.Value era),
    HasField "address" (Core.TxOut era) (Addr (Crypto era)),
    -- HashAnnotated
    HashAnnotated (Core.AuxiliaryData era) EraIndependentAuxiliaryData (Crypto era),
    HashAnnotated (Core.TxBody era) EraIndependentTxBody (Crypto era),
    SupportsSegWit era,
    Val (Core.Value era),
    Compactible (Core.Value era) -- TxOut stores a CompactForm(Core.Value)
  )

{-  TODO, there are a few other constraints which are WellFormed and we should add
them when time permits. Some are not added because the types they mentions reside
in files that cause circular import dependencies.
   -- import Shelley.Spec.Ledger.TxBody(DCert,Wdrl,WitVKey)
   -- import Shelley.Spec.Ledger.Tx(TxIn)
These would have to be moved into a module such as Cardano.Ledger.TxBase(TxIn,DCert,Wdrl)
   -- HasField "inputs" (Core.TxBody era) (Set (TxIn (Crypto era))),       -- all possible inputs
   -- HasField "txinputs_fee" (Core.TxBody era) (Set (TxIn (Crypto era)))  -- inputs that can be used to pay fees
   -- HasField "certs" (Core.TxBody era) (StrictSeq (DCert (Crypto era))),
   -- HasField "wdrls" (Core.TxBody era) (Wdrl (Crypto era)),
   -- HasField "addrWits" (Core.Tx era) (Set (WitVKey 'Witness (Crypto era)))
others where the concrete type (Update and WitnessSet) will have to be made into a type family
   -- import Shelley.Spec.Ledger.PParams (Update)
   -- import Shelley.Spec.Ledger.Tx(WitnessSet)
   -- import Cardano.Ledger.Alonzo.Scripts (ExUnits)
   -- HasField "update" (Core.TxBody era) (StrictMaybe (Update era)),
   -- HasField "wits" (Core.Tx era) (WitnessSet era),
   -- HasField "exUnits" (Core.Tx era) ExUnits,
-}
