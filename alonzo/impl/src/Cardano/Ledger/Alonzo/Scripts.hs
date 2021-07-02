{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
-- Needed for FromCBOR(Annotator CostModel)
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Cardano.Ledger.Alonzo.Scripts
  ( Tag (..),
    Script (TimelockScript, PlutusScript),
    scriptfee,
    ppTag,
    ppScript,
    isPlutusScript,
    alwaysSucceeds,
    alwaysFails,
    pointWiseExUnits,

    -- * Cost Model
    CostModel (..),
    ExUnits (..),
    Prices (..),
    defaultCostModel,
    hashCostModel,
    validateCostModelParams,
    ppExUnits,
    ppCostModel,
    ppPrices,
  )
where

import Cardano.Binary (DecoderError (..), FromCBOR (fromCBOR), ToCBOR (toCBOR), serialize')
import Cardano.Ledger.Coin (Coin (..))
import qualified Cardano.Ledger.Core as Core
import qualified Cardano.Ledger.Crypto as CC (Crypto)
import Cardano.Ledger.Era (Era (Crypto), ValidateScript (hashScript))
import Cardano.Ledger.Pretty
  ( PDoc,
    PrettyA (..),
    ppCoin,
    ppInteger,
    ppMap,
    ppRecord,
    ppScriptHash,
    ppSexp,
    ppString,
    ppWord64,
    text,
  )
import Cardano.Ledger.SafeHash
  ( HashWithCrypto (..),
    SafeHash,
    SafeToHash (..),
  )
import Cardano.Ledger.Serialization (mapFromCBOR)
import Cardano.Ledger.ShelleyMA.Timelocks
import Cardano.Ledger.Val (Val ((<+>), (<×>)))
import Control.DeepSeq (NFData (..))
import Data.ByteString.Short (ShortByteString, fromShort)
import Data.Coders
import Data.Map (Map)
import Data.Text (Text)
import Data.Typeable
import Data.Word (Word64, Word8)
import GHC.Generics (Generic)
import NoThunks.Class (InspectHeapNamed (..), NoThunks)
import Numeric.Natural (Natural)
import Plutus.V1.Ledger.Api (defaultCostModelParams, validateCostModelParams)
import qualified Plutus.V1.Ledger.Examples as Plutus (alwaysFailingNAryFunction, alwaysSucceedingNAryFunction)
import qualified Prettyprinter as PP

-- | Marker indicating the part of a transaction for which this script is acting
-- as a validator.
data Tag
  = -- | Validates spending a script-locked UTxO
    Spend
  | -- | Validates minting new tokens
    Mint
  | -- | Validates certificate transactions
    Cert
  | -- | Validates withdrawl from a reward account
    Rewrd
  deriving (Eq, Generic, Ord, Show, Enum, Bounded)

instance NoThunks Tag

-- =======================================================

-- | Scripts in the Alonzo Era, Either a Timelock script or a Plutus script.
data Script era
  = TimelockScript (Timelock (Crypto era))
  | PlutusScript (ShortByteString) -- A Plutus.V1.Ledger.Scripts(Script) that has been 'CBOR' encoded
  deriving (Eq, Generic, Ord)

instance (ValidateScript era, Core.Script era ~ Script era) => Show (Script era) where
  show (TimelockScript x) = "TimelockScript " ++ show x
  show (s@(PlutusScript _)) = "PlutusScript " ++ show (hashScript @era s)

deriving via
  InspectHeapNamed "Script" (Script era)
  instance
    NoThunks (Script era)

instance NFData (Script era)

-- | Both constructors know their original bytes
instance SafeToHash (Script era) where
  originalBytes (TimelockScript t) = originalBytes t
  originalBytes (PlutusScript bs) = fromShort bs

alwaysSucceeds, alwaysFails :: Natural -> Script era
alwaysSucceeds n = PlutusScript (Plutus.alwaysSucceedingNAryFunction n)
alwaysFails n = PlutusScript (Plutus.alwaysFailingNAryFunction n)

isPlutusScript :: Script era -> Bool
isPlutusScript (PlutusScript _) = True
isPlutusScript (TimelockScript _) = False

-- ===========================================

-- | Arbitrary execution unit in which we measure the cost of scripts.
data ExUnits = ExUnits
  { exUnitsMem :: !Word64,
    exUnitsSteps :: !Word64
  }
  deriving (Eq, Generic, Show) -- It is deliberate that there is NO ORD instance.

instance NoThunks ExUnits

instance NFData ExUnits

instance Semigroup ExUnits where
  ExUnits a c <> ExUnits b d = ExUnits (a + b) (c + d)

instance Monoid ExUnits where
  mempty = ExUnits 0 0

-- | It is deliberate that there is no ORD instace for EXUnits. Use this function
--   to compare if one ExUnit is pointwise compareable to another.
pointWiseExUnits :: (Word64 -> Word64 -> Bool) -> ExUnits -> ExUnits -> Bool
pointWiseExUnits oper (ExUnits m1 s1) (ExUnits m2 s2) = (m1 `oper` m2) && (s1 `oper` s2)

-- =====================================

newtype CostModel = CostModel (Map Text Integer)
  deriving (Eq, Generic, Show, Ord)

-- NOTE: Since cost model serializations need to be independently reproduced,
-- we use the 'canonical' serialization approach used in Byron.
deriving instance ToCBOR CostModel

instance SafeToHash CostModel where
  originalBytes = serialize'

-- CostModel does not determine 'crypto' so make a HashWithCrypto
-- rather than a HashAnotated instance.

instance HashWithCrypto CostModel CostModel

instance NoThunks CostModel

instance NFData CostModel

checkCostModel :: Map Text Integer -> Either String CostModel
checkCostModel cm =
  if validateCostModelParams cm
    then Right (CostModel cm)
    else Left ("Invalid cost model: " ++ show cm)

defaultCostModel :: Maybe CostModel
defaultCostModel = CostModel <$> defaultCostModelParams

instance FromCBOR CostModel where
  fromCBOR = decode $ SumD checkCostModel <? (D mapFromCBOR)

-- CostModel is not parameterized by Crypto or Era so we use the
-- hashWithCrypto function, rather than hashAnnotated

hashCostModel ::
  forall e.
  Era e =>
  Proxy e ->
  CostModel ->
  SafeHash (Crypto e) CostModel
hashCostModel _proxy = hashWithCrypto (Proxy @(Crypto e))

-- ==================================

-- | Prices per execution unit
data Prices = Prices
  { prMem :: !Coin,
    prSteps :: !Coin
  }
  deriving (Eq, Generic, Show, Ord)

instance NoThunks Prices

instance NFData Prices

-- | Compute the cost of a script based upon prices and the number of execution
-- units.
scriptfee :: Prices -> ExUnits -> Coin
scriptfee (Prices pr_mem pr_steps) (ExUnits mem steps) =
  (mem <×> pr_mem) <+> (steps <×> pr_steps)

--------------------------------------------------------------------------------
-- Serialisation
--------------------------------------------------------------------------------

tagToWord8 :: Tag -> Word8
tagToWord8 = toEnum . fromEnum

word8ToTag :: Word8 -> Maybe Tag
word8ToTag e
  | fromEnum e > fromEnum (maxBound :: Tag) = Nothing
  | fromEnum e < fromEnum (minBound :: Tag) = Nothing
  | otherwise = Just $ toEnum (fromEnum e)

instance ToCBOR Tag where
  toCBOR = toCBOR . tagToWord8

instance FromCBOR Tag where
  fromCBOR =
    word8ToTag <$> fromCBOR >>= \case
      Nothing -> cborError $ DecoderErrorCustom "Tag" "Unknown redeemer tag"
      Just n -> pure n

instance ToCBOR ExUnits where
  toCBOR (ExUnits m s) = encode $ Rec ExUnits !> To m !> To s

instance FromCBOR ExUnits where
  fromCBOR = decode $ RecD ExUnits <! From <! From

instance ToCBOR Prices where
  toCBOR (Prices m s) = encode $ Rec Prices !> To m !> To s

instance FromCBOR Prices where
  fromCBOR = decode $ RecD Prices <! From <! From

instance forall era. (Typeable (Crypto era), Typeable era) => ToCBOR (Script era) where
  toCBOR x = encode (encodeScript x)

encodeScript :: (Typeable (Crypto era)) => Script era -> Encode 'Open (Script era)
encodeScript (TimelockScript i) = Sum TimelockScript 0 !> To i
encodeScript (PlutusScript s) = Sum PlutusScript 1 !> To s -- Use the ToCBOR instance of ShortByteString

instance
  (CC.Crypto (Crypto era), Typeable (Crypto era), Typeable era) =>
  FromCBOR (Annotator (Script era))
  where
  fromCBOR = decode (Summands "Alonzo Script" decodeScript)
    where
      decodeScript :: Word -> Decode 'Open (Annotator (Script era))
      decodeScript 0 = Ann (SumD TimelockScript) <*! From
      decodeScript 1 = Ann (SumD PlutusScript) <*! Ann From
      decodeScript n = Invalid n

-- ============================================================
-- Pretty printing versions

ppTag :: Tag -> PDoc
ppTag x = ppString (show x)

instance PrettyA Tag where prettyA = ppTag

ppScript :: forall era. (ValidateScript era, Core.Script era ~ Script era) => Script era -> PDoc
ppScript (s@(PlutusScript _)) = ppString "PlutusScript " PP.<+> ppScriptHash (hashScript @era s)
ppScript (TimelockScript x) = ppTimelock x

instance (ValidateScript era, Core.Script era ~ Script era) => PrettyA (Script era) where prettyA = ppScript

ppExUnits :: ExUnits -> PDoc
ppExUnits (ExUnits mem step) =
  ppRecord "ExUnits" [("memory", ppWord64 mem), ("steps", ppWord64 step)]

instance PrettyA ExUnits where prettyA = ppExUnits

ppCostModel :: CostModel -> PDoc
ppCostModel (CostModel m) =
  ppSexp "CostModel" [ppMap text ppInteger m]

instance PrettyA CostModel where prettyA = ppCostModel

ppPrices :: Prices -> PDoc
ppPrices (Prices mem step) =
  ppRecord "Prices" [("prMem", ppCoin mem), ("prSteps", ppCoin step)]

instance PrettyA Prices where prettyA = ppPrices
