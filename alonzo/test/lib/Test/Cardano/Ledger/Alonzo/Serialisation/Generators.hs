{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Test.Cardano.Ledger.Alonzo.Serialisation.Generators where

import Cardano.Ledger.Alonzo (AlonzoEra)
import Cardano.Ledger.Alonzo.Data (AuxiliaryData (..), Data (..))
import Cardano.Ledger.Alonzo.Language
import Cardano.Ledger.Alonzo.PParams
import Cardano.Ledger.Alonzo.Rules.Utxo (UtxoPredicateFailure (..))
import Cardano.Ledger.Alonzo.Rules.Utxos (UtxosPredicateFailure (..))
import Cardano.Ledger.Alonzo.Rules.Utxow (AlonzoPredFail (..))
import Cardano.Ledger.Alonzo.Scripts
  ( CostModel (..),
    ExUnits (..),
    Prices (..),
    Script (..),
    Tag (..),
    alwaysFails,
    alwaysSucceeds,
  )
import Cardano.Ledger.Alonzo.Tx
import Cardano.Ledger.Alonzo.TxBody
  ( TxOut (..),
  )
import Cardano.Ledger.Alonzo.TxWitness
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Era (Crypto, Era, ValidateScript (..))
import Cardano.Ledger.Hashes (ScriptHash)
import Cardano.Ledger.SafeHash (HasAlgorithm, SafeHash, unsafeMakeSafeHash)
import Cardano.Ledger.Shelley.Constraints (UsesScript, UsesValue)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text (pack)
import qualified Data.Text as T (pack)
import Numeric.Natural (Natural)
import qualified PlutusTx as Plutus
import Test.Cardano.Ledger.ShelleyMA.Serialisation.Generators (genMintValues)
import Test.QuickCheck
import Test.Shelley.Spec.Ledger.ConcreteCryptoTypes (Mock)
import Test.Shelley.Spec.Ledger.Serialisation.EraIndepGenerators ()

instance Arbitrary (Data era) where
  arbitrary = Data <$> arbitrary

genPair :: Gen a -> Gen b -> Gen (a, b)
genPair x y = do a <- x; b <- y; pure (a, b)

instance Arbitrary Plutus.Data where
  arbitrary = resize 5 (sized gendata)
    where
      gendata n
        | n > 0 =
          oneof
            [ (Plutus.I <$> arbitrary),
              (Plutus.B <$> arbitrary),
              (Plutus.Map <$> listOf (genPair (gendata (n `div` 2)) (gendata (n `div` 2)))),
              ( Plutus.Constr <$> fmap fromIntegral (arbitrary :: Gen Natural)
                  <*> listOf (gendata (n `div` 2))
              ),
              (Plutus.List <$> listOf (gendata (n `div` 2)))
            ]
      gendata _ = oneof [Plutus.I <$> arbitrary, Plutus.B <$> arbitrary]

instance
  ( UsesScript era,
    Ord (Core.Script era),
    Core.Script era ~ Script era,
    Arbitrary (Core.Script era)
  ) =>
  Arbitrary (AuxiliaryData era)
  where
  arbitrary = AuxiliaryData <$> arbitrary <*> arbitrary

instance Arbitrary Tag where
  arbitrary = elements [Spend, Mint, Cert, Rewrd]

instance Arbitrary RdmrPtr where
  arbitrary = RdmrPtr <$> arbitrary <*> arbitrary

instance Arbitrary ExUnits where
  arbitrary = ExUnits <$> arbitrary <*> arbitrary

instance (Era era) => Arbitrary (Redeemers era) where
  arbitrary = Redeemers <$> arbitrary

instance
  ( Era era,
    UsesValue era,
    Mock (Crypto era),
    Arbitrary (Core.Script era),
    Script era ~ Core.Script era,
    ValidateScript era,
    UsesScript era
  ) =>
  Arbitrary (TxWitness era)
  where
  arbitrary =
    TxWitness
      <$> arbitrary
      <*> arbitrary
      <*> genScripts
      <*> genData
      <*> arbitrary

keyBy :: Ord k => (a -> k) -> [a] -> Map k a
keyBy f xs = Map.fromList ((\x -> (f x, x)) <$> xs)

genScripts ::
  forall era.
  ( Core.Script era ~ Script era,
    ValidateScript era,
    Arbitrary (Script era)
  ) =>
  Gen (Map (ScriptHash (Crypto era)) (Core.Script era))
genScripts = keyBy (hashScript @era) <$> (arbitrary :: Gen [Core.Script era])

genData :: forall era. Era era => Gen (TxDats era)
genData = TxDats <$> keyBy hashData <$> arbitrary

instance HasAlgorithm c => Arbitrary (SafeHash c i) where
  arbitrary = unsafeMakeSafeHash <$> arbitrary

instance
  ( Era era,
    UsesValue era,
    Mock (Crypto era),
    Arbitrary (Core.Value era)
  ) =>
  Arbitrary (TxOut era)
  where
  arbitrary =
    TxOut
      <$> arbitrary
      <*> arbitrary
      <*> arbitrary

instance
  forall c.
  (Mock c) =>
  Arbitrary (TxBody (AlonzoEra c))
  where
  arbitrary =
    TxBody
      <$> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> genMintValues @c
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary

deriving newtype instance Arbitrary IsValidating

instance Mock c => Arbitrary (ValidatedTx (AlonzoEra c)) where
  arbitrary =
    ValidatedTx
      <$> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary

instance Mock c => Arbitrary (Script (AlonzoEra c)) where
  arbitrary =
    frequency
      [ (1, pure (alwaysSucceeds 1)),
        (1, pure (alwaysFails 1)),
        (10, TimelockScript <$> arbitrary)
      ]

-- ==========================
--

instance Arbitrary Language where
  arbitrary = elements [PlutusV1]

instance Arbitrary Prices where
  arbitrary = Prices <$> arbitrary <*> arbitrary

newtype AlphaString = AlphaString {unAlphaString :: String}
  deriving (Show, Eq, Ord)

instance Arbitrary AlphaString where
  arbitrary = AlphaString <$> listOf (elements ['a' .. 'z'])

instance Arbitrary CostModel where
  arbitrary = (CostModel . (Map.mapKeys (T.pack . unAlphaString))) <$> arbitrary

instance Arbitrary (PParams era) where
  arbitrary =
    PParams
      <$> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary

instance Arbitrary (PParamsUpdate era) where
  arbitrary =
    PParams
      <$> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary

instance Mock c => Arbitrary (UtxosPredicateFailure (AlonzoEra c)) where
  arbitrary =
    oneof
      [ ValidationTagMismatch <$> arbitrary <*> (pack <$> arbitrary),
        UpdateFailure <$> arbitrary
      ]

instance Mock c => Arbitrary (UtxoPredicateFailure (AlonzoEra c)) where
  arbitrary =
    oneof
      [ (BadInputsUTxO) <$> arbitrary,
        OutsideValidityIntervalUTxO <$> arbitrary <*> arbitrary,
        MaxTxSizeUTxO <$> arbitrary <*> arbitrary,
        pure InputSetEmptyUTxO,
        FeeTooSmallUTxO <$> arbitrary <*> arbitrary,
        (ValueNotConservedUTxO) <$> arbitrary <*> arbitrary,
        (OutputTooSmallUTxO) <$> arbitrary,
        (UtxosFailure) <$> arbitrary,
        (WrongNetwork) <$> arbitrary <*> arbitrary,
        (WrongNetworkWithdrawal) <$> arbitrary <*> arbitrary,
        (OutputBootAddrAttrsTooBig) <$> arbitrary,
        pure TriesToForgeADA,
        (OutputTooBigUTxO) <$> arbitrary,
        InsufficientCollateral <$> arbitrary <*> arbitrary,
        ScriptsNotPaidUTxO <$> arbitrary,
        ExUnitsTooBigUTxO <$> arbitrary <*> arbitrary,
        CollateralContainsNonADA <$> arbitrary
      ]

instance Mock c => Arbitrary (AlonzoPredFail (AlonzoEra c)) where
  arbitrary =
    oneof
      [ WrappedShelleyEraFailure <$> arbitrary,
        UnRedeemableScripts <$> arbitrary,
        MissingRequiredDatums <$> arbitrary <*> arbitrary,
        PPViewHashesDontMatch <$> arbitrary <*> arbitrary
      ]

instance Mock c => Arbitrary (ScriptPurpose c) where
  arbitrary =
    oneof
      [ Minting <$> arbitrary,
        Spending <$> arbitrary,
        Rewarding <$> arbitrary,
        Certifying <$> arbitrary
      ]

instance Mock c => Arbitrary (WitnessPPData (AlonzoEra c)) where
  arbitrary =
    WitnessPPData
      <$> arbitrary
      <*> genData
      <*> (Set.singleton <$> (getLanguageView <$> arbitrary <*> arbitrary))
