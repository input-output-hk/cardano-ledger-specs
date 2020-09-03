{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Cardano.Ledger.EraDefinitions where

import qualified Cardano.Ledger.Crypto as CryptoClass
import Cardano.Ledger.Era
import Shelley.Spec.Ledger.Coin

--------------------------------------------------------------------------------
-- Shelley Era
--------------------------------------------------------------------------------

data Shelley c

instance CryptoClass.Crypto c => Era (Shelley c) where
  type Crypto (Shelley c) = c
  type ValueType (Shelley c) = Coin
