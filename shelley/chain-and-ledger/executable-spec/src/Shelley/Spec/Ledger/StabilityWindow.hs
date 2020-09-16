{-# LANGUAGE TypeApplications #-}

module Shelley.Spec.Ledger.StabilityWindow
  ( computeStabilityWindow,
    computeRandomnessStabilisationWindow,
  )
where

import Data.Word (Word64)
import Shelley.Spec.Ledger.Data.BaseTypesData

-- | Calculate the stability window (e.g. the number of slots needed for a block
-- to become stable) from the security param and the active slot coefficient.
--
-- The value 3k/f is determined to be a suitabe value as per
-- https://docs.google.com/document/d/1B8BNMx8jVWRjYiUBOaI3jfZ7dQNvNTSDODvT5iOuYCU/edit#heading=h.qh2zcajmu6hm
computeStabilityWindow ::
  Word64 ->
  ActiveSlotCoeff ->
  Word64
computeStabilityWindow k asc =
  ceiling $ fromIntegral @_ @Double (3 * k) / fromRational (toRational f)
  where
    f = intervalValue . activeSlotVal $ asc

-- | Calculate the randomness stabilisation window from the security param and
-- the active slot coefficient.
--
-- The value 4k/f is determined to be a suitabe value as per
-- https://docs.google.com/document/d/1B8BNMx8jVWRjYiUBOaI3jfZ7dQNvNTSDODvT5iOuYCU/edit#heading=h.qh2zcajmu6hm
computeRandomnessStabilisationWindow ::
  Word64 ->
  ActiveSlotCoeff ->
  Word64
computeRandomnessStabilisationWindow k asc =
  ceiling $ fromIntegral @_ @Double (4 * k) / fromRational (toRational f)
  where
    f = intervalValue . activeSlotVal $ asc
