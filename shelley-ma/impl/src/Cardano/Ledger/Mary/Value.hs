{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

module Cardano.Ledger.Mary.Value
  ( PolicyID (..),
    AssetName (..),
    Value (..),
    insert,
    lookup,
    policies,
    prune,
    representationSize,
    showValue,
    valueFromList,
    ppValue,
  )
where

import Cardano.Binary
  ( Decoder,
    DecoderError (..),
    Encoding,
    FromCBOR,
    ToCBOR,
    TokenType (..),
    decodeInteger,
    decodeWord64,
    fromCBOR,
    peekTokenType,
    toCBOR,
  )
import qualified Cardano.Crypto.Hash.Class as Hash
import Cardano.Ledger.Coin (Coin (..), integerToWord64)
import Cardano.Ledger.Compactible (Compactible (..))
import qualified Cardano.Ledger.Crypto as CC
import Cardano.Ledger.Pretty (PDoc, PrettyA (..), ppCoin, ppInteger, ppList, ppLong, ppScriptHash, ppSexp, ppString)
import Cardano.Ledger.Serialization (decodeMap, encodeMap)
import Cardano.Ledger.Val
  ( DecodeMint (..),
    DecodeNonNegative (..),
    EncodeMint (..),
    Val (..),
  )
import Cardano.Prelude (HeapWords (..), cborError)
import Control.DeepSeq (NFData (..))
import Control.Monad (forM_)
import Control.Monad.ST (runST)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Base16 as BS16
import qualified Data.ByteString.Short as SBS
import Data.ByteString.Short.Internal (ShortByteString (SBS))
import Data.CanonicalMaps
  ( canonicalMap,
    canonicalMapUnion,
    pointWise,
  )
import Data.Coders
  ( Decode (..),
    Encode (..),
    decode,
    encode,
    (!>),
    (<!),
  )
import Data.Group (Abelian, Group (..))
import Data.Int (Int64)
import Data.List (nub, sort, sortBy)
import Data.Map.Internal
  ( Map (..),
    link,
    link2,
    splitLookup,
  )
import Data.Map.Strict (assocs)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import Data.Ord (Down (..), comparing)
import qualified Data.Primitive.ByteArray as BA
import Data.Proxy (Proxy (..))
import Data.Set (Set)
import Data.Text.Encoding (decodeUtf8)
import Data.Typeable (Typeable)
import Data.Word (Word16, Word32, Word64)
import GHC.Generics (Generic)
import NoThunks.Class (NoThunks (..), OnlyCheckWhnfNamed (..))
import Prettyprinter (hsep)
import Shelley.Spec.Ledger.Scripts (ScriptHash (..))
import Prelude hiding (lookup)

-- | Asset Name
newtype AssetName = AssetName {assetName :: BS.ByteString}
  deriving newtype
    ( Show,
      Eq,
      ToCBOR,
      Ord,
      NoThunks,
      NFData
    )

instance FromCBOR AssetName where
  fromCBOR = do
    an <- fromCBOR
    if BS.length an > 32
      then cborError $ DecoderErrorCustom "asset name exceeds 32 bytes:" (decodeUtf8 $ BS16.encode an)
      else pure . AssetName $ an

-- | Policy ID
newtype PolicyID crypto = PolicyID {policyID :: ScriptHash crypto}
  deriving (Show, Eq, ToCBOR, FromCBOR, Ord, NoThunks, NFData)

-- | The Value representing MultiAssets
data Value crypto = Value !Integer !(Map (PolicyID crypto) (Map AssetName Integer))
  deriving (Show, Generic)

instance CC.Crypto crypto => Eq (Value crypto) where
  x == y = pointwise (==) x y

-- TODO make these specific
instance NFData (Value crypto)

instance NoThunks (Value crypto)

instance Semigroup (Value crypto) where
  Value c m <> Value c1 m1 =
    Value (c + c1) (canonicalMapUnion (canonicalMapUnion (+)) m m1)

instance Monoid (Value crypto) where
  mempty = Value 0 mempty

instance Group (Value crypto) where
  invert (Value c m) =
    Value
      (- c)
      (canonicalMap (canonicalMap ((-1 :: Integer) *)) m)

instance Abelian (Value crypto)

-- ===================================================
-- Make the Val instance of Value

instance CC.Crypto crypto => Val (Value crypto) where
  s <×> (Value c v) =
    Value
      (fromIntegral s * c)
      (canonicalMap (canonicalMap ((fromIntegral s) *)) v)
  isZero (Value c v) = c == 0 && Map.null v
  coin (Value c _) = Coin c
  inject (Coin c) = Value c mempty
  modifyCoin f (Value c m) = Value n m where (Coin n) = f (Coin c)
  pointwise p (Value c x) (Value d y) = (p c d) && (pointWise (pointWise p) x y)

  -- returns the size, in Word64's, of the CompactValue representation of Value
  size vv@(Value _ v)
    -- when Value contains only ada
    | v == mempty = fromIntegral $ adaWords
    -- when Value contains ada as well as other tokens
    -- sums up :
    -- i) adaWords : the space taken up by the ada amount
    -- ii) numberMulAssets : the space taken by number of words used to store number of non-ada assets in a value
    -- iii) the space taken up by the rest of the representation (quantities, PIDs, AssetNames, indeces)
    | otherwise =
      fromIntegral $
        (roundupBytesToWords $ representationSize (snd $ gettriples vv))
          + repOverhead

instance CC.Crypto crypto => HeapWords (Value crypto) where
  heapWords v = fromIntegral $ size v

-- space (in Word64s) taken up by the ada amount
adaWords :: Int
adaWords = 1

-- 64 bit machine Word64 length
wordLength :: Int
wordLength = 8

-- overhead in MA compact rep
repOverhead :: Int
repOverhead = 4 + adaWords + numberMulAssets

-- number of words used to store number of MAs in a value
numberMulAssets :: Int
numberMulAssets = 1

-- converts bytes to words (rounding up)
roundupBytesToWords :: Int -> Int
roundupBytesToWords b = quot (b + wordLength - 1) wordLength

-- ==============================================================
-- CBOR

-- TODO filter out 0s at deserialization
-- TODO Probably the actual serialization will be of the formal Coin OR Value type
-- Maybe better to make this distinction in the TxOut de/serialization

decodeValue ::
  CC.Crypto crypto =>
  Decoder s (Value crypto)
decodeValue = do
  tt <- peekTokenType
  case tt of
    TypeUInt -> inject . Coin <$> decodeInteger
    TypeUInt64 -> inject . Coin <$> decodeInteger
    TypeNInt -> inject . Coin <$> decodeInteger
    TypeNInt64 -> inject . Coin <$> decodeInteger
    TypeListLen -> decodeValuePair decodeInteger
    TypeListLen64 -> decodeValuePair decodeInteger
    TypeListLenIndef -> decodeValuePair decodeInteger
    _ -> fail $ "Value: expected array or int, got " ++ show tt

decodeValuePair ::
  CC.Crypto crypto =>
  (forall t. Decoder t Integer) ->
  Decoder s (Value crypto)
decodeValuePair decodeAmount =
  decode $
    RecD Value
      <! D decodeAmount
      <! D (decodeMultiAssetMaps decodeAmount)

encodeMultiAssetMaps ::
  CC.Crypto crypto =>
  Map (PolicyID crypto) (Map AssetName Integer) ->
  Encoding
encodeMultiAssetMaps = encodeMap toCBOR (encodeMap toCBOR toCBOR)

decodeMultiAssetMaps ::
  CC.Crypto crypto =>
  Decoder s Integer ->
  Decoder s (Map (PolicyID crypto) (Map AssetName Integer))
decodeMultiAssetMaps decodeAmount =
  prune <$> decodeMap fromCBOR (decodeMap fromCBOR decodeAmount)

decodeNonNegativeInteger :: Decoder s Integer
decodeNonNegativeInteger = fromIntegral <$> decodeWord64

decodeNonNegativeValue ::
  CC.Crypto crypto =>
  Decoder s (Value crypto)
decodeNonNegativeValue = do
  tt <- peekTokenType
  case tt of
    TypeUInt -> inject . Coin <$> decodeNonNegativeInteger
    TypeUInt64 -> inject . Coin <$> decodeNonNegativeInteger
    TypeListLen -> decodeValuePair decodeNonNegativeInteger
    TypeListLen64 -> decodeValuePair decodeNonNegativeInteger
    TypeListLenIndef -> decodeValuePair decodeNonNegativeInteger
    _ -> fail $ "Value: expected array or int, got " ++ show tt

instance
  CC.Crypto crypto =>
  ToCBOR (Value crypto)
  where
  toCBOR (Value c v) =
    if Map.null v
      then toCBOR c
      else
        encode $
          Rec Value
            !> To c
            !> E encodeMultiAssetMaps v

instance
  CC.Crypto crypto =>
  FromCBOR (Value crypto)
  where
  fromCBOR = decodeValue

instance
  CC.Crypto crypto =>
  DecodeNonNegative (Value crypto)
  where
  decodeNonNegative = decodeNonNegativeValue

instance
  CC.Crypto crypto =>
  DecodeMint (Value crypto)
  where
  decodeMint = Value 0 <$> decodeMultiAssetMaps decodeIntegerBounded64

-- Note: we do not use `decodeInt64` from the cborg library here because the
-- implementation contains "-- TODO FIXME: overflow"
decodeIntegerBounded64 :: Decoder s Integer
decodeIntegerBounded64 = do
  tt <- peekTokenType
  case tt of
    TypeUInt -> pure ()
    TypeUInt64 -> pure ()
    TypeNInt -> pure ()
    TypeNInt64 -> pure ()
    _ -> fail "expected major type 0 or 1 when decoding mint field"
  x <- decodeInteger
  if x >= minval && x <= maxval
    then pure x
    else
      fail $
        concat
          [ "overflow when decoding mint field. min value: ",
            show minval,
            " max value: ",
            show maxval,
            " got: ",
            show x
          ]
  where
    maxval = fromIntegral (maxBound :: Int64)
    minval = fromIntegral (minBound :: Int64)

instance
  CC.Crypto crypto =>
  EncodeMint (Value crypto)
  where
  encodeMint (Value _ multiasset) = encodeMultiAssetMaps multiasset

-- ========================================================================
-- Compactible
-- This is used in the TxOut which stores the (CompactForm Value).

instance CC.Crypto crypto => Compactible (Value crypto) where
  newtype CompactForm (Value crypto) = CompactValue (CompactValue crypto)
    deriving (Eq, Typeable, Show, NoThunks, ToCBOR, FromCBOR)
  toCompact x = CompactValue <$> to x
  fromCompact (CompactValue x) = from x

instance CC.Crypto crypto => ToCBOR (CompactValue crypto) where
  toCBOR = toCBOR . from

instance CC.Crypto crypto => FromCBOR (CompactValue crypto) where
  fromCBOR = do
    v <- decodeNonNegativeValue
    case to v of
      Nothing ->
        fail
          "impossible failure: decoded nonnegative value that cannot be compacted"
      Just x -> pure x

data CompactValue crypto
  = CompactValueAdaOnly {-# UNPACK #-} !Word64
  | CompactValueMultiAsset
      {-# UNPACK #-} !Word64 -- ada
      {-# UNPACK #-} !Word32 -- number of ma's
      {-# UNPACK #-} !ShortByteString -- rep
  deriving (Show, Typeable)

instance CC.Crypto crypto => Eq (CompactValue crypto) where
  a == b = from a == from b

deriving via
  OnlyCheckWhnfNamed "CompactValue" (CompactValue crypto)
  instance
    NoThunks (CompactValue crypto)

{-
The Value surface type uses a nested map. For the compact version we use a
flattened representation, equivalent to a list of triples:
  [(PolicyID, AssetName, Quantity)]

Example:
  [ ("0xa519f84e...", "",       42)  -- empty asset name
  , ("0xf820a82c...", "Snark",  1)
  , ("0xf820a82c...", "Boojum", 1)   -- shared policy id, different name
  ]

We start by sorting in /descending/ order by asset name. Note that descending
order puts empty strings last:
  [ ("0xf820a82c...", "Snark",  1)
  , ("0xf820a82c...", "Boojum", 1)
  , ("0xa519f84e...", "",      42)
  ]

This example will be serialised as:
  ┏━━━━━━━━━━━━━━━┳━━━━━━━━━━━━━━━┳━━━━━━━━━━━━━━━┓
A)┃             1 ┃             1 ┃            42 ┃ Word64 quantities
  ┣━━━┳━━━┳━━━┳━━━┻━━━━━━━━━━━━━━━┻━━━━━━━━━━━━━━━┛
B)┃ 36┃ 36┃ 64┃                                     Word16 policyId offsets
  ┣━━━╋━━━╋━━━┫
C)┃ 92┃ 98┃103┃                                     Word16 asset name offsets
  ┣━┯━╇━┯━╇━┯━╇━┯━┯━┯━┯━┯━┯━┯━┯━┯━┯━┯━┯━┯━┯━┯━┯━┯━┯━┯━┯━┯━┓
D)┃f820a82c.. ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┃ 28 byte policyId #1
  ┣━┿━┿━┿━┿━┿━┿━┿━┿━┿━┿━┿━┿━┿━┿━┿━┿━┿━┿━┿━┿━┿━┿━┿━┿━┿━┿━┿━┫
  ┃a519f84e.. ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┊ ┃ 28 byte policyId #2
  ┣━┿━┿━┿━┿━┿━┿━┿━┿━┿━┿━╈━╈━┷━┷━┷━┷━┷━┷━┷━┷━┷━┷━┷━┷━┷━┷━┷━┛
E)┃S┊n┊a┊r┊k┊B┊o┊o┊j┊u┊m┃◀╂─padding to word size    Asset names, plus padding
  ┗━┷━┷━┷━┷━┷━┷━┷━┷━┷━┷━┻━┛
   ▲         ▲           ▲
   92-offset 97-offset   103-offset, end of string

Note that the asset name offsets end up sorted in ascending order, with empty
asset names pointing to the offset past the end of the concatenated names.

The serialised representation consists of five parts, concatenated together:
  A) A sequence of Word64s representing asset quantities.

  B) A sequence of Word16s representing policyId string offsets within D.
     We do not need to store a length because policyIds are fixed size.

  C) A sequence of Word16s representing asset name string offsets within E.
     We store only the starting offset and not a end offset or length. We can
     do this because we keep the assets in A,B,C sorted by the asset name, so
     the offsets in C are sorted. This means the next distinct entry gives the
     (exclusive) end offset of the asset name string. As a special case for
     empty asset names, the index points to the end of the string E.

     Note: If there are duplicate asset names, this can yield a sequence of
     multiple of the same offset. For example, if the assets are named
     "Snark","Snark","Boojum", region E would contain "SnarkBoojum",
     and region C would contain 92, 92, 97. For the decoder to determine the
     length of the first asset, it would subtract 92 from 97 (and not from the
     duplicate 92).

  D) a blob of policyIDs, without duplicates, concatenated.

  E) a blob of asset names, sorted, without duplicates, concatenated.

The size of the regions A,B,C are known based on the number of values. The
string offsets in B and C are relative to the whole of the representation, not
relative to the start of D & E (since D is variable size depending on whether
there were duplicate policyIDs)

The encoding strategy is
 - Collect all (unique) policy Ids.
 - Collect all (unique) asset names.
 - Determine the sizes of the regions and allocate them.
   - size A = 8 * numassets
   - size B = 2 * numassets
   - size C = 2 * numassets
   - size D = length (concat policyIds)
   - size E = length (concat assetNames)
   - sum = 12*numassets
         + length (concat policyIds)
         + length (concat assetNames)
 - Write the policyIds to region D
 - Write the asset names to region E
 - For each asset entry
   - Locate the corresponding asset name and policyId
   - Write quantity, policyId location, and asset name location to corresponding
     regions
   - For the special case of 0 length asset names, the location is the end of
     region E

The decoding strategy is
 - Use length information to determine the beginnings of regions A,B,C
   (We do not need to do this for regions D and E because the policyId
   and asset name locations are relative to the beginning of entire rep.)
 - For each integer in 0..(numassets -1)
   - Read corresponding quantity, pid offset, and asset name offset from regions
     A, B, and C, respectively.
   - Read (pid length) bytes from pid offset. assume it points into region D
   - Determine asset name lengths using the difference between the offset and
     the next greater offset (if it exists). If there is no next greater offset,
     use the difference from the end of the rep. (Note: for the special case of
     0 length asset names, this calculation results in 0 because we are
     subtracting the end of the rep from itself.)
   - Read (asset name length) bytes from asset name offset. assume it points
     into region E.
 -}

to ::
  forall crypto.
  (CC.Crypto crypto) =>
  Value crypto ->
  -- The Nothing case of the return value corresponds to a quantity that is outside
  -- the bounds of a Word64. x < 0 or x > (2^64 - 1)
  Maybe (CompactValue crypto)
to (Value ada ma)
  | Map.null ma =
    CompactValueAdaOnly <$> integerToWord64 ada
to v = do
  c <- integerToWord64 ada
  -- Here we convert the (pid, assetName, quantity) triples into
  -- (Int, (Word16,Word16,Word64))
  -- These represent the index, pid offset, asset name offset, and quantity.
  -- If any of the quantities out of bounds, this will produce Nothing.
  -- The triples are ordered by asset name in descending order.
  preparedTriples <-
    zip [0 ..]
      . sortBy (comparing (\(_, x, _) -> x))
      <$> traverse prepare triples
  pure $
    CompactValueMultiAsset c (fromIntegral numTriples) $
      runST $ do
        byteArray <- BA.newByteArray repSize
        forM_ preparedTriples $ \(i, (pidoff, anoff, q)) ->
          do
            -- For each triple, we write the quantity to region A,
            -- the pid offset to region B, and the asset name offset to region C.
            -- We can calculate the sizes (and therefore the starts) of each region
            -- using the number of triples.
            -- A:
            --   size: (#triples * 8) bytes
            --   start: offset 0
            -- B:
            --   size: (#triples * 2) bytes
            --   start: size(A) = #triples * 8
            -- C:
            --   size: (#triples * 2) bytes
            --   start: size(A) + size(B) = #triples * 10
            --
            -- The position argument to writeByteArray is an index in terms of the
            -- size of the value being written. So writeByteArray of a Word64 at
            -- position 1 writes at offset 8.
            --
            -- For the following, the byte offsets calculated above are converted to
            -- ByteArray positions by division.
            --
            -- The byte offset of the ith...
            --   quantity: 8i
            --   pid offset: 8n + 2i
            --   asset name offset: 8n + 2n + 2i
            -- Dividing by the respective sizes (8,2,2) yields the indices below.
            BA.writeByteArray byteArray i q
            BA.writeByteArray byteArray (4 * numTriples + i) pidoff
            BA.writeByteArray byteArray (5 * numTriples + i) anoff

        forM_ (Map.toList pidOffsetMap) $
          \(pid, offset) ->
            let PolicyID (ScriptHash (Hash.UnsafeHash pidBytes)) = pid
             in BA.copyByteArray
                  byteArray
                  (fromIntegral offset)
                  (sbsToByteArray pidBytes)
                  0
                  pidSize

        forM_ (Map.toList assetNameOffsetMap) $
          \(AssetName anameBS, offset) ->
            let anameBytes = SBS.toShort anameBS
                anameLen = BS.length anameBS
             in BA.copyByteArray
                  byteArray
                  (fromIntegral offset)
                  (sbsToByteArray anameBytes)
                  0
                  anameLen
        byteArrayToSbs <$> BA.unsafeFreezeByteArray byteArray
  where
    (ada, triples) = gettriples v
    numTriples = length triples

    -- abcRegionSize is the combined size of regions A, B, and C
    abcRegionSize = numTriples * 12

    pidSize = fromIntegral (Hash.sizeHash (Proxy :: Proxy (CC.ADDRHASH crypto)))

    -- pids is the collection of all distinct pids
    pids = nub $ sort $ (\(pid, _, _) -> pid) <$> triples

    pidOffsetMap :: Map (PolicyID crypto) Word16
    pidOffsetMap =
      -- the pid offsets are:
      --   X, X + s, X + 2s, X + 3s, ...
      -- where X is the start of block D and s is the size of a pid
      let offsets = enumFromThen abcRegionSize (abcRegionSize + pidSize)
       in fromIntegral <$> Map.fromList (zip pids offsets)

    pidOffset pid = fromJust (Map.lookup pid pidOffsetMap)

    pidBlockSize = length pids * pidSize

    -- Putting asset names in (comparing Down) order ensures that the empty string
    -- is last, so the associated offset is pointing to the end of the array
    assetNames = nub $ sortBy (comparing Down) $ (\(_, an, _) -> an) <$> triples

    assetNameLengths = fromIntegral . BS.length . assetName <$> assetNames

    assetNameOffsetMap :: Map AssetName Word16
    assetNameOffsetMap =
      -- The asset name offsets are the running sum of the asset lengths,
      -- but starting with the offset of the start of block E.
      let offsets = scanl (+) (abcRegionSize + pidBlockSize) assetNameLengths
       in fromIntegral <$> Map.fromList (zip assetNames offsets)

    assetNameOffset aname = fromJust (Map.lookup aname assetNameOffsetMap)

    anameBlockSize = sum assetNameLengths

    -- size = size(A+B+C)      + size(D)      + size(E)
    repSize = abcRegionSize + pidBlockSize + anameBlockSize

    prepare (pid, aname, q) = do
      q' <- integerToWord64 q
      pure (pidOffset pid, assetNameOffset aname, q')

representationSize ::
  forall crypto.
  CC.Crypto crypto =>
  [(PolicyID crypto, AssetName, Integer)] ->
  Int
representationSize xs = abcRegionSize + pidBlockSize + anameBlockSize
  where
    len = length xs
    abcRegionSize = len * 12

    numPids = length . nub . sort $ (\(pid, _, _) -> pid) <$> xs
    pidSize = fromIntegral (Hash.sizeHash (Proxy :: Proxy (CC.ADDRHASH crypto)))
    pidBlockSize = numPids * pidSize

    assetNames = nub $ sort $ (\(_, an, _) -> an) <$> xs
    assetNameLengths = fromIntegral . BS.length . assetName <$> assetNames
    anameBlockSize = sum assetNameLengths

from :: forall crypto. (CC.Crypto crypto) => CompactValue crypto -> Value crypto
from (CompactValueAdaOnly c) = Value (fromIntegral c) mempty
from (CompactValueMultiAsset c numAssets rep) =
  valueFromList (fromIntegral c) triples
  where
    n = fromIntegral numAssets

    ba = sbsToByteArray rep

    getTripleForIndex :: Int -> (Word16, Word16, Word64)
    getTripleForIndex i =
      -- indexByteArray indices are in terms of the size of the value being indexed
      -- rather than byte offsets.
      -- The corresponding byte offsets are:
      -- q: 0 + 8i
      -- pidix: 8n + 2i
      -- anameix: 8n + 2n + 2i
      -- Dividing by the sized (resp 8,2,2) yields the indices below
      let q = BA.indexByteArray ba i
          pidix = BA.indexByteArray ba (4 * n + i)
          anameix = BA.indexByteArray ba (5 * n + i)
       in (pidix, anameix, q)

    -- raw triples :: [(pid offset, asset name offset, quantity)]
    rawTriples :: [(Word16, Word16, Word64)]
    rawTriples = map getTripleForIndex [0 .. (fromIntegral $ numAssets -1)]

    triples :: [(PolicyID crypto, AssetName, Integer)]
    triples = map convertTriple rawTriples

    -- Asset name length are calculated by subtracting the offset from the
    -- next greater offset (or from the end of the rep, if there is none.)
    -- For an index pointing to the end of the array, the associated
    -- length will be: offset - length(rep) = 0
    assetLens =
      -- This assumes that the triples are ordered by nondecreasing asset name offset
      let ixs = nub $ map (\(_, x, _) -> x) rawTriples
          ixPairs = zip ixs (drop 1 ixs ++ [fromIntegral $ SBS.length rep])
       in Map.fromList $ (\(a, b) -> (a, fromIntegral $ b - a)) <$> ixPairs
    assetLen :: Word16 -> Int
    assetLen ix = fromJust (Map.lookup ix assetLens)

    convertTriple ::
      (Word16, Word16, Word64) -> (PolicyID crypto, AssetName, Integer)
    convertTriple (p, a, i) =
      ( PolicyID $
          ScriptHash $
            Hash.UnsafeHash $
              readShortByteString
                rep
                (fromIntegral p)
                (fromIntegral $ Hash.sizeHash ([] :: [CC.ADDRHASH crypto])),
        AssetName $
          SBS.fromShort $ readShortByteString rep (fromIntegral a) (assetLen a),
        fromIntegral i
      )

sbsToByteArray :: ShortByteString -> BA.ByteArray
sbsToByteArray (SBS bah) = BA.ByteArray bah

byteArrayToSbs :: BA.ByteArray -> ShortByteString
byteArrayToSbs (BA.ByteArray bah) = SBS bah

readShortByteString :: ShortByteString -> Int -> Int -> ShortByteString
readShortByteString sbs start len =
  byteArrayToSbs $ BA.cloneByteArray (sbsToByteArray sbs) start len

-- ========================================================================
-- Operations on Values

-- | Extract the set of policies in the Value.
--
--   This function is equivalent to computing the support of the value in the
--   spec.
policies :: Value crypto -> Set (PolicyID crypto)
policies (Value _ m) = Map.keysSet m

lookup :: PolicyID crypto -> AssetName -> Value crypto -> Integer
lookup pid aid (Value _ m) =
  case Map.lookup pid m of
    Nothing -> 0
    Just m2 -> Map.findWithDefault 0 aid m2

-- | insert comb policy asset n v,
--   if comb = \ old new -> old, the integer in the Value is prefered over n
--   if comb = \ old new -> new, then n is prefered over the integer in the Value
--   if (comb old new) == 0, then that value should not be stored in the Map part of the Value.
insert ::
  (Integer -> Integer -> Integer) ->
  PolicyID crypto ->
  AssetName ->
  Integer ->
  Value crypto ->
  Value crypto
insert combine pid aid new (Value cn m1) =
  case splitLookup pid m1 of
    (l1, Just m2, l2) ->
      case splitLookup aid m2 of
        (v1, Just old, v2) ->
          if n == 0
            then
              let m3 = (link2 v1 v2)
               in if Map.null m3
                    then Value cn (link2 l1 l2)
                    else Value cn (link pid m3 l1 l2)
            else Value cn (link pid (link aid n v1 v2) l1 l2)
          where
            n = combine old new
        (_, Nothing, _) ->
          Value
            cn
            ( link
                pid
                ( if new == 0
                    then m2
                    else (Map.insert aid new m2)
                )
                l1
                l2
            )
    (l1, Nothing, l2) ->
      Value
        cn
        ( if new == 0
            then link2 l1 l2
            else link pid (Map.singleton aid new) l1 l2
        )

-- ========================================================

-- | Remove 0 assets from a map
prune ::
  Map (PolicyID crypto) (Map AssetName Integer) ->
  Map (PolicyID crypto) (Map AssetName Integer)
prune assets =
  Map.filter (not . null) $ Map.filter (/= 0) <$> assets

-- | Rather than using prune to remove 0 assets, when can avoid adding them in the
--   first place by using valueFromList to construct a Value.
valueFromList :: Integer -> [(PolicyID era, AssetName, Integer)] -> Value era
valueFromList ada =
  foldr
    (\(p, n, i) ans -> insert (+) p n i ans)
    (Value ada Map.empty)

-- | Display a Value as a String, one token per line
showValue :: Value crypto -> String
showValue v = show c ++ "\n" ++ unlines (map trans ts)
  where
    (c, ts) = gettriples v
    trans (PolicyID x, hash, cnt) =
      show x
        ++ ",  "
        ++ show hash
        ++ ",  "
        ++ show cnt

-- | Turn the nested 'Value' map-of-maps representation into a flat sequence
-- of policyID, asset name and quantity, plus separately the ada quantity.
gettriples' :: Value crypto -> (Integer, [(PolicyID crypto, AssetName, Integer)], [PolicyID crypto])
gettriples' (Value c m1) = (c, triples, bad)
  where
    triples =
      [ (policyId, aname, amount)
        | (policyId, m2) <- assocs m1,
          (aname, amount) <- assocs m2
      ]
    bad = Map.keys (Map.filter Map.null m1) -- This is a malformed value, not in cannonical form.

gettriples :: Value crypto -> (Integer, [(PolicyID crypto, AssetName, Integer)])
gettriples v = case gettriples' v of
  (a, b, _) -> (a, b)

-- =====================================
-- Pretty printing functions

ppValue :: Value crypto -> PDoc
ppValue v = case gettriples' v of
  (n, triples, []) -> ppSexp "Value" [ppCoin (Coin n), ppList pptriple triples]
  (n, triples, bad) -> ppSexp "Value" [ppCoin (Coin n), ppList pptriple triples, ppString "Bad " <> ppList ppPolicyID bad]
  where
    pptriple (i, asset, num) = hsep [ppPolicyID i, ppAssetName asset, ppInteger num]

ppPolicyID :: PolicyID crypto -> PDoc
ppPolicyID (PolicyID sh) = ppScriptHash sh

ppAssetName :: AssetName -> PDoc
ppAssetName (AssetName bs) = ppLong bs

instance PrettyA (Value crypto) where prettyA = ppValue

instance PrettyA (PolicyID crypto) where prettyA x = ppSexp "PolicyID" [ppPolicyID x]

instance PrettyA AssetName where prettyA x = ppSexp "AssetName" [ppAssetName x]
