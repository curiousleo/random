{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GHCForeignImportPrim #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnliftedFFITypes #-}

#include "MachDeps.h"

module System.Random.Internal.IEEE where

import Data.Proxy
import Data.Word
import Data.Bits
import GHC.Exts
import GHC.Word

-------------------------------------------------------------------------------
-- IEEE representation
-------------------------------------------------------------------------------

class (RealFloat a, Bits (Repr a), Integral (Repr a), Num (Repr a)) => IEEERepr a where
  type Repr a
  toRepr :: a -> Repr a
  fromRepr :: Repr a -> a
  infinity :: Proxy a -> a
  mantissaWidth :: Proxy a -> Int
  exponentWidth :: Proxy a -> Int
  exponentBias :: Proxy a -> Int

instance IEEERepr Float where
  type Repr Float = Word32
  fromRepr = castWord32ToFloat
  toRepr = castFloatToWord32
  infinity _ = 1/0
  mantissaWidth _ = 23
  exponentWidth _ = 8
  exponentBias _ = 127

instance IEEERepr Double where
  type Repr Double = Word64
  fromRepr = castWord64ToDouble
  toRepr = castDoubleToWord64
  infinity _ = 1/0
  mantissaWidth _ = 52
  exponentWidth _ = 11
  exponentBias _ = 1023

decode :: forall a. IEEERepr a => a -> (Bool, Int, Repr a)
decode f = (sign, expo, mant)
  where
    p = Proxy :: Proxy a
    r = toRepr f
    mantW = mantissaWidth p
    expoW = exponentWidth p

    sign = (r `unsafeShiftR` (mantW + expoW)) .&. 1 /= 0
    expo = fromIntegral $ (r `unsafeShiftR` mantW) .&. (mask expoW)
    mant = r .&. (mask mantW)

encode :: forall a. IEEERepr a => (Bool, Int, Repr a) -> a
encode (sign, expo, mant) = fromRepr r
  where
    p = Proxy :: Proxy a
    mantW = mantissaWidth p
    expoW = exponentWidth p

    s = if sign then 1 else 0
    e = fromIntegral expo .&. mask expoW
    m = mant .&. mask mantW
    r = (s `unsafeShiftL` (mantW + expoW)) .|. (e `unsafeShiftL` mantW) .|. m

mask :: (Bits a, Num a) => Int -> a
mask width = (1 `unsafeShiftL` width) - 1

isNegative :: IEEERepr a => a -> Bool
isNegative f = let (sign, _expo, _mant) = decode f in sign

encodePowerOfTwo :: IEEERepr a => Int -> a
encodePowerOfTwo expo = encode (False, expo, 0)

-------------------------------------------------------------------------------
-- IEEE generation primitives
-------------------------------------------------------------------------------

-- | Returns the least power of two greater than or equal to the positive
-- argument.
--
-- >>> leastGreaterOrEqualExponent (1 :: Float)
-- 127
-- >>> leastGreaterOrEqualExponent (0.5 :: Float)
-- 126
-- >>> leastGreaterOrEqualExponent (0.4 :: Float)
-- 126
-- >>> leastGreaterOrEqualExponent (0.6 :: Float)
-- TODO
-- >>> leastGreaterOrEqualExponent (2^10 + 1 :: Float)
-- TODO
-- >>> leastGreaterOrEqualExponent (2^127 + 2^126 :: Float)
-- TODO
--
-- Special values are handled as follows:
--
-- >>> leastGreaterOrEqualExponent (read "NaN" :: Float)
-- TODO
-- >>> leastGreaterOrEqualExponent (read "Infinity" :: Float)
-- TODO
leastGreaterOrEqualExponent :: forall a. IEEERepr a => a -> Int
leastGreaterOrEqualExponent f
  | sign = error "leastGreaterOrEqualExponent: negative argument"
  | isInfinite f || isNaN f || f == 0 || mant == 0 = expo
  | otherwise = expo + 1
  where
    (sign, expo, mant) = decode f

-- | Draws a number uniformly from @[0, 2^e]@.
uniformUpToPowerOfTwo ::
  forall a.
  IEEERepr a =>
  -- | @e@, the maximum exponent, biased
  Int ->
  -- | @(x, y)@ such that @x@ is drawn from a geometric distribution with
  -- @p = 0.5@ and @y@ is drawn uniformly from @[0, 2^(exponentWidth + 1))@
  (Int, Repr a) ->
  -- | sample drawn uniformly from @[0, 2^e]@
  a
uniformUpToPowerOfTwo maxExpo (geom, unif) = encode (False, expo + carry, unif)
  where
    p = Proxy :: Proxy a
    expo = max 0 (maxExpo - geom)

    mantW = mantissaWidth p
    carryMask = 2^mantW
    carry = if (unif .&. mask mantW) /= 0
      then 0
      else fromIntegral $ (unif .&. carryMask) `unsafeShiftR` mantW

-- | Draws a number uniformly from @[0, f]@ via rejection sampling.
uniformUpTo ::
  IEEERepr a =>
  -- | @f@, the upper bound (inclusive)
  a ->
  -- | @(x, y)@ such that @x@ is drawn from a geometric distribution with
  -- @p = 0.5@ and @y@ is drawn uniformly from @[0, 2^(exponentWidth + 1))@
  (Int, Repr a) ->
  -- | sample drawn uniformly from @[0, f]@ or 'Nothing' if the sample was
  -- rejected
  Maybe a
uniformUpTo f p
  | negative = error "uniformUpTo: negative upper bound"
  | isInfinite f || isNaN f || f == 0 = Just f
  | mant == 0 = Just $ uniformUpToPowerOfTwo expo p
  | otherwise =
      -- TODO: opportunity for bitmask rejection here?
      -- consider minimal exponent
      let u = uniformUpToPowerOfTwo (leastGreaterOrEqualExponent f) p
      in if u <= f then Just u else Nothing
  where
    (negative, expo, mant) = decode f

-- | Draws a number uniformly from @[a, b]@ via rejection sampling.
--
-- TODO: convert this to CPS so we only consume as much entropy as we actually
-- need.
uniformInRange ::
  forall a.
  IEEERepr a =>
  -- | lower and upper bounds @(a, b)@ such that @a <= b@
  (a, a) ->
  -- | @(x, y)@ such that @x@ is drawn from a geometric distribution with
  -- @p = 0.5@ and @y@ is drawn uniformly from @[0, 2^(exponentWidth + 1))@
  (Int, Repr a) ->
  -- | @(x, y)@ such that @x@ is drawn from a geometric distribution with
  -- @p = 0.5@ and @y@ is drawn uniformly from @[0, 2^(exponentWidth + 1))@
  (Int, Repr a) ->
  -- | sample drawn uniformly from @[a, b]@ or 'Nothing' if the sample was
  -- rejected
  Maybe a
uniformInRange (a, b) p q
  | not (a <= b) = error "uniformInRange: a <= b required"
  | isNegative b = negate <$> uniformInRange (negate b, negate a) p q
  | a < 0 && b > 0 = do
      let expoA' = leastGreaterOrEqualExponent (negate a)
          expoB' = leastGreaterOrEqualExponent b
          a' = encodePowerOfTwo expoA' :: a
          b' = encodePowerOfTwo expoB' :: a
      d <- uniformUpTo (a' + b') p -- TODO: what if a' or b' are not representable?
      let u = if d <= a' -- True with p = x / (x + y)
                then negate $ uniformUpToPowerOfTwo expoA' q
                else uniformUpToPowerOfTwo expoB' q
      if a <= u && u <= b
        then Just u
        else Nothing
  | otherwise = do
      let d = b - a -- TODO: round up
      v <- uniformUpTo d p
      let u = v + a -- TODO: round to zero
      if a <= u && u <= b
        then Just u
        else Nothing

-------------------------------------------------------------------------------
-- Foreign conversion functions
-------------------------------------------------------------------------------

castWord32ToFloat :: Word32 -> Float
castWord32ToFloat (W32# w#) = F# (stgWord32ToFloat w#)

foreign import prim "stg_word32ToFloatyg"
    stgWord32ToFloat :: Word# -> Float#

castFloatToWord32 :: Float -> Word32
castFloatToWord32 (F# f#) = W32# (stgFloatToWord32 f#)

foreign import prim "stg_floatToWord32zh"
    stgFloatToWord32 :: Float# -> Word#

castWord64ToDouble :: Word64 -> Double
castWord64ToDouble (W64# w) = D# (stgWord64ToDouble w)

foreign import prim "stg_word64ToDoubleyg"
#if WORD_SIZE_IN_BITS == 64
    stgWord64ToDouble :: Word# -> Double#
#else
    stgWord64ToDouble :: Word64# -> Double#
#endif

castDoubleToWord64 :: Double -> Word64
castDoubleToWord64 (D# d) = W64# (stgDoubleToWord64 d)

foreign import prim "stg_doubleToWord64zh"
#if WORD_SIZE_IN_BITS == 64
    stgDoubleToWord64 :: Double# -> Word#
#else
    stgDoubleToWord64 :: Double# -> Word64#
#endif

-- $setup
-- >>> :set -XTypeApplications
