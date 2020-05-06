{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GHCForeignImportPrim #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnliftedFFITypes #-}

#include "MachDeps.h"

module System.Random.Internal.IEEE
  ( IEEERepr(..)
  , uniformUpToPowerOfTwo
  , uniformInRange
  ) where

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
  {-# INLINE fromRepr #-}
  toRepr = castFloatToWord32
  {-# INLINE toRepr #-}
  infinity _ = 1/0
  {-# INLINE infinity #-}
  mantissaWidth _ = 23
  {-# INLINE mantissaWidth #-}
  exponentWidth _ = 8
  {-# INLINE exponentWidth #-}
  exponentBias _ = 127
  {-# INLINE exponentBias #-}

instance IEEERepr Double where
  type Repr Double = Word64
  fromRepr = castWord64ToDouble
  {-# INLINE fromRepr #-}
  toRepr = castDoubleToWord64
  {-# INLINE toRepr #-}
  infinity _ = 1/0
  {-# INLINE infinity #-}
  mantissaWidth _ = 52
  {-# INLINE mantissaWidth #-}
  exponentWidth _ = 11
  {-# INLINE exponentWidth #-}
  exponentBias _ = 1023
  {-# INLINE exponentBias #-}

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
{-# INLINE decode #-}

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
{-# INLINE encode #-}

mask :: (Bits a, Num a) => Int -> a
mask width = (1 `unsafeShiftL` width) - 1
{-# INLINE mask #-}

isNegative :: IEEERepr a => a -> Bool
isNegative f = let (sign, _expo, _mant) = decode f in sign
{-# INLINE isNegative #-}

-------------------------------------------------------------------------------
-- IEEE floating point number generation
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
{-# INLINE leastGreaterOrEqualExponent #-}

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
{-# INLINE uniformUpToPowerOfTwo #-}

-- | Draws a number uniformly from @[0, f]@ via rejection sampling.
uniformUpTo ::
  (IEEERepr a, Monad m) =>
  -- | @f@, the upper bound (inclusive)
  a ->
  -- | @(x, y)@ such that @x@ is drawn from a geometric distribution with
  -- @p = 0.5@ and @y@ is drawn uniformly from @[0, 2^(exponentWidth + 1))@
  m (Int, Repr a) ->
  -- | sample drawn uniformly from @[0, f]@ or 'Nothing' if the sample was
  -- rejected
  m a
uniformUpTo f gen
  | negative = error "uniformUpTo: negative upper bound"
  | isInfinite f || isNaN f || f == 0 = return f
  | mant == 0 = uniformUpToPowerOfTwo expo <$> gen
  | otherwise =
      -- TODO: opportunity for bitmask rejection here?
      -- consider minimal exponent
      let go = do
            u <- uniformUpToPowerOfTwo (leastGreaterOrEqualExponent f) <$> gen
            if u <= f then return u else go
      in go
  where
    (negative, expo, mant) = decode f
{-# INLINE uniformUpTo #-}

-- | Draws a number uniformly from @[a, b]@ via rejection sampling.
uniformInRange ::
  forall m a.
  (Monad m, IEEERepr a) =>
  -- | lower and upper bounds @(a, b)@ such that @a <= b@
  (a, a) ->
  -- | generates @(x, y)@ such that @x@ is drawn from a geometric distribution
  -- with @p = 0.5@ and @y@ is drawn uniformly from @[0, 2^(exponentWidth + 1))@
  m (Int, Repr a) ->
  -- | sample drawn uniformly from @[a, b]@ or 'Nothing' if the sample was
  -- rejected
  m a
uniformInRange (a, b) gen
  | not (a <= b) = error "uniformInRange: a <= b required"
  | isNegative b = negate <$> uniformInRange (negate b, negate a) gen
  | a < 0 && b > 0 =
      let mantW = mantissaWidth (Proxy :: Proxy a)
          carryMask = 2^mantW
          go = do
            d <- uniformUpTo (max (abs a) b) gen
            (_geom, unif) <- gen -- TODO: we're wasting a lot of entropy here!
            let neg = unif .&. carryMask /= 0
                u = if neg then negate d else d
            if a <= u && u <= b
              then return u
              else go
      in go
  | otherwise =
      let d = b - a -- TODO: round up
          go = do
            v <- uniformUpTo d gen
            let u = v + a -- TODO: round to zero
            if a <= u && u <= b
              then return u
              else go
      in go
{-# INLINE uniformInRange #-}

-------------------------------------------------------------------------------
-- Foreign conversion functions
-------------------------------------------------------------------------------

castWord32ToFloat :: Word32 -> Float
castWord32ToFloat (W32# w#) = F# (stgWord32ToFloat w#)
{-# INLINE castWord32ToFloat #-}

foreign import prim "stg_word32ToFloatyg"
    stgWord32ToFloat :: Word# -> Float#

castFloatToWord32 :: Float -> Word32
castFloatToWord32 (F# f#) = W32# (stgFloatToWord32 f#)
{-# INLINE castFloatToWord32 #-}

foreign import prim "stg_floatToWord32yg"
    stgFloatToWord32 :: Float# -> Word#

castWord64ToDouble :: Word64 -> Double
castWord64ToDouble (W64# w) = D# (stgWord64ToDouble w)
{-# INLINE castWord64ToDouble #-}

foreign import prim "stg_word64ToDoubleyg"
#if WORD_SIZE_IN_BITS == 64
    stgWord64ToDouble :: Word# -> Double#
#else
    stgWord64ToDouble :: Word64# -> Double#
#endif

castDoubleToWord64 :: Double -> Word64
castDoubleToWord64 (D# d) = W64# (stgDoubleToWord64 d)
{-# INLINE castDoubleToWord64 #-}

foreign import prim "stg_doubleToWord64yg"
#if WORD_SIZE_IN_BITS == 64
    stgDoubleToWord64 :: Double# -> Word#
#else
    stgDoubleToWord64 :: Double# -> Word64#
#endif

-- $setup
-- >>> :set -XTypeApplications