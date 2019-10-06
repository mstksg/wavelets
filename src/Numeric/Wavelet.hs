{-# LANGUAGE FlexibleContexts                         #-}
{-# LANGUAGE GADTs                                    #-}
{-# LANGUAGE KindSignatures                           #-}
{-# LANGUAGE LambdaCase                               #-}
{-# LANGUAGE NoStarIsType                             #-}
{-# LANGUAGE ScopedTypeVariables                      #-}
{-# LANGUAGE TypeFamilyDependencies                   #-}
{-# LANGUAGE TypeInType                               #-}
{-# LANGUAGE UndecidableInstances                     #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}

module Numeric.Wavelet where

-- module Numeric.Wavelet (
--   ) where


import           Data.Finite
import           Data.Kind
import           Data.Vector.Generic.Sized (Vector)
import           GHC.TypeNats
import qualified Data.Vector               as UV
import qualified Data.Vector.Generic       as UVG
import qualified Data.Vector.Generic.Sized as VG
import qualified Data.Vector.Sized         as V


data N = Z | S N

data SN :: N -> Type where
    SZ :: SN 'Z
    SS :: SN n -> SN ('S n)

type family NNat n where
    NNat 'Z     = 0
    NNat ('S n) = 1 + NNat n

data WaveDec :: N -> (Type -> Type) -> Nat -> Type -> Type where
    WDZ :: { _wdDetailZ :: Vector v (2 ^ n) a
           , _wdApprox  :: Vector v (2 ^ n) a
           } -> WaveDec 'Z v n a
    WDS :: { _wdDetailS :: Vector    v (2 ^ n) a
           , _wdNext    :: WaveDec q v (n - 1) a
           } -> WaveDec ('S q) v n a

deriving instance Show (v a) => Show (WaveDec q v n a)

_wdDetail :: WaveDec q v n a -> Vector v (2 ^ n) a
_wdDetail = \case
    WDZ d _ -> d
    WDS d _ -> d

testDec :: WaveDec ('S ('S 'Z)) UV.Vector 4 Double
testDec = WDS (0 :: V.Vector 16 Double)
        . WDS (0 :: V.Vector 8 Double )
        $ WDZ (0 :: V.Vector 4 Double ) (0 :: V.Vector 4 Double)

haar
    :: (UVG.Vector v a, KnownNat n, 1 <= n, Fractional a)
    => SN q
    -> Vector v (2 ^ n) a
    -> WaveDec q v (n - 1) a
haar = \case
    SZ   -> uncurry (flip WDZ) . haarPass
    SS r -> \xs ->
      let (a, d) = haarPass xs
      in  WDS d $ haar r a

haarPass
    :: (UVG.Vector v a, KnownNat n, Fractional a)
    => Vector v (2 ^ (n + 1)) a
    -> (Vector v (2 ^ n) a, Vector v (2 ^ n) a)
haarPass xs = (app, det)
  where
    app = VG.generate $ \i -> ( xs `VG.index` combineProduct (0, i)
                              + xs `VG.index` combineProduct (1, i)
                              ) / 2
    det = VG.generate $ \i -> ( xs `VG.index` combineProduct (0, i)
                              - xs `VG.index` combineProduct (1, i)
                              ) / 2

-- waveDec
--     :: SN q
--     -> Vector v (2 ^ n) a
--     -> WaveDec q v (n - 1) a
-- waveDec = \case
--     SZ -> 

-- convolve
--     :: forall v n m a. (KnownNat n, KnownNat m, UVG.Vector v a, Num a, 1 <= n + m)
--     => Vector v n a
--     -> Vector v m a
--     -> Vector v (n + m - 1) a
-- convolve x y = VG.generate $ \i -> sum $ map (go i) finites
--   where
--     go  :: Finite (n + m - 1) -> Finite n -> a
--     go n k
--       | Right j <- sub n k
--       , Just l  <- strengthenN j
--       = x `VG.index` k * y `VG.index` l
--       | otherwise = 0

-- convolve'
--     :: forall v n m a. (KnownNat n, KnownNat m, UVG.Vector v a, Num a, 1 <= n + m)
--     => Vector v n a
--     -> Vector v m a
--     -> Vector v (n + m - 1) a
-- convolve' x y = VG.generate $ \i -> sum $ _
--   where
--     go  :: Finite n -> Finite m -> a
--     go j k = x `VG.index` j * y `VG.index` k


    -- (x `VG.index` k) * (y `VG.index` j)
    --   where
    --     j = n - k
    -- (n - k))

-- newtype DWT v n a = DWT { getDWT :: Vector v (2^(n - 1)) (Vector v n a) }

-- data WaveletType = WTDaubechies
--                  | WTHaar
--                  | WTBSpline

-- wave :: (UVG.Vector v a, UVG.Vector v (Vector v n a))
--     => Vector v (2^n) a
--     -> DWT v n a
-- dwt = undefined

