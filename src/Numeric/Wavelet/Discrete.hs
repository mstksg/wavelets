{-# LANGUAGE DeriveFunctor                            #-}
{-# LANGUAGE DeriveGeneric                            #-}
{-# LANGUAGE FlexibleContexts                         #-}
{-# LANGUAGE GADTs                                    #-}
{-# LANGUAGE KindSignatures                           #-}
{-# LANGUAGE LambdaCase                               #-}
{-# LANGUAGE NoStarIsType                             #-}
{-# LANGUAGE RankNTypes                               #-}
{-# LANGUAGE RecordWildCards                          #-}
{-# LANGUAGE ScopedTypeVariables                      #-}
{-# LANGUAGE StandaloneDeriving                       #-}
{-# LANGUAGE TypeApplications                         #-}
{-# LANGUAGE TypeFamilyDependencies                   #-}
{-# LANGUAGE TypeInType                               #-}
{-# LANGUAGE TypeOperators                            #-}
{-# LANGUAGE UndecidableInstances                     #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}

module Numeric.Wavelet.Discrete (
    DWavelet(..)
  , DWT(..)
  , cdwt
  , dwt
  , idwt
  , haar
    -- DWD(..)
  -- , dwdApprox, dwdDetail
  -- , flattenDWD
  -- , denseDWD
  -- , haar
  -- , unHaar
  ) where

import           Data.Complex
import           Data.Finite
import           Data.Finite.Internal
import           Data.Kind
import           Data.Proxy
import           Data.Vector.Generic.Sized    (Vector)
import           GHC.Generics
import           GHC.TypeLits.Compare
import           GHC.TypeNats
import           Numeric.Wavelet.Internal.FFT
import qualified Data.Vector                  as UV
import qualified Data.Vector.Generic          as UVG
import qualified Data.Vector.Generic.Sized    as VG
import qualified Data.Vector.Sized            as V


data DWavelet v l a = DW
    { dwHiDecomp :: VG.Vector v l a      -- ^ High-pass decomposition filter
    , dwLoDecomp :: VG.Vector v l a      -- ^ Low-pass decomposition filter
    , dwHiRecon  :: VG.Vector v l a      -- ^ High-pass reconstruction filter
    , dwLoRecon  :: VG.Vector v l a      -- ^ Low-pass reconstruction filter
    }
  deriving (Show, Eq, Ord, Functor, Generic)

data DWT v n a = DWT
    { dwtApprox :: VG.Vector v n a
    , dwtDetail :: VG.Vector v n a
    }
  deriving (Show, Eq, Ord, Functor, Generic)

cdwt
    :: (UVG.Vector v (Complex a), KnownNat l, KnownNat n, 1 <= l, 1 <= n, FFTWReal a)
    => DWavelet  v l (Complex a)
    -> VG.Vector v n (Complex a)
    -> DWT v ((n + l - 1) `Div` 2) (Complex a)
cdwt DW{..} x = DWT{..}
  where
    dwtApprox = downsamp $ convolve x dwLoDecomp
    dwtDetail = downsamp $ convolve x dwHiDecomp

dwt
    :: (UVG.Vector v (Complex a), UVG.Vector v a, KnownNat l, KnownNat n, 1 <= l, 1 <= n, FFTWReal a)
    => DWavelet  v l a
    -> VG.Vector v n a
    -> DWT v ((n + l - 1) `Div` 2) a
dwt DW{..} x = DWT{..}
  where
    dwtApprox = downsamp $ rconvolve x dwLoDecomp
    dwtDetail = downsamp $ rconvolve x dwHiDecomp

idwt
    :: forall v l n a.
     ( UVG.Vector v (Complex a)
     , UVG.Vector v a
     , KnownNat l
     , KnownNat n
     , FFTWReal a
     , Div ((((Div ((n + l) - 1) 2 * 2) + l) - 1) - n) 2 <= ((((Div ((n + l) - 1) 2 * 2) + l) - 1) - n)
     )
    => DWavelet  v l a
    -> DWT v ((n + l - 1) `Div` 2) a
    -> VG.Vector v n a      -- todo: remove the choice
idwt DW{..} DWT{..} = VG.slice @_ @((((n+l-1)`Div`2)*2+l-1-n)`Div`2) @n @(((n+l-1)`Div`2)*2+l-1-n-((((n+l-1)`Div`2)*2+l-1-n)`Div`2)) Proxy $
                VG.zipWith (+) x y
  where
    x = rconvolve (upsamp dwtApprox) dwLoRecon
    y = rconvolve (upsamp dwtDetail) dwHiRecon

downsamp :: (UVG.Vector v a, KnownNat n) => VG.Vector v n a -> VG.Vector v (n `Div` 2) a
downsamp v = VG.generate $ \i -> v `VG.index` doubleFinite i
  where
    doubleFinite :: Finite (n `Div` 2) -> Finite n
    doubleFinite (Finite x) = Finite (x * 2 + 1)

upsamp :: (UVG.Vector v a, KnownNat n, Num a) => VG.Vector v n a -> VG.Vector v (n * 2) a
upsamp v = VG.generate $ \i -> case separateProduct @2 i of
    (j, k)
      | j == 0    -> v `VG.index` k
      | otherwise -> 0

-- upsamp :: forall v n a. (UVG.Vector v a, KnownNat n, Num a) => VG.Vector v (n `Div` 2) a -> VG.Vector v n a
-- upsamp v = VG.generate $ \(Finite i) -> case i `divMod` 2 of
--     (d, m)
--       | m == 0    -> v `VG.index` Finite d
--       | otherwise -> 0


    -- let (j, k) = case separateProduct @2 i
    -- in  if j == 0
    --       then

-- unhaarPass
--     :: (UVG.Vector v a, KnownNat n, Num a)
--     => Vector v (2 ^ n) a
--     -> Vector v (2 ^ n) a
--     -> Vector v (2 ^ (n + 1)) a
-- unhaarPass app det = VG.generate $ \i ->
--     let (j, k) = separateProduct @2 i
--         combiner
--           | j == 0    = (+)
--           | otherwise = (-)
--     in  combiner (app `VG.index` k) (det `VG.index` k)


haar :: (UVG.Vector v a, Floating a) => DWavelet v 2 a
haar = DW{..}
  where
    srtot = sqrt 2 / 2
    dwHiDecomp = VG.fromTuple (-srtot, srtot)
    dwLoDecomp = VG.fromTuple ( srtot, srtot)
    dwHiRecon  = VG.fromTuple ( srtot,-srtot)
    dwLoRecon  = VG.fromTuple ( srtot, srtot)

-- data DWD :: (Type -> Type) -> Nat -> Type -> Type where
--     DWDZ :: { _dwdDetailZ :: !a
--            , _dwdApprox  :: !a
--            } -> DWD v 0 a
--     DWDS :: { _dwdDetailS :: !(Vector  v (2 ^ (n + 1)) a)
--            , _dwdNext    :: !(DWD v n             a)
--            } -> DWD v (n + 1) a

-- deriving instance (Show (v a), Show a) => Show (DWD v n a)

-- dwdDetail :: UVG.Vector v a => DWD v n a -> Vector v (2 ^ n) a
-- dwdDetail = \case
--     DWDZ d _ -> VG.singleton d
--     DWDS d _ -> d

-- dwdApprox :: DWD v n a -> a
-- dwdApprox = \case
--     DWDZ _ a -> a
--     DWDS _ a -> dwdApprox a

-- testDec :: DWD UV.Vector 4 Double
-- testDec = DWDS (0 :: V.Vector 16 Double)
--         . DWDS (0 :: V.Vector  8 Double)
--         . DWDS (0 :: V.Vector  4 Double)
--         . DWDS (0 :: V.Vector  2 Double)
--         $ DWDZ 0 0

-- flattenDWD :: UVG.Vector v a => DWD v n a -> Vector v (2 ^ (n + 1)) a
-- flattenDWD = \case
--     DWDZ d  a  -> VG.fromTuple (a, d)
--     -- whoops this is O(n^2)
--     DWDS ds as -> flattenDWD as VG.++ ds

-- denseDWD
--     :: forall v n a. (KnownNat n, UVG.Vector v a)
--     => DWD v n a
--     -> V.Vector (n + 1) (Vector v (2 ^ n) a)
-- denseDWD = \case
--     DWDZ d  _  -> VG.singleton $ VG.singleton d
--     -- whoops this is O(n^3) or something
--     DWDS ds as -> (densify @_ @_ @(n - 1) <$> denseDWD as) `VG.snoc` ds

-- densify
--     :: (UVG.Vector v a, KnownNat n)
--     => Vector v (2 ^ n) a
--     -> Vector v (2 ^ (n + 1)) a
-- densify xs = VG.generate $ \i -> xs `VG.index` snd (separateProduct @2 i)

-- haar
--     :: forall v n a. (UVG.Vector v a, KnownNat n, Fractional a)
--     => Vector  v (2 ^ (n + 1)) a
--     -> DWD v n a
-- haar xs = case pNat (Proxy @n) of
--     PZ -> let x = xs `VG.index` 0
--               y = xs `VG.index` 1
--           in  DWDZ ((x - y) / 2) ((x + y) / 2)
--     PS -> let (a, d) = haarPass xs
--           in  DWDS d (haar a)

-- unHaar
--     :: (UVG.Vector v a, KnownNat n, Num a)
--     => DWD v n a
--     -> Vector v (2 ^ (n + 1)) a
-- unHaar = \case
--     DWDZ d  a  -> VG.fromTuple (a + d, a - d)
--     DWDS ds as -> unhaarPass (unHaar as) ds

-- haarPass
--     :: (UVG.Vector v a, KnownNat n, Fractional a)
--     => Vector v (2 ^ (n + 1)) a
--     -> (Vector v (2 ^ n) a, Vector v (2 ^ n) a)
-- haarPass xs = (app, det)
--   where
--     app = VG.generate $ \i -> ( xs `VG.index` combineProduct (0, i)
--                               + xs `VG.index` combineProduct (1, i)
--                               ) / 2
--     det = VG.generate $ \i -> ( xs `VG.index` combineProduct (0, i)
--                               - xs `VG.index` combineProduct (1, i)
--                               ) / 2

-- unhaarPass
--     :: (UVG.Vector v a, KnownNat n, Num a)
--     => Vector v (2 ^ n) a
--     -> Vector v (2 ^ n) a
--     -> Vector v (2 ^ (n + 1)) a
-- unhaarPass app det = VG.generate $ \i ->
--     let (j, k) = separateProduct @2 i
--         combiner
--           | j == 0    = (+)
--           | otherwise = (-)
--     in  combiner (app `VG.index` k) (det `VG.index` k)

