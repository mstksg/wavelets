{-# LANGUAGE FlexibleContexts                         #-}
{-# LANGUAGE GADTs                                    #-}
{-# LANGUAGE KindSignatures                           #-}
{-# LANGUAGE LambdaCase                               #-}
{-# LANGUAGE NoStarIsType                             #-}
{-# LANGUAGE RankNTypes                               #-}
{-# LANGUAGE ScopedTypeVariables                      #-}
{-# LANGUAGE StandaloneDeriving                       #-}
{-# LANGUAGE TypeApplications                         #-}
{-# LANGUAGE TypeFamilyDependencies                   #-}
{-# LANGUAGE TypeInType                               #-}
{-# LANGUAGE TypeOperators                            #-}
{-# LANGUAGE UndecidableInstances                     #-}
{-# LANGUAGE ViewPatterns                             #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}


module Numeric.Wavelet.Continuous (
    CWD(..)
  , CWDLine(..)
  , cwd
  ) where

import           Data.Complex
import           Data.Finite
import           Data.Maybe
import           Data.Proxy
import           Data.Type.Equality
import           Data.Vector.Generic.Sized (Vector)
import           GHC.TypeLits.Compare
import           GHC.TypeNats
import           Math.FFT.Base
import           Numeric.Wavelet.Internal
import qualified Data.Vector.Generic       as UVG
import qualified Data.Vector.Generic.Sized as VG
import qualified Data.Vector.Sized         as V


newtype CWD v n m a = CWD { cwdLines :: V.Vector m (CWDLine v n a) }
  deriving Show

data CWDLine v n a = CWDLine
    { cwdlData  :: Vector v n a
    , cwdlScale :: Finite (n `Div` 2 + 1) -- ^ Scale factor, in number of ticks
    , cwdlCoI   :: Finite (n `Div` 2 + 1)
    }
  deriving Show

-- | Morelet continuous wavelet decomposition.
cwd :: forall v n m a.
     ( UVG.Vector v a
     , UVG.Vector v (Complex a)
     , KnownNat n
     , KnownNat m
     , FFTWReal a
     , 1 <= n
     )
    => Finite (n `Div` 2 + 1)         -- ^ minimum scale (period)
    -> Finite (n `Div` 2 + 1)         -- ^ maximum scale (period)
    -> Vector v n a
    -> CWD v n m a
cwd minS maxS xs = CWD . VG.generate $ \i ->
      let s   = scaleOf i
      in  case someNatVal (round s) of
            SomeNat p@(Proxy :: Proxy q) ->
              case isLE (Proxy @1) (Proxy @(8 * q)) of
                Just Refl ->
                  let ms :: Vector v (8 * q) a
                      ms = morletScaled p
                      ys :: Vector v (n + (8 * q) - 1) a
                      ys = convolve xs ms
                      coi = fromMaybe maxBound . packFinite . round $ sqrt 2 * s
                  in  CWDLine (VG.slice (Proxy @(4 * q)) ys) (round s) coi
                Nothing -> undefined
  where
    n = natVal (Proxy @n)
    m = natVal (Proxy @m)
    maxScale = fromIntegral maxS `min` (fromIntegral n / (3 * sqrt 2))
    minScale = fromIntegral minS `max` 1
    scaleStep = (log maxScale - log minScale) / (fromIntegral m - 1)
    scaleOf :: Finite m -> a
    scaleOf i = exp $ log minScale + fromIntegral i * scaleStep

-- | Morelet wavelet from -4 to 4, normalized to dt.
morlet :: forall v n a. (UVG.Vector v a, KnownNat n, Floating a) => Vector v n a
morlet = VG.generate $ \i -> f (fromIntegral i * dt - 4) * dt
  where
    dt = 8 / fromIntegral (natVal (Proxy @n) - 1)
    f x = exp(-x*x/2) * cos(5*x)

morletScaled :: forall v n a p. (UVG.Vector v a, KnownNat n, Floating a) => p n -> Vector v (8 * n) a
morletScaled _ = morlet

-- morlet :: RealFloat a => a -> a -> Complex a
-- morlet σ t = ((c * (pi ** (-4)) * exp (- t**2 / 2)) :+ 0)
--            * (exp (0 :+ σ * t) - (κ :+ 0))
--   where
--     σ2 = σ ** 2
--     c = (1 + exp (- σ2) - 2 * exp (- 3 / 4 * σ2)) ** (-1/2)
--     κ = exp (-σ2/2)

-- morseF :: (UVG.Vector v a, KnownNat n, Floating a) => a -> a -> a -> Vector v n a
-- morseF dω p γ = VG.generate $ \((* dω) . fromIntegral->ω) -> ω ** (p*p/γ) * exp (- (ω ** γ))

convolve
    :: forall v n m a.
     ( UVG.Vector v a
     , UVG.Vector v (Complex a)
     , KnownNat n, 1 <= n
     , KnownNat m, 1 <= m
     , FFTWReal a
     )
    => Vector v n a
    -> Vector v m a
    -> Vector v (n + m - 1) a
convolve x y = VG.map realPart . ifft $ fft x' * fft y'
  where
    x' = ((:+ 0) `VG.map` x) VG.++ 0
    y' = ((:+ 0) `VG.map` y) VG.++ 0

-- convolve
--     :: forall v n m a. (KnownNat n, KnownNat m, UVG.Vector v a, Num a, 1 <= n + m)
--     => Vector v n a
--     -> Vector v m a
--     -> Vector v (n + m - 1) a
-- convolve x y = VG.generate $ \i -> sum $ map (go i) finites
  -- where
    -- go  :: Finite (n + m - 1) -> Finite n -> a
    -- go n k
    --   | Right j <- sub n k
    --   , Just l  <- strengthenN j
    --   = x `VG.index` k * y `VG.index` l
    --   | otherwise = 0
