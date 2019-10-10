{-# LANGUAGE BangPatterns                             #-}
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
{-# LANGUAGE ViewPatterns                             #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}


module Numeric.Wavelet.Continuous (
    CWD(..)
  , CWDLine(..)
  , cwd
  , AWavelet(..)
  , morlet
  , meyer
  ) where

import           Data.Complex
import           Data.Finite
import           Data.Maybe
import           Data.Proxy
import           Data.Type.Equality
import           Data.Vector.Generic.Sized    (Vector)
import           GHC.TypeLits.Compare
import           GHC.TypeNats
import           Math.FFT.Base
import           Numeric.Wavelet.Internal.FFT
import qualified Data.Vector.Generic          as UVG
import qualified Data.Vector.Generic.Sized    as VG
import qualified Data.Vector.Sized            as V


newtype CWD v n m a = CWD { cwdLines :: V.Vector m (CWDLine v n a) }
  deriving Show

data CWDLine v n a = CWDLine
    { cwdlData  :: Vector v n a
    , cwdlScale :: Finite (n `Div` 2 + 1) -- ^ Scale factor, in number of ticks.
    , cwdlFreq  :: a                      -- ^ The frequency associated with this scale, in inverse tick
    , cwdlCoI   :: Finite (n `Div` 2 + 1) -- ^ How many items are /outside/ of the Cone of Influence, on each side.
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
    => AWavelet v a
    -> Finite (n `Div` 2 + 1)         -- ^ minimum scale (period)
    -> Finite (n `Div` 2 + 1)         -- ^ maximum scale (period)
    -> Vector v n a
    -> CWD v n m a
cwd AW{..} minS maxS xs = CWD . VG.generate $ \i ->
      let s   = scaleOf i
          dt  = 1/s
      in  case awVector dt of
            VG.SomeSized (wv :: Vector v q a)
              | Just Refl <- isLE (Proxy @1) (Proxy @q)
              , Just Refl <- isLE (Proxy @((q-1)`Div`2)) (Proxy @(q-1))
              -> let ys :: Vector v (n + q - 1) a
                     ys  = (* dt) `VG.map` convolve xs wv   -- rescale
                     coi = fromMaybe maxBound . packFinite . round $ sqrt 2 * s
                     ys' :: Vector v n a
                     ys' = VG.slice @_ @((q - 1)`Div`2) @n @((q-1)-((q-1)`Div`2)) Proxy ys
                 in  CWDLine ys' (round s) (awFreq * s) coi
            _ -> error "bad wavelet"
  where
    n = natVal (Proxy @n)
    m = natVal (Proxy @m)
    maxScale = fromIntegral maxS `min` (fromIntegral n / (2 * sqrt 2))
    minScale = fromIntegral minS `max` 1
    scaleStep = (log maxScale - log minScale) / (fromIntegral m - 1)
    scaleOf :: Finite m -> a
    scaleOf i = exp $ log minScale + fromIntegral i * scaleStep

-- | Analytical Wavelet
data AWavelet v a = AW
    { awVector :: a -> v a    -- ^ generate a vector within awRange with a given dt
    , awFreq   :: a
    , awRange  :: a
    }

morlet
    :: (UVG.Vector v a, RealFloat a)
    => a
    -> AWavelet v a
morlet σ = AW{..}
  where
    awRange  = 4
    awVector = renderFunc awRange $ \t ->
      realPart $ (c * exp(-t*t/2) :+ 0) * ( exp (0 :+ σ * t) - (exp (-σ2/2) :+ 0))
    c        = pi ** (-1/4) * (1 + exp (-σ2) - 2 * exp (-3/4*σ2)) ** (-1/2)
    σ2       = σ * σ
    awFreq   = flip (converge 20) σ $ \q -> σ / (1 - exp (-σ * q))

meyer :: (UVG.Vector v a, RealFloat a) => AWavelet v a
meyer = AW{..}
  where
    awRange = 6
    -- https://arxiv.org/ftp/arxiv/papers/1502/1502.00161.pdf
    -- Close expressions for Meyer Wavelet and Scale Function
    -- Valenzuela, V., de Oliveira, H.M.
    --
    -- we set singular points to 0 which shouldn't be bad if dt small
    awVector = renderFunc awRange $ \t ->
      let t' = t - 0.5
          t'3 = t'**3
          sinTerm = sin(4*pi/3*t') / pi
          ψ1 = (4/3/pi*t'*cos(2*pi/3*t') - sinTerm)
             / (t' - 16/9 * t'3)
          ψ2 = (8/3/pi*t'*cos(8*pi/3*t') + sinTerm)
             / (t' - 64/9 * t'3)
          ψ = ψ1 + ψ2
      in  if isNaN ψ || isInfinite ψ then 0 else ψ
    awFreq = 4 * pi / 3

-- -- TODO: check if mutable vectors helps at all
-- desingularize :: (UVG.Vector v a, RealFloat a) => v a -> v a
-- desingularize xs = UVG.imap go xs
--   where
--     go i x
--       | isBad x   = if nn > 0 then ns / nn else 0
--       | otherwise = x
--       where
--         (Sum ns, Sum nn) = (foldMap . foldMap) (\y -> (Sum y, Sum 1))
--           [ mfilter (not . isBad) $ xs UVG.!? (i - 1)
--           , mfilter (not . isBad) $ xs UVG.!? (i + 1)
--           ]
--     isBad x = isNaN x || isInfinite x


-- | Render the effective range of a wavelet (based on 'awRange'), centered
-- around zero.  Takes a timestep.
renderFunc
    :: (UVG.Vector v a, RealFrac a)
    => a              -- ^ range about zero
    -> (a -> a)       -- ^ func
    -> a              -- ^ dt
    -> v a
renderFunc r f dt = UVG.generate (round n) $ \i ->
    f (fromIntegral i * dt - r)
  where
    n  = r * 2 / dt

-- morlet :: RealFloat a => a -> a -> Complex a
-- morlet σ t = (c * exp(-t*t/2) :+ 0) * ( exp (0 :+ σ * t) - (exp (-σ * σ/2) :+ 0))
--   where
--     c = pi ** (-1/4) * (1 + exp (-σ * σ) - 2 * exp (-3/4*σ*σ)) ** (-1/2)

-- meyer :: RealFloat a => a -> a
-- meyer t = (sin (2 * pi * t) - sin (pi * t)) / pi / t

-- -- | Morelet wavelet from -4 to 4, normalized to dt.
-- morlet :: forall v n a. (UVG.Vector v a, KnownNat n, Floating a) => Vector v n a
-- morlet = VG.generate $ \i -> f (fromIntegral i * dt - 4) * dt
--   where
--     dt = 8 / fromIntegral (natVal (Proxy @n) - 1)
--     f x = exp(-x*x/2) * cos(5*x)

-- morletScaled :: forall v n a p. (UVG.Vector v a, KnownNat n, Floating a) => p n -> Vector v (8 * n) a
-- morletScaled _ = morlet

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

converge
    :: (Fractional a, Ord a)
    => Int      -- ^ maximum iterations
    -> (a -> a) -- ^ function to find the fixed point convergence
    -> a        -- ^ starting value
    -> a
converge n f = go 0
  where
    go !i !x
        | i >= n                = 0
        | abs (x - y) < 0.00001 = x
        | otherwise             = go (i + 1) y
      where
        !y = f x

