{-# LANGUAGE BangPatterns                             #-}
{-# LANGUAGE DeriveFunctor                            #-}
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
  -- * Continuous Wavelet Transform
    CWD(..), mapCWD
  , CWDLine(..), mapCWDLine
  , cwd
  , cwdReal
  -- * Wavelets
  , AWavelet(..), mapAWavelet
  , morlet, morletFunc
  , meyer, meyerComplex, meyerFunc
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


newtype CWD v n m a b = CWD { cwdLines :: V.Vector m (CWDLine v n a b) }
  deriving (Show, Functor)

data CWDLine v n a b = CWDLine
    { cwdlData  :: Vector v n b
    , cwdlScale :: Finite (n `Div` 2 + 1) -- ^ Scale factor, in number of ticks.
    , cwdlFreq  :: a                      -- ^ The frequency associated with this scale, in inverse tick
    , cwdlCoI   :: Finite (n `Div` 2 + 1) -- ^ How many items are /outside/ of the Cone of Influence, on each side.
    }
  deriving (Show, Functor)

mapCWDLine
    :: (UVG.Vector v b, UVG.Vector v c)
    => (b -> c)
    -> CWDLine v n a b
    -> CWDLine v n a c
mapCWDLine f (CWDLine d s q c) = CWDLine (VG.map f d) s q c

mapCWD
    :: (UVG.Vector v b, UVG.Vector v c)
    => (b -> c)
    -> CWD v n m a b
    -> CWD v n m a c
mapCWD f (CWD l) = CWD (mapCWDLine f <$> l)

-- | 'cwd' for complex-valued analytic wavelets.
cwd :: forall v n m a b.
     ( UVG.Vector v (Complex b)
     , KnownNat n
     , KnownNat m
     , FFTWReal b
     , 1 <= n
     , RealFloat a
     )
    => AWavelet v a (Complex b)
    -> Finite (n `Div` 2 + 1)         -- ^ minimum scale (period)
    -> Finite (n `Div` 2 + 1)         -- ^ maximum scale (period)
    -> Vector v n (Complex b)
    -> CWD v n m a (Complex b)
cwd AW{..} minS maxS xs = CWD . VG.generate $ \i ->
      let s   = scaleOf i
          dt  = 1/s
      in  case awVector dt of
            VG.SomeSized (wv :: Vector v q (Complex b))
              | Just Refl <- isLE (Proxy @1) (Proxy @q)
              , Just Refl <- isLE (Proxy @((q-1)`Div`2)) (Proxy @(q-1))
              -> let ys :: Vector v (n + q - 1) (Complex b)
                     ys  = (* (realToFrac dt :+ 0)) `VG.map` convolve xs wv   -- rescale
                     coi = fromMaybe maxBound . packFinite . round $ sqrt 2 * s
                     ys' :: Vector v n (Complex b)
                     ys' = VG.slice @_ @((q - 1)`Div`2) @n @((q-1)-((q-1)`Div`2)) Proxy ys
                 in  CWDLine ys' (round s) (awFreq / s) coi
            _ -> error "bad wavelet"
  where
    n = natVal (Proxy @n)
    m = natVal (Proxy @m)
    maxScale = fromIntegral maxS `min` (fromIntegral n / (2 * sqrt 2))
    minScale = fromIntegral minS `max` 1
    scaleStep = (log maxScale - log minScale) / (fromIntegral m - 1)
    scaleOf :: Finite m -> a
    scaleOf i = exp $ log minScale + fromIntegral i * scaleStep

-- | 'cwd' for real-valued analytic wavelets.
cwdReal
    :: forall v n m a b.
     ( UVG.Vector v b
     , UVG.Vector v (Complex b)
     , KnownNat n
     , KnownNat m
     , FFTWReal b
     , 1 <= n
     , RealFloat a
     )
    => AWavelet v a b
    -> Finite (n `Div` 2 + 1)         -- ^ minimum scale (period)
    -> Finite (n `Div` 2 + 1)         -- ^ maximum scale (period)
    -> Vector v n b
    -> CWD v n m a b
cwdReal aw minS maxS = mapCWD magnitude
                     . cwd (mapAWavelet (:+ 0) aw) minS maxS
                     . VG.map (:+ 0)

-- | Analytical Wavelet
data AWavelet v a b = AW
    { awVector :: a -> v b    -- ^ generate a vector within awRange with a given dt
    , awFreq   :: a
    , awRange  :: a
    }
  deriving Functor

mapAWavelet
    :: (UVG.Vector v b, UVG.Vector v c)
    => (b -> c)
    -> AWavelet v a b
    -> AWavelet v a c
mapAWavelet f (AW v q r) = AW (UVG.map f . v) q r

morlet
    :: (UVG.Vector v (Complex a), RealFloat a)
    => a
    -> AWavelet v a (Complex a)
morlet σ = AW{..}
  where
    awRange  = 4
    (!awFreq, mf) = morletFunc_ σ
    awVector = renderFunc awRange mf

morletFunc :: RealFloat a => a -> a -> Complex a
morletFunc = snd . morletFunc_

morletFunc_ :: RealFloat a => a -> (a, a -> Complex a)
morletFunc_ σ = (q, f)
  where
    f t = (c * exp(-t*t/2) :+ 0) * (exp (0 :+ (σ * t)) - (exp (-σ2/2) :+ 0))
    !c   = pi ** (-1/4) * (1 + exp (-σ2) - 2 * exp (-3/4*σ2)) ** (-1/2)
    !σ2  = σ * σ
    !q   = converge 20 iter σ / (2 * pi)
    iter w = σ / (1 - exp (-σ * w))

meyer
    :: (UVG.Vector v a, RealFloat a)
    => AWavelet v a a
meyer = AW{..}
  where
   awRange  = 6
   awVector = renderFunc awRange meyerFunc
   awFreq   = 4 * pi / 3

meyerComplex
    :: (UVG.Vector v (Complex a), RealFloat a)
    => AWavelet v a (Complex a)
meyerComplex = AW{..}
  where
   awRange  = 6
   awVector = renderFunc awRange ((:+ 0) . meyerFunc)
   awFreq   = 4 * pi / 3

meyerFunc :: RealFloat a => a -> a
meyerFunc t
    | isNaN ψ || isInfinite ψ = 0
    | otherwise               = ψ
  where
    t' = t - 0.5
    t'3 = t'**3
    sinTerm = sin(4*pi/3*t') / pi
    ψ1 = (4/3/pi*t'*cos(2*pi/3*t') - sinTerm)
       / (t' - 16/9 * t'3)
    ψ2 = (8/3/pi*t'*cos(8*pi/3*t') + sinTerm)
       / (t' - 64/9 * t'3)
    ψ = ψ1 + ψ2


--meyer :: (UVG.Vector v a, RealFloat a) => AWavelet v a
--meyer = AW{..}
--  where

--    awRange = 6
--    -- https://arxiv.org/ftp/arxiv/papers/1502/1502.00161.pdf
--    -- Close expressions for Meyer Wavelet and Scale Function
--    -- Valenzuela, V., de Oliveira, H.M.
--    --
--    -- we set singular points to 0 which shouldn't be bad if dt small
--    awVector = renderFunc awRange $ \t ->
--      let t' = t - 0.5
--          t'3 = t'**3
--          sinTerm = sin(4*pi/3*t') / pi
--          ψ1 = (4/3/pi*t'*cos(2*pi/3*t') - sinTerm)
--             / (t' - 16/9 * t'3)
--          ψ2 = (8/3/pi*t'*cos(8*pi/3*t') + sinTerm)
--             / (t' - 64/9 * t'3)
--          ψ = ψ1 + ψ2
--      in  if isNaN ψ || isInfinite ψ then 0 else ψ
--    awFreq = 4 * pi / 3

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
    :: (UVG.Vector v b, RealFrac a)
    => a              -- ^ range about zero
    -> (a -> b)       -- ^ func
    -> a              -- ^ dt
    -> v b
renderFunc r f dt = UVG.generate (round n) $ \i ->
    f (fromIntegral i * dt - r)
  where
    n  = r * 2 / dt

-- morseF :: (UVG.Vector v a, KnownNat n, Floating a) => a -> a -> a -> Vector v n a
-- morseF dω p γ = VG.generate $ \((* dω) . fromIntegral->ω) -> ω ** (p*p/γ) * exp (- (ω ** γ))

convolve
    :: forall v n m a.
     ( UVG.Vector v (Complex a)
     , KnownNat n, 1 <= n
     , KnownNat m, 1 <= m
     , FFTWReal a
     )
    => Vector v n (Complex a)
    -> Vector v m (Complex a)
    -> Vector v (n + m - 1) (Complex a)
convolve x y = ifft $ fft x' * fft y'
  where
    x' = x VG.++ 0
    y' = y VG.++ 0

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

