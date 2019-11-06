{-# LANGUAGE BangPatterns                             #-}
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
{-# LANGUAGE ViewPatterns                             #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}


module Numeric.Wavelet.Continuous (
  -- * Continuous Wavelet Transform
    CWD(..), mapCWD
  , CWDLine(..), mapCWDLine
  , LNorm(..), CWDOpts(..), defaultCWDO
  , cwd
  , cwdReal
  -- * Wavelets
  , AWavelet(..), mapAWavelet
  , morlet, morletFunc
  , meyer, meyerFunc
  , fbsp, fbspFunc
  ) where

import           Data.Complex
import           Data.Finite
import           Data.Foldable
import           Data.Maybe
import           Data.Ord
import           Data.Proxy
import           Data.Type.Equality
import           Data.Vector.Generic.Sized    (Vector)
import           GHC.Generics                 (Generic)
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

data LNorm = L1 | L2
  deriving (Show, Eq, Ord, Enum, Bounded, Generic)

data CWDOpts n = CWDO
    { cwdoNorm     :: LNorm                     -- ^ wavelet normalization
    , cwdoMinScale :: Finite (n `Div` 2 + 1)    -- ^ min scale (period)
    , cwdoMaxScale :: Finite (n `Div` 2 + 1)    -- ^ max scale (period)
    }
  deriving (Show, Eq, Ord, Generic)

defaultCWDO :: KnownNat n => CWDOpts n
defaultCWDO = CWDO
    { cwdoNorm     = L2
    , cwdoMinScale = minBound
    , cwdoMaxScale = maxBound
    }

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
    -> CWDOpts n
    -> Vector v n (Complex b)
    -> CWD v n m a (Complex b)
cwd AW{..} CWDO{..} xs = CWD . VG.generate $ \i ->
      let s   = scaleOf i
          dt  = 1/s
      in  case awVector dt of
            VG.SomeSized (wv :: Vector v q (Complex b))
              | Just Refl <- isLE (Proxy @1) (Proxy @q)
              , Just Refl <- isLE (Proxy @((q-1)`Div`2)) (Proxy @(q-1))
              -> let ys :: Vector v (n + q - 1) (Complex b)
                     ys  = (* (realToFrac (normie dt) :+ 0)) `VG.map` convolve xs wv
                     coi = fromMaybe maxBound . packFinite . round @a @Integer $ sqrt 2 * s
                     s'  = fromMaybe maxBound . packFinite . round @a @Integer $ s
                     ys' :: Vector v n (Complex b)
                     ys' = VG.slice @_ @((q - 1)`Div`2) @n @((q-1)-((q-1)`Div`2)) Proxy ys
                 in  CWDLine ys' s' (awFreq / s) coi
            _ -> error "Bad scale: wavelet vector is empty?"
  where
    n = natVal (Proxy @n)
    m = natVal (Proxy @m)
    normie :: a -> a
    normie = case cwdoNorm of
      L1 -> sqrt
      L2 -> id
    minScale = fromIntegral cwdoMinScale `max` 1
    maxScale = (fromIntegral cwdoMaxScale `min` (fromIntegral n / (2 * sqrt 2)))
         `max` (minScale + 1)
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
    -> CWDOpts n
    -> Vector v n b
    -> CWD v n m a b
cwdReal aw cwdo = mapCWD realPart
                . cwd (mapAWavelet (:+ 0) aw) cwdo
                . VG.map (:+ 0)

-- | Analytical Wavelet
data AWavelet v a b = AW
    { awVector :: a -> v b    -- ^ generate a vector within awRange with a given dt
    , awFreq   :: a           -- ^ Dominant frequency component
    , awRange  :: a           -- ^ range away from zero outside of which wavelet can be considered negligible
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

fbsp
    :: (UVG.Vector v (Complex a), FFTWReal a)
    => Int      -- ^ m, >= 1
    -> a        -- ^ f_b, bandwidth
    -> a        -- ^ f_c, wavelet center frequency
    -> AWavelet v a (Complex a)
fbsp m fb fc = AW{..}
  where
    awRange  = 4/fb
    awVector = renderFunc awRange (fbspFunc m fb fc)
    awFreq   = autoDeriveFreq awRange awVector

autoDeriveFreq
    :: (UVG.Vector v (Complex a), FFTWReal a)
    => a
    -> (a -> v (Complex a))
    -> a
autoDeriveFreq r fv = case fv 0.001 of
    VG.SomeSized v ->
      let vv    = zip [1..] . map magnitude . VG.toList $ fft v
          (i,_) = maximumBy (comparing snd) vv
      in  fromInteger i / (r * 2)
    _ -> error "bad vector"

fbspFunc :: RealFloat a => Int -> a -> a -> a -> Complex a
fbspFunc m fb fc t =
    ((sqrt fb * sinc (fb * t / fromIntegral m))^m :+ 0) * exp (0 :+ (2 * pi * fc * t))
  where
    sinc x = sin x / x

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

