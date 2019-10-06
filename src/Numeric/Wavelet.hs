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
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}

module Numeric.Wavelet (
    WaveDec(..)
  , wdApprox, wdDetail
  , flattenWD
  , denseWD
  , haar
  , unHaar
  , itraverseDec
  , ifoldMapDec
  ) where

import           Control.Monad
import           Data.Finite
import           Data.Kind
import           Data.Proxy
import           Data.Vector.Generic.Sized          (Vector)
import           GHC.TypeLits.Compare
import           GHC.TypeNats
import qualified Data.Finite.Internal               as FI
import qualified Data.Vector                        as UV
import qualified Data.Vector.Generic                as UVG
import qualified Data.Vector.Generic.Sized          as VG
import qualified Data.Vector.Generic.Sized.Internal as VGI
import qualified Data.Vector.Sized                  as V


data WaveDec :: (Type -> Type) -> Nat -> Type -> Type where
    WDZ :: { _wdDetailZ :: !a
           , _wdApprox  :: !a
           } -> WaveDec v 0 a
    WDS :: { _wdDetailS :: !(Vector  v (2 ^ (n + 1)) a)
           , _wdNext    :: !(WaveDec v n             a)
           } -> WaveDec v (n + 1) a

deriving instance (Show (v a), Show a) => Show (WaveDec v n a)

wdDetail :: UVG.Vector v a => WaveDec v n a -> Vector v (2 ^ n) a
wdDetail = \case
    WDZ d _ -> VG.singleton d
    WDS d _ -> d

wdApprox :: WaveDec v n a -> a
wdApprox = \case
    WDZ _ a -> a
    WDS _ a -> wdApprox a

testDec :: WaveDec UV.Vector 4 Double
testDec = WDS (0 :: V.Vector 16 Double)
        . WDS (0 :: V.Vector  8 Double)
        . WDS (0 :: V.Vector  4 Double)
        . WDS (0 :: V.Vector  2 Double)
        $ WDZ 0 0

flattenWD :: UVG.Vector v a => WaveDec v n a -> Vector v (2 ^ (n + 1)) a
flattenWD = \case
    WDZ d  a  -> VG.fromTuple (a, d)
    -- whoops this is O(n^2)
    WDS ds as -> flattenWD as VG.++ ds

denseWD
    :: forall v n a. (KnownNat n, UVG.Vector v a)
    => WaveDec v n a
    -> V.Vector (n + 1) (Vector v (2 ^ n) a)
denseWD = \case
    WDZ d  _  -> VG.singleton $ VG.singleton d
    -- whoops this is O(n^3) or something
    WDS ds as -> (densify @_ @_ @(n - 1) <$> denseWD as) `VG.snoc` ds

densify
    :: (UVG.Vector v a, KnownNat n)
    => Vector v (2 ^ n) a
    -> Vector v (2 ^ (n + 1)) a
densify xs = VG.generate $ \i -> xs `VG.index` snd (separateProduct @2 i)

itraverseDec
    :: (UVG.Vector v a, UVG.Vector v b, KnownNat n, Applicative f)
    => (a -> f b)
    -> (forall q. (KnownNat q, q <= (n + 1)) => Finite (2 ^ q) -> a -> f b)
    -> WaveDec v n a
    -> f (WaveDec v n b)
itraverseDec f g = \case
    WDZ d  a  -> flip WDZ <$> f a <*> g @1 0 d
    WDS ds as -> flip WDS <$> itraverseDec f g as
                          <*> itraverseVector g ds

ifoldMapDec
    :: (UVG.Vector v a, KnownNat n, Monoid m)
    => (a -> m)
    -> (forall q. (KnownNat q, q <= (n + 1)) => Finite (2 ^ q) -> a -> m)
    -> WaveDec v n a
    -> m
ifoldMapDec f g = \case
    WDZ d  a  -> f a <> g @1 0 d
    WDS ds as -> ifoldMapDec f g as <> ifoldMapVector g ds

haar
    :: forall v n a. (UVG.Vector v a, KnownNat n, Fractional a)
    => Vector  v (2 ^ (n + 1)) a
    -> WaveDec v n a
haar xs = case pNat (Proxy @n) of
    PZ -> let x = xs `VG.index` 0
              y = xs `VG.index` 1
          in  WDZ ((x - y) / 2) ((x + y) / 2)
    PS -> let (a, d) = haarPass xs
          in  WDS d (haar a)

unHaar
    :: (UVG.Vector v a, KnownNat n, Num a)
    => WaveDec v n a
    -> Vector v (2 ^ (n + 1)) a
unHaar = \case
    WDZ d  a  -> VG.fromTuple (a + d, a - d)
    WDS ds as -> unhaarPass (unHaar as) ds

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

unhaarPass
    :: (UVG.Vector v a, KnownNat n, Num a)
    => Vector v (2 ^ n) a
    -> Vector v (2 ^ n) a
    -> Vector v (2 ^ (n + 1)) a
unhaarPass app det = VG.generate $ \i ->
    let (j, k) = separateProduct @2 i
        combiner
          | j == 0    = (+)
          | otherwise = (-)
    in  combiner (app `VG.index` k) (det `VG.index` k)

itraverseVector
    :: (UVG.Vector v a, UVG.Vector v b, Applicative f)
    => (Finite n -> a -> f b)
    -> Vector v n a
    -> f (Vector v n b)
itraverseVector f (VGI.Vector xs) = VGI.Vector . UVG.fromList <$> zipWithM f (FI.Finite <$> [0..]) (UVG.toList xs)

ifoldMapVector
    :: (UVG.Vector v a, Monoid m)
    => (Finite n -> a -> m)
    -> Vector v n a
    -> m
ifoldMapVector f (VGI.Vector xs) = foldMap (uncurry f) $ zip (FI.Finite <$> [0..]) (UVG.toList xs)

