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

module Numeric.Wavelet.Discrete (
    DWD(..)
  , dwdApprox, dwdDetail
  , flattenDWD
  , denseDWD
  , haar
  , unHaar
  ) where

import           Data.Finite
import           Data.Kind
import           Data.Proxy
import           Data.Vector.Generic.Sized (Vector)
import           GHC.TypeLits.Compare
import           GHC.TypeNats
import qualified Data.Vector               as UV
import qualified Data.Vector.Generic       as UVG
import qualified Data.Vector.Generic.Sized as VG
import qualified Data.Vector.Sized         as V


data DWD :: (Type -> Type) -> Nat -> Type -> Type where
    DWDZ :: { _dwdDetailZ :: !a
           , _dwdApprox  :: !a
           } -> DWD v 0 a
    DWDS :: { _dwdDetailS :: !(Vector  v (2 ^ (n + 1)) a)
           , _dwdNext    :: !(DWD v n             a)
           } -> DWD v (n + 1) a

deriving instance (Show (v a), Show a) => Show (DWD v n a)

dwdDetail :: UVG.Vector v a => DWD v n a -> Vector v (2 ^ n) a
dwdDetail = \case
    DWDZ d _ -> VG.singleton d
    DWDS d _ -> d

dwdApprox :: DWD v n a -> a
dwdApprox = \case
    DWDZ _ a -> a
    DWDS _ a -> dwdApprox a

testDec :: DWD UV.Vector 4 Double
testDec = DWDS (0 :: V.Vector 16 Double)
        . DWDS (0 :: V.Vector  8 Double)
        . DWDS (0 :: V.Vector  4 Double)
        . DWDS (0 :: V.Vector  2 Double)
        $ DWDZ 0 0

flattenDWD :: UVG.Vector v a => DWD v n a -> Vector v (2 ^ (n + 1)) a
flattenDWD = \case
    DWDZ d  a  -> VG.fromTuple (a, d)
    -- whoops this is O(n^2)
    DWDS ds as -> flattenDWD as VG.++ ds

denseDWD
    :: forall v n a. (KnownNat n, UVG.Vector v a)
    => DWD v n a
    -> V.Vector (n + 1) (Vector v (2 ^ n) a)
denseDWD = \case
    DWDZ d  _  -> VG.singleton $ VG.singleton d
    -- whoops this is O(n^3) or something
    DWDS ds as -> (densify @_ @_ @(n - 1) <$> denseDWD as) `VG.snoc` ds

densify
    :: (UVG.Vector v a, KnownNat n)
    => Vector v (2 ^ n) a
    -> Vector v (2 ^ (n + 1)) a
densify xs = VG.generate $ \i -> xs `VG.index` snd (separateProduct @2 i)

haar
    :: forall v n a. (UVG.Vector v a, KnownNat n, Fractional a)
    => Vector  v (2 ^ (n + 1)) a
    -> DWD v n a
haar xs = case pNat (Proxy @n) of
    PZ -> let x = xs `VG.index` 0
              y = xs `VG.index` 1
          in  DWDZ ((x - y) / 2) ((x + y) / 2)
    PS -> let (a, d) = haarPass xs
          in  DWDS d (haar a)

unHaar
    :: (UVG.Vector v a, KnownNat n, Num a)
    => DWD v n a
    -> Vector v (2 ^ (n + 1)) a
unHaar = \case
    DWDZ d  a  -> VG.fromTuple (a + d, a - d)
    DWDS ds as -> unhaarPass (unHaar as) ds

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

