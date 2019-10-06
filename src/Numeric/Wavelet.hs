{-# LANGUAGE FlexibleContexts                         #-}
{-# LANGUAGE GADTs                                    #-}
{-# LANGUAGE KindSignatures                           #-}
{-# LANGUAGE LambdaCase                               #-}
{-# LANGUAGE NoStarIsType                             #-}
{-# LANGUAGE ScopedTypeVariables                      #-}
{-# LANGUAGE StandaloneDeriving                       #-}
{-# LANGUAGE TypeApplications                         #-}
{-# LANGUAGE TypeFamilyDependencies                   #-}
{-# LANGUAGE TypeInType                               #-}
{-# LANGUAGE TypeOperators                            #-}
{-# LANGUAGE UndecidableInstances                     #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}

module Numeric.Wavelet where

-- module Numeric.Wavelet (
--   ) where


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


data WaveDec :: (Type -> Type) -> Nat -> Type -> Type where
    WDZ :: { _wdDetailZ :: !a
           , _wdApprox  :: !a
           } -> WaveDec v 0 a
    WDS :: { _wdDetailS :: !(Vector  v (2 ^ (n + 1)) a)
           , _wdNext    :: !(WaveDec v n             a)
           } -> WaveDec v (n + 1) a

deriving instance (Show (v a), Show a) => Show (WaveDec v n a)

_wdDetail :: UVG.Vector v a => WaveDec v n a -> Vector v (2 ^ n) a
_wdDetail = \case
    WDZ d _ -> VG.singleton d
    WDS d _ -> d

testDec :: WaveDec UV.Vector 4 Double
testDec = WDS (0 :: V.Vector 16 Double)
        . WDS (0 :: V.Vector  8 Double)
        . WDS (0 :: V.Vector  4 Double)
        . WDS (0 :: V.Vector  2 Double)
        $ WDZ 0 0

flattenWD :: UVG.Vector v a => WaveDec v n a -> Vector v (2 ^ (n + 1)) a
flattenWD = \case
    WDZ d  a  -> VG.fromTuple (a, d)
    WDS ds as -> flattenWD as VG.++ ds

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

