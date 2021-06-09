{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE RoleAnnotations     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Type
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
--  Primitive scalar types supported by Accelerate
--
--  Integral types:
--    * Int
--    * Int8
--    * Int16
--    * Int32
--    * Int64
--    * Word
--    * Word8
--    * Word16
--    * Word32
--    * Word64
--
--  Floating types:
--    * Half
--    * Float
--    * Double
--
--  SIMD vector types of the above:
--    * Vec2
--    * Vec3
--    * Vec4
--    * Vec8
--    * Vec16
--
-- Note that 'Int' has the same bit width as in plain Haskell computations.
-- 'Float' and 'Double' represent IEEE single and double precision floating
-- point numbers, respectively.
--

module Data.Array.Accelerate.Type (

  Half(..), Float, Double,
  module Data.Int,
  module Data.Word,
  module Foreign.C.Types,
  module Data.Array.Accelerate.Type,

) where

import Data.Array.Accelerate.Orphans () -- Prim Half
import Data.Primitive.Vec

import Data.Bits
import Data.Int
import Data.Primitive.Types
import Data.Type.Equality
import Data.Word
import Foreign.C.Types
import Foreign.Storable                                             ( Storable )
import Language.Haskell.TH
import Numeric.Half
import Text.Printf

import GHC.Prim
import GHC.TypeLits
import Data.Bifunctor (first)
import Unsafe.Coerce (unsafeCoerce)


-- Scalar types
-- ------------

-- Reified dictionaries
--
data SingleDict a where
  SingleDict :: ( Eq a, Ord a, Show a, Storable a, Prim a )
             => SingleDict a

data IntegralDict a where
  IntegralDict :: ( Eq a, Ord a, Show a
                  , Bounded a, Bits a, FiniteBits a, Integral a, Num a, Real a, Storable a )
               => IntegralDict a

data FloatingDict a where
  FloatingDict :: ( Eq a, Ord a, Show a
                  , Floating a, Fractional a, Num a, Real a, RealFrac a, RealFloat a, Storable a )
               => FloatingDict a


-- Scalar type representation
--

-- | Integral types supported in array computations.
--
-- data IntegralType a where -- 0 - 9
--   TypeInt     :: IntegralType Int
--   TypeInt8    :: IntegralType Int8
--   TypeInt16   :: IntegralType Int16
--   TypeInt32   :: IntegralType Int32
--   TypeInt64   :: IntegralType Int64
--   TypeWord    :: IntegralType Word
--   TypeWord8   :: IntegralType Word8
--   TypeWord16  :: IntegralType Word16
--   TypeWord32  :: IntegralType Word32
--   TypeWord64  :: IntegralType Word64

newtype IntegralType a = UnsafeIType { runUnsafeIType :: Int }
{-# COMPLETE TypeInt, TypeInt8, TypeInt16, TypeInt32, TypeInt64, TypeWord, TypeWord8, TypeWord16, TypeWord32, TypeWord64 #-}
pattern TypeInt    :: forall a. () => (a ~ Int)    => IntegralType a
pattern TypeInt    <- ((, unsafeCoerce @_ @(a :~: Int)    Refl) . runUnsafeIType -> (0, Refl))
  where TypeInt    = UnsafeIType 0
pattern TypeInt8   :: forall a. () => (a ~ Int8)   => IntegralType a
pattern TypeInt8   <- ((, unsafeCoerce @_ @(a :~: Int8)   Refl) . runUnsafeIType -> (1, Refl))
  where TypeInt8   = UnsafeIType 1
pattern TypeInt16  :: forall a. () => (a ~ Int16)  => IntegralType a
pattern TypeInt16  <- ((, unsafeCoerce @_ @(a :~: Int16)  Refl) . runUnsafeIType -> (2, Refl))
  where TypeInt16  = UnsafeIType 2
pattern TypeInt32  :: forall a. () => (a ~ Int32)  => IntegralType a
pattern TypeInt32  <- ((, unsafeCoerce @_ @(a :~: Int32)  Refl) . runUnsafeIType -> (3, Refl))
  where TypeInt32  = UnsafeIType 3
pattern TypeInt64  :: forall a. () => (a ~ Int64)  => IntegralType a
pattern TypeInt64  <- ((, unsafeCoerce @_ @(a :~: Int64)  Refl) . runUnsafeIType -> (4, Refl))
  where TypeInt64  = UnsafeIType 4
pattern TypeWord   :: forall a. () => (a ~ Word)   => IntegralType a
pattern TypeWord   <- ((, unsafeCoerce @_ @(a :~: Word)   Refl) . runUnsafeIType -> (5, Refl))
  where TypeWord   = UnsafeIType 5
pattern TypeWord8  :: forall a. () => (a ~ Word8)  => IntegralType a
pattern TypeWord8  <- ((, unsafeCoerce @_ @(a :~: Word8)  Refl) . runUnsafeIType -> (6, Refl))
  where TypeWord8  = UnsafeIType 6
pattern TypeWord16 :: forall a. () => (a ~ Word16) => IntegralType a
pattern TypeWord16 <- ((, unsafeCoerce @_ @(a :~: Word16) Refl) . runUnsafeIType -> (7, Refl))
  where TypeWord16 = UnsafeIType 7
pattern TypeWord32 :: forall a. () => (a ~ Word32) => IntegralType a
pattern TypeWord32 <- ((, unsafeCoerce @_ @(a :~: Word32) Refl) . runUnsafeIType -> (8, Refl))
  where TypeWord32 = UnsafeIType 8
pattern TypeWord64 :: forall a. () => (a ~ Word64) => IntegralType a
pattern TypeWord64 <- ((, unsafeCoerce @_ @(a :~: Word64) Refl) . runUnsafeIType -> (9, Refl))
  where TypeWord64 = UnsafeIType 9

-- | Floating-point types supported in array computations.
--
-- data FloatingType a where -- 10 - 12
--   TypeHalf    :: FloatingType Half
--   TypeFloat   :: FloatingType Float
--   TypeDouble  :: FloatingType Double

newtype FloatingType a =  UnsafeFType { runUnsafeFType :: Int }
{-# COMPLETE TypeHalf, TypeFloat, TypeDouble #-}
pattern TypeHalf   :: forall a. () => (a ~ Half)   => FloatingType a
pattern TypeHalf   <- ((, unsafeCoerce @_ @(a :~: Half)   Refl) . runUnsafeFType -> (10, Refl))
  where TypeHalf = UnsafeFType 10
pattern TypeFloat  :: forall a. () => (a ~ Float)  => FloatingType a
pattern TypeFloat  <- ((, unsafeCoerce @_ @(a :~: Float)  Refl) . runUnsafeFType -> (11, Refl))
  where TypeFloat = UnsafeFType 11
pattern TypeDouble :: forall a. () => (a ~ Double) => FloatingType a
pattern TypeDouble <- ((, unsafeCoerce @_ @(a :~: Double) Refl) . runUnsafeFType -> (12, Refl))
  where TypeDouble = UnsafeFType 12


-- | Numeric element types implement Num & Real
--
-- data NumType a where -- 0 - 12
--   IntegralNumType :: IntegralType a -> NumType a -- 0 - 9
--   FloatingNumType :: FloatingType a -> NumType a -- 10 - 12

newtype NumType a = UnsafeNType { runUnsafeNType :: Int}
{-# COMPLETE IntegralNumType, FloatingNumType #-}
pattern IntegralNumType :: IntegralType a -> NumType a
pattern IntegralNumType x <- (between 0 9 UnsafeIType . runUnsafeNType -> Just x)
  where IntegralNumType (UnsafeIType x) = UnsafeNType x
pattern FloatingNumType :: FloatingType a -> NumType a
pattern FloatingNumType x <- (between 10 12 UnsafeFType . runUnsafeNType -> Just x)
  where FloatingNumType (UnsafeFType x) = UnsafeNType x

-- | Bounded element types implement Bounded
--
newtype BoundedType a = IntegralBoundedType (IntegralType a)

-- | All scalar element types implement Eq & Ord
--
-- data ScalarType a where -- 0 - 25
--   SingleScalarType :: SingleType a         -> ScalarType a -- 0 - 12
--   VectorScalarType :: VectorType (Vec n a) -> ScalarType (Vec n a) -- 13 - 25

newtype ScalarType a = UnsafeSType { runUnsafeSType :: (Int, Maybe Int) }
{-# COMPLETE SingleScalarType, VectorScalarType #-}
pattern SingleScalarType :: SingleType a -> ScalarType a
pattern SingleScalarType x <- (first (NumSingleType . UnsafeNType) . runUnsafeSType -> (x, Nothing))  -- ((\(UnsafeSType y, Nothing) -> NumSingleType (UnsafeNType y) -> x)) -- . NumSingleType . UnsafeNType . runUnsafeSType -> Just x)
  where SingleScalarType (NumSingleType (UnsafeNType x)) = UnsafeSType (x, Nothing)
pattern VectorScalarType :: forall n a b. () => (b ~ Vec n a) => VectorType (Vec n a) -> ScalarType b
pattern VectorScalarType x <- (((, unsafeCoerce @_ @(b :~: Vec n a) Refl) . UnsafeVType @(Vec n a) <$>) . (sequence :: (Int, Maybe Int) -> Maybe (Int, Int)). runUnsafeSType -> Just (x, Refl))
  where VectorScalarType (UnsafeVType (x, n)) = UnsafeSType (x, Just n)

newtype SingleType a = NumSingleType (NumType a)


-- data VectorType a where
--   VectorType :: KnownNat n => {-# UNPACK #-} !Int -> SingleType a -> VectorType (Vec n a) -- 13 - 25 (SingleType + 13)

newtype VectorType a = UnsafeVType { runUnsafeVType :: (Int, Int) }
{-# COMPLETE VectorType #-}
pattern VectorType :: forall n a b. () => ({-KnownNat n, -} b ~ Vec n a) => Int -> SingleType a -> VectorType b
pattern VectorType a b <- ((, unsafeCoerce @_ @(b :~: Vec n a) Refl) . first (NumSingleType . UnsafeNType @a) . runUnsafeVType -> ((b, a), Refl))
  where VectorType n (NumSingleType (UnsafeNType x)) = UnsafeVType (x, n)

-- For defining pattern synonyms: matches if the fourth argument is between the first two (inclusive on both ends)
between :: Int -> Int -> (Int -> a) -> Int -> Maybe a
between l u f x
  | x >= l && x <= u = Just (f x)
  | otherwise        = Nothing


instance Show (IntegralType a) where
  show TypeInt    = "Int"
  show TypeInt8   = "Int8"
  show TypeInt16  = "Int16"
  show TypeInt32  = "Int32"
  show TypeInt64  = "Int64"
  show TypeWord   = "Word"
  show TypeWord8  = "Word8"
  show TypeWord16 = "Word16"
  show TypeWord32 = "Word32"
  show TypeWord64 = "Word64"

instance Show (FloatingType a) where
  show TypeHalf   = "Half"
  show TypeFloat  = "Float"
  show TypeDouble = "Double"

instance Show (NumType a) where
  show (IntegralNumType ty) = show ty
  show (FloatingNumType ty) = show ty

instance Show (BoundedType a) where
  show (IntegralBoundedType ty) = show ty

instance Show (SingleType a) where
  show (NumSingleType ty) = show ty

instance Show (VectorType a) where
  show (VectorType n ty) = printf "<%d x %s>" n (show ty)

instance Show (ScalarType a) where
  show (SingleScalarType ty) = show ty
  show (VectorScalarType ty) = show ty

-- | Querying Integral types
--
class (IsSingle a, IsNum a, IsBounded a) => IsIntegral a where
  integralType :: IntegralType a

-- | Querying Floating types
--
class (Floating a, IsSingle a, IsNum a) => IsFloating a where
  floatingType :: FloatingType a

-- | Querying Numeric types
--
class (Num a, IsSingle a) => IsNum a where
  numType :: NumType a

-- | Querying Bounded types
--
class IsBounded a where
  boundedType :: BoundedType a

-- | Querying single value types
--
class IsScalar a => IsSingle a where
  singleType :: SingleType a

-- | Querying all scalar types
--
class IsScalar a where
  scalarType :: ScalarType a


integralDict :: IntegralType a -> IntegralDict a
integralDict TypeInt    = IntegralDict
integralDict TypeInt8   = IntegralDict
integralDict TypeInt16  = IntegralDict
integralDict TypeInt32  = IntegralDict
integralDict TypeInt64  = IntegralDict
integralDict TypeWord   = IntegralDict
integralDict TypeWord8  = IntegralDict
integralDict TypeWord16 = IntegralDict
integralDict TypeWord32 = IntegralDict
integralDict TypeWord64 = IntegralDict

floatingDict :: FloatingType a -> FloatingDict a
floatingDict TypeHalf   = FloatingDict
floatingDict TypeFloat  = FloatingDict
floatingDict TypeDouble = FloatingDict

singleDict :: SingleType a -> SingleDict a
singleDict = single
  where
    single :: SingleType a -> SingleDict a
    single (NumSingleType t) = num t

    num :: NumType a -> SingleDict a
    num (IntegralNumType t) = integral t
    num (FloatingNumType t) = floating t

    integral :: IntegralType a -> SingleDict a
    integral TypeInt    = SingleDict
    integral TypeInt8   = SingleDict
    integral TypeInt16  = SingleDict
    integral TypeInt32  = SingleDict
    integral TypeInt64  = SingleDict
    integral TypeWord   = SingleDict
    integral TypeWord8  = SingleDict
    integral TypeWord16 = SingleDict
    integral TypeWord32 = SingleDict
    integral TypeWord64 = SingleDict

    floating :: FloatingType a -> SingleDict a
    floating TypeHalf   = SingleDict
    floating TypeFloat  = SingleDict
    floating TypeDouble = SingleDict


scalarTypeInt :: ScalarType Int
scalarTypeInt = SingleScalarType $ NumSingleType $ IntegralNumType TypeInt

scalarTypeWord :: ScalarType Word
scalarTypeWord = SingleScalarType $ NumSingleType $ IntegralNumType TypeWord

scalarTypeInt32 :: ScalarType Int32
scalarTypeInt32 = SingleScalarType $ NumSingleType $ IntegralNumType TypeInt32

scalarTypeWord8 :: ScalarType Word8
scalarTypeWord8 = SingleScalarType $ NumSingleType $ IntegralNumType TypeWord8

scalarTypeWord32 :: ScalarType Word32
scalarTypeWord32 = SingleScalarType $ NumSingleType $ IntegralNumType TypeWord32

rnfScalarType :: ScalarType t -> ()
rnfScalarType (SingleScalarType t) = rnfSingleType t
rnfScalarType (VectorScalarType t) = rnfVectorType t

rnfSingleType :: SingleType t -> ()
rnfSingleType (NumSingleType t) = rnfNumType t

rnfVectorType :: VectorType t -> ()
rnfVectorType (VectorType !_ t) = rnfSingleType t

rnfBoundedType :: BoundedType t -> ()
rnfBoundedType (IntegralBoundedType t) = rnfIntegralType t

rnfNumType :: NumType t -> ()
rnfNumType (IntegralNumType t) = rnfIntegralType t
rnfNumType (FloatingNumType t) = rnfFloatingType t

rnfIntegralType :: IntegralType t -> ()
rnfIntegralType TypeInt    = ()
rnfIntegralType TypeInt8   = ()
rnfIntegralType TypeInt16  = ()
rnfIntegralType TypeInt32  = ()
rnfIntegralType TypeInt64  = ()
rnfIntegralType TypeWord   = ()
rnfIntegralType TypeWord8  = ()
rnfIntegralType TypeWord16 = ()
rnfIntegralType TypeWord32 = ()
rnfIntegralType TypeWord64 = ()

rnfFloatingType :: FloatingType t -> ()
rnfFloatingType TypeHalf   = ()
rnfFloatingType TypeFloat  = ()
rnfFloatingType TypeDouble = ()


liftScalar :: ScalarType t -> t -> Q (TExp t)
liftScalar (SingleScalarType t) = liftSingle t
liftScalar (VectorScalarType t) = liftVector t

liftSingle :: SingleType t -> t -> Q (TExp t)
liftSingle (NumSingleType t) = liftNum t

liftVector :: VectorType t -> t -> Q (TExp t)
liftVector VectorType{} = liftVec

liftNum :: NumType t -> t -> Q (TExp t)
liftNum (IntegralNumType t) = liftIntegral t
liftNum (FloatingNumType t) = liftFloating t

liftIntegral :: IntegralType t -> t -> Q (TExp t)
liftIntegral TypeInt    x = [|| x ||]
liftIntegral TypeInt8   x = [|| x ||]
liftIntegral TypeInt16  x = [|| x ||]
liftIntegral TypeInt32  x = [|| x ||]
liftIntegral TypeInt64  x = [|| x ||]
liftIntegral TypeWord   x = [|| x ||]
liftIntegral TypeWord8  x = [|| x ||]
liftIntegral TypeWord16 x = [|| x ||]
liftIntegral TypeWord32 x = [|| x ||]
liftIntegral TypeWord64 x = [|| x ||]

liftFloating :: FloatingType t -> t -> Q (TExp t)
liftFloating TypeHalf   x = [|| x ||]
liftFloating TypeFloat  x = [|| x ||]
liftFloating TypeDouble x = [|| x ||]


liftScalarType :: ScalarType t -> Q (TExp (ScalarType t))
liftScalarType (SingleScalarType t) = [|| SingleScalarType $$(liftSingleType t) ||]
liftScalarType (VectorScalarType t) = [|| VectorScalarType $$(liftVectorType t) ||]

liftSingleType :: SingleType t -> Q (TExp (SingleType t))
liftSingleType (NumSingleType t) = [|| NumSingleType $$(liftNumType t) ||]

liftVectorType :: VectorType t -> Q (TExp (VectorType t))
liftVectorType (VectorType n t) = [|| VectorType n $$(liftSingleType t) ||]

liftNumType :: NumType t -> Q (TExp (NumType t))
liftNumType (IntegralNumType t) = [|| IntegralNumType $$(liftIntegralType t) ||]
liftNumType (FloatingNumType t) = [|| FloatingNumType $$(liftFloatingType t) ||]

liftBoundedType :: BoundedType t -> Q (TExp (BoundedType t))
liftBoundedType (IntegralBoundedType t) = [|| IntegralBoundedType $$(liftIntegralType t) ||]

liftIntegralType :: IntegralType t -> Q (TExp (IntegralType t))
liftIntegralType TypeInt    = [|| TypeInt ||]
liftIntegralType TypeInt8   = [|| TypeInt8 ||]
liftIntegralType TypeInt16  = [|| TypeInt16 ||]
liftIntegralType TypeInt32  = [|| TypeInt32 ||]
liftIntegralType TypeInt64  = [|| TypeInt64 ||]
liftIntegralType TypeWord   = [|| TypeWord ||]
liftIntegralType TypeWord8  = [|| TypeWord8 ||]
liftIntegralType TypeWord16 = [|| TypeWord16 ||]
liftIntegralType TypeWord32 = [|| TypeWord32 ||]
liftIntegralType TypeWord64 = [|| TypeWord64 ||]

liftFloatingType :: FloatingType t -> Q (TExp (FloatingType t))
liftFloatingType TypeHalf   = [|| TypeHalf ||]
liftFloatingType TypeFloat  = [|| TypeFloat ||]
liftFloatingType TypeDouble = [|| TypeDouble ||]


-- Type-level bit sizes
-- --------------------

-- | Constraint that values of these two types have the same bit width
--
type BitSizeEq a b = (BitSize a == BitSize b) ~ 'True
type family BitSize a :: Nat


-- Instances
-- ---------
--
-- Generate instances for the IsX classes. It would be preferable to do this
-- automatically based on the members of the IntegralType (etc.) representations
-- (see for example FromIntegral.hs) but TH phase restrictions would require us
-- to split this into a separate module.
--

$(runQ $ do
  let
      bits :: FiniteBits b => b -> Integer
      bits = toInteger . finiteBitSize

      integralTypes :: [(Name, Integer)]
      integralTypes =
        [ (''Int,    bits (undefined::Int))
        , (''Int8,   8)
        , (''Int16,  16)
        , (''Int32,  32)
        , (''Int64,  64)
        , (''Word,   bits (undefined::Word))
        , (''Word8,  8)
        , (''Word16, 16)
        , (''Word32, 32)
        , (''Word64, 64)
        ]

      floatingTypes :: [(Name, Integer)]
      floatingTypes =
        [ (''Half,   16)
        , (''Float,  32)
        , (''Double, 64)
        ]

      vectorTypes :: [(Name, Integer)]
      vectorTypes = integralTypes ++ floatingTypes

      mkIntegral :: Name -> Integer -> Q [Dec]
      mkIntegral t n =
        [d| instance IsIntegral $(conT t) where
              integralType = $(conE (mkName ("Type" ++ nameBase t)))

            instance IsNum $(conT t) where
              numType = IntegralNumType integralType

            instance IsBounded $(conT t) where
              boundedType = IntegralBoundedType integralType

            instance IsSingle $(conT t) where
              singleType = NumSingleType numType

            instance IsScalar $(conT t) where
              scalarType = SingleScalarType singleType

            type instance BitSize $(conT t) = $(litT (numTyLit n))
          |]

      mkFloating :: Name -> Integer -> Q [Dec]
      mkFloating t n =
        [d| instance IsFloating $(conT t) where
              floatingType = $(conE (mkName ("Type" ++ nameBase t)))

            instance IsNum $(conT t) where
              numType = FloatingNumType floatingType

            instance IsSingle $(conT t) where
              singleType = NumSingleType numType

            instance IsScalar $(conT t) where
              scalarType = SingleScalarType singleType

            type instance BitSize $(conT t) = $(litT (numTyLit n))
          |]

      mkVector :: Name -> Integer -> Q [Dec]
      mkVector t n =
        [d| instance KnownNat n => IsScalar (Vec n $(conT t)) where
              scalarType = VectorScalarType (VectorType (fromIntegral (natVal' (proxy# :: Proxy# n))) singleType)

            type instance BitSize (Vec w $(conT t)) = w GHC.TypeLits.* $(litT (numTyLit n))
          |]
      --
  is <- mapM (uncurry mkIntegral) integralTypes
  fs <- mapM (uncurry mkFloating) floatingTypes
  vs <- mapM (uncurry mkVector)   vectorTypes
  --
  return (concat is ++ concat fs ++ concat vs)
 )

