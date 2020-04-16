{-# LANGUAGE CPP                 #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Analysis.Type
-- Copyright   : [2008..2019] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- The Accelerate AST does not explicitly store much type information.  Most of
-- it is only indirectly through type class constraints -especially, 'Elt'
-- constraints- available. This module provides functions that reify that type
-- information in the form of a 'TupleType value. This is, for example, needed
-- to emit type information in a backend.
--

module Data.Array.Accelerate.Analysis.Type (

  accType,

  sizeOf,
  sizeOfScalarType,
  sizeOfSingleType,
  sizeOfVectorType,
  sizeOfNumType,
  sizeOfNonNumType,

) where

-- friends
import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Array.Representation
import Data.Array.Accelerate.Type

-- standard library
import qualified Foreign.Storable as F


-- |Determine the type of an expressions
-- -------------------------------------

accType :: forall acc aenv sh e. HasArraysRepr acc => acc aenv (Array sh e) -> TupleType e
accType = arrayRtype . arrayRepr


-- |Size of a tuple type, in bytes
--
sizeOf :: TupleType a -> Int
sizeOf TupRunit       = 0
sizeOf (TupRpair a b) = sizeOf a + sizeOf b
sizeOf (TupRsingle t) = sizeOfScalarType t

sizeOfScalarType :: ScalarType t -> Int
sizeOfScalarType (SingleScalarType t) = sizeOfSingleType t
sizeOfScalarType (VectorScalarType t) = sizeOfVectorType t

sizeOfSingleType :: SingleType t -> Int
sizeOfSingleType (NumSingleType t)    = sizeOfNumType t
sizeOfSingleType (NonNumSingleType t) = sizeOfNonNumType t

sizeOfVectorType :: VectorType t -> Int
sizeOfVectorType (VectorType n t) = n * sizeOfSingleType t

sizeOfNumType :: forall t. NumType t -> Int
sizeOfNumType (IntegralNumType t) | IntegralDict <- integralDict t = F.sizeOf (undefined::t)
sizeOfNumType (FloatingNumType t) | FloatingDict <- floatingDict t = F.sizeOf (undefined::t)

sizeOfNonNumType :: forall t. NonNumType t -> Int
sizeOfNonNumType TypeBool{} = 1 -- stored as Word8
sizeOfNonNumType t | NonNumDict <- nonNumDict t = F.sizeOf (undefined::t)

