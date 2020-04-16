{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE FlexibleContexts      #-}
-- |
-- Module      : Data.Array.Accelerate.Unsafe
-- Copyright   : [2009..2019] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Operations which may be unsafe. Use with care.
--
-- @since 1.2.0.0
--

module Data.Array.Accelerate.Unsafe (

  -- ** Unsafe operations
  undef, coerce, Coerce

) where

import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.Smart


-- | The function 'coerce' allows you to convert a value between any two types
-- whose underlying representations have the same bit size at each component.
--
-- For example:
--
-- > coerce (x :: Exp Double)         :: Exp Word64
-- > coerce (x :: Exp (Int64,Float))  :: Exp (Complex Float, Word32)
--
-- Furthermore, as we typically declare newtype wrappers similarly to:
--
-- > type instance EltRepr (Sum a) = ((), EltRepr a)
--
-- This can be used instead of the newtype constructor, to go from the newtype's
-- abstract type to the concrete type by dropping the extra @()@ from the
-- representation, and vice-versa.
--
-- The type class 'Coerce' assures that there is a coercion between the two
-- types.
--
-- @since 1.2.0.0
--
coerce :: Coerce (EltRepr a) (EltRepr b) => Exp a -> Exp b
coerce = mkCoerce
