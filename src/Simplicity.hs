{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Simplicity where

import           Prelude hiding (not)

-- The Simplicity type language has three type constructs:
-- unit, pairs, sums.
--
-- How do you model this as a Haskell datatype?
--
-- unit is not a datatype
--
-- please fill in the dots for SimplicityType

data SimplicityType =
    U -- let's make it clear which one is which
  | SimplicityType :+: SimplicityType
  | SimplicityType :*: SimplicityType
    deriving Show

infixl 5 :+:
infixl 6 :*:

class HasBitSize (a :: SimplicityType) where
  bitSize :: Int

instance HasBitSize 'U where
  bitSize = 0

instance (HasBitSize a, HasBitSize b) => HasBitSize (a ':+: b) where
  bitSize = 1 + max (bitSize @a) (bitSize @b)

instance (HasBitSize a, HasBitSize b) => HasBitSize (a ':*: b) where
  bitSize = bitSize @a + bitSize @b

class CanPad (a :: SimplicityType) where
  padL :: Int
  padR :: Int

instance (HasBitSize a, HasBitSize b) => CanPad (a ':+: b) where
  padL = max (bitSize @a) (bitSize @b) - (bitSize @a)
  padR = max (bitSize @a) (bitSize @b) - (bitSize @b)

class CanDrop (a :: SimplicityType) where
  droppedSize :: Int

instance (HasBitSize a, HasBitSize b) => CanDrop (a ':*: b) where
  droppedSize = bitSize @a

-- SimplicityExpr has an input type and an output type
data SimplicityExpr :: SimplicityType -> SimplicityType -> * where
    Iden :: HasBitSize a =>
            SimplicityExpr a a
    Unit :: SimplicityExpr a 'U
    Comp :: (HasBitSize a, HasBitSize b, HasBitSize c) =>
            SimplicityExpr a b -> SimplicityExpr b c -> SimplicityExpr a c
    Injl :: (HasBitSize a, HasBitSize b, HasBitSize c) =>
            SimplicityExpr a b -> SimplicityExpr a (b ':+: c)
    Injr :: (HasBitSize a, HasBitSize b, HasBitSize c) =>
            SimplicityExpr a c -> SimplicityExpr a (b ':+: c)
    Case :: (HasBitSize a, HasBitSize b, HasBitSize c, HasBitSize d) =>
            SimplicityExpr (a ':*: c) d -> SimplicityExpr (b ':*: c) d
            -> SimplicityExpr ((a ':+: b) ':*: c) d
    Pair :: SimplicityExpr a b -> SimplicityExpr a c -> SimplicityExpr a (b ':*: c)
    Take :: SimplicityExpr a c -> SimplicityExpr (a ':*: b) c
    Drop :: (HasBitSize a, HasBitSize b, HasBitSize c) =>
            SimplicityExpr b c -> SimplicityExpr (a ':*: b) c

type Bit = 'U ':+: 'U

not :: SimplicityExpr Bit Bit
not = Comp (Pair Iden Unit) (Case (Injr Unit) (Injl Unit))

halfAdder :: SimplicityExpr (Bit ':*: Bit) (Bit ':*: Bit)
halfAdder = Case (Drop (Pair (Injl Unit) Iden)) (Drop (Pair Iden not))

data SimplicityValue :: SimplicityType -> * where
    Un  :: SimplicityValue 'U
    P   :: SimplicityValue a -> SimplicityValue b -> SimplicityValue (a ':*: b)
    L   :: SimplicityValue a -> SimplicityValue (a ':+: b)
    R   :: SimplicityValue b -> SimplicityValue (a ':+: b)

instance Show (SimplicityValue a) where
    show  Un     = "()"
    show (P a b) = "(" ++ show a ++ "," ++ show b ++ ")"
    show (L Un)  = "0"
    show (L a)   = "L " ++ show a
    show (R Un)  = "1"
    show (R a)   = "R " ++ show a

sem :: SimplicityExpr a b -> (SimplicityValue a -> SimplicityValue b)
sem  Iden      = id
sem  Unit      = const Un
sem (Comp s t) = sem t . sem s
sem (Injl s)   = L . sem s
sem (Injr s)   = R . sem s
sem (Case s t) = \ case
                   (P (L a) c) -> sem s (P a c)
                   (P (R b) c) -> sem t (P b c)
sem (Pair s t) = \  a             -> P (sem s a) (sem t a)
sem (Take t)   = \ (P a _)        -> sem t a
sem (Drop t)   = \ (P _ b)        -> sem t b

zero :: SimplicityValue Bit
zero = L Un

one :: SimplicityValue Bit
one = R Un

-- show exampleHalfAdder
exampleHalfAdder :: SimplicityValue (Bit ':*: Bit)
exampleHalfAdder = sem halfAdder $  P one zero
