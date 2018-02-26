{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs, DataKinds, KindSignatures , LambdaCase #-}

import Prelude hiding (not)

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

-- SimplicityExpr has an input type and an output type
data SimplicityExpr :: SimplicityType -> SimplicityType -> * where
    Iden :: SimplicityExpr a a
    Unit :: SimplicityExpr a U
    Comp :: SimplicityExpr a b -> SimplicityExpr b c -> SimplicityExpr a c
    Injl :: SimplicityExpr a b -> SimplicityExpr a (b :+: c)
    Injr :: SimplicityExpr a c -> SimplicityExpr a (b :+: c)
    Case :: SimplicityExpr (a :*: c) d -> SimplicityExpr (b :*: c) d -> SimplicityExpr ((a :+: b) :*: c) d
    Pair :: SimplicityExpr a b -> SimplicityExpr a c -> SimplicityExpr a (b :*: c)
    Take :: SimplicityExpr a c -> SimplicityExpr (a :*: b) c
    Drop :: SimplicityExpr b c -> SimplicityExpr (a :*: b) c

type Bit = U :+: U

not :: SimplicityExpr Bit Bit
not = Comp (Pair Iden Unit) (Case (Injr Unit) (Injl Unit))

halfAdder :: SimplicityExpr (Bit :*: Bit) (Bit :*: Bit)
halfAdder = Case (Drop (Pair (Injl Unit) Iden)) (Drop (Pair Iden not))

data SimplicityValue :: SimplicityType -> * where
    Un  :: SimplicityValue U
    P   :: SimplicityValue a -> SimplicityValue b -> SimplicityValue (a :*: b)
    L   :: SimplicityValue a -> SimplicityValue (a :+: b)
    R   :: SimplicityValue b -> SimplicityValue (a :+: b)

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

main :: IO ()
main = return ()
