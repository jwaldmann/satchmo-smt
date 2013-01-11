module Satchmo.SMT.Dictionary where

import Language.SMTLIB

data Domain = Int | Arctic | Tropical | Fuzzy  
    deriving ( Show, Eq )

data Dictionary m num val bool = Dictionary
    { info :: String
    , domain :: Domain
    , number   :: m num
    , nbits :: Int
    , nconstant :: val -> m num
    , decode :: num -> m val
    , add :: num -> num -> m num
    , times :: num -> num -> m num
    , times_lo :: num -> num -> m num
    , times_hi :: num -> num -> m num
    , positive :: num -> m bool
    , gt :: num -> num -> m bool
    , ge :: num -> num -> m bool
    , neq :: num -> num -> m bool -- ^ numeric equal (not: not equal)
    , boolean :: m bool
    , bconstant :: Bool -> m bool
    , and :: [ bool ] -> m bool
    , or :: [ bool ] -> m bool
    , not :: bool -> bool
    , beq :: bool -> bool -> m bool
    , assert :: [ bool ] -> m ()
    }
