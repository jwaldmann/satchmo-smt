module Satchmo.SMT.Dictionary where

import Language.SMTLIB
import qualified Satchmo.Boolean as B

data Domain = Int | Arctic | Tropical | Fuzzy  
    deriving ( Show, Eq )

data Dictionary m num val = Dictionary
    { info :: String
    , domain :: Domain
    , number   :: m num
    , nbits :: Int
    , nconstant :: val -> m num
    , decode :: num -> m val
    , add :: num -> num -> m num
    , times :: num -> num -> m num
    , positive :: num -> m B.Boolean
    , gt :: num -> num -> m B.Boolean
    , ge :: num -> num -> m B.Boolean
    , neq :: num -> num -> m B.Boolean -- ^ numeric equal (not: not equal)
    , boolean :: m B.Boolean
    , bconstant :: Bool -> m B.Boolean
    , and :: [ B.Boolean ] -> m B.Boolean
    , or :: [ B.Boolean ] -> m B.Boolean
    , not :: B.Boolean -> B.Boolean
    , beq :: B.Boolean -> B.Boolean -> m B.Boolean
    , assert :: [ B.Boolean ] -> m ()
    }
