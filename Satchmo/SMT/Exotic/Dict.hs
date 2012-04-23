module Satchmo.SMT.Exotic.Dict where

data Dict m d e b = Dict 
    { fresh :: m e
    , finite :: e -> m b
    , gg :: e -> e -> m b
    , ge :: e -> e -> m b
    , plus :: [e] -> m e
    , times :: [e] -> m e
    }

logic dict = "QF_" ++ show ( domain dict )

