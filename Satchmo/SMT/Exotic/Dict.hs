module Satchmo.SMT.Exotic.Dict where

import Satchmo.SMT.Dictionary ( Domain )

data Dict m d e b = Dict 
    { domain :: Domain
    , fresh :: m e
    , finite :: e -> m b
    , gg :: e -> e -> m b
    , ge :: e -> e -> m b
    , plus :: [e] -> m e
    , times :: [e] -> m e
    }

logic dict = "QF_" ++ show ( domain dict )

