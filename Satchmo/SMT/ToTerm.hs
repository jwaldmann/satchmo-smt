module Satchmo.SMT.ToTerm where

import Language.SMTLIB

-- | for printing the answer in (get_value)
class ToTerm a where 
    toTerm :: a -> Term
