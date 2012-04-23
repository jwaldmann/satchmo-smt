module Satchmo.SMT.Exotic.Util where

import Language.SMTLIB

import Control.Monad.RWS hiding ( mplus )
import Control.Monad.Trans

import Data.Char ( toLower )

type Sym a = RWS () [ Command ] Int a

assert :: Term -> Sym ()
assert f = case f of
    Term_qual_identifier_ (Qual_identifier (Identifier "and")) args -> 
       void $ forM args assert
    _ -> do
        c <- get ; put $ succ c
        let a = Attribute_s_expr ":named" $ S_expr_symbol $ "assert" ++ show c
        tell [ Assert $ Term_attributes f [ a ] ]

fresh :: String -> Sym Symbol
fresh s = do
    c <- get
    put $ succ c
    return $ s ++ show c

declare :: String -> Sym Term
declare sort = do
    f <- fresh $ take 1 $ map toLower sort
    tell [ Declare_fun f [] ( Sort_identifier ( Identifier sort )) ]
    return $ Term_qual_identifier $ Qual_identifier $ Identifier f

define :: String -> Term -> Sym Term
define sort x = do
    f <- fresh $ take 1 $ map toLower sort
    tell [ Define_fun f [] ( Sort_identifier ( Identifier sort )) x ]
    return $ Term_qual_identifier $ Qual_identifier $ Identifier f

apply :: Symbol -> [Term ] -> Term
apply fun args = 
    Term_qual_identifier_ ( Qual_identifier ( Identifier fun  )) args 

and xs = case length xs of
    0 -> sym2term "true" 
    1 -> head xs
    _ -> apply "and" xs

or xs = case length xs of
    0 -> sym2term "false" 
    1 -> head xs
    _ -> apply "or" xs

for = flip map

sym2term fun = 
    Term_qual_identifier ( Qual_identifier ( Identifier fun  ))  

integer e = case e of
    Term_spec_constant (Spec_constant_numeral i) -> 
        fromIntegral i 
    Term_qual_identifier_ (Qual_identifier (Identifier "-")) [ arg ] -> 
        negate $ integer arg
    e -> error $ " Fuzzy.Simplified_IDL.script: missing case " ++ show e

