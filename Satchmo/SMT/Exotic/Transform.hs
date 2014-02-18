module Exotic.Transform where

import Prelude hiding ( and, or )

import Language.SMTLIB
import SMT.Util

import qualified Data.Map as M

import Control.Monad.RWS
import Control.Monad ( forM, forM_ )
import Data.Functor ( (<$>) )

import qualified Semiring as S

import Data.Ratio

(sort, logic) = ("Int" , "QF_IDL")


transform :: Script 
          -> ( Script, M.Map Symbol Term -> M.Map Symbol (F.Fuzzy Integer))
transform sc = 
    let ( a, s, w ) = runRWS ( script sc ) () 0
    in  ( Script w, a )

script (Script cs) = do
    forM_ cs command
    let ks = do 
           Get_value vs <- cs 
           v <- vs
           case v of
               Term_qual_identifier ( Qual_identifier (Identifier k)) -> [k]
               Term_qual_identifier_ ( Qual_identifier (Identifier k)) v -> [k]
               _ -> []            
    return $ \ m -> M.fromList $ do
        let pi = integer $ m M.! "plus_infinity"
            mi = integer $ m M.! "minus_infinity"
        k <- ks
        return $ let v = integer $ m M.! k 
                 in  case ( compare mi v, compare v pi ) of    
                        ( EQ, LT ) -> ( k, F.Minus_Infinite )
                        ( LT, LT ) -> ( k, F.Finite v )
                        ( LT, EQ ) -> ( k, F.Plus_Infinite )
                        e -> error $ " Fuzzy.Simplified_IDL.script: missing case " ++ show e



newtype Fuzzy = Fuzzy { contents :: Term }

-- contents = sym2term . contents_

plus_infinite f = apply "=" [ plus_infinity, contents f ]
minus_infinite f = apply "=" [ minus_infinity, contents f ]
finite x = apply ">" [ plus_infinity, contents x ]
plus_infinity = sym2term "plus_infinity"
minus_infinity = sym2term "minus_infinity"

command c = case c of
    Set_option o -> case o of
        Produce_models True -> tell [c]
        Produce_unsat_cores True -> tell [c]

        -- HACK: because sometimes parsing (lexing?) fails
        Option_attribute (Attribute_s_expr ":produce-models" (S_expr_symbol "true")) ->
            tell [ Set_option (Produce_models True) ]
        Option_attribute (Attribute_s_expr ":produce-unsat-cores" (S_expr_symbol "true")) ->
            tell [ Set_option (Produce_unsat_cores True) ]
        _ -> error $ "Fuzzy.Simplified_IDL.command.set_option: " ++ show c
    Set_logic "QF_Fuzzy" -> do
        tell [ Set_logic logic ]
    Set_info _ -> do
        tell [c]
        tell [ Declare_fun "plus_infinity" [] (Sort_identifier (Identifier sort))
             , Declare_fun "minus_infinity" [] (Sort_identifier (Identifier sort)) 
             , Assert $ apply "<" [ minus_infinity, plus_infinity ]
             ]  
    Declare_fun f [] ( Sort_identifier ( Identifier "Fuzzy" )) -> do
        tell [ Declare_fun f [] (Sort_identifier (Identifier sort))
             , Assert $ apply "<=" [ minus_infinity, sym2term f ]
             , Assert $ apply "<=" [ sym2term f, plus_infinity ]
             ]
    Define_fun f [] (Sort_identifier ( Identifier "Fuzzy") ) x -> do
        a <- term x
        tell [ Define_fun f [] 
               (Sort_identifier (Identifier sort) ) ( contents a )
             ]
    Assert f -> do
        v <- formula f
        tell [ Assert v ]
    Check_sat -> tell [ Check_sat ]
    Get_value vs -> tell $ return $ Get_value $ [ plus_infinity, minus_infinity ] ++ do 
              Term_qual_identifier (Qual_identifier (Identifier f)) <- vs 
              return $ sym2term $ f
    Get_unsat_core -> tell [ c ]
    _ -> error $ "Fuzzy.Simplified_IDL.command: " ++ show c

term :: Term -> RWS () [ Command ] Int Fuzzy
term t = case t of
    Term_qual_identifier ( Qual_identifier ( Identifier fun  ))  -> do
        return $ Fuzzy t
    Term_qual_identifier_ ( Qual_identifier ( Identifier fun  )) args -> 
        case fun of
            "+" -> do -- min, really
                xs <- forM args term 
                y <- Fuzzy <$> declare sort 
                tell [ Assert $ and $ for xs $ \ x -> apply "<=" [contents y, contents x] 
                     , Assert $ or $ for xs $ \ x -> apply "=" [ contents y, contents x] 
                     ]
                return $ y     
            "*" -> do  -- max, really
                xs <- forM args term 
                y <- Fuzzy <$> declare sort
                tell [ Assert $ and $ for xs $ \ x -> apply ">=" [contents y, contents x] 
                     , Assert $ or $ for xs $ \ x -> apply "=" [ contents y, contents x] 
                     ]
                return $ y     
            _ -> error $ "Fuzzy.Simplified_IDL.term.1: " ++ show t
    _ -> error $ "Fuzzy.Simplified_IDL.term.2: " ++ show t

formula f = case f of
    Term_attributes g atts -> case atts of
        [ Attribute_s_expr ":named" _ ] -> do
            h <- formula g
            return $ Term_attributes h atts
        _ -> error $ "Fuzzy.Simplified_IDL.formula.3: " ++ show f
    Term_qual_identifier (Qual_identifier (Identifier "true")) -> do
        return f
    Term_qual_identifier (Qual_identifier (Identifier "false")) -> do
        return f
    Term_qual_identifier_ ( Qual_identifier ( Identifier fun  )) args -> 
        case fun of
            "and" -> do xs <- forM args formula ; return $ and xs
            "or" -> do xs <- forM args formula ; return $ or xs
            ">=" -> do 
                [l,r] <- forM args term 
                return $ or 
                       [ plus_infinite l
                       , apply ">" [ contents l, contents r ]
                       , minus_infinite r
                       ]
            ">>" -> do
                [l,r] <- forM args term 
                return $ or 
                       [ plus_infinite l
                       , apply ">" [ contents l, contents r ]
                       ]
            "finite" -> do 
                [x] <- forM args term 
                return $ finite x
            _ -> error $ "Fuzzy.Simplified_IDL.formula.1: " ++ show f
    _ -> error $ "Fuzzy.Simplified_IDL.formula.2: " ++ show f

