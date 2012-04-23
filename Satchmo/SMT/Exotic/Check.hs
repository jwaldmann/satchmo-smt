{-# language FlexibleInstances #-}
{-# language UndecidableInstances #-}
{-# language FlexibleContexts #-}
{-# language MultiParamTypeClasses #-}

module Exotic.Check where

import Exotic.Dict

import Language.SMTLIB
import qualified Data.Map as M

import qualified Semiring.Fuzzy as F
import qualified Semiring  as S

import Control.Monad ( forM_, forM )
import Control.Monad.State.Strict

import System.IO

execute :: (Eq a, Show a, S.Semiring a) 
        => M.Map String a -> Script -> IO ( )
execute m (Script cs) = 
    evalStateT ( forM_ cs command ) m

command  c = case c of
    Set_option ( Produce_models True ) -> return ()
    Set_logic l -> return () -- UNCHECKED
    Set_info _ -> return ()
    Declare_fun f [] ( Sort_identifier ( Identifier s )) -> return ()
    Define_fun f [] (Sort_identifier ( Identifier s) ) x -> do
        a <- term x
        m <- get ; let a' = m M.! f
        when ( a /= a' ) $ error $ unlines      
             [ "Exotic.Check.command: conflict"
             , "command: " ++ show c
             , "computed: " ++ show a
             , "stored: " ++ show a'
             ]
    Assert f -> do
        v <- formula f
        when ( v /= True ) $ error $ unlines      
             [ "Exotic.Check.assert: conflict"
             , "formula: " ++ show c
             , "computed: " ++ show v
             ]
    Check_sat -> return ()
    Get_value _ -> return ()
    _ -> error $ "cannot handle command " ++ show c    

formula  :: (S.Semiring a, MonadState (M.Map Symbol a) m) => Term -> m Bool
formula f = case f of
    Term_attributes f [ Attribute_s_expr ":named" _ ] -> formula f
    Term_qual_identifier (Qual_identifier (Identifier "true")) -> do
        return $ True
    Term_qual_identifier (Qual_identifier (Identifier "false")) -> do
        return $ False
    Term_qual_identifier_ ( Qual_identifier ( Identifier fun  )) args -> 
        case fun of
            "and" -> do xs <- forM args formula ; return $ and xs
            "or" -> do xs <- forM args formula ; return $ or xs
            ">=" -> do [l,r] <- forM args term ; return $ S.ge l r
            ">>" -> do [l,r] <- forM args term ; return $ S.gt l r
            "finite" -> do 
                [x] <- forM args term 
                return $ S.strictly_positive x
            _ -> error $ "Exotic.Check.formula.1: " ++ show f
    _ -> error $ "Exotic.Check.formula.2: " ++ show f


term  :: (S.Semiring a, MonadState (M.Map Symbol a) m) => Term -> m a
term t = case t of
    Term_qual_identifier ( Qual_identifier ( Identifier fun  ))  -> do
        m <- get 
        case M.lookup fun m of
             Just x -> return x
             _ -> error $ "Exotic.Check.term: not bound: " ++ show t
    Term_qual_identifier_ ( Qual_identifier ( Identifier fun  )) args -> 
        case fun of
            "+" -> do xs <- forM args term ; return $ foldr (S.plus) S.zero  xs
            "*" -> do xs <- forM args term ; return $ foldr (S.times) S.one xs
            _ -> error $ "Exotic.Check.term.1: " ++ show t
    _ -> error $ "Exotic.Check.term.2: " ++ show t

