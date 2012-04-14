{-# language PatternSignatures #-}
{-# language FlexibleInstances #-}
{-# language UndecidableInstances #-}
{-# language FlexibleContexts #-}
{-# language MultiParamTypeClasses #-}
{-# language ConstraintKinds #-}

module Satchmo.SMT.Solve where

import Prelude hiding ( and, or, not )
import qualified Prelude

import Satchmo.SMT.Config

import qualified Satchmo.Unary.Op.Fixed
import qualified Satchmo.Unary.Op.Flexible
import qualified Satchmo.Unary as Un

import qualified Satchmo.Binary as Bin
import qualified Satchmo.Binary.Op.Fixed  
import qualified Satchmo.Binary.Op.Flexible

import qualified Satchmo.Boolean as B
import qualified Satchmo.SAT.Mini
import Satchmo.Code

import Language.SMTLIB
import qualified Data.Map as M

import Control.Monad ( forM_, forM )
import Control.Monad.Reader
import Control.Monad.Error
import Control.Applicative ( (<$>) )
import Control.Monad.State
import System.IO

import qualified Control.Exception as CE
import Control.Concurrent.MVar
import Control.Concurrent 


data Value = Value_Integer Integer
         | Value_Bool Bool

data Code n b = Code_Integer n
          | Code_Bool b

instance SolverC m n b
         => Decode m (Code n b) Value where
    decode c = case c of
        Code_Integer i -> Value_Integer <$> decode i
        Code_Bool b -> Value_Bool <$> decode b

data Dictionary m num bool = Dictionary
    { number   :: m num
    , nconstant :: Integer -> m num
    , add :: num -> num -> m num
    , gt :: num -> num -> m bool
    , ge :: num -> num -> m bool
    , neq :: num -> num -> m bool
    , boolean :: m bool
    , bconstant :: Bool -> m bool
    , and :: [ bool ] -> m bool
    , or :: [ bool ] -> m bool
    , not :: bool -> bool
    , beq :: bool -> bool -> m bool
    , assert :: [ bool ] -> m ()
    }

unary_fixed :: Int -> Dictionary Satchmo.SAT.Mini.SAT Un.Number B.Boolean
unary_fixed bits = Dictionary
    { number = Un.number bits
    , nconstant = Un.constant
    , boolean = B.boolean
    , bconstant = B.constant
    , add = Satchmo.Unary.Op.Fixed.add
    , gt = Un.gt
    , ge = Un.ge
    , neq = Un.eq
    , and = B.and, or = B.or, not = B.not, beq = B.equals2, assert = B.assert
    }

binary_fixed :: Int -> Dictionary Satchmo.SAT.Mini.SAT Bin.Number B.Boolean
binary_fixed bits = Dictionary
    { number = Bin.number bits
    , nconstant = Bin.constant
    , boolean = B.boolean
    , bconstant = B.constant
    , add = Satchmo.Binary.Op.Fixed.add
    , gt = Bin.gt
    , ge = Bin.ge
    , neq = Bin.eq
    , and = B.and, or = B.or, not = B.not, beq = B.equals2, assert = B.assert
    }

    
execute :: Config -> Script -> IO ( Maybe ( M.Map String Value ))
execute conf s = do
    out <- execute0 conf s
    -- print ( "Solve", out )
    -- case out of { Just m -> C.execute m s ; Nothing -> return () }
    -- print ( "Solve", out )
    return out

execute0 :: Config -> Script -> IO ( Maybe ( M.Map String Value ))
execute0 conf s = do
    out <- newEmptyMVar 
    pid <- forkIO $ do
        result <- solve_script conf s 
        putMVar out result
    takeMVar out `CE.catch` \ (e :: CE.AsyncException) -> do
        hPutStrLn stderr "caught Exception in execute0"
        forkIO $ killThread pid
        return Nothing



solve_script conf s = Satchmo.SAT.Mini.solve $ 
    case encoding conf of
        Unary { bits = b } -> 
            evalStateT (script (unary_fixed b) s) 
                       ( M.empty :: M.Map Symbol ( Code Un.Number B.Boolean ))
        Binary { bits = b } -> 
            evalStateT (script (binary_fixed b) s) 
                       ( M.empty :: M.Map Symbol ( Code Bin.Number B.Boolean ))



type Solver m n b = StateT (M.Map Symbol ( Code n b )) m 

type SolverC m n b = 
    ( Functor m, Monad m, Decode m n Integer, Decode m b Bool )

script :: SolverC m n b
       => Dictionary m n b -> Script -> Solver m n b (m (M.Map Symbol Value)) 
script dict (Script cs) =  do
    forM_ cs $ command dict
    m <- get
    return $ decode m

command :: SolverC m n b
       => Dictionary m n b -> Command -> Solver m n b ()
command dict c = case c of
    Set_option ( Produce_models True ) -> return ()

    -- HACK
    Set_option ( Option_attribute (Attribute_s_expr ":produce-models" (S_expr_symbol "true" ))) -> return ()

    Set_logic "QF_LIA" -> return ()
    Set_logic "QF_LRA" -> return ()
    Set_logic "QF_IDL" -> return ()

    Set_info _ -> return ()

    Declare_fun f [] ( Sort_identifier ( Identifier s )) | s `elem` [ "Int", "Real" ] -> do
        m <- get 
        a <- lift $ number dict
        put $ M.insertWith ( error "LIA.Satchmo.command: conflict" ) 
              f ( Code_Integer a ) m

    Declare_fun f [] ( Sort_bool ) -> do
        m <- get 
        a <- lift $ boolean dict
        put $ M.insertWith ( error "LIA.Satchmo.command: conflict" ) 
              f ( Code_Bool a ) m

    Define_fun f [] (Sort_identifier ( Identifier s) ) x  | s `elem` [ "Int", "Real" ] -> do
        Code_Integer a <- term dict x
        m <- get
        put $ M.insertWith ( error "LIA.Satchmo.command: conflict" ) 
              f (Code_Integer a) m

    Define_fun f [] ( Sort_bool ) x -> do
        Code_Bool a <- term dict x
        m <- get
        put $ M.insertWith ( error "LIA.Satchmo.command: conflict" ) 
              f (Code_Bool a) m

    Assert f -> do
        Code_Bool v <- term dict f
        lift $ assert dict [ v ]

    Check_sat -> return ()
    Get_value _ -> return ()
    _ -> error $ "cannot handle command " ++ show c    

term :: SolverC m n b
       => Dictionary m n b -> Term -> Solver m n b ( Code n b )
term dict f = case f of
    Term_spec_constant ( Spec_constant_numeral n ) -> do
        c <- lift $ nconstant dict n
        return $ Code_Integer c
    Term_qual_identifier ( Qual_identifier ( Identifier "true"  ))  -> do
        b <- lift $ bconstant dict True
        return $ Code_Bool b
    Term_qual_identifier ( Qual_identifier ( Identifier "false"  ))  -> do
        b <- lift $ bconstant dict False
        return $ Code_Bool b
    Term_qual_identifier ( Qual_identifier ( Identifier fun  ))  -> do
        m <- get 
        return $ case M.lookup fun m of
            Just v -> v
            Nothing -> error $ "Satchmo.SMT.Solve: " ++ show fun
    Term_qual_identifier_ ( Qual_identifier ( Identifier fun  )) args -> 
        case fun of
            "not" -> do [Code_Bool x] <- forM args $ term dict 
                        lift $ return $ Code_Bool $ not dict x
            "and" -> do xs <- forM args $ term dict 
                        fmap Code_Bool $ lift $ and dict $ map unbool xs
            "or" -> do xs <- forM args $ term dict 
                       fmap Code_Bool $ lift $ or dict $ map unbool xs

            ">=" -> do [Code_Integer l, Code_Integer r] <- forM args $ term dict 
                       fmap Code_Bool $ lift $ ge dict l r
            "<=" -> do [Code_Integer l, Code_Integer r] <- forM args $ term dict 
                       fmap Code_Bool $ lift $ ge dict r l
            ">" -> do  [Code_Integer l, Code_Integer r] <- forM args $ term dict 
                       fmap Code_Bool $ lift $ gt dict l r
            "<" -> do  [Code_Integer l, Code_Integer r] <- forM args $ term dict 
                       fmap Code_Bool $ lift $ gt dict r l

            "=" -> do 
                [l,r] <- forM args $ term dict 
                fmap Code_Bool $ lift $ case (l,r) of 
                    (Code_Integer a, Code_Integer b) -> neq dict a b
                    (Code_Bool a, Code_Bool b) -> beq dict a b

            "+" -> do xs <- forM args $ term dict 
                      fmap Code_Integer $ lift $ plus dict $ map unint xs

            _ -> error $ "Satchmo.SMT.Solve.term.1: " ++ show f
    _ -> error $ "Satchmo.SMT.Solve.term.2: " ++ show f


unbool (Code_Bool b) = b
unint ( Code_Integer i ) = i

plus dict (x:xs) = foldM (add dict) x xs

