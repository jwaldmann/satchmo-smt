{-# language FlexibleInstances #-}
{-# language UndecidableInstances #-}
{-# language FlexibleContexts #-}
{-# language MultiParamTypeClasses #-}
{-# language PatternSignatures #-}

module Exotic.Solve where

import qualified Exotic.Check as C
import Exotic.Dict

import qualified Satchmo.Unary.Op.Flexible as X
import qualified Satchmo.Unary as N

-- import qualified Satchmo.Binary as N
-- import qualified Satchmo.Binary.Op.Fixed as X

import qualified Satchmo.Boolean as B
import qualified Satchmo.SAT.Mini
import Satchmo.SAT.Mini (SAT)
import Satchmo.Code

import Language.SMTLIB
import qualified Data.Map as M
import qualified Semiring as S


import Control.Monad ( forM_, forM )
import Control.Monad.State
import System.IO
import Control.Exception
import Control.Concurrent.MVar
import Control.Concurrent 


-- execute :: Int -> Script -> IO ( Maybe ( M.Map String ( F.Fuzzy Integer )))
execute dict s = do
    out <- execute0 dict s
    -- print ( "Solve", out )
    case out of { Just m -> C.execute m s ; Nothing -> return () }
    -- print ( "Solve", out )
    return out

-- execute0 :: Int -> Script -> IO ( Maybe ( M.Map String ( F.Fuzzy Integer ) ))
execute0 dict (Script cs) = do
    out <- newEmptyMVar 
    pid <- forkIO $ do
        result <- Satchmo.SAT.Mini.solve $ flip evalStateT M.empty $ do
            forM_ cs $ command dict
            m <- get
            return $ decode m
        putMVar out result
    takeMVar out `Control.Exception.catch` \ (e::AsyncException) -> do
        hPutStrLn stderr "caught Exception in execute0"
        forkIO $ killThread pid
        return Nothing

-- command :: Dict d e -> Command -> SAT ()
command dict c = case c of
    Set_option ( Produce_models _ ) -> return ()
    Set_option ( Produce_unsat_cores _ ) -> return ()
    Set_logic l | l == logic dict -> return ()
    Set_info _ -> return ()
    Declare_fun f [] ( Sort_identifier ( Identifier s )) | s == show ( domain dict ) -> do
        m <- get 
        a <- lift $ fresh dict 
        put $ M.insertWith ( error "Exotic.Solve.command: conflict" ) f a m
    Define_fun f [] (Sort_identifier ( Identifier s) ) x | s == show ( domain dict ) -> do
        a <- term dict x
        m <- get
        put $ M.insertWith ( error "Exotic.Solve.command: conflict" ) f a m
    Assert f -> do
        v <- formula dict f
        lift $ B.assert [ v ]
    Check_sat -> return ()
    Get_unsat_core -> return ()
    Get_value _ -> return ()
    _ -> error $ "cannot handle command " ++ show c    

-- formula :: Dict d e -> Term -> SAT B.Boolean
formula dict f = case f of
    Term_attributes f [ Attribute_s_expr ":named" _ ] -> do
        formula dict f
    Term_qual_identifier (Qual_identifier (Identifier "true")) -> do
        lift $ B.constant True
    Term_qual_identifier (Qual_identifier (Identifier "false")) -> do
        lift $ B.constant False
    Term_qual_identifier_ ( Qual_identifier ( Identifier fun  )) args -> 
        case fun of
            "and" -> do xs <- forM args $ formula dict ; lift $ B.and xs
            "or" -> do xs <- forM args $ formula dict ; lift $ B.or xs
            ">=" -> do [l,r] <- forM args $ term dict ; lift $ ge dict l r
            ">>" -> do [l,r] <- forM args $ term dict ; lift $ gg dict l r
            "finite" -> do 
                [x] <- forM args $ term dict 
                lift $ finite dict x
            _ -> error $ "Fuzzy.Solve.formula.1: " ++ show f
    _ -> error $ "Fuzzy.Solve.formula.2: " ++ show f

-- term :: Dict d e -> Term -> SAT e
term dict t = case t of
    Term_qual_identifier ( Qual_identifier ( Identifier fun  ))  -> do
        m <- get 
        case M.lookup fun m of
             Just x -> return x
             _ -> error $ "Fuzzy.Solve.term: not bound: " ++ show t
    Term_qual_identifier_ ( Qual_identifier ( Identifier fun  )) args -> 
        case fun of
            "+" -> do xs <- forM args $ term dict ; lift $ plus dict xs
            "*" -> do xs <- forM args $ term dict ; lift $ times dict xs
            _ -> error $ "Fuzzy.Solve.term.1: " ++ show t
    _ -> error $ "Fuzzy.Solve.term.2: " ++ show t

