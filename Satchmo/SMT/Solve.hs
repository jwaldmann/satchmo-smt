{-# language PatternSignatures #-}
{-# language FlexibleInstances #-}
{-# language UndecidableInstances #-}
{-# language FlexibleContexts #-}
{-# language MultiParamTypeClasses #-}
{-# language ConstraintKinds #-}
{-# language ExistentialQuantification #-}

module Satchmo.SMT.Solve where

import Prelude hiding ( and, or, not )
import qualified Prelude

import Satchmo.SMT.Config
import Satchmo.SMT.Dictionary hiding ( decode )
import Satchmo.SMT.ToTerm

import Satchmo.SAT.Mini (SAT)

import qualified Satchmo.Boolean as B
import qualified Satchmo.SAT.Mini
import Satchmo.Code

import Language.SMTLIB
import qualified Data.Map as M

-- import qualified Satchmo.SMT.Exotic.Arctic as A
-- import qualified Satchmo.SMT.Exotic.Tropical as T
-- import qualified Satchmo.SMT.Exotic.Fuzzy as F
import Satchmo.SMT.Integer

import Control.Monad ( forM_, forM )
import Control.Monad.Reader
import Control.Monad.Error
import Control.Applicative ( (<$>) )
import Control.Monad.State
import System.IO

import qualified Control.Exception as CE
import Control.Concurrent.MVar
import Control.Concurrent 


data Value n = Value_Number n
         | Value_Bool Bool

data Code n = Code_Number n
          | Code_Bool B.Boolean


instance (Decode m B.Boolean Bool, Decode m n v, Functor m)
         => Decode m (Code n ) (Value v)  where
    decode c = case c of
        Code_Number i -> Value_Number <$> decode i
        Code_Bool b -> Value_Bool <$> decode b


-- execute :: Config -> Script -> IO ( Maybe ( M.Map String Value ))
execute conf s = do
    out <- execute0 conf s
    -- print ( "Solve", out )
    -- case out of { Just m -> C.execute m s ; Nothing -> return () }
    -- print ( "Solve", out )
    return out

-- execute0 :: Config -> Script -> IO ( Maybe ( M.Map String Value ))
execute0 conf s = do
    out <- newEmptyMVar 
    pid <- forkIO $ do
        result <- solve_script conf s 
        putMVar out result
    takeMVar out `CE.catch` \ (e :: CE.AsyncException) -> do
        hPutStrLn stderr "caught Exception in execute0"
        forkIO $ killThread pid
        return Nothing

data D = forall n . Decode SAT n Integer => D (Dictionary SAT n Integer)

solve_script conf s = do
    let b = bits conf ; a = unary_addition conf
        dict = case (encoding conf, extension conf) of
            (Unary, Fixed) -> D $ unary_fixed b a
            (Unary, Flexible) -> D $ unary_flexible b a
            (Binary, Fixed) -> D $ binary_fixed b
            (Binary, Flexible) -> D $ binary_flexible b
    case dict of 
        D d -> do
            hPutStrLn stderr $ info d
            Satchmo.SAT.Mini.solve $ evalStateT (script d s) M.empty

type Solver m n  = StateT (M.Map Symbol ( Code n )) m 

type SolverC m n v = 
    ( Functor m, Monad m
    , Decode m n v, Decode m B.Boolean Bool
    , Num v , ToTerm v )


script :: ( SolverC m n v )
       => Dictionary m n v
       -> Script -> Solver m n (m [( Term, Term)] ) 
script (dict :: Dictionary m n v) (Script cs) =  do
    forM_ cs $ command dict
    m <- get
    return $ do
        m <- decode m
        return $ do (k , v ) <- M.toList m
                    return ( sym2term k , case v of
                         Value_Number (n :: v) -> toTerm n 
                         Value_Bool b -> bool2term b
                         )

sym2term fun = 
    Term_qual_identifier ( Qual_identifier ( Identifier fun  ))  


bool2term b =
    Term_qual_identifier $ Qual_identifier $ Identifier $ case b of
        False -> "false" ; True -> "true"


command :: SolverC m n v
       => Dictionary m n v 
       -> Command -> Solver m n ()
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
              f ( Code_Number a ) m

    Declare_fun f [] ( Sort_bool ) -> do
        m <- get 
        a <- lift $ boolean dict
        put $ M.insertWith ( error "LIA.Satchmo.command: conflict" ) 
              f ( Code_Bool a ) m

    Define_fun f [] (Sort_identifier ( Identifier s) ) x  | s `elem` [ "Int", "Real" ] -> do
        Code_Number a <- term dict x
        m <- get
        put $ M.insertWith ( error "LIA.Satchmo.command: conflict" ) 
              f (Code_Number a) m

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
    
    Exit -> return ()

    _ -> error $ "cannot handle command " ++ show c    

term :: SolverC m n v
       => Dictionary m n v
       -> Term 
       -> Solver m n ( Code n )
term dict f = case f of
    Term_attributes f [ Attribute_s_expr ":named" _ ] -> do
        term dict f
    Term_spec_constant ( Spec_constant_numeral n ) -> do
        c <- lift $ nconstant dict $ fromIntegral n
        return $ Code_Number c
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
    Term_let bindings body -> do
        svs <- forM bindings $ \ (Var_binding s t) -> do
            v <- term dict t
            return ( s, v )
        m <- get
        put $ M.union (M.fromList svs) m
        v <- term dict body
        put m -- restore original environment
        return v

    Term_qual_identifier_ ( Qual_identifier ( Identifier fun  )) args -> 
        case fun of
            "not" -> do [Code_Bool x] <- forM args $ term dict 
                        lift $ return $ Code_Bool $ not dict x
            "and" -> do xs <- forM args $ term dict 
                        fmap Code_Bool $ lift $ and dict $ map unbool xs
            "or" -> do xs <- forM args $ term dict 
                       fmap Code_Bool $ lift $ or dict $ map unbool xs

            ">=" -> do [Code_Number l, Code_Number r] <- forM args $ term dict 
                       fmap Code_Bool $ lift $ ge dict l r
            "<=" -> do [Code_Number l, Code_Number r] <- forM args $ term dict 
                       fmap Code_Bool $ lift $ ge dict r l
            ">" -> do  [Code_Number l, Code_Number r] <- forM args $ term dict 
                       fmap Code_Bool $ lift $ gt dict l r
            "<" -> do  [Code_Number l, Code_Number r] <- forM args $ term dict 
                       fmap Code_Bool $ lift $ gt dict r l

            "=" -> do 
                [l,r] <- forM args $ term dict 
                fmap Code_Bool $ lift $ case (l,r) of 
                    (Code_Number a, Code_Number b) -> neq dict a b
                    (Code_Bool a, Code_Bool b) -> beq dict a b

            "+" -> do xs <- forM args $ term dict 
                      fmap Code_Number $ lift $ plus dict $ map unint xs

            "-" -> do xs <- forM args $ term dict 
                      fmap Code_Number $ lift $ minus dict $ map unint xs

            "*" -> do let [ num , arg ] = args
                      val <- term dict arg
                      fmap Code_Number $ lift 
                           $ mul_by_const dict (integer num) $ unint val

            _ -> error $ "Satchmo.SMT.Solve.term.1: " ++ show f
    _ -> error $ "Satchmo.SMT.Solve.term.2: " ++ show f


unbool (Code_Bool b) = b
unint ( Code_Number i ) = i

integer t = case t of
   Term_spec_constant ( Spec_constant_numeral n ) -> n
   Term_qual_identifier_ (Qual_identifier (Identifier "-")) [ arg ] -> 
       integer arg
   _ -> error $ unwords [ "integer", show t ]


mul_by_const dict f x | f < 0 = error "huh"
mul_by_const dict 0 x = nconstant dict 0
mul_by_const dict 1 x = return x
mul_by_const dict f x = do
    let (d,m) = divMod f 2
    y <- mul_by_const dict d x
    z <- add dict x x    
    case m of
        0 -> return y
        1 -> add dict y x

plus dict (x:xs) = foldM (add dict) x xs

minus dict [ x ] = do
    z <- nconstant dict 0
    sub dict z x
    
minus dict [ x,y ] = do
    sub dict x y
    
sub dict x y = do    
    d <- number dict
    s <- add dict y d
    e <- neq dict x s
    assert dict [e]
    return d
    