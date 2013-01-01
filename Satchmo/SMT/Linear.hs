module Satchmo.SMT.Linear where

import qualified Satchmo.SMT.Matrix as M
import qualified Satchmo.Boolean as B
import qualified Satchmo.SMT.Exotic.Semiring.Class as S

import Control.Monad ( forM )
import Data.List ( transpose )

import Prelude hiding ( abs )

data Linear a = 
     Linear { dim :: (Int,Int)
            , abs :: a , lin :: [a] 
            }
   deriving Show

to = fst . dim ; from = snd . dim

data Dictionary m num val =
     Dictionary { make :: Int -> (Int,Int) 
                      -> m (Linear num)
                , decode :: 
                    Linear num -> m (Linear val) 
                , substitute ::
                      Linear num -> [Linear num]
                      -> m (Linear num)
                , weakly_monotone :: 
                      Linear num -> m B.Boolean
                , strictly_monotone :: 
                      Linear num -> m B.Boolean
                , positive :: 
                      Linear num -> m B.Boolean
                , weakly_greater :: Linear num 
                      -> Linear num -> m B.Boolean 
                , strictly_greater :: Linear num 
                      -> Linear num -> m B.Boolean 
                } 

linear :: (B.MonadSAT m)
       => M.Dictionary m num val 
       -> Dictionary m (M.Matrix num) (M.Matrix val)
linear d = Dictionary
    { make = \ ar (to, from) -> do
        ms <- forM [ 1 .. ar ] $ \ i -> 
            M.make d (to,from)
        a <- M.make d (to, 1)
        return $ Linear { dim=(to,from)
                        , abs = a, lin = ms }
    , decode = \ f -> do
        a <- M.decode d $ abs f
        ls <- forM (lin f) $ M.decode d 
        return $ Linear { dim = dim f
                        , abs = a, lin = ls }
    , substitute = \ f gs -> do
        as <- forM (  zip (lin f) (map abs gs)) 
           $ \ (l,a) -> M.times d l a
        a <- M.bfoldM (M.add d) $ abs f : as
        ls <- forM (transpose $ map lin gs) 
            $ \ ms -> do
                out <- forM ( zip (lin f) ms ) 
                   $ \ (l,m) -> M.times d l m
                M.bfoldM (M.add d) out
        return $ Linear 
               { dim = (to f, -1)
               , abs = a, lin = ls
               }   
    , positive = \ f -> do
        ms <- forM ( lin f ) $ M.positive d
        B.and ms
    , strictly_monotone = \ f -> do
        ms <- forM ( lin f ) $ M.strictly_monotone d
        B.and ms
    , weakly_monotone = \ f -> do
        ms <- forM ( lin f ) $ M.weakly_monotone d
        B.and ms
    , strictly_greater = \ f g -> do
        a <- M.strictly_greater d (abs f) (abs g)
        ls <- forM (zip (lin f) (lin g)) $ \ (a,b) ->
             M.weakly_greater d a b
        B.and $ a : ls
    , weakly_greater = \ f g -> do
        a <- M.weakly_greater d (abs f) (abs g)
        ls <- forM (zip (lin f) (lin g)) $ \ (a,b) ->
             M.weakly_greater d a b
        B.and $ a : ls
    }
 