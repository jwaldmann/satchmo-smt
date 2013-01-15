module Satchmo.SMT.Linear where

import qualified Satchmo.SMT.Dictionary as D
import qualified Satchmo.SMT.Matrix as M
-- import qualified Satchmo.Boolean as B
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

data Dictionary m num val bool =
     Dictionary { domain :: D.Domain
                , make :: Int -> (Int,Int) 
                      -> m (Linear num)
                , decode :: 
                    Linear num -> m (Linear val) 
                , substitute ::
                      Linear num -> [Linear num]
                      -> m (Linear num)
                , weakly_monotone :: 
                      Linear num -> m bool
                , strictly_monotone :: 
                      Linear num -> m bool
                , positive :: 
                      Linear num -> m bool
                , weakly_greater :: Linear num 
                      -> Linear num -> m bool 
                , strictly_greater :: Linear num 
                      -> Linear num -> m bool 
                , and :: [ bool ] -> m bool
                , assert :: [ bool ] -> m ()
                , bconstant :: Bool -> m bool
                } 

linear :: Monad m
       => M.Dictionary m num val bool
       -> Dictionary m (M.Matrix num) (M.Matrix val) bool
linear d = Dictionary
    { domain = M.domain d
    , make = \ ar (to, from) -> do
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
    , positive = \ f -> case M.domain d of
        D.Int -> do
            ms <- forM ( lin f ) $ M.positive d
            M.and d ms
        D.Arctic -> do
            a <- M.positive d $ abs f
            ms <- forM ( lin f ) $ M.positive d
            M.or d $ a : ms
{-
    , strictly_monotone = \ f -> do
        ms <- forM ( lin f ) $ M.strictly_monotone d
        M.and d ms
    , weakly_monotone = \ f -> do
        ms <- forM ( lin f ) $ M.weakly_monotone d
        M.and d ms
-}
    , strictly_greater = \ f g -> case M.domain d of
        D.Int -> do
          a <- M.strictly_greater d (abs f) (abs g)
          ls <- forM (zip (lin f) (lin g)) $ \ (a,b) ->
             M.weakly_greater d a b
          M.and d $ a : ls
        D.Arctic -> do
          a <- M.strictly_greater d (abs f) (abs g)
          ls <- forM (zip (lin f) (lin g)) $ \ (a,b) ->
             M.strictly_greater d a b
          M.and d $ a : ls
      , weakly_greater = \ f g -> do
        a <- M.weakly_greater d (abs f) (abs g)
        ls <- forM (zip (lin f) (lin g)) $ \ (a,b) ->
             M.weakly_greater d a b
        M.and d $ a : ls

    , Satchmo.SMT.Linear.and = M.and d
    , Satchmo.SMT.Linear.assert = M.assert d
    , Satchmo.SMT.Linear.bconstant = M.bconstant d

    }
 