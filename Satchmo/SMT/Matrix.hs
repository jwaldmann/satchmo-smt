module Satchmo.SMT.Matrix where

import qualified Satchmo.SMT.Dictionary as D
import qualified Satchmo.Boolean as B
import Satchmo.SMT.Exotic.Semiring.Class

import Control.Monad ( forM )

data Matrix a 
     = Zero { dim :: (Int,Int) }
     | Unit { dim :: (Int,Int) }
     | Matrix { dim :: (Int,Int) 
              , contents :: [[a]] }
    deriving Show

height = fst . dim ; width = snd . dim

data Dictionary m num val =
     Dictionary { make :: m (Matrix num)
                , weakly_monotone :: 
                      Matrix num -> m B.Boolean
                , strictly_monotone :: 
                      Matrix num -> m B.Boolean
                , positive :: 
                      Matrix num -> m B.Boolean
                , add :: Matrix num -> Matrix num
                       -> m (Matrix num)
                , times :: Matrix num -> Matrix num
                       -> m (Matrix num)
                , strictly_greater :: 
                          Matrix num -> Matrix num
                       -> m B.Boolean
                , weakly_greater :: 
                          Matrix num -> Matrix num
                       -> m B.Boolean
                }
       
matrix :: (Monad m, Semiring val)
       => (Int,Int)
       -> D.Dictionary m num val
       -> Dictionary m num val
matrix (w, h) d = Dictionary
    { make = do
         cs <- forM [1..h] $ \ r ->
               forM [1..w] $ \ c ->
                    D.number d
         return $ Matrix { dim = (w,h), contents = cs} 
    , positive = \ m -> case m of
        Zero {} -> D.bconstant d False
        Unit {} -> D.bconstant d True
        Matrix {} -> D.positive d
           $ head $ head $ contents m
    , add = \ a b -> case (a,b) of
        _ | dim a /= dim b -> error "Matrix.plus"
        ( Zero {} , _ ) -> return b
        ( _ , Zero {} ) -> return a       
        ( Matrix {}, Matrix {} ) -> do
            css <- forM ( zip (contents a)(contents b))
               $ \ (xs,ys) -> forM (zip xs ys) 
               $ \ (x,y) -> D.add d x y
            return $ Matrix { dim = dim a
                            , contents = css }
{-
                , times :: Matrix num -> Matrix num
                       -> m (Matrix num)
                , strictly_greater :: 
                          Matrix num -> Matrix num
                       -> m B.Boolean
                , weakly_greater :: 
                          Matrix num -> Matrix num
                       -> m B.Boolean
-}
                }
