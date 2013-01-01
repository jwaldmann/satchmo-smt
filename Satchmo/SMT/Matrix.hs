module Satchmo.SMT.Matrix where

import qualified Satchmo.SMT.Dictionary as D
import qualified Satchmo.Boolean as B
import qualified Satchmo.SMT.Exotic.Semiring.Class as S

import Control.Monad ( forM )
import Data.List ( transpose )

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

expand d a = case a of
    Zero {} -> do
        cs <- forM [1 .. height a] $ \ h ->
              forM [1 .. width  a] $ \ w -> 
              D.nconstant d S.zero
        return $ Matrix {dim=dim a, contents = cs}
    Unit {} -> do
        cs <- forM [1 .. height a] $ \ h ->
              forM [1 .. width  a] $ \ w -> 
              D.nconstant d
                  $ if h==w then S.one else S.zero
        return $ Matrix {dim=dim a, contents = cs}
    Matrix {} -> return a
       
matrix :: (Monad m, S.Semiring val)
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
        _ | dim a /= dim b -> error "Matrix.add"
        ( Zero {} , _ ) -> return b
        ( _ , Zero {} ) -> return a       
        _ -> do
            a <- expand d a ; b <- expand d b
            css <- forM ( zip (contents a)(contents b))
               $ \ (xs,ys) -> forM (zip xs ys) 
               $ \ (x,y) -> D.add d x y
            return $ Matrix { dim = dim a
                            , contents = css }
    , times = \ a b -> case (a,b) of
        _ | width a /= height b -> error "Matrix.times"
        (Zero{}, _) -> return a
        (_, Zero{}) -> return b
        (Unit{}, _) -> return b
        (_, Unit{}) -> return a
        (Matrix{},Matrix{}) -> do
            let bfoldM f [x] = return x
                bfoldM f (x:y:zs) = do
                    xy <- f x y ; bfoldM f (zs ++ [xy])
                dot xs ys = do
                    xys <- forM (zip xs ys) $ \(x,y) ->
                        D.times d x y
                    bfoldM (D.add d) xys
            css <- forM (contents a) $ \ row ->
               forM (transpose $ contents b) $ \ col ->
               dot row col
            return $ Matrix { dim = (height a,width b)
                            , contents = css }
    , strictly_greater = \ a b -> case (a,b) of
         _ | D.domain d /= D.Int -> 
             error "Matrix.strictly_greater"
         (Zero{}, Zero{}) -> D.bconstant d False
         (Zero{}, Unit{}) -> D.bconstant d False
         (Unit{}, Zero{}) -> D.bconstant d True
         (Unit{}, Unit{}) -> D.bconstant d False
         _ -> do
             ea <- expand d a ; eb <- expand d b
             let (x,y) : rest =  
                    zip (concat $ contents ea) 
                        (concat $ contents eb)
             c <- D.gt d x y
             cs <- forM rest $ \ (x,y) -> D.ge d x y
             D.and d $ c : cs     
    , weakly_greater = \ a b -> case (a,b) of
         _ | D.domain d /= D.Int -> 
             error "Matrix.weakly_greater"
         (Zero{}, Zero{}) -> D.bconstant d True
         (Zero{}, Unit{}) -> D.bconstant d False
         (Unit{}, Zero{}) -> D.bconstant d True
         (Unit{}, Unit{}) -> D.bconstant d True
         _ -> do
             ea <- expand d a ; eb <- expand d b
             cs <- forM ( zip (concat $ contents ea) 
                              (concat $ contents eb))
                 $ \ (x,y) -> D.ge d x y
             D.and d cs     
                }
