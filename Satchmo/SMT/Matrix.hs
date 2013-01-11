module Satchmo.SMT.Matrix where

import qualified Satchmo.SMT.Dictionary as D
-- import qualified Satchmo.Boolean as B
import qualified Satchmo.SMT.Exotic.Semiring.Class as S

import Control.Monad ( forM )
import Data.List ( transpose )

data Matrix a 
     = Zero { dim :: (Int,Int) }
     | Unit { dim :: (Int,Int) }
     | Matrix { dim :: (Int,Int) 
              , contents :: [[a]] }
    deriving Show



to = fst . dim ; from = snd . dim

data Dictionary m num val bool =
     Dictionary { make :: (Int,Int) -> m (Matrix num)
                , decode :: 
                      Matrix num -> m (Matrix val)
                , weakly_monotone :: 
                      Matrix num -> m bool
                , strictly_monotone :: 
                      Matrix num -> m bool
                , positive :: 
                      Matrix num -> m bool
                , add :: Matrix num -> Matrix num
                       -> m (Matrix num)
                , times :: Matrix num -> Matrix num
                       -> m (Matrix num)
                , strictly_greater :: 
                          Matrix num -> Matrix num
                       -> m bool
                , weakly_greater :: 
                          Matrix num -> Matrix num
                       -> m bool
                , and :: [ bool ] -> m bool
                }

expand d a = case a of
    Zero {} -> do
        cs <- forM [1 .. to a] $ \ h ->
              forM [1 .. from  a] $ \ w -> 
              D.nconstant d S.zero
        return $ Matrix {dim=dim a, contents = cs}
    Unit {} -> do
        cs <- forM [1 .. to a] $ \ h ->
              forM [1 .. from  a] $ \ w -> 
              D.nconstant d
                  $ if h==w then S.one else S.zero
        return $ Matrix {dim=dim a, contents = cs}
    Matrix {} -> return a
       
matrix :: (Monad m, S.Semiring val)
       => D.Dictionary m num val bool
       -> Dictionary m num val bool
matrix  d = Dictionary
    { make = \ (to, from) -> do
         cs <- forM [1..to] $ \ r ->
               forM [1..from] $ \ c ->
                    D.number d
         return $ Matrix { dim = (to,from)
                         , contents = cs} 
    , decode = \ m -> case m of 
         Zero {} -> return $ Zero (dim m) 
         Unit {} -> return $ Unit (dim m) 
         Matrix {} -> do
             css <- forM (contents m) $ \ row ->
                    forM row $ D.decode d
             return $ Matrix { dim = dim m
                             , contents = css }
    , positive = \ m -> case m of
        Zero {} -> D.bconstant d False
        Unit {} -> D.bconstant d True
        Matrix {} -> D.positive d
           $ head $ head $ contents m
    , add = \ a b -> case (a,b) of
        _ | dim a /= dim b -> 
              error $ "Matrix.add " ++ show (dim a,dim b)
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
        _ | from a /= to b -> 
              error $ "Matrix.times " ++ show (dim a,dim b)
        (Zero{}, _) -> 
                 return $ a { dim = (to a, from b) }
        (_, Zero{}) -> 
                 return $ b { dim = (to a, from b) }
        (Unit{}, _) -> 
                 return $ b { dim = (to a, from b) }
        (_, Unit{}) -> 
                 return $ a { dim = (to a, from b) }
        (Matrix{},Matrix{}) -> do
            let 
                dot xs ys = do
                    xys <- forM (zip xs ys) $ \(x,y) ->
                        D.times d x y
                    bfoldM (D.add d) xys
            css <- forM (contents a) $ \ row ->
               forM (transpose $ contents b) $ \ col ->
               dot row col
            return $ Matrix { dim = (to a,from b)
                            , contents = css }
    , strictly_greater = \ a b -> case (a,b) of
         _ | D.domain d /= D.Int -> 
             error "Matrix.strictly_greater"
         (Zero{}, _) -> D.bconstant d False
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
         (_, Zero{}) -> D.bconstant d True
         (Zero{}, Unit{}) -> D.bconstant d False
         (Unit{}, Unit{}) -> D.bconstant d True
         _ -> do
             ea <- expand d a ; eb <- expand d b
             cs <- forM ( zip (concat $ contents ea) 
                              (concat $ contents eb))
                 $ \ (x,y) -> D.ge d x y
             D.and d cs     
                }

bfoldM f [x] = return x
bfoldM f (x:y:zs) = 
    do xy <- f x y ; bfoldM f (zs ++ [xy])
