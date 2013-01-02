module Satchmo.SMT.Opt.Integer where

import qualified Satchmo.Binary as Bin
import qualified Satchmo.Boolean as B

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad ( forM, guard )
import Data.List ( inits, tails, nub )

op2 cnf bits x y = do
    z <- Bin.number bits
    forM (S.toList cnf) $ \ clause -> 
        B.assert $ do
            ((k,b), v) <- M.toList clause
            let var = case k of
                    0 -> x ; 1 -> y ; 2 -> z
                trans = if v then id else B.not    
            return $ trans $ Bin.bits var !! b
    return z

type CNF v = S.Set (M.Map v Bool)

-- | the (canonical) cnf for the formula  
-- f(x,y) = z && x,y,z are representable (with bits)
fun2 :: (Int -> Int -> Int)
     -> Int -- ^ bits
     -> CNF (Int,Int)
fun2 f bits = S.fromList $ do
    x <- sequence $ replicate bits [False,True]
    y <- sequence $ replicate bits [False,True]
    z <- sequence $ replicate bits [False,True]
    guard $ f (frombits x) (frombits y) /= frombits z
    return $ M.fromList $ do 
        i <- [ 0..bits-1]
        [   ((0,i), not $ x!!i)
          , ((1,i), not $ y!!i)
          , ((2,i), not $ z!!i)
          ]

frombits = foldl ( \ x b -> 2*x + fromEnum b ) 0

weight s = length $ filter id $ M.elems s

combine (w1,s1) (w2, s2) = do
    guard $ 1 == abs (w1 - w2)
    guard $ M.keysSet s1 == M.keysSet s2
    let m = M.intersectionWith (,) s1 s2
        same = M.filter (uncurry (==)) m
    guard $ M.size same + 1 == M.size m
    let out = M.map fst same
    return (weight out, out)

-- | search for combination, and remove!
combines s = do
    ( pre, this : post ) <- splits s
    ( pre', that : post' ) <- splits post
    c <- combine this that
    let rest 
          = filter ( not . M.isSubmapOf (snd c) . snd )
          $ pre ++ pre' ++ post'
    return $ rest ++ [c]

splits xs = zip ( inits xs ) ( tails xs )
          
primes s =
    let handle s = case combines s of
            [] -> s
            s' : _ -> handle s'
    in    S.fromList 
        $ map snd
        $ handle 
        $ map (\ m -> (weight m,m)) 
        $ S.toList s

