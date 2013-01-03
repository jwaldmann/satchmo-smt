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
    let m k x = M.fromList $ do
             i <- [0..bits-1]
             return ( (k,i), not $ x !! i )
    x <- sequence $ replicate bits [False,True]
    y <- sequence $ replicate bits [False,True] 
    let (z,ok) = tobits bits 
               $ f (frombits x) (frombits y)
    let mxy = M.union (m 0 x) (m 1 y)
    if ok
       then do
           i <- [ 0 .. bits-1 ]
           return $ M.insert (2,i) (z!!i) mxy
       else return mxy

frombits = foldr ( \ b x -> 2*x + fromEnum b ) 0

tobits :: Int -> Int -> ( [Bool], Bool )
tobits bits x = 
    if bits <= 0 then ( [], x == 0 )
    else let (d,m) = divMod x 2 
             (ms, rest) = tobits (bits-1) d
         in  (toEnum m : ms, rest)

weight s = length $ filter id $ M.elems s

combine (w1,s1) (w2, s2) = do
    guard $ 1 == abs (w1 - w2)
    combine0 s1 s2

combine0 s1 s2 = do
    guard $ M.keysSet s1 == M.keysSet s2
    let m = M.intersectionWith (,) s1 s2
        same = M.filter (uncurry (==)) m
    guard $ M.size same + 1 == M.size m
    let out = M.map fst same
    return (weight out, out)

levels cnf = M.fromListWith S.union $ do
    cl <- S.toList cnf
    return (weight cl, S.singleton cl)

climb [(c1,s1)] = [s1]
climb ((c1,s1) : (c2,s2) : later) = 
    let here = S.fromList $ do 
            guard $ c1 == c2 + 1
            x <- S.toList s1 ; y <- S.toList s2
            (w,z) <- combine0 x y
            if (w==c2) then return z else error "huh"
    in  here : climb ( (c2, S.union s2 here) : later )

-- | search for combination, and remove!
combines s = do
    ( pre, this : post ) <- splits s
    ( pre', that : post' ) <- splits post
    c <- combine this that
    let rest 
          = filter ( not . M.isSubmapOf (snd c) . snd )
          $ pre ++ pre' ++ post'
    return $ c : rest

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

