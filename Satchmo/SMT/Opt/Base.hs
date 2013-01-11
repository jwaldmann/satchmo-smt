module Satchmo.SMT.Opt.Base where

import qualified OBDD as O
import qualified Satchmo.Boolean as B
import qualified Satchmo.Binary as N

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad ( guard )
import Data.List ( inits, tails, sortBy, minimumBy )
import Data.Function (on)

improve cnf = S.fromList
            $ imp merges (vcnf cnf) 
            $ reverse
            $ S.toList cnf

canonical cnf = imp super (vcnf cnf) $ S.toList cnf

imp find v clauses = 
    case find v clauses
    of
        [] -> clauses
        c : cs -> 
           let ok e = not $ M.isSubmapOf c e
           in imp find v 
               $ c : filter ok clauses

with_super v clauses = super v clauses ++ clauses

super v clauses = do
    x <- clauses
    k <- M.keys x
    let x' = M.delete k x
    guard $ implies v (vclause x')
    return x'

merges v clauses = do
    (xs , y : ys) <- splits clauses
    x <- xs
    let xy = M.map fst
           $ M.filter (uncurry (==))
           $ M.intersectionWith (,) x y
    guard $ implies v (vclause xy)    
    return xy 

splits xs = zip (inits xs) (tails xs)

implies a b = O.null $ a O.&& O.not b

vcnf c = O.and $ map vclause $ S.toList c

vclause c = O.or $ do
    (k,v) <- M.toList c
    return $ O.unit k v

type CNF v = S.Set (Clause v)
type Clause v = M.Map v Bool

fun :: Int -- ^ arity
    -> ( [Int] -> Int )
    -> Int -- ^ bits
    -> CNF (Int,Int)
fun ar f bits = S.fromList $ do
    xs <- sequence $ replicate (ar + 1)
        $ sequence $ replicate bits [ False, True ]
    guard $ frombits (last xs)      
         /= f ( map frombits $ init xs )
    return $ M.fromList $ do
         (k,x) <- zip [0..] xs
         (i,b) <- zip [0..] x
         return ( (k,i) , not b )


rel2 :: (Int -> Int -> Bool)
     -> Int -- ^ bits
     -> CNF (Int,Int)
rel2 r bits = S.fromList $ do
    let digit k x i = ((k,i) , not (x!!i))
    let m k x bits = M.fromList 
              $ map (digit k x) [0..bits-1]
    x <- sequence $ replicate bits [False,True]
    y <- sequence $ replicate bits [False,True] 
    z <- [False,True] 
    guard $ z /= r (frombits x) (frombits y)
    return $ M.unions 
           [ m 0 x bits, m 1 y bits, m 2 [z] 1 ]

-- | OBDD for the formula  
-- f(x,y) = z && x,y,z are representable (with bits)
fun2 :: (Int -> Int -> Int)
     -> Int -- ^ bits
     -> CNF (Int,Int)
fun2 f bits = S.fromList $ do
    let digit k x i = ((k,i) , not (x!!i))
    let m k x = M.fromList 
              $ map (digit k x) [0..bits-1]
    x <- sequence $ replicate bits [False,True]
    y <- sequence $ replicate bits [False,True] 
    z <- sequence $ replicate bits [False,True] 
    guard $ frombits z /= f (frombits x) (frombits y)
    return $ M.unions [ m 0 x, m 1 y, m 2 z ]

frombits = foldr ( \ b x -> 2*x + fromEnum b ) 0

tobits :: Int -> Int -> ( [Bool], Bool )
tobits bits x = 
    if bits <= 0 then ( [], x == 0 )
    else let (d,m) = divMod x 2 
             (ms, rest) = tobits (bits-1) d
         in  (toEnum m : ms, rest)

