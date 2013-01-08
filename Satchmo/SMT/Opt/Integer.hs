module Satchmo.SMT.Opt.Integer where



import qualified Satchmo.Binary as Bin
import qualified Satchmo.Boolean as B

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad ( forM, guard )
import Data.List ( inits, tails, nub )

prop2 cnf x y = do
    z <- B.boolean
    forM (S.toList cnf) $ \ clause -> 
        B.assert $ do
            ((k,i), v) <- M.toList clause
            let bits = case k of
                    0 -> Bin.bits x 
                    1 -> Bin.bits y 
                    2 -> [z]
                trans = if v then id else B.not
            return $ trans $ bits !! i
    return z

op2 cnf bits x y = do
    z <- Bin.number bits
    forM (S.toList cnf) $ \ clause -> 
        B.assert $ do
            ((k,i), v) <- M.toList clause
            let var = case k of
                    0 -> x ; 1 -> y ; 2 -> z
                trans = if v then id else B.not
            return $ trans $ Bin.bits var !! i
    return z

