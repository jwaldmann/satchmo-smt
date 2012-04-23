{-# language FlexibleContexts #-}
{-# language RankNTypes #-}

module Exotic.Generate where

import Strategy
import Remove ( Prover, Processor )
import Claim
import qualified Proof
import qualified Matrix
import Config hiding ( domain )

import Exotic.Dict ( Dict ,logic, domain )
import qualified Exotic.Solve
import qualified Exotic.Check

import qualified SMT.Meta
import SMT.Util
import Prelude hiding ( and, or )

import qualified Semiring as S

import Satchmo.SAT.Mini ( SAT)
import Satchmo.Code ( Decode )
import qualified Satchmo.Boolean as B

import TPDB.Pretty
import qualified TPDB.Data as T
import Language.SMTLIB 

import Control.Monad.RWS hiding ( mplus, All )
import Control.Monad.Trans

import qualified Data.Set as S
import qualified Data.Map as M
import Data.List ( nub, transpose )

symbolic :: ( S.Semiring d, Pretty d, Eq d, Show d
            , Pretty a, Ord a, Pretty ( T.SRS a ) 
            , Decode SAT e d ) 
         => Dict SAT d e B.Boolean
         -> Config         
         -> Claim a 
         -> IO ( Maybe ( Proof.Interpretation a ))
symbolic dict conf c = do
    let ( decoder, _, w) = runRWS ( claim dict conf c ) () 0 
        s = Script w
    out <- 
        if True
        then do             
            out_sat <- SMT.Meta.logged conf 
                ( Exotic.Solve.execute dict ) s
            return -- $ fmap ( M.map  $ fmap fromInteger ) 
                   $ out_sat
        else do
            let ( sc, back ) = undefined -- transform dict s
            out_z3 <- SMT.Meta.solve ( solvers conf ) sc
            return $ fmap back out_z3

    case out of 
        Just m -> Exotic.Check.execute  m s 
        Nothing -> return () 
    return $ fmap decoder out 


claim :: ( S.Semiring d,  Pretty d, Pretty a, Ord a, Decode SAT e d ) 
      => Dict SAT d e B.Boolean 
      -> Config 
      -> Claim a 
      -> Sym ( M.Map Symbol d -> Proof.Interpretation a )
claim dict conf c = do
    let [dim] = dims conf
    tell [ Set_option $ Produce_models True ]
    when (unsatcore conf) $ do
        tell [ Set_option $ Produce_unsat_cores True ]
    tell [ Set_logic $ logic dict ]
    tell [ Set_info $ Attribute_s_expr ":source" 
         $ S_expr_symbol 
         $ "|remove " ++ show (remove conf) ++ " strict rules from\n" 
         ++ show (pretty $ system c) 
         ++ "\nby matrix interpretation with dimension " ++ show dim ++ "|"
         ]

    let sig = Data.List.nub $ do 
            u <- T.rules $ system c ; T.lhs u ++ T.rhs u
    int <- interpretation dict sig dim
    tell [ Assert $ monotone (property c) int ]

    rs <- forM ( T.rules $ system c ) $ \ u -> do
        l <- eval dict int $ T.lhs u
        r <- eval dict int $ T.rhs u
        return ( T.strict u, (l, r))

    case remove conf of
        Some -> do
            assert $ and $ for rs $ \ ( s, (l,r)) -> weakly_greater l r 
            assert $ or $ for (filter fst rs) $ \ ( True, (l,r)) -> 
                                    strictly_greater l r 
        All -> assert $ and $ for rs $ \ ( s, (l,r)) -> 
                let rel =  if s then strictly_greater else weakly_greater
                in  rel l r 
    tell [ Check_sat ]

    case unsatcore conf of
        True -> tell [ Get_unsat_core ]
        False -> do
            top <- get
            tell [ Get_value $ do 
                   k <- [ 0 .. top-1 ]
                   -- FIXME ("f" cannot be right)
                   return $ sym2term $ "f" ++ show k 
               ]

    return $ decode dict dim int

decode dict dim int m = 
    let int' = flip M.map int $ \ l -> 
              let get ( Term_qual_identifier ( Qual_identifier ( Identifier f))) = m M.! f
                  c = for ( coeff l ) $ \ row -> for row get
                  a = for ( absolute l ) $ \ row -> for row get
              in  Matrix.Matrix $ zipWith (++) 
                  ( c ++ [ replicate dim S.zero  ] ) 
                  ( a ++ [[ S.one ]] )
    in  Proof.Interpretation ( Exotic.Dict.domain dict ) int'


type Matrix = [[ Term ]]

data Linear = Linear { coeff :: Matrix , absolute :: Matrix }

matrices l = [ coeff l , absolute l ]

-- linear :: Dict d -> Int -> Sym Linear
linear dict dim = do
    m <- matrix dict (dim,dim)
    a <- matrix dict (dim,1)
    return $ Linear m a

-- matrix :: Dict d -> (Int,Int) -> Sym Matrix
matrix dict (height, width) = 
    forM [ 1 .. height ] $ \ i -> forM [ 1 .. width ] $ \ j -> 
        declare $ show $ domain dict

-- interpretation :: Ord a => Dict d -> [a] -> Int -> Sym ( M.Map a Linear )
interpretation dict sig dim = do
    pairs <- forM sig $ \ a -> do m <- linear dict dim ; return ( a, m )
    return $ M.fromList pairs

-- times :: Dict d -> Linear -> Linear -> Sym Linear 
times dict f g = do
    c <- mtimes dict ( coeff f ) ( coeff g )
    a <- mtimes dict ( coeff f ) ( absolute g )
    b <- mplus  dict ( absolute f ) a
    return $ Linear c b

-- mtimes :: Dict d -> Matrix -> Matrix -> Sym Matrix
mtimes dict a b = forM a $ \ row -> 
            forM ( transpose b ) $ \ col -> 
            manifest dict $ dot row col

-- mplus :: Dict d -> Matrix -> Matrix -> Sym Matrix
mplus dict a b = forM ( zip a b) $ \ (c,d) -> 
            forM ( zip c d) $ \ (x,y) -> 
            manifest dict $ apply "+" [x,y]

dot :: [Term] -> [Term] -> Term
dot xs ys = apply "+" $ for ( zip xs ys ) $ \ (x,y) -> apply "*" [x,y]

-- manifest :: Dict d -> Term -> Sym Term
manifest dict x = do 
    define ( show $ domain dict ) x

eval dict int w = foldM1 (flip $ times dict) 
                $ for ( reverse w ) $ \ a -> int M.! a
foldM1 f (z : zs) = foldM f z zs

strictly_greater :: Linear -> Linear -> Term
strictly_greater f g = 
    and $ for ( zip ( matrices f ) ( matrices g ) ) $ \ (a,b) -> 
    and $ for ( zip a b ) $ \ (r,s) -> 
    and $ for ( zip r s ) $ \ (x,y) -> apply ">>" [x,y]
        
weakly_greater :: Linear -> Linear -> Term
weakly_greater f g = 
    and $ for ( zip ( matrices f ) ( matrices g ) ) $ \ (a,b) ->
    and $ for ( zip a b ) $ \ (r,s) -> 
    and $ for ( zip r s ) $ \ (x,y) -> apply ">=" [x,y]

monotone prop int = 
    and $ for (M.elems int) $ \ l -> ( case prop of
        Top_Termination -> 
          \ f -> or [ apply "finite" [ head $ head $ absolute l ]
                    , f ]  
        Termination -> id
      ) $ apply "finite" [ head $ head $ coeff l ]

