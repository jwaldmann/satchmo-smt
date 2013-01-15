module Satchmo.SMT.Arctic where

import Prelude hiding ( not, and, or )
import qualified Prelude
import Control.Monad.Error ( throwError )

import Language.SMTLIB

import Satchmo.SMT.Config

import Satchmo.SMT.Dictionary

import qualified Satchmo.SMT.Exotic.Dict as D
import qualified Satchmo.SMT.Exotic.Semiring as S
import qualified Satchmo.SMT.Exotic.Semiring.Arctic 
       as A -- arctic
import qualified Satchmo.SMT.Exotic.Arctic 
       as C -- coded arctic

import qualified Satchmo.SAT.Mini
import qualified Satchmo.Code
import qualified Satchmo.Boolean as B

import qualified Satchmo.Unary as N

import Control.Monad ( forM, when )

direct :: Dictionary (Either String) 
       (A.Arctic Integer) (A.Arctic Integer) Bool
direct = Dictionary 
    { info = unwords [ "arctic (direct)" ]
    , domain = Satchmo.SMT.Dictionary.Arctic
    , nconstant = \ n -> return n
    , bconstant = \ b -> return b
    , add   = \ x y -> return $ S.plus x y
    , times = \ x y -> return $ S.times x y
    , positive = \ x -> return $ S.strictly_positive x
    , gt = \ x y -> return $ S.gt x y
    , ge = \ x y -> return $ S.ge x y 
    , and = \ xs -> return $ Prelude.and xs
    , or  = \ xs -> return $ Prelude.or xs
    , not = Prelude.not 
    , assert = \ bs -> if Prelude.or bs then return () 
       else throwError "Satchmo.SMT.Arctic.assert"
    }

unary_fixed :: Int 
 -> Dictionary Satchmo.SAT.Mini.SAT 
      C.Arctic (A.Arctic Integer) B.Boolean
unary_fixed bits = let d = C.dict bits in
   Dictionary
    { info = unwords 
          [ "unary", "bits:", show bits, "(fixed)" ]
    , domain = Satchmo.SMT.Dictionary.Arctic
    , number = D.fresh d 
    , nbits = bits
    , nconstant = \ a -> case a of
        A.Minus_Infinite -> do
            f <- B.constant False
            C.make $ N.make $ replicate bits f
        A.Finite c -> do
            let fs = map ( c >= ) 
                     [0 .. fromIntegral bits] 
            when ( Prelude.not (head fs) || last fs) 
                 $ error "Arctic.nconstant: range"
            bs <- forM (init fs) B.constant
            C.make $ N.make $ bs
    , decode = Satchmo.Code.decode
    , positive = D.finite d
    , boolean = B.boolean
    , bconstant = B.constant
    , add = \ x y -> D.plus d [x,y]
    , times = \ x y -> D.times d [x,y]
    , gt = D.gg d
    , ge = D.ge d
    -- , neq = Un.eq
    , and = B.and, or = B.or
    , not = B.not
    -- , beq = B.equals2
    , assert = B.assert
    }
