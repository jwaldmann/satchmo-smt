module Satchmo.SMT.Integer where

import Prelude hiding ( not, and, or )
import Language.SMTLIB

import Satchmo.SMT.Config

import Satchmo.SMT.Dictionary
import Satchmo.SMT.Exotic.Semiring.Integer 
import qualified Satchmo.SAT.Mini
import qualified Satchmo.Code
import qualified Satchmo.Boolean as B

import qualified Satchmo.Unary.Op.Fixed
import qualified Satchmo.Unary.Op.Flexible
import qualified Satchmo.Unary as Un

import qualified Satchmo.Binary as Bin
import qualified Satchmo.Binary.Op.Fixed  
import qualified Satchmo.Binary.Op.Flexible

import qualified Satchmo.SMT.Opt.Integer as OI
import qualified Satchmo.SMT.Opt.Base as OB

import Satchmo.SMT.ToTerm

import Control.Monad ( forM )

unary_fixed :: Int -> Unary_Addition 
            -> Dictionary Satchmo.SAT.Mini.SAT Un.Number Integer
unary_fixed bits a = Dictionary
    { info = unwords [ "unary", "bits:", show bits, "(fixed)", "addition:", show a ]
    , domain = Satchmo.SMT.Dictionary.Int
    , number = Un.number bits
    , nconstant = Un.constant
    , boolean = B.boolean
    , bconstant = B.constant
    , add = case a of
          Quadratic -> Satchmo.Unary.Op.Fixed.add_quadratic
          Bitonic_Sort -> Satchmo.Unary.Op.Fixed.add_by_bitonic_sort
          Odd_Even_Merge -> Satchmo.Unary.Op.Fixed.add_by_odd_even_merge
    , gt = Un.gt
    , ge = Un.ge
    , neq = Un.eq
    , and = B.and, or = B.or, not = B.not, beq = B.equals2, assert = B.assert
    }

unary_flexible :: Int -> Unary_Addition
               -> Dictionary Satchmo.SAT.Mini.SAT Un.Number Integer
unary_flexible bits a = Dictionary
    { info = unwords [ "unary", "bits:", show bits, "(flexible)", "addition:", show a ]
    , domain = Satchmo.SMT.Dictionary.Int
    , number = Un.number bits
    , nconstant = Un.constant
    , boolean = B.boolean
    , bconstant = B.constant
    , add = case a of
          Quadratic -> Satchmo.Unary.Op.Flexible.add_quadratic
          Bitonic_Sort -> Satchmo.Unary.Op.Flexible.add_by_bitonic_sort
          Odd_Even_Merge -> Satchmo.Unary.Op.Flexible.add_by_odd_even_merge
    , gt = Un.gt
    , ge = Un.ge
    , neq = Un.eq
    , and = B.and, or = B.or, not = B.not, beq = B.equals2, assert = B.assert
    }

binary_fixed bits =
    if bits <= 3 
    then binary_fixed_opt   bits
    else -- binary_fixed_plain bits
        binary_fixed_double 
            $ binary_fixed (div bits 2)

binary_fixed_opt bits = Dictionary
    { info = unwords [ "binary", "bits:", show bits, "(fixed)" ]
    , domain = Satchmo.SMT.Dictionary.Int
    , number = Bin.number bits
    , nbits = bits
    , decode = Satchmo.Code.decode
    , nconstant = Bin.constant
    , boolean = B.boolean
    , bconstant = B.constant
    , add = OI.op2 ( OB.improve $ OB.fun2 (+) bits ) bits
    , times = OI.op2 ( OB.improve $ OB.fun2 (*) bits ) bits
    , times_lo = OI.op2 
            ( OB.improve 
            $ OB.fun2 (\x y -> mod(x*y) (2^bits)) bits ) bits
    , times_hi = OI.op2 
            ( OB.improve 
            $ OB.fun2 (\x y -> div(x*y) (2^bits)) bits ) bits
    , positive = \ n -> B.or $ Bin.bits n
    , gt = OI.prop2 ( OB.improve $ OB.rel2 (>) bits) 
    , ge = OI.prop2 ( OB.improve $ OB.rel2 (>=) bits) 
    , neq = OI.prop2 ( OB.improve $ OB.rel2 (/=) bits) 
    , and = B.and, or = B.or, not = B.not, beq = B.equals2, assert = B.assert
    }


binary_fixed_plain :: Int 
  -> Dictionary Satchmo.SAT.Mini.SAT Bin.Number Integer
binary_fixed_plain bits = Dictionary
    { info = unwords [ "binary", "bits:", show bits, "(fixed)" ]
    , domain = Satchmo.SMT.Dictionary.Int
    , nbits = bits
    , number = Bin.number bits
    , decode = Satchmo.Code.decode
    , nconstant = Bin.constant
    , boolean = B.boolean
    , bconstant = B.constant
    , add = Satchmo.Binary.Op.Fixed.add
    , times = Satchmo.Binary.Op.Fixed.times
    , positive = \ n -> B.or $ Bin.bits n
    , gt = Bin.gt
    , ge = Bin.ge
    , neq = Bin.eq
    , and = B.and, or = B.or, not = B.not, beq = B.equals2, assert = B.assert
    }

binary_fixed_double d = 
    let h = nbits d ; bits = 2 * h
        split x = 
                let (lo,hi) = splitAt h $ Bin.bits x
                in  (Bin.make lo, Bin.make hi)
        join x y = 
                Bin.make $ Bin.bits x ++ Bin.bits y
    in  Dictionary
    { info = unwords [ "binary", "bits:", show bits, "(fixed)" ]
    , domain = Satchmo.SMT.Dictionary.Int
    , number = Bin.number bits
    , nbits = bits
    , decode = Satchmo.Code.decode
    , nconstant = Bin.constant
    , boolean = B.boolean
    , bconstant = B.constant

    , add = \ x y -> do
         let (xl, xh) = split x
             (yl, yh) = split y
         -- FIXME: allow carry in the middle:
         l <- add d xl yl
         h <- add d xh yh
         return $ join l h

    , times = \ x y -> do
         let (xl, xh) = split x
             (yl, yh) = split y
         l <- times_lo d xl yl
         m1 <- times_hi d xl yl
         m2 <- times d xl yh
         m3 <- times d xh yl
         m23 <- add d m2 m3
         m123 <- add d m1 m23
         h <- times d xh yh
         forM ( Bin.bits h) $ \ b -> 
              B.assert [ B.not b ]
         return $ join l m123

    , positive = \ n -> B.or $ Bin.bits n
    , gt = Bin.gt
    , ge = Bin.ge
    , neq = Bin.eq

    , and = B.and, or = B.or, not = B.not
    , beq = B.equals2, assert = B.assert
    }


binary_flexible :: Int -> Dictionary Satchmo.SAT.Mini.SAT Bin.Number Integer
binary_flexible bits = Dictionary
    { info = unwords [ "binary", "bits:", show bits, "(flexbible)" ]
    , domain = Satchmo.SMT.Dictionary.Int
    , number = Bin.number bits
    , decode = Satchmo.Code.decode
    , nconstant = Bin.constant
    , boolean = B.boolean
    , bconstant = B.constant
    , add = Satchmo.Binary.Op.Flexible.add
    , times = Satchmo.Binary.Op.Flexible.times
    , positive = \ n -> B.or $ Bin.bits n
    , gt = Bin.gt
    , ge = Bin.ge
    , neq = Bin.eq
    , and = B.and, or = B.or, not = B.not, beq = B.equals2, assert = B.assert
    }

instance ToTerm Integer where
  toTerm int =
    if int >= 0  
    then Term_spec_constant ( Spec_constant_numeral int )
    else Term_qual_identifier_ ( Qual_identifier ( Identifier "-"))
             [ toTerm $ negate int ]
