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

import Satchmo.SMT.ToTerm

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


binary_fixed :: Int -> Dictionary Satchmo.SAT.Mini.SAT Bin.Number Integer
binary_fixed bits = Dictionary
    { info = unwords [ "binary", "bits:", show bits, "(fixed)" ]
    , domain = Satchmo.SMT.Dictionary.Int
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


binary_flexible :: Int -> Dictionary Satchmo.SAT.Mini.SAT Bin.Number Integer
binary_flexible bits = Dictionary
    { info = unwords [ "binary", "bits:", show bits, "(flexbible)" ]
    , domain = Satchmo.SMT.Dictionary.Int
    , number = Bin.number bits
    , nconstant = Bin.constant
    , boolean = B.boolean
    , bconstant = B.constant
    , add = Satchmo.Binary.Op.Flexible.add
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
