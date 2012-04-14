-- | read script in SMT2-format from stdin,
-- write status and model to stdout.

-- Solver uses bit blasting where details of the encoding
-- can be chosen via command line parameters.

-- Accepts input logic QF_LIA, QF_LRA, QF_IDL
-- but actually all variables are assumed to be non-negative integers.

-- Assumption: input contains exactly one (check-sat)
-- followed by (get-value) for all global names.

-- Assumption: input does not contain local bindings (LET)


import Satchmo.SMT.Config
import Satchmo.SMT.Solve

import Language.SMTLIB

import qualified Data.Map as M
import Control.Monad ( mapM_ )
import System.IO
import System.Environment

main = do
    argv <- getArgs
    conf <- parse_options argv
    s <- getContents
    let input = parseScript s

    output <- execute conf input  

    mapM_ print $ case output of
           Nothing -> [ Cs_response Unknown ]
           Just m -> [ Cs_response Sat
                  , Gv_response $ do
                      (k,v) <- M.toList m
                      return ( sym2term k , case v of
                         Value_Integer i -> int2term i 
                         Value_Bool b -> bool2term b
                         )
                  ]

sym2term fun = 
    Term_qual_identifier ( Qual_identifier ( Identifier fun  ))  

int2term int =
    if int >= 0  
    then Term_spec_constant ( Spec_constant_numeral int )
    else Term_qual_identifier_ ( Qual_identifier ( Identifier "-"))
             [ int2term $ negate int ]

bool2term b =
    Term_qual_identifier $ Qual_identifier $ Identifier $ case b of
        False -> "false" ; True -> "true"

