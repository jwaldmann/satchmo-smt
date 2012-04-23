-- | read script in SMT2-format from stdin,
-- write status and model to stdout.

-- Solver uses bit blasting where details of the encoding
-- can be chosen via command line parameters.

-- Accepts input logic QF_LIA, QF_LRA, QF_IDL
-- but actually all variables are assumed to be non-negative integers.
-- (also QF_Arctic, QF_Tropical, QF_Fuzzy)

-- Assumption: input contains exactly one (check-sat)
-- followed by (get-value) for all global names.

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
           Just values -> [ Cs_response Sat
                  , Gv_response values 
                  ]


