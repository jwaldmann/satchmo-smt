module Satchmo.SMT.Config where

import System.Console.GetOpt

data Encoding = Unary | Binary deriving Show
data Unary_Addition = Odd_Even_Merge | Bitonic_Sort | Quadratic deriving Show
data Extension = Fixed | Flexible deriving Show

data Config = 
     Config { encoding :: Encoding
            , unary_addition :: Unary_Addition
            , bits :: Int
            , extension :: Extension
            }
    deriving Show

config0 = Config { encoding = Unary, unary_addition = Quadratic, bits = 5, extension = Fixed }

options =
    [ Option "u" [ "unary" ] 
      ( ReqArg ( \ s conf -> conf { encoding = Unary , bits = read s }) "INT")
      "use unary encoding with given number of bits"
    , Option "o" [ "odd-even" ]
      ( NoArg $ \ conf -> conf { unary_addition = Odd_Even_Merge } ) 
      "unary addition via odd-even-merge"
    , Option "n" [ "bitonic" ]
      ( NoArg $ \ conf -> conf { unary_addition = Bitonic_Sort } ) 
      "unary addition via bitonic sort"
    , Option "q" [ "quadratic" ]
      ( NoArg $ \ conf -> conf { unary_addition = Quadratic } ) 
      "unary addition via bitonic sort"
    , Option "b" [ "binary" ] 
      ( ReqArg ( \ s conf -> conf { encoding = Binary , bits = read s }) "INT")
      "use binary encoding with given number of bits"
    , Option "i" [ "fixed" ]
      ( NoArg $ \ conf -> conf { extension = Fixed } ) 
      "fixed bit width (also for intermediate results)"
    , Option "l" [ "flexible" ]
      ( NoArg $ \ conf -> conf { extension = Flexible } ) 
      "flexible bit width (increase as needed for intermediates)"
    ]

parse_options argv = case getOpt Permute options argv of
        (o,_,[]) -> return $ foldl (flip id) config0 o
        (_,_,errs) -> do
            let header = "Usage: satchmo-smt [OPTION...]"
            ioError $ userError $ concat errs ++ usageInfo header options
