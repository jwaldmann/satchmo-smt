module Satchmo.SMT.Config where

import System.Console.GetOpt

data Encoding = Unary  { bits :: Int }
              | Binary { bits :: Int }
    deriving Show

data Config = 
     Config { encoding :: Encoding
            }
    deriving Show

config0 = Config { encoding = Unary 8 }

options =
    [ Option "u" [ "unary" ] 
      ( ReqArg ( \ s conf -> conf { encoding = Unary { bits = read s }}) "INT")
      "use unary encoding with given number of bits"
    , Option "b" [ "binary" ] 
      ( ReqArg ( \ s conf -> conf { encoding = Binary { bits = read s }}) "INT")
      "use binary encoding with given number of bits"
    ]

parse_options argv = case getOpt Permute options argv of
        (o,_,[]) -> return $ foldl (flip id) config0 o
        (_,_,errs) -> do
            let header = "Usage: satchmo-smt [OPTION...]"
            ioError $ userError $ concat errs ++ usageInfo header options
