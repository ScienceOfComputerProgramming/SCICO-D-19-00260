--
-- Authors: Emilio Tuosto <emilio@le.ac.uk>
--
-- This main returns the Erlang AST of the global graph in the .sgg file
-- given in input
--

import GGParser
import ErlangBridge
import Misc(rmQuotes)
import Data.List as L
import Data.Set as S
import CFSM(Ptp)
import qualified Data.Map as M
import System.Environment

main :: IO ()
main = do progargs <- getArgs
          let sourcefile =
                head progargs
          ggtxt <- readFile sourcefile
          let (_, gg, ptps, funs ) =
                ((gggrammar . GGParser.lexer) ggtxt) 1
          let ptpList = show $ L.map (\p -> erlAtom "ptp_" p) (S.toList ptps)
          let toErlTuple p = 
          let dcfList = L.foldr (\p l -> l ++ [p]) "" (M.keys funs)
          putStrLn $ rmQuotes $ erlTuple [ptpList, dcfList, fst $ gg2erl 1 gg]


