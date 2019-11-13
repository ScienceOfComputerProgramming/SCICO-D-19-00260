--
-- Author: Emilio Tuosto <emilio@le.ac.uk>
--
-- This module contains function to transform a syntactic choreography
-- to an Erlang data structure.
--

module ErlangBridge where

import Data.Set as S
import Data.List as L
import Data.Char(isLower)
import Data.Map.Strict as M
import Misc
import CFSM

type Tag = String
type Fname = String
type Sort = String
type CP = Int
type Funs = M.Map Ptp [M.Map Fname ([Sort], Set Tag)]

-- A syntactic global graph is a set of nodes, a source, a sink, and a
-- set of edges We assume that cp's will be automatically generated
-- (uniquely) during parsing
data GG = Emp
        | Act Channel Message
        | Par [GG]
        | Bra Ptp Fname [Sort] (M.Map Tag GG)
        | Seq [GG]
        | Rep Ptp Fname [Sort] GG
        deriving (Eq, Ord, Show)

erlTuple :: [String] -> String
erlTuple tuple = case tuple of
  [] -> ""
  _  -> "{ " ++ (mkSep tuple ", ") ++ " }"

erlAtom :: String -> String -> String
erlAtom pre s = case s of
  "" -> ""
  _  -> if isLower(head s) then s else pre ++ s

mkErl :: Int -> String -> [String] -> String
mkErl ln op strs =
  rmQuotes $ erlTuple [show ln, op, (show strs)]

gg2erl :: Int -> GG -> (String, Int)
gg2erl ln _gg =
  case _gg of
    Emp -> ("", ln)
    Act (s,r) m -> (mkErl ln "com" [erlAtom "ptp_" s, erlAtom "ptp_" r, erlAtom "msg_" m], 1+ln)
    Par ggs ->
      let aux = \(ts, l) g -> let (t', ln') = gg2erl l g in (if t' == "" then ts else ts ++ [t'], ln')
          (threads, ln'') = L.foldl aux ([], 1+ln) ggs
      in (mkErl ln "par" threads, ln'')
    Bra p fname sorts tagMap ->
      let aux = \(branches, l) (t,g) -> let (branch, ln') = gg2erl l g in (branches ++ [erlTuple [t, branch]], ln')
          (pairs, ln'') = L.foldl aux ([],1+ln) (M.toList tagMap)
      in (mkErl ln "bra" ([erlAtom "ptp_" p, fname, show sorts] ++ pairs), ln'')
    Seq ggs ->
      let aux = \(seqg, l) g -> let (next, ln') = gg2erl l g in (if next == "" then seqg else seqg ++ [next], ln')
          (seqList, ln'') = L.foldl aux ([],1+ln) ggs
      in (mkErl ln "seq" seqList, ln'')
    Rep p fname sorts gg ->
      let (body, ln') = gg2erl (1+ln) gg
      in (mkErl ln "rec" ([erlAtom "ptp_" p, fname, show sorts] ++ [body]), ln')
