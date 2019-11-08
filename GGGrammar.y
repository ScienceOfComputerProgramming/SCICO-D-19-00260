--
-- Author: Emilio Tuosto <emilio@le.ac.uk>
--

-- A very basic grammar and parser for the textual editing of global
-- graphs. The grammar is a revised version of the one used in the
-- ICE16
--
--    G ::= (o)
--       |  P -> P : M
--       |  P => P, ..., P : M
--	 |  G | G
--       |  G ; G
--       |  choose exp @ P { Brc }
--       |  repeat { G } until exp @ P
--       |  { G }
--
--    Brc   ::= tag :: G | tag :: G + Brc
--
-- where the operators are in ascending order of precedence and exp is
-- of the form 'f(s1 ... sh)' represents the use of a function 'f' to
-- be defined in the target language taking h parameters of sort
-- s1,...,sh and such that the function returns
--    - a boolean in the 'repeat' construct or
--    - the value of an enumerated type enum(t1,...,tn) in choose
--      f(s1 ... sh) @ P { t1 :: G1 + ... + tn :: Gn }
--
-- Note: strings are made of the following characters
--
--   0123456789
--   \_$#&~
--   ABCDEFGHIJKLMNOPQRSTUVWXYZ
--   abcdefghijklmnopqrstuvwxyz
--
-- and must start with a letter when specifying the identity of a
-- participant.
--
-- Reserved characters not usable in strings are:
--
--   @ . , ; : ( ) [ ] { } | + - * / ^ ! ? % §
--
-- Text enclosed by '[' and ']' is treated as multi-line comment and,
-- after '..', so is the rest of a line.
--
-- The parser generator is Haskell's 'Happy' and the parser
-- (GGParser.hs) is obtained by typing 'make parser'.
--
-- Basic syntactic checks are made during the parsing (e.g, (i) that
-- sender and receiver of interactions have to be different and (2)
-- that the participant controlling a loop is active in the
-- loop). More are planned together with some more informative error
-- messages.
--
-- TODO: improve parseError
--
{
module GGParser where
import SyntacticGlobalGraphs
import ErlanGG
import Data.Set as S (empty, singleton, intersection, union, unions, difference, fromList, difference, toList, member, foldr, Set)
import Data.List as L
import qualified Data.Map as M (keys, empty, insert, union, Map)
import Misc
import CFSM
}

%name gggrammar
%tokentype { Token }
%error { parseError }

%token
  str	        { TokenStr $$   }
  '(o)'         { TokenEmp      }
  '->'	     	{ TokenArr      }
  '=>'	        { TokenMAr      }
  '|'	        { TokenPar      }
  '+'	        { TokenBra      }
  '*'	        { TokenSta      }
  ';'	        { TokenSeq      }
  '@'   	{ TokenUnt      }
  ':'	        { TokenSec      }
  '('	        { TokenFno      }
  ')'	        { TokenFnc      }
  ','	        { TokenCom      }
  '{'	        { TokenCurlyo   }
  '}'	        { TokenCurlyc   }
  'choose'      { TokenSel      }
  'repeat'      { TokenRep      }
  'until'       { TokenUnt      }

%right '|'
%right '+'
%right ';'
%right ','

%%

G :: { (GG, Set Ptp) }
G : B                                   { $1 }
  | B '|' G  	     	        	{ (Par ((checkToken TokenPar $1)
                                                ++ (checkToken TokenPar $3)),
                                            S.union (snd $1) (snd $3))
                                        }


B :: { (GG, Set Ptp) }
B : S                                   { $1 }
  | choiceop '{' S '+' Bs '}'        	{ (Bra (S.fromList $
                                                 (L.foldr (\g -> \l -> l ++ (checkToken TokenBra g))
                                                   []
                                                   (L.map fst ([$3] ++ $5))
                                                 )
                                               ),
                                            ptpsBranches ([$3] ++ $5))
                                        }

Bs :: { [((GG, Set Ptp), M.Map String String)] }
Bs : S                                 { [ $1 ] }
   | S '+' Bs                          { [$1] ++ $3 }


S :: { (GG, Set Ptp) }
S : '(o)'                               { (Emp, S.empty) }
  | Blk                                 { $1 }
  | B ';' B                           { (Seq ((checkToken TokenSeq $1)
                                                 ++ (checkToken TokenSeq $3)),
                                            S.union (snd $1) (snd $3))
                                        }



Blk :: { (GG, Set Ptp) }
Blk : str '->' str ':' str              { case ((isPtp $1), (isPtp $3), not($1 == $3)) of
        				    (True, True, True)   -> ((Act ($1 , $3) $5), S.fromList [$1,$3])
	        			    (True, False, True)  -> myErr ("Bad name " ++ $3)
		        		    (True, True, False)  -> myErr ("A sender " ++ $3 ++ " cannot be also the receiver in an interaction")
			        	    (_, False, False)    -> myErr ("Whaaat??? Sender " ++ $1 ++ " and receiver " ++ $3 ++ " are equal AND different!!!")
				            (_, True, True)      -> myErr ("Whaaat??? Sender " ++ $1 ++ " and receiver " ++ $3 ++ " are equal AND different!!!")
        				    (False, False, True) -> myErr ("Bad names " ++ $1 ++ " and " ++ $3)
	        			    (False, _, False)    -> myErr ("Bad name " ++ $1 ++ " and sender and receiver must be different")
                                        }
  | str '=>' ptps ':' str               { case ((isPtp $1), not(L.elem $1 $3)) of
                                            (True,  True)  -> case $3 of
                                                                []   -> myErr ($1 ++ " cannot be empty") -- ($1 ++ " => " ++ "[]")
                                                                s:[] -> ((Act ($1 , s) $5), S.fromList([$1,s]))
                                                                _    -> (Par (L.map (\s -> (Act ($1 , s) $5)) $3),S.fromList($1:$3))
                                            (True,  False) -> myErr ($1 ++ " must be in " ++ (show $3))
                                            (False, _)     -> myErr ("Bad name " ++ $1)
                                        }
  | 'repeat' str '{' G 'unless' guard '}'    {
                                               case ((isPtp $2), (S.member $2 (snd $4))) of
                                                 (True, True)  -> (Rep (fst $4) $2 , S.union (S.singleton $2) (snd $4))
                                                 (False, _)    -> myErr ("Bad name " ++ $2)
                                                 (True, False) -> myErr ("Participant " ++ $2 ++ " is not among the loop's participants: " ++ (show $ toList $ snd $4))
                                             }
  | '{' G '}'                           { $2 }


ptps :: { [String] }
ptps : str                      { if (isPtp $1) then [$1] else myErr ("Bad name " ++ $1) }
     | str ',' ptps             { if (isPtp $1)
                                  then (case $3 of
                                        [] ->  [$1]
                                        (s:l) -> ($1:s:l))
                                  else myErr ("Bad name " ++ $1)
                                }

exp : str '(' ')'
    | str '(' sorts ')'

sorts : str        { [$1] }
      | str sorts  { $1 : $2 }

{
type Tag = String
type Sort = String
type Funs = M.Map Ptp [(String, [Sort], Set Tag)]

data Token = TokenStr String
  | TokenPtps [Ptp]
  | TokenEmp
  | TokenArr
  | TokenPar
  | TokenBra
  | TokenSel
  | TokenGrd
  | TokenSeq
  | TokenRep
  | TokenSta
  | TokenUnt
  | TokenSec
  | TokenBro
  | TokenBrc
  | TokenCom
  | TokenMAr
  | TokenUnl
  | TokenErr String
  | TokenCurlyo
  | TokenCurlyc
        deriving (Show)


lexer s = case s of
    []                             -> []
    '(':'o':')':r                  -> TokenEmp : lexer r
    '[':r                          -> lexer $ mytail (L.dropWhile (\c->c/=']') r)
    '.':'.':r                      -> lexer $ mytail (L.dropWhile (\c->c/='\n') r)
    ' ':r                          -> lexer r
    '\n':r                         -> lexer r
    '\t':r                         -> lexer r
    '-':'>':r                      -> TokenArr : (lexer r)
    '=':'>':r                      -> TokenMAr : (lexer r)
    '|':r                          -> TokenPar : lexer r
    '+':r                          -> TokenBra : lexer r
    's':'e':'l':' ':r              -> TokenSel : (lexer r)
    's':'e':'l':'\n':r             -> TokenSel : (lexer r)
    's':'e':'l':'\t':r             -> TokenSel : (lexer r)
    'b':'r':'a':'n':'c':'h':' ':r  -> TokenSel : (lexer r)
    'b':'r':'a':'n':'c':'h':'\n':r -> TokenSel : (lexer r)
    'b':'r':'a':'n':'c':'h':'\t':r -> TokenSel : (lexer r)
    '*':r                          -> TokenSta : lexer r
    'r':'e':'p':'e':'a':'t':' ':r  -> TokenRep : (lexer r)
    'r':'e':'p':'e':'a':'t':'\n':r -> TokenRep : (lexer r)
    'r':'e':'p':'e':'a':'t':'\t':r -> TokenRep : (lexer r)
    'u':'n':'l':'e':'s':'s':' ':r  -> TokenUnl : (lexer r)
    'u':'n':'l':'e':'s':'s':'\t':r -> TokenUnl : (lexer r)
    'u':'n':'l':'e':'s':'s':'\r':r -> TokenUnl : (lexer r)
    '%':r                          -> TokenGrd : lexer r
    '@':r                          -> TokenUnt : lexer r
    ':':r                          -> TokenSec : lexer r
    ';':r                          -> TokenSeq : lexer r
    ',':r                          -> TokenCom : lexer r
    '(':r                          -> TokenBro : lexer r
    ')':r                          -> TokenBrc : lexer r
    '{':r                          -> TokenCurlyo : lexer r
    '}':r                          -> TokenCurlyc : lexer r
    _                              -> TokenStr (fst s') : (lexer $ snd s')
        where s' = span isAlpha s

mytail :: [t] -> [t]
mytail l = if L.null l
           then l
           else tail l

parseError :: [Token] -> a
parseError err = case err of
                    TokenErr s:_ -> myErr $ show s
                    _            -> myErr (show err)


ptpsBranches :: [((GG, Set Ptp), ReversionGuard)] -> Set Ptp
ptpsBranches = \l -> L.foldr S.union S.empty (L.map (\x -> snd $ fst x) l)


checkGuard :: (GG, Set Ptp) -> ReversionGuard -> ((GG, Set Ptp), ReversionGuard)
checkGuard g m = let tmp = [ x | x <- M.keys m, not (S.member x (snd g)) ] in
                 if L.null tmp
                 then (g, m)
                 else myErr ("Unknown participant(s): " ++ (show tmp))

-- checkToken 'flattens', parallel, branching, and sequential composition
checkToken :: Token -> (GG, Set Ptp) -> [GG]
checkToken t (g,_) = case t of
                      TokenPar -> case g of
                                   Par l -> l
                                   _ -> [g]
                      TokenBra -> case g of
                                   Bra l -> S.toList l
                                   _ -> [g]
                      TokenSeq -> case g of
                                   Seq l -> l
                                   _ -> [g]
                      _        -> [g]

-- ggsptp computes the set of participants of a syntactic global graph
ggsptp :: Set Ptp -> GG -> Set Ptp
ggsptp ps g = case g of
               Emp         -> ps
               Act (s,r) _ -> S.union ps (S.fromList [s,r])
               Par gs      -> S.union ps (S.unions (L.map (ggsptp S.empty) gs))
               Bra gs      -> S.union ps (S.unions (L.map (ggsptp S.empty) (S.toList gs)))
               Seq gs      -> S.union ps (S.unions (L.map (ggsptp S.empty) gs))
               Rep g' p    -> S.union ps (ggsptp (S.singleton p) g')

myErr :: String -> a
myErr err = error ("sggparser: ERROR - " ++ err)
}
