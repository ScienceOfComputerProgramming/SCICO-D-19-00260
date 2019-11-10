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
{ -- Haskell header of the parser
module GGParser where
import SyntacticGlobalGraphs
import ErlanGG
import Data.Set as S (empty, singleton, intersection, union, unions, difference, fromList, difference, toList, member, foldr, Set)
import Data.List as L
import qualified Data.Map as M (keys, empty, insert, Map, fromList, elems)
import Misc
import CFSM
}

%name gggrammar       -- parsing function
%tokentype { Token }  -- which has type [Token] -> GGParse
%error { parseError } -- and invokes parseError if parsing errors occur

%token
  str	        { TokenStr $$   }
  '(o)'         { TokenEmp      }
  '->'	     	{ TokenArr      }
  '=>'	        { TokenMAr      }
  '|'	        { TokenPar      }
  '+'	        { TokenBra      }
  ';'	        { TokenSeq      }
  '@'   	{ TokenUnt      }
  ':'	        { TokenSec      }
  '::'	        { TokenTag      }
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

%%  -- Pointless line customary in yacc

G :: { GGparse }
G : Blk                                 { $1 }
  | G '|' Blk  	     	        	{ (Par ((checkToken TokenPar $1)
                                                ++ (checkToken TokenPar $3)),
                                            S.union (snd $1) (snd $3))
                                        }
  | G ';' Blk                           { (Seq ((checkToken TokenSeq $1)
                                                 ++ (checkToken TokenSeq $3)),
                                            S.union (snd $1) (snd $3))
                                        }

Branch :: { M.Map Tag GGparse }
Branch : str '::' G                    { M.fromList ($1, $3) }

Branches :: { M.Map Tag GGparse }
Branches : Branch                      { $1 }
         | Branches '+' Branch         { sumBranches $1 $3 }

Blk :: { GGparse }
Blk : '(o)'                                { (0, Emp, S.empty, M.empty) }
    | str '->' str ':' str                 { case ((isPtp $1), (isPtp $3), not($1 == $3)) of
        		 		         (True, True, True)   -> (1, (Act ($1 , $3) $5), S.fromList [$1,$3], M.empty)
	        			         (True, False, True)  -> myErr ("Bad name " ++ $3)
		        		         (True, True, False)  -> myErr ("A sender " ++ $3 ++ " cannot be also the receiver in an interaction")
			        	         (_, False, False)    -> myErr ("Whaaat??? Sender " ++ $1 ++ " and receiver " ++ $3 ++ " are equal AND different!!!")
				                 (_, True, True)      -> myErr ("Whaaat??? Sender " ++ $1 ++ " and receiver " ++ $3 ++ " are equal AND different!!!")
             				         (False, False, True) -> myErr ("Bad names " ++ $1 ++ " and " ++ $3)
	        			         (False, _, False)    -> myErr ("Bad name " ++ $1 ++ " and sender and receiver must be different")
                                           }
    | str '=>' ptps ':' str                { case ((isPtp $1), not(L.elem $1 $3)) of
                                                 (True, False) -> case $3 of
                                                                     []   -> myErr ($1 ++ " cannot be empty")
                                                                     s:[] -> (1, Act ($1 , s) $5, S.fromList([$1,s]), M.empty)
                                                                     _    -> (1, Par (L.map (\s -> (Act ($1 , s) $5)) $3), S.fromList($1:$3), M.empty)
                                                 (_,  True) -> myErr ($1 ++ " must not be in " ++ (show $3))
                                                 (False, _) -> myErr ("Bad name " ++ $1)
                                            }
    | 'choose' exp '@' str '{' Branches '}' { case (S.member p ptps) of
                                                False -> myErr (p ++ " is not in " ++ (show ptps))
                                                _ -> (cp, Bra (S.fromList $
                                                         (L.foldr (\g -> \l -> l ++ (checkToken TokenBra g))
                                                          []
                                                          (L.map fst ([p] ++ $4))
                                                         )
                                                       ),
                                                      ptps,
                                                      bs
                                                     )
                                                 where (p, f, sorts) = $2
                                                       (cp, ptps, bs) = (updBranches p (f, sorts) $4)
                                            }
  | 'repeat' G 'until' exp                  { case (S.member p ptps) of
                                                 True -> (cp+1, Rep g p , ptps, catFun p (f, sorts, loopTags cp) funs)
                                                 _ -> myErr ("Participant " ++ p ++ " is not among the loop's participants: " ++ (show $ toList $ ptps))
                                                   where (p, f, sorts) = $4
                                                         (cp, g, ptps, funs) = $2
                                            }
  | '{' G '}'                               { $2 }


ptps :: { [Ptp] }
ptps : str                      { if (isPtp $1) then [$1] else myErr ("Bad name " ++ $1) }
     | str ',' ptps             { if (isPtp $1)
                                  then (case $3 of
                                        [] ->  [$1]
                                        (s:l) -> ($1:s:l))
                                  else myErr ("Bad name " ++ $1)
                                }

exp :: { (Ptp, Fname, [Sort]) }
exp : str '(' ')' '@' str              { if (isPtp $5) then ($5, $1, []) else myErr ("Bad name " ++ $5) }
    | str '(' sorts ')' '@' str        { if (isPtp $6) then ($5, $1, $3) else myErr ("Bad name " ++ $6) }

sorts :: { [Sort] }
sorts : str                            { [$1] }
      | str sorts                      { $1 : $2 }

{
type Tag = String
type Fname = String
type Sort = String
type CP = Int
type Funs = M.Map Ptp [M.Map Fname ([Sort], Set Tag)]
type GGparse = (CP, GG, Set Ptp, Funs)

parseError :: [Token] -> a
parseError err = case err of
                    TokenErr s:_ -> myErr $ show s
                    _            -> myErr (show err)

data Token = TokenStr String
  | TokenEmp
  | TokenArr
  | TokenMAr
  | TokenPar
  | TokenBra
  | TokenSel
  | TokenRep
  | TokenUnl
  | TokenUnt
  | TokenTag
  | TokenSec
  | TokenSeq
  | TokenCom
  | TokenFno
  | TokenFnc
  | TokenCurlyo
  | TokenCurlyc
  | TokenErr String
        deriving (Show)

lexer :: String -> [Token]
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
    'c':'h':'o':'o':'s':'e':' ':r  -> TokenSel : (lexer r)
    'c':'h':'o':'o':'s':'e':'\n':r -> TokenSel : (lexer r)
    'c':'h':'o':'o':'s':'e':'\t':r -> TokenSel : (lexer r)
    'r':'e':'p':'e':'a':'t':' ':r  -> TokenRep : (lexer r)
    'r':'e':'p':'e':'a':'t':'\n':r -> TokenRep : (lexer r)
    'r':'e':'p':'e':'a':'t':'\t':r -> TokenRep : (lexer r)
    'u':'n':'t':'i':'l':' ':r      -> TokenUnl : (lexer r)
    'u':'n':'t':'i':'l':'\t':r     -> TokenUnl : (lexer r)
    'u':'n':'t':'i':'l':'\r':r     -> TokenUnl : (lexer r)
    '@':r                          -> TokenUnt : lexer r
    ':':':':r                       -> TokenTag : lexer r
    ':':r                          -> TokenSec : lexer r
    ';':r                          -> TokenSeq : lexer r
    ',':r                          -> TokenCom : lexer r
    '(':r                          -> TokenFno : lexer r
    ')':r                          -> TokenFnc : lexer r
    '{':r                          -> TokenCurlyo : lexer r
    '}':r                          -> TokenCurlyc : lexer r
    _                              -> TokenStr (fst s') : (lexer $ snd s')
        where s' = span isAlpha s

mytail :: [t] -> [t]
mytail l = if L.null l
           then l
           else tail l

catFun :: Ptp -> (Fname, [Sort], [Tag]) -> Funs -> Funs
catFun p (f, sorts, tags) funs =
  M.insert p (M.fromList (f, (sorts, tags)):(if p € (M.keys funs) then funs!p else [])) funs

updBranches :: Ptp -> (Fname, [Sort]) -> M.Map Tag GGparse -> (CP, Set Ptp, Funs)
updBranches p (f, sorts) branches =
  let aux = L.foldr (\t l -> let (_, _, _, funs) = (branches!t) in funs ++ l) [] (M.keys branches)
      newf = M.fromList (f, (sorts, M.keys branches))
      funs = L.foldr (\m -> catFut p (f, sorts, M.keys branches) m) M.empty (M.elems aux)
--      funs = L.foldr (\m -> M.insert p ((aux!p) ++ if p € (M.keys m) then m!p else []) m) M.empty (M.elems aux)
  in M.insert p (newf:fs) funs
     where fs = if p € (M.keys funs)
                then (funs!p)
                else []

loopTags :: CP -> [Tag]
loopTags cp = ["enter__" ++ (show cp), "exit__" ++ (show cp)]

-- checkToken 'flattens', parallel, branching, and sequential composition
checkToken :: Token -> GGparse -> [GG]
checkToken t (_,g,_,_) =
  case t of
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
