--
-- Author: Emilio Tuosto <emilio@le.ac.uk>
--

-- A very basic grammar and parser for the textual editing of global
-- graphs. The grammar is a revised version of the one used in the
-- ICE16 and is is geared towards the generation of executable code.
-- 
--
--    G ::= (o)
--       |  P -> P : M
--       |  P => P, ..., P : M
--	 |  G | G
--       |  G ; G
--       |  choose f(x y ...) @ P { Brc }
--       |  repeat G until f(x y ...) @ P
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
import ErlangBridge
import Data.Set as S (empty, singleton, union, fromList, toList, member, Set)
import Data.List as L
import qualified Data.Map as M -- (keys, empty, insert, Map, fromList, toList, elems)
import Misc
import CFSM
}

%name gggrammar       -- parsing function
%tokentype { Token }  -- which has type [Token] -> GGParse
%error { parseError } -- and invokes parseError if parsing errors occur

%token
  str	        { TokenStr $$   }
  "(o)"         { TokenEmp      }
  "->"	     	{ TokenArr      }
  "=>"	        { TokenMAr      }
  "|"	        { TokenPar      }
  "+"	        { TokenBra      }
  ";"	        { TokenSeq      }
  "@"   	{ TokenAt      }
  ":"	        { TokenSec      }
  "::"	        { TokenTag      }
  "("	        { TokenFno      }
  ")"	        { TokenFnc      }
  ","	        { TokenCom      }
  "{"	        { TokenCurlyo   }
  "}"	        { TokenCurlyc   }
  "choose"      { TokenSel      }
  "repeat"      { TokenRep      }
  "until"       { TokenUnt      }

%right "|"
%right "+"
%right ";"
%right ","
%left "until"

%%  -- Pointless line customary in yacc

G :: { CP -> GGparse }
G : Blk                                 { $1 }
  | G "|" Blk
    { \cp ->
        let (cp', g, ptps, funs) = ($1 cp)
            (cp'', gb, ptpsb, funsb) = ($3 cp')
        in (cp'',
            Par ((checkToken TokenPar g) ++ (checkToken TokenPar gb)),
            S.union ptps ptpsb,
            mergeFuns funs funsb
           )
    }

  | G ";" Blk
    { \cp ->
        let (cp', g, ptps, funs) = ($1 cp)
            (cp'', gb, ptpsb, funsb) = ($3 cp')
        in  (cp'',
             Seq ((checkToken TokenSeq g) ++ (checkToken TokenSeq gb)),
             S.union ptps ptpsb,
             mergeFuns funs funsb
            )
    }


Blk :: { CP -> GGparse }
Blk : "(o)"
  { \cp ->
      (cp, Emp, S.empty, M.empty)
  }

  | str "->" str ":" str
  { \cp ->
      case ((isPtp $1), (isPtp $3), not($1 == $3)) of
        (True, True, True)   -> (cp, (Act ($1 , $3) $5), S.fromList [$1,$3], M.empty)
        (True, False, True)  -> myErr ("Bad name " ++ $3)
        (True, True, False)  -> myErr ("Sender " ++ $3 ++ " cannot be also the receiver in an interaction")
        (_, False, False)    -> myErr ("Whaaat??? Sender " ++ $1 ++ " and receiver " ++ $3 ++ " are equal AND different!!!")
        (_, True, True)      -> myErr ("Whaaat??? Sender " ++ $1 ++ " and receiver " ++ $3 ++ " are equal AND different!!!")
        (False, False, True) -> myErr ("Bad names " ++ $1 ++ " and " ++ $3)
        (False, _, False)    -> myErr ("Bad name " ++ $1 ++ " and sender and receiver must be different")
  }
  
  | str "=>" ptps ":" str
    { \cp ->
        case ((isPtp $1), not(L.elem $1 $3)) of
          (True, False) -> case $3 of
                             []   -> myErr ($1 ++ " cannot be empty")
                             s:[] -> (cp, Act ($1 , s) $5, S.fromList([$1,s]), M.empty)
                             _    -> (cp, Par (L.map (\s -> (Act ($1 , s) $5)) $3), S.fromList($1:$3), M.empty)
          (_,  True) -> myErr ($1 ++ " must not be in " ++ (show $3))
          (False, _) -> myErr ("Bad name " ++ $1)
    }
      
    | "choose" exp "{" Branches "}"
      { \cp ->
          let (p, fID, sorts) = $2
              (cp', tagMap) = ($4 cp)
              (ptps, funs) = (updBranches (p, fID, sorts) tagMap)
          in case (S.member p ptps) of
               False -> myErr (p ++ " is not in " ++ (show ptps))
               _ -> (cp'+1,
                     Bra p fID sorts (M.fromList $ L.map (\(t,(_,g,_,_)) -> (t,g)) (M.toList tagMap)),
                     ptps,
                     funs
                    )
      }
      
  | "repeat" G "until" exp
    { \cp ->
        let (p, fID, sorts) = $4
            (cp', g, ptps, funs) = ($2 cp)
        in case (S.member p ptps) of
          True -> (cp'+1, Rep p fID sorts g, ptps, addFun p (fID, sorts, loopTags cp') funs)
          _ -> myErr ("Participant " ++ p ++ " is not among the loop's participants: " ++ (show $ toList $ ptps))
    }

  | "{" G "}"
    { $2 }


Branch :: { CP -> (CP, M.Map Tag GGparse) }
Branch : str "::" G
  { \cp ->
      let (cp', g, ptps, funs) = ($3 cp)
      in (cp', M.fromList [($1, (cp', g, ptps, funs))])
  }


Branches :: { CP -> (CP, M.Map Tag GGparse) }
Branches : Branch
  { $1 }
  
  | Branches "+" Branch
    { \cp ->
        let (cp', tagMap) = ($1 cp)
            (cp'', tagMap') = ($3 cp')
        in if L.intersect (M.keys tagMap) (M.keys tagMap') == []
           then (cp'', M.fromList ((M.toList tagMap) ++ (M.toList tagMap')))
           else myErr ("Reused tags: " ++ (show $ M.keys tagMap'))
    }


ptps :: { [Ptp] }
ptps : str
  { if (isPtp $1) then [$1] else myErr ("Bad name " ++ $1) }
  
  | ptps "," str
    { if (isPtp $3) then $1 ++ [$3] else myErr ("Bad name " ++ $3) }


exp :: { (Ptp, Fname, [Sort]) }
exp : str "(" sorts ")" "@" str
  { if (isPtp $6) then ($6, $1, $3) else myErr ("Bad name " ++ $6) }


sorts :: { [Sort] }
sorts : {- no sorts -}
  { [] }
  
  | sorts str
    { $1 ++ [$2] }

{
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
  | TokenUnt
  | TokenAt
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
    'u':'n':'t':'i':'l':' ':r      -> TokenUnt : (lexer r)
    'u':'n':'t':'i':'l':'\n':r     -> TokenUnt : (lexer r)
    'u':'n':'t':'i':'l':'\t':r     -> TokenUnt : (lexer r)
    '@':r                          -> TokenAt : lexer r
    ':':':':r                      -> TokenTag : lexer r
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

funsOf :: Ptp -> Funs -> [(Fname, [Sort], Set Tag)]
funsOf p funs = if p € (M.keys funs) then ((M.!) funs p) else []

addFun :: Ptp -> (Fname, [Sort], Set Tag) -> Funs -> Funs
addFun p fun funs = M.insert p (fun:(funsOf p funs)) funs

mergeFuns :: Funs -> Funs -> Funs
mergeFuns f g =
  L.foldr
    (\p m -> M.insert p ((funsOf p f) ++ (funsOf p g)) m)
    M.empty
    ((M.keys f) ++ (M.keys g))

updBranches :: (Ptp, Fname, [Sort]) -> M.Map Tag GGparse -> (Set Ptp, Funs)
-- computes the participants occurring in branches and the updated map of call-back functions
updBranches (p, fID, sorts) tagMap =
  let (ptps, funs) = L.foldr
                      (\t (ps, funs') -> let (_, _, ps', funs) = ((M.!) tagMap t) in (S.union ps ps', mergeFuns funs funs'))
                      (S.empty, M.empty)
                      (M.keys tagMap)
      newf = (fID, sorts, S.fromList $ M.keys tagMap)
  in (ptps, M.insert p (newf:(funsOf p funs)) funs)

loopTags :: CP -> Set Tag
loopTags cp = S.fromList ["enter__" ++ (show cp), "exit__" ++ (show cp)]

-- checkToken 'flattens', parallel and sequential composition
checkToken :: Token -> GG -> [GG]
checkToken t g =
  case t of
    TokenPar -> case g of
                  Par l -> l
                  _ -> [g]
    TokenSeq -> case g of
                  Seq l -> l
                  _ -> [g]
    _        -> [g]

myErr :: String -> a
myErr err = error ("sggparser: ERROR - " ++ err)
}
