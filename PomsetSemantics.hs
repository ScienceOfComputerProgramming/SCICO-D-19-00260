--
-- Author: Emilio Tuosto <emilio@le.ac.uk>
--
-- This module implements the pomset semantics of JLAMP 17 (but for
-- the well-formedness checking)
--

module PomsetSemantics where

import Misc
import Data.Set as S
import Data.List as L
import Data.Map.Strict as M
import CFSM
import SyntacticGlobalGraphs
import Text.XML.HXT.Parser.XmlParsec(xreadDoc)
import Data.Tree.NTree.TypeDefs
import Text.XML.HXT.DOM.TypeDefs
-- import Text.XML.HXT.DOM.QualifiedName

type Event = Int
type Lab   = Map Event Action
type Pomset = (Set Event, Set (Event, Event), Lab)

emptySem :: Event -> (Set Pomset, Event)
-- emptySem e = (S.singleton (S.singleton e, S.empty, M.fromList [(e, (("?","?"), Tau, "?"))]), e+1)
emptySem e = (S.empty, e)

emptyPom :: Pomset
emptyPom = (S.empty, S.empty, M.empty)

eventsOf :: Pomset -> Set Event
eventsOf (events, _, _) = events

orderOf :: Pomset -> Set (Event, Event)
orderOf (_, rel, _) = rel

labOf :: Pomset -> Lab
labOf (_, _, lab) = lab

sprod :: Ord t => Ord t' => Set t -> Set t' -> Set (t,t')
sprod xs ys = S.fromList [(x,y) | x <- S.toList xs, y <- S.toList ys]

pomsetsOf :: GG -> Int -> Event -> (Set Pomset, Event)
pomsetsOf gg iter e =
  -- PRE: gg is well-formed
  -- POST: returns the set of pomsets [[gg]] with n-unfolds of each loop for n = |iter|
  --       (eventually) well-formedness is checked iff iter >= 0
  -- e is the 'counter' of the events
  let unfold g n = Seq (L.replicate (abs n) g)
      -- TODO: uniform unfoldind for the moment. Eventually to generate random numbers between 0 and iter.
  in
    case gg of
      Emp -> emptySem e
      Act c m -> (S.fromList [ (S.fromList [e, e+1], (S.singleton (e,e+1)), lab )], e+2)
        where lab = M.fromList [(e, (c, Send, m)), (e+1, (c, Receive, m) )]
      LAct c m -> pomsetsOf (Act c m) iter e
      Par ggs -> (combine (tail pomsets) (head pomsets), e'')
        where (pomsets, e'') = L.foldl aux ([], e) ggs
              aux = \(gs, e') g ->
                let (p, e_) = pomsetsOf g iter e'
                in (p : gs, e_)
              combine pps ps =
                case pps of
                  [] -> ps
                  ps':pps' ->
                    let f = \(p, p') a -> S.insert (pUnion p p') a
                    in combine pps' (S.foldr f S.empty (sprod ps ps'))
              pUnion = \(events, rel, lab) (events', rel', lab') ->
                (S.union events events', S.union rel rel', M.union lab lab')
      Bra ggs -> L.foldl aux (emptySem e) ggs
        where aux = \(gs, e') g -> let (p, e'') = pomsetsOf g iter e' in (S.union p gs, e'')
      Seq ggs ->
        case ggs of
          [] -> emptySem e
          [g'] -> pomsetsOf g' iter e
          g':ggs' -> (S.map pseq (sprod p' p''), e'')
            where (p', e') = pomsetsOf g' iter e
                  (p'', e'') = pomsetsOf (Seq ggs') iter e'
                  pseq (pom@(events, rel, lab), pom'@(events', rel', lab')) =
                    (S.union events events',
                     S.union (seqrel pom pom') (S.union rel rel'),
                     M.union lab lab')
                  seqrel (events, _, lab) (events', _, lab') =
                    S.filter (\(e1,e2) -> case (M.lookup e1 lab, M.lookup e2 lab') of
                                            (Just x, Just y) -> subjectOf x == subjectOf y
                                            _                -> False
                             ) (sprod events events')
      Rep gg' _ -> pomsetsOf (unfold gg' iter) iter e

getClosure :: Set Event -> Pomset -> Set Event
getClosure evs p@(events, rel, _)=
  let p' = subpom evs p
      right = S.difference events evs
      p'' = subpom right p
      rel' = [(x,y) | (x,y) <- reflexoTransitiveClosure (S.toList events) (S.toList rel), x /= y]
      new = S.filter (\e -> not (S.null $ getNonPred e p' rel')) (minOfPomset p'')
  in if S.null new then
       evs
     else getClosure (S.union evs new) p

-- getNonPred :: Event -> Pomset -> Set Event
-- getNonPred e p@(events, rel, _) rel' =
--   let rel' = reflexoTransitiveClosure (S.toList events) (S.toList rel)
--   in dropElems (\e' -> (e',e) € rel') (maxOfPomset p)

getNonPred :: Event -> Pomset -> [(Event, Event)] -> Set Event
getNonPred e p rel = dropElems (\e' -> (e',e) € rel) (maxOfPomset p)

mkInteractions :: Pomset -> Pomset
-- replaces matching output/input pairs of events with the
-- corresponding interaction while preserving the order
mkInteractions p@(_, rel, lab) =
  let dualpairs = S.filter getDuals rel
  in L.foldr aux p (S.toList dualpairs)
     where getDuals = \(i,j) -> (isSend (lab!i)) && (dualAction (lab!i) == (lab!j))
           aux (i,j) (events', rel', lab') = (S.delete j events', replace i j rel', M.delete j lab')
           replace e e' r = (S.foldr (\x r' -> S.insert (change x e e') r') S.empty r)
           change (h,k) e e' = let f = \x -> if x == e' then e else x in (f h, f k)

minOfPomset :: Pomset -> Set Event
minOfPomset (events, rel, _) =
  let cod = S.map snd (S.filter (\(x,y) -> x /= y) rel)
      ismin e acc = if S.member e cod then
                      acc
                    else S.insert e acc
  in S.foldr ismin S.empty events

maxOfPomset :: Pomset -> Set Event
maxOfPomset (events, rel, _) =
  let domrel = S.map fst (S.filter (\(x,y) -> x /= y) rel)
      ismax e acc = if S.member e domrel then
                      acc
                    else S.insert e acc
  in S.foldr ismax S.empty events

subpom :: Set Event -> Pomset -> Pomset
subpom evs (_, rel, lab) = (evs, rel', lab')
-- PRE: evs included in the events of p
-- POST: returns the sub pomset made of the events in evs from p
  where rel' = S.foldr f S.empty rel
        f (h,k) res = if (S.member h evs) && (S.member k evs) then
                         S.insert (h,k) res
                      else res
        lab' = S.foldr (\e m -> M.insert e (lab!e) m) M.empty evs

components :: Pomset -> Set (Set Event)
-- computes the connected components in the order relation of the pomset
-- TODO: pretty inefficient; improve
components (events, rel, _) = S.foldr aux S.empty events
  where aux e l = S.insert (connected [] [e] S.empty) l
        connected visited tovisit acc =
          case tovisit of
            [] -> acc
            e:tovisit' ->
              if L.elem e visited then
                 connected visited tovisit' acc
              else
                let r = reflexoTransitiveClosure (S.toList events) (S.toList rel)
                    todo = L.map fst [(x,y) | (x,y) <- r, y == e] ++
                           L.map snd [(x,y) | (x,y) <- r, x == e]
                in connected (e:visited) (tovisit' ++ todo) (S.union acc (S.fromList todo))

pomset2gg :: Pomset -> Maybe GG
pomset2gg p@(_, _, lab) =
  let comps = components $ mkInteractions p
  in if S.null comps then
        Just Emp
     else let tmp = S.foldr aux (Just []) comps
          in case tmp of
               Nothing -> Nothing
               Just [gg] -> Just gg
               Just ggs -> Just (Par ggs)
  where aux evs l =
          case l of
            Nothing -> Nothing
            Just l' ->
              let
                subp = subpom evs (mkInteractions p)
                closure = getClosure (S.filter (\e -> S.member e (minOfPomset subp)) evs) subp
              in
                if closure == evs then
                  if S.size evs > 1 then                -- A closure with more than one event
                    Nothing                             -- cannot be represented with parallel or sequential
                  else                                  -- we just return the interatction
                    let act = lab!(head $ S.toList evs) -- recall that those must be output actions
                        s = subjectOf act
                        r = objectOf act
                        m = msgOf act
                    in Just ((Act (s,r) m) : l')
                else                                       -- a split is possible and we recur
                  let p' = subpom closure subp
                      p'' = subpom (S.difference (eventsOf subp) closure) subp
                  in
                    case (pomset2gg p', pomset2gg p'') of
                      (Nothing, _) -> Nothing
                      (_, Nothing) -> Nothing
                      (Just g1, Just g2) -> Just ((Seq [g1,g2]):l')


-- GML stuff

pomset2gml :: Pomset -> String
pomset2gml (events, rel, lab) =
  -- returns the graphML representation of the pomset
  let mlpref =          "<?xml version='1.0' encoding='utf-8'?>\n<graphml xmlns=\"http://graphml.graphdrawing.org/xmlns\" xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\" xsi:schemaLocation=\"http://graphml.graphdrawing.org/xmlns http://graphml.graphdrawing.org/xmlns/1.0/graphml.xsd\">\n  <key attr.name=\"in\" attr.type=\"string\" for=\"node\" id=\"d0\" />\n  <key attr.name=\"out\" attr.type=\"string\" for=\"node\" id=\"d1\" />\n  <key attr.name=\"subject\" attr.type=\"string\" for=\"node\" id=\"d2\" />\n  <key attr.name=\"partner\" attr.type=\"string\" for=\"node\" id=\"d3\" />\n  <graph edgedefault=\"directed\">\n"
      snodetag nodeid = "    <node id=\"" ++ nodeid ++ "\">\n"
      datatag key v =   "      <data key=\"" ++ key ++ "\">" ++ v ++ "</data>\n"
      enodetag =        "    </node>\n"
      edgetab src tgt = "    <edge source=\"" ++ src ++ "\" target=\"" ++ tgt ++ "\" />\n"
      mlsuff =          "  </graph>\n</graphml>\n"
      (inkey, outkey, subjkey, othkey) = ("d0", "d1", "d2", "d3") 
      nodeGL e = (snodetag $ show e) ++ labGL e ++ enodetag
      edgeGL (e,e') = edgetab (show e) (show e')
      labGL e = case M.lookup e lab of
                  Just ((s,r), Receive, m) -> (datatag subjkey r) ++ (datatag othkey s) ++ (datatag inkey m)
                  Just ((s,r), Send,    m) -> (datatag subjkey s) ++ (datatag othkey r) ++ (datatag outkey m)
                  Just ((s,_), Tau, _)     -> (datatag subjkey s)
                  _                        -> error (msgFormat GG2POM "Unknown action: " ++ (show (M.lookup e lab)))
  in mlpref ++ (L.foldr (++) "" (S.map nodeGL events)) ++ (L.foldr (++) "" (S.map edgeGL rel)) ++ mlsuff

-- gml2pomset :: String -> Pomset
-- gml2pomset s = emptyPom
--   -- return the pomset from its gml representation
--   where 

checkTag :: QName -> String -> a -> a
checkTag tag val expr =
  if localPart tag == val then
    expr
  else error (msgFormat POM2GG "Bad " ++ val)

xgml2pomset :: String -> Pomset
xgml2pomset xml = aux (xreadDoc xml) M.empty
  where
    aux t m =
      case t of
        [] -> emptyPom
        (NTree (XPi _ _ ) _):rest -> aux rest m
        (NTree (XTag tag xtree) xtree'):rest ->
          case localPart tag of
            "key" -> aux rest (addKey xtree m)
            "graph" -> aux xtree' m
            "graphml" -> aux xtree' m
            "node" -> addNode xtree xtree' m (aux rest m)
            "edge" -> addEdge xtree (aux rest m)
            _ -> error (msgFormat POM2GG "Bad Tag " ++ (localPart tag))
        _:rest -> aux rest m
    addKey xkey dict =
      case xkey of
        [NTree (XAttr attrtag) [NTree (XText k) _], _, _, NTree (XAttr idtag) [NTree (XText v) _]] ->
          checkTag attrtag "attr.name" (checkTag idtag "id" (M.insert v k dict))
        _ -> error (msgFormat POM2GG "Bad key " ++ (show xkey))
    addEdge e (events, rel, lab) =
      case e of
        [NTree (XAttr srctag) [NTree (XText s) []], NTree (XAttr tgttag) [NTree (XText t) _]] ->
          checkTag srctag "source" (checkTag tgttag "target" (events, S.insert ((read s)::Int, (read t)::Int) rel, lab))
        _ -> error (msgFormat POM2GG "Bad edge " ++ (show e))
    addNode n d dict (events, rel, lab) = 
      let
        nodeid = 
          case n of
            [NTree _ [NTree (XText xid) _]] -> (read xid)::Int
            _ -> error (msgFormat POM2GG "Bad node")
        getData pairs datum =
          case datum of
            [] -> pairs
            (NTree (XTag tag xkey) xval):ds ->
              checkTag tag "data" (
              let
                getPair k v =
                  case (k, v) of
                    ([NTree (XAttr tag') [NTree (XText k') _]], [NTree (XText v') _]) ->
                      checkTag tag' "key" (dict!k', v')
                    _ -> error (msgFormat POM2GG "Bad key at node " ++ (show nodeid))
              in (getPair xkey xval):(getData pairs ds)
              )
            (NTree (XText _) _):ds -> (getData pairs ds)
            _ -> error (msgFormat POM2GG "Bad action at node " ++ (show nodeid) ++ "\t" ++ (show datum))
        action =
          let
            tmpMap = M.fromList (getData [] d)
          in if L.elem "in" (M.keys tmpMap) then
            ((tmpMap!"partner", tmpMap!"subject"), Receive, tmpMap!"in")
          else ((tmpMap!"subject",tmpMap!"partner"), Send, tmpMap!"out")
      in
        (S.insert nodeid events, rel, M.insert nodeid action lab)