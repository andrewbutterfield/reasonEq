\section{Rooted Directed Acyclic Graphs (RDAGs)}

\begin{code}
module RDAG where
import Data.List
\end{code}

\subsection{Introduction}

We want to view theories as forming a DAG with many top
elements but all leading down to a common root (a \emph{rooted}-DAG or \textbf{rDAG}):

\begin{center}
\includegraphics[scale=0.25]{doc/images/block-RDAG}
\end{center}

We assume that every node has an identifier component
and is associated with some  extra data.
This could be rendered in pseudo-haskell as
\begin{verbatim}
let
  r = Root 'r' ...
  a = Node 'a' ... [r]
  b = Node 'b' ... [r]
  c = Node 'c' ... [a]
  d = Node 'd' ... [a,b]
  e = Node 'e' ... [d]
in Top [c,e]
\end{verbatim}
We shall assume that nodes contain identifiers
of type $I$, which are then associated independently with
their data using another indexing structure.
So all we implement here is
\begin{verbatim}
let
  r = Root 'r'
  a = Node 'a' [r]
  b = Node 'b' [r]
  c = Node 'c' [a]
  d = Node 'd' [a,b]
  e = Node 'e' [d]
in Top [c,e]
\end{verbatim}

\begin{center}
\includegraphics[scale=0.25]{doc/images/circle-RDAG}
\end{center}

Given a node, we then want to easily produce the list of nodes
leading from it down to the root.
Also, we want the representation to be minimal w.r.t to transitivity,
i.e. if $c$ links to $a$ and $a$ links to $r$ then we do not need to
explicitly represent the link from $c$ to $r$.
This ensure that the lists described above can easily be constructed,
as we anticipate building such lists will occur frequently,
whereas changes to the rDAG will be relatively rare.

We want to construct an rDAG either by providing a root object,
or a new object with a list of objects to which it should link,
all of which must already be present, modulo some equivalence
relation.
\begin{eqnarray*}
   rDAG_{I} &\defs& \ldots
\\ root &:& I \fun rDAG_{I}
\\ add &:& I \fun \finset_1 I \fun rDAG_{I} \fun rDAG_{I}
\\ pre\_add~i~S~r &\defs& i \notin r \land \forall j \in S @ j \in r
\\ \_ \in \_ &:&   I \times rDAG_{I} \fun \Bool
\end{eqnarray*}
In addition we want to search for a object by identifier,
and return its node (as the sub-rDAG with it as the only top object):
\begin{eqnarray*}
   search &:& I \fun rDAG_{I} \fun [rDAG_{I}]
\\ i \in r &\equiv& search~i~r \neq null
\end{eqnarray*}
Given a rDAG we want to return all the paths to the root,
topologically sorted into a single list.
\begin{eqnarray*}
   stack &:& rDAG_{I} \fun I^+
\end{eqnarray*}

\newpage
\subsubsection{rDAG Datatype}

Considering all of the above we now design our datatype.

An rDAG over identifier $I$ ($rDAG_I$)
\begin{code}
data RDAG i
\end{code}
is either:
\begin{itemize}
  \item a root node, containing an element of type $I$:
\begin{code}
 = DRoot i
\end{code}
  \item
    or a non-root node, containing an element of type $I$,
    along with a non-empty list of immediate descendant rDAGs,
    and an annotation giving the length of the longest
    path to the root%
    \footnote{Simplifies topological sort}%
    .
\begin{code}
 | DNode i [RDAG i] Int
\end{code}
  \item or a list of top rDAG nodes:
\begin{code}
 | DTop [RDAG i]
\end{code}
\end{itemize}
First, a way to view rDAGs over $I$:
\begin{code}
instance Show i => Show (RDAG i) where
  show r = showRDAG 0 r

showRDAG ind (DRoot i) = "\n" ++ indent ind ++ "ROOT " ++ show i
showRDAG ind (DNode i rs h)
  = "\n" ++ indent ind ++ "Node@" ++ show h ++ " "++ show i
     ++ ( concat $ map (showRDAG (ind+1)) rs )

showRDAG ind (DTop rs)
 = unlines $ map (showRDAG ind) rs
\end{code}

An alternative look that exposes structure a bit more:
\begin{code}
showRDStruct :: Show i => RDAG i -> String
showRDStruct (DRoot i) = "\nROOT = "++show i
showRDStruct (DNode i deps h)
 = "\nNODE: "++show i++" -> "++show (map rdId deps)++", h="++show h
 ++ concat (map showRDStruct deps)
showRDStruct (DTop tops)
 = "TOP = "++show (map rdId tops) ++ concat (map showRDStruct tops)
\end{code}


\newpage
\subsubsection{rDAG Analysis}

Getting the rDAG ``top names'':
\begin{code}
rdNames :: RDAG i -> [i]
rdNames (DRoot r) = [r]
rdNames (DNode n _ _) = [n]
rdNames (DTop rs) = map rdName rs
\end{code}

Getting the rDAG ``name'' (if it has a unique top):
\begin{code}
rdName :: RDAG i -> i
rdName (DRoot r) = r
rdName (DNode n _ _) = n
rdName (DTop [r]) = rdName r
rdName (DTop _) = error "Tables.rdName: multi-DTop has no name"
\end{code}

We have a simple rDAG equivalence based on root and node names:
\begin{code}
eqvRDAG :: Eq i => RDAG i -> RDAG i -> Bool
eqvRDAG (DRoot r1) (DRoot r2) = r1 == r2
eqvRDAG (DNode r1 _ _) (DNode r2 _ _) = r1 == r2
eqvRDAG _ _ = False
\end{code}

Also, a way to extract the height:
\begin{code}
rdHeight :: RDAG i -> Int
rdHeight (DRoot _)      =  0
rdHeight (DNode _ _ h)  =  h
rdHeight (DTop tops)    =  pmaxima $ map rdHeight tops

rdHOrd :: RDAG i -> RDAG i -> Ordering
rdHOrd r1 r2 = compare (rdHeight r1) (rdHeight r2)
\end{code}


We want to search by name
and get the relevant sub-rDAG, if it exists.
We will in fact generalise to searching a list of names
to get a list of rDAGs
\begin{eqnarray*}
   search &:& I \fun rDAG_{I} \fun [rDAG_{I}]
\\ search &:& I^* \fun rDAG_{I} \fun (rDAG_{I})^*
\end{eqnarray*}
\begin{code}
rdSearch :: Eq i => [i] -> RDAG i -> [RDAG i]

rdSearch ids root@(DRoot r)
 | r `elem` ids  =  [root]
 | otherwise     =  []

rdSearch ids node@(DNode n subn _)
 | n `elem` ids  = [node]
 | otherwise     = concat $ map (rdSearch ids) subn

rdSearch ids (DTop tops)
 = nubBy eqvRDAG $ concat $ map (rdSearch ids) tops
\end{code}

\newpage
Pruning maintains transitive non-redundancy,
by eliminating any descendants whose parents are already present.
\begin{code}
rdPrune :: Eq i => [RDAG i] -> [RDAG i]
rdPrune nodes
 = prune1 nodes `intsct` (reverse $ prune1 $ reverse nodes)
 where
    intsct = intersectBy eqvRDAG

   --prune1 :: Eq i => [RDAG i] -> [RDAG i]
    prune1 [] = []
    prune1 (node:nodes)
     | notsubnode  =  node:prune1 nodes
     | otherwise   =  prune1 nodes
     where
       asubnode = rdSearch [rdName node]
       notsubnode = null $ concat $ map asubnode nodes
-- end rdPrune
\end{code}


We want to build a stacked context for a node,
which is a sequence leading from it to the root,
through all its downstream nodes,
i.e., we include all parallel paths,
and maintain  order.
\begin{eqnarray*}
   stack &:& rDAG_I \fun I^+
\end{eqnarray*}
In effect we do a topological sort of the rDAG elements whose top
is the note of concern.
We shall consider a generalisation
that returns each element tagged with its height.
\begin{eqnarray*}
   stack &:& rDAG_I \fun (\Nat \times I )^+
\end{eqnarray*}
\begin{code}
rdStack :: Eq i => RDAG i -> [(Int,i)]
rdStack r = nub $ sortBy hord $ stk r
 where stk (DRoot i)         =  [(0,i)]
       stk (DTop tops)       =  stack tops
       stk (DNode i subn h)  =  (h,i) : (stack subn)

       stack rs = concat $ map stk rs

       sameelem (_,i1) (_,i2) = i1 == i2

       hord (h1,i1) (h2,i2)
               | h1 <  h2  =  GT
               | h1 >  h2  =  LT
               | i1 == i2  =  EQ
               | otherwise =  LT -- compare i2 i1
-- end rdStack
\end{code}
Now, a stratification function
that returns lists of lists of elements at the same level:
\begin{eqnarray*}
   stratify &:& rDAG_I \fun (I^+)^+
\end{eqnarray*}
\begin{code}
rdStratify :: Eq i => RDAG i -> [[i]]
rdStratify = hstratify . rdStack

hstratify
 = reverse . hstrat (-1) [] []
 where
   hstrat _  [] ees []  =  ees
   hstrat _  es ees []  =  es:ees
   hstrat ch es ees ((h,i):rest)
    | h == ch  = hstrat ch (i:es) ees rest
    | otherwise  =  hstrat h [i] ees' rest
    where
      ees' | null es    =  ees
           | otherwise  =  (reverse es):ees

rdNamesOf :: Eq i => RDAG i -> [i]
rdNamesOf = concat . reverse . rdStratify
\end{code}

Given an identifier, and RDAG,
it would be nice to know its immediate descendants:
\begin{eqnarray*}
  desc &:& I \fun RDAG_I \fun I^*
\end{eqnarray*}
\begin{code}
rdDesc :: Eq i => i -> RDAG i -> [i]
rdDesc i rdag
           = concat
             $ map (map rdId . rdAncs)
             $ rdSearch [i] rdag

rdAncs :: RDAG i -> [RDAG i]
rdAncs (DNode _ nds _) = nds
rdAncs _ = []

rdId :: RDAG i -> i
rdId (DRoot i)      =  i
rdId (DNode i _ _)  =  i
rdId (DTop _)       =  undefined
\end{code}


Given a node id, it can be useful to know all
its relatives (ancestors and descendants).
We ensure that descendants are returned in height order,
highest first.
\begin{code}
rdAncestors i   = fst . rdRelatives i
rdDescendants i = snd . rdRelatives i

rdRelatives :: Ord i => i -> RDAG i -> ([i],[i])
rdRelatives _ (DRoot _)  = ([],[])
rdRelatives _ (DNode _ _ _)  = ([],[])
rdRelatives i (DTop tops)
 = (ancs, nub $ map snd $ reverse $ sort rawrels)
 where
   (ancs,rawrels) = relMrg $ map (relsrch i []) tops

   relMrg = foldr relmrg norel
   norel = ([],[])
   (a1,d1) `relmrg` (a2,d2) = (nub (a1++a2), (d1++d2) )

   -- relsrch from top, looking for i, recording path followed
   -- relsrch :: t -> [t] -> RDAG t -> ([t],[(Int,t)])
   relsrch i ipath (DRoot r)
    | i == r     =  (ipath,[])
    | otherwise  =  norel
   relsrch i ipath (DNode j deps _)
    | i == j     =  (ipath,concat $ map rdStack $ deps)
    | otherwise  =  relMrg $ map (relsrch i (j:ipath)) deps
   relsrch _ _ (DTop _) = norel
\end{code}

When adding new links they can always be done to/from
any non-relative node:
\begin{code}
rdNonRelatives i rdag = rdNamesOf rdag \\ (i:(ancs++descs))
 where (ancs,descs) = rdRelatives i rdag
\end{code}


\newpage
\subsubsection{rDAG Construction}

The key principle here is that every RDAG at the top-level
is represented by a \texttt{DTop} constructor (even a root-only graph).
The root-node only appears in the DTop when it is the only node
in the graph.

We have two functions, \texttt{rdAdd} and \texttt{rdExtend} designed for internal use,
that add a new node in the first case, and a link in the second,
reporting various errors.
\begin{code}
data RDAGError i
 = RDAGOK
 | RDAGErr String i
 deriving (Eq,Show)

type RDAGRes i = Either (RDAGError i) (RDAG i)
\end{code}
% We define a monad instance for this
% \begin{code}
% -- IMPORTANT: INCOMPATIBLE LIBRARY CHANGES
% -- Data.Either has a Monad instance from 7.x.x onwards
% #if __GLASGOW_HASKELL__ < 700
% instance Monad (Either (RDAGError i)) where
%   return r = Right r
%   (Left e)  >>= _   =   Left e
%   (Right d) >>= f   =   f d
% #endif
% \end{code}


The general purpose builder function is \texttt{rdUpdate} that add nodes
and links as required, by calling \texttt{rdAdd} and \texttt{rdExtend}.


Now, the main builder functions.
\begin{code}
rdROOT :: i -> RDAG i
rdROOT i = DTop [DRoot i]
\end{code}
Code to return the root is also useful:
\begin{code}
rdGetRoot :: RDAG i -> RDAG i
rdGetRoot r@(DRoot _)         =  r
rdGetRoot (DNode _ (sn:_) _)  =  rdGetRoot sn
rdGetRoot (DTop (top:_))      =  rdGetRoot top
rdGetRoot rdag = error "rdGetRoot - can't find root"
\end{code}


\begin{eqnarray*}
   add &:& I \fun rDAG_I \fun rDAG_I
\\ pre\_add~i~r &\defs& i \notin r
\end{eqnarray*}
The code is more liberal,
but also reports back if the new node has a name clash,
or if requested names were unavailable.
This algorithm is designed to be thorough
and correct, rather than fast.
\begin{code}
rdAdd :: (Eq i,Show i) => i -> RDAG i -> RDAGRes i
rdAdd i top@(DTop tops)
 | nameclash      =  err "already present" i
 | otherwise      =  return $ DTop $ rdPrune $ add (DNode i [root] 1) tops
 where
   nameclash = not $ null $ rdSearch [i] top
   root = rdGetRoot top
   add node [DRoot _] = [node]
   add node tops      = node:tops

   err s i = Left $ RDAGErr s i

rdAdd i r = Left $ RDAGErr "Not a DTop!" i
\end{code}

\newpage
Once an element is in, we may wish to modify it
to point to other elements already present
and not a parent of oneself:
\begin{eqnarray*}
   link &:& I \fun I \fun RDAG_{I} \fun RDAG_{I}
\\ pre\_link~p~c~r &\defs& p \neq c \land p \in r \land p \neq root(r) \land c \in r \land c \notin ancs(p)
\end{eqnarray*}
\begin{code}
rdLink :: (Eq i,Show i) => i -> i -> RDAG i -> RDAGRes i
rdLink pid chid r
 | pid == chid        = err "Cannot link to itself" pid
 | null psrch         = err "Parent not present" pid
 | isroot pnode      = err "Root cannot be parent" pid
 | null chsrch        = err "Child not present" chid
 | not $ null pcsrch  = err "Child is parent" chid
 | not $ null cpsrch  = return r
 | otherwise          = return $ update pid pe newsub newh r
 where

  err s i = Left $ RDAGErr s i

  psrch = rdSearch [pid] r
  (pnode:_) = psrch

  root = rdGetRoot r
  isroot (DRoot _) = True
  isroot _ = False

  chsrch = rdSearch [chid] r
  cpsrch = rdSearch [chid] pnode
  (chnode:_) = chsrch
  pcsrch = rdSearch [pid] chnode
  (DNode pe subn ph) = pnode

  newsub = adjroot $ filter (not . isroot) (chnode:subn)
  adjroot [] = [root]
  adjroot subs = subs

  newh =  max ph (rdHeight chnode + 1)

  update tgtnm orige newsub newh r
   = u r
   where
     u (DTop tops) = DTop $ rdPrune $ (map u tops)
     u r@(DRoot _) = r
     u (DNode i sub h)
       | i == tgtnm  =  DNode orige newsub newh
       | otherwise    =  DNode i msub mh
       where
         msub = map u sub
         mh = (pmaxima $ map rdHeight msub)+1
\end{code}

\begin{code}
rdUpdate :: (Eq i,Show i) => i -> [i] -> RDAG i -> RDAGRes i
rdUpdate i deps rdag
 = case rdAdd i rdag of
    Left _  ->  dolinks i rdag deps
    Right rdag'  ->  dolinks i rdag' deps
 where
  dolinks i rdag [] = return rdag
  dolinks i rdag (dep:deps)
   = do rdag' <- rdLink i dep rdag
        dolinks i rdag' deps
\end{code}

It is also useful to output an RDAG as a list of tuples
indicating the immediate first level dependencies
of the whole graph, form the bottom upwards.
\begin{code}
rdToList :: Eq i => RDAG i -> [(i,[i])]
rdToList = map drop3rd . sortBy compare3rd . nub . rdlist
 where
  rdlist (DRoot i) = [(i,[],0)]
  rdlist (DNode i subn h)
                      = (i,map rdId subn,h):(concat $ map rdlist subn)
  rdlist (DTop tops) = concat $ map rdlist tops
  compare3rd (_,_,a) (_,_,b) = compare a b
  drop3rd (a,b,_) = (a,b)
\end{code}

The converse of this is code to construct an RDAG from
such a list of tuples:
\begin{code}
rdFromList :: (Eq i, Show i) => [(i,[i])] -> RDAGRes i
rdFromList [] = error "rdFromList: emptylist"
rdFromList ((r,[]):rest)
 = rdFrom (rdROOT r) rest
 where

  rdFrom rdag [] = return rdag

  rdFrom rdag ((n,deps):rest)
    = do rdag' <- rdUpdate n deps rdag
         rdFrom rdag' rest

rdFromList ((_,(d:_)):_) = Left $ RDAGErr "rdFromList: root has deps" d
\end{code}



Given a list of identifiers, build a linear rDAG from them
(top down):
\begin{code}
linRdFromList :: (Eq i, Show i) => [i] -> RDAGRes i
linRdFromList [] = error "linRdFromList: empty list"
linRdFromList [i] = return $ rdROOT i
linRdFromList (i:rest@(j:_))
 = do rdag <- linRdFromList rest
      rdUpdate i [j] rdag
\end{code}

\newpage
\subsubsection{rDAG Deconstruction}

Remove a top node:
\begin{code}
rdRemoveTop :: Eq i => i -> RDAG i -> RDAG i
rdRemoveTop i rdag@(DTop [DNode i' rs h])
 | i == i'  = DTop rs
rdRemoveTop i (DTop rs) = DTop (rdRem i rs)
 where
   rdRem :: Eq i => i -> [RDAG i] -> [RDAG i]
   rdRem _ [] = []
   rdRem i (r@(DNode i' rs' h):rs)
    | i == i'  =  rs'++rs
   rdRem i (r:rs)  =  r : rdRem i rs
rdRemoveTop _ rdag = rdag
\end{code}

\subsection{Random Stuff}

\begin{code}
indent 0 = " "
indent n = '.':(indent (n-1))

pmaxima :: (Ord a, Num a) => [a] -> a
pmaxima  =  maximum . (0:)
\end{code}
