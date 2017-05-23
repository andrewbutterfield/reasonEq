\section{Data Types}

\begin{code}
module AST where
\end{code}

\newpage
\subsection{Variables}

A variable has a \emph{name}.
\begin{code}
type Name = String -- no whitespace !
\end{code}

A variable will have one of the following \emph{kinds}:
\begin{description}
  \item[Observational]
    Corresponds to some observation that can be made of a program,
    and hence belongs, in UTP,  to the alphabet of the corresponding predicate.
  \item[Schematic]
    Stands for an arbitrary chunk of abstract syntax,
    of which we recognise two broad classes:
    \begin{description}
      \item[Expression] denotes an arbitrary expression
      \item[Predicate] denotes an arbitrary predicate
    \end{description}
  \item[Script]
    Represents an actual program variable itself,
    rather than any associated value it may take.
\end{description}
The above kinds all have different roles in the logic underlying UTP.

\begin{code}
data VKind = VObs
           | VExpr
           | VPred
           | VScript
           deriving (Eq, Ord, Show)
\end{code}

In addition, with most of the variable kinds above,
we can associate one of the following \emph{roles}:
\begin{description}
  \item[Static]
    variables whose values a fixed for the life of a (program) behaviour
  \item[Dynamic]
    variables whose values are expected to change over the life of a behaviour.
    \begin{description}
      \item[Pre]
        variables that record the values taken when a behaviour starts
      \item[Post]
        variables that record the values taken when a behaviour ends
      \item[Relational]
        Expression or Predicate variables that denote relations
        between the start and end of behaviours.
      \item[Intermediate]
        indexed variables that record values that arise between successive behaviours
    \end{description}
\end{description}
These distinct roles do not effect how the underlying logic handles
variables, but are used to tailor definitional shorthands that
assume that these are enacting the relevant UTP variable conventions.

\begin{code}
data VRole = VAny -- can play any role, useful for generic laws
           | VStatic
           | VPre
           | VPost
           | VRel          -- VExpr, VPred only
           | VInter String -- VObs, VList VObs only
           deriving (Eq, Ord, Show)
\end{code}


A variable has a name, kind and role:
\begin{code}
type Variable = ( Name
                , VKind
                , VRole
                )
\end{code}

Invariant:
\begin{enumerate}
  \item only kinds \texttt{VExpr} and \texttt{VPred} can have role \texttt{VRel}.
  \item only kind \texttt{VObs} can have role \texttt{VInter}.
\end{enumerate}
\begin{code}
invVariable reserved (name, kind, role, roots)
 = (role == VRel)    `implies`  (kind `elem` [VExpr,VPred])
   &&
   isVInter role     `implies`  (kind == VObs)

isVInter (VInter _) = True
isVInter _          = False
\end{code}

We also need to introduce the idea of lists of variables,
for use in binding constructs,
which may themselves contain special variables
that denote lists of variables.
We start by defining a list-variable as a variable with the addition
of a list of names, corresponding to variable `roots'
\begin{code}
type ListVar
 = ( Variable -- variable denoting a list of variables
   , [Name]   -- list of roots to be ignored)
   )
\end{code}
A variable-list is composed in general of a mix of normal variables
and list-variables.
We gather these into a `general' variable type
\begin{code}
data GenVar
 = V Variable -- regular variable
 | L ListVar  -- variable denoting a list of variables
 deriving (Eq, Ord, Show)
type VarList = [GenVar]
\end{code}

\newpage
\subsection{Substitutions}

Substitutions associate a list of things (types,expressions,predicates)
with some (quantified) variables.
We also want to allow list-variables of the appropriate kind
to occur for things, but only when the target variable is also
a list variable.
\begin{code}
type Substn v lv a
  =  ( [(v,a)]     -- target variable, then replacememt object
     , [(lv,lv)] ) -- target list-variable, then replacement l.v.
\end{code}

\subsection{Types}

For now, type variables are strings:
\begin{code}
type TVar = String
\end{code}

The ordering of data-constructors here is important,
as type-inference relies on it.
\begin{code}
data Type -- most general types first
 = Tarb
 | Tvar TVar
 | TApp String [Type]
 | Tfree String [(String,[Type])]
 | Tfun Type Type
 | Tenv
 | Z
 | B
 | Terror String Type
 deriving (Eq,Ord,Show)
\end{code}

\newpage
\subsection{Type-Tables}
When we do type-inference,
we need to maintain tables mapping variables to types.
Given the presence of binders/quantifiers,
these tables need to be nested.
We shall use integer tags to identify the tables:
\begin{code}
type TTTag = Int
\end{code}

At each level we have a table mapping variables to types,
and then we maintain a master table mapping type-table tags to such
tables:
\begin{code}
type VarTypes = Trie Type                -- Var -+-> Type
type TVarTypes = Trie Type               -- TVar -+-> Type
type TypeTables = Btree TTTag VarTypes
\end{code}
Quantifiers induce nested scopes which we capture as a list of
type-table tags. Tag 0 is special and always denotes the topmost global
table.


\newpage
\subsection{Terms}

We can posit a very general notion of terms ($t$),
within which we can also embed some other term syntax ($s$).
Terms are parameterised by a notion of constants ($k$)
and with some fixed notion of variables ($v$)
and a distinct notion of \emph{names} ($n$).
\begin{eqnarray*}
   n &\in& Names
\\ k &\in& Constants
\\ v &\in& Variables
\\ \ell &\in& GenVar
\\ vs \in VarList &=& (v | \ell)^*
\\ s &\in& Syntax (other)
\\ t \in Term~k~s
   &::=& k
\\ & | & v
\\ & | & n(t,\dots,t)
\\ & | & n~vs~@ (t,\dots,t)
\\ & | & t[t,\dots,t/v,\dots,v]
\\ & | & [s]
\end{eqnarray*}

So, we expect to have two mutually recursive instantiations
of terms: Expressions ($E$) and Predicates ($P$).
\begin{eqnarray*}
   E &\simeq& Term~\Int~P
\\ P &\simeq& Term~\Bool~E
\end{eqnarray*}

We need to consider zippers.
For term alone, assuming fixed $s$:
\begin{eqnarray*}
   t' \in Term'~k~s
   &::=& n(t,\dots,t,[\_]t,\dots,t)
\\ & | & n~vs~@ (t,\dots,t,[\_]t,\dots,t)
\\ & | & \_[t,\dots,t/v,\dots,v]
\\ & | & t[t,\dots,t,[\_]t,\dots,t/v,\dots,v,v,v,\dots,v]
\end{eqnarray*}
Intuitively, if we have descended into $s$, then
we should have $s'$ here.
So we really have:
\begin{eqnarray*}
   t' \in Term'~k~s
   &::=& n(t,\dots,t [\_]t,\dots,t)
\\ & | & n~vs~@ (t,\dots,t [\_]t,\dots,t)
\\ & | & \_[t,\dots,t/v,\dots,v]
\\ & | & t[t,\dots,t,[\_]t,\dots,t/v,\dots,v,v,v,\dots,v]
\\ & | & [s']
\end{eqnarray*}


\newpage
\subsection{Expressions}

We have a very simple expression abstract syntax
\begin{code}
data Expr
 = Num Int
 | Var Variable
 | App String [Expr]
 | Abs String TTTag VarList [Expr]
 | ESub Expr ESubst
 | EPred Pred
 deriving (Eq, Ord, Show)


n_Eerror = "EXPR_ERR: "
eerror str = App (n_Eerror ++ str) []

type ESubst = Substn Variable ListVar Expr

getESubstGenVar :: ESubst -> VarList
getESubstGenVar (vas, lvs) = map (V . fst) vas ++ map (L . fst) lvs
\end{code}

We need some builders that perform
tidying up for corner cases:
\begin{code}
mkEsub e ([],[]) = e
mkEsub e sub = ESub e sub
\end{code}

Useful to know when an expression is a variable:
\begin{code}
isVar :: Expr -> Bool
isVar (Var _)   =  True
isVar _         =  False

getVar :: Expr -> Variable
getVar (Var v)   =  v
getVar _         =  nulgVar
nulgVar  = ("",VScript,VStatic)

mgetVar :: Expr -> Maybe Variable
mgetVar (Var v)   =  Just v
mgetVar _         =  Nothing
\end{code}

\newpage
\subsection{Predicates}

Again, a very simple abstract syntax,
but with the add of a typing hook,
and an explicit 2-place predicate construct.
\begin{code}
data Pred
 = TRUE
 | FALSE
 | PVar Variable
 | PApp String [Pred]
 | PAbs String TTTag VarList [Pred]
 | Sub Pred ESubst
 | PExpr Expr
 | TypeOf Expr Type
 | P2 String ListVar ListVar
 deriving (Eq, Ord, Show)


n_Perror = "PRED_ERR: "
perror str = PApp (n_Perror ++ str) []

type PSubst = Substn Variable ListVar Pred
\end{code}

We define two constructor functions to handle
the \texttt{Expr}/\texttt{Pred} ``crossovers'':
\begin{code}
ePred (PExpr e)             =  e
ePred (PVar v)              =  Var v
ePred (Sub (PExpr e) sub)   =  ESub e sub
ePred pr                    =  EPred pr

pExpr (EPred pr)            =  pr
pExpr (Var v)               =  PVar v
pExpr (ESub (EPred pr) sub) =  Sub pr sub
pExpr e                     =  PExpr e
\end{code}

We also define smart constructors for certain constructs
to deal with corner cases.

THIS NEEDS TO GO TO A SPECIAL "builtins" MODULE

\begin{code}
n_Not = "Not"
mkNot p = PApp n_Not [p]

n_And = "And"
mkAnd [] = TRUE
mkAnd [pr] = pr
mkAnd prs = PApp "And" prs

n_Or = "Or"
mkOr [] = FALSE
mkOr [pr] = pr
mkOr prs = PApp "Or" prs

n_Eqv = "Eqv"
mkEqv pr1 pr2 = PApp n_Eqv [pr1,pr2]

n_Forall = "Forall"
mkForall ([]) p = p
mkForall qvs p = PAbs "Forall" 0 qvs [p]

n_Exists = "Exists"
mkExists ([]) p = p
mkExists qvs p = PAbs "Exists" 0 qvs [p]

n_Exists1 = "Exists1"
mkExists1 ([]) p = FALSE
mkExists1 qvs p = PAbs "Exists1" 0 qvs [p]

n_Univ = "Univ"
mkUniv p =  PAbs n_Univ 0 [] [p]

mkSub p ([],[]) = p
mkSub p sub = Sub p sub

n_Pforall = "Pforall"
mkPforall ([]) p  = p
mkPforall qvs p = PAbs "Pforall" 0 qvs [p]

n_Pexists = "Pexists"
mkPexists ([]) p  = p
mkPexists qvs p = PAbs "Pexists" 0 qvs [p]

n_Peabs = "Peabs"
mkPeabs ([]) p  = p
mkPeabs qvs p = PAbs "Peabs" 0 qvs [p]

n_Equal = "Equal"
mkEqual e1 e2 = App n_Equal [e1,e2]
\end{code}
Some query functions:
\begin{code}
isObs (PExpr _) = True
isObs _       = False
\end{code}

\newpage
\subsection{Quantifier Variables}

We want to be able to match predicates and expressions
against laws involving quantifiers in a flexible manner,
so we need to represent quantified variables, and lists of them
as well as variables that can match against these.
Generally we want to match against a specified list of
variables, and then ``all the rest''.

\subsection{Language Constructs}

We need to surround language elements by a syntax specification:
\begin{code}
data SynSpec
 = SSNull
 | SSTok String
 | SSObj String  -- Type, Expr, Pred, List, Tuple....
 | SSSep String
 deriving (Eq,Ord,Show)
\end{code}

A Language Specification is list of \texttt{SynSpec}:
\begin{code}
data LangSpec = LangSpec [SynSpec] deriving (Eq,Ord,Show)
\end{code}


\subsection{Equality}

These are old definitions used when type-table information
was stored in expressions and predicates
We want to define equality that ignores type-inference markings
(\texttt{TTTag}s).

We want to compare two predicates for equality,
 modulo ``liberal type equivalence''
\begin{code}
pequiv :: Pred -> Pred -> Bool

pequiv TRUE TRUE = True
pequiv FALSE FALSE = True
pequiv (PExpr e1) (PExpr e2) = e1 `eequiv` e2

pequiv (Sub pr1 sub1) (Sub pr2 sub2)
  = pr1 `pequiv` pr2 && sub1 `estlequiv` sub2

pequiv (PVar s1) (PVar s2) = s1==s2
pequiv (PAbs s1 _ qs1 prs1) (PAbs s2 _ qs2 prs2)
  = s1==s2 && qs1==qs2 && samelist pequiv prs1 prs2
pequiv (PApp s1 prs1) (PApp s2 prs2)
  = s1==s2 && samelist pequiv prs1 prs2

pequiv _ _ = False
\end{code}

And for expressions:
\begin{code}
eequiv :: Expr -> Expr -> Bool

eequiv (Num i1) (Num i2) = i1==i2
eequiv (Var v1) (Var v2) = v1==v2
eequiv (App s1 es1) (App s2 es2)
 = s1==s2 && samelist eequiv es1 es2
eequiv (Abs s1 _ qs1 es1) (Abs s2 _ qs2 es2)
 = s1==s2 && qs1==qs2 && samelist eequiv es1 es2
eequiv (ESub e1 sub1) (ESub e2 sub2)
 = e1 `eequiv` e2 && sub1 `estlequiv` sub2

eequiv _ _ = False
\end{code}

Substitution equivalence:
\begin{code}
estlequiv :: (Eq v, Eq lv) => Substn v lv Expr -> Substn v lv Expr -> Bool
(vas1, lvs1) `estlequiv` (vas2, lvs2)
  =  samelist (subpairequiv eequiv) vas1 vas2
     &&
     samelist (subpairequiv (==)) lvs1 lvs2

subpairequiv :: Eq v => (a -> a -> Bool) -> (v,a) -> (v,a) -> Bool
subpairequiv eqv (v1, a1) (v2, a2)  =  v1 == v2 && a1 `eqv` a2
\end{code}

For now:
\begin{code}
tequiv :: Type -> Type -> Bool
tequiv = (==)
\end{code}




\newpage
\subsection{Observation Variables}

UTP is based on the notion of alphabetised predicates,
which we support by maintaining information about
variables in the alphabet.
In addition to alphabet membership,
it is useful to be able to distinguish observation variables
that corresponds to program/specification variables ($Script$),
and those that describe other aspects of a languages behaviour ($Model$),
capturing the peculiarities of a given semantic model%
\footnote{
Often referred to in the literature, as \emph{auxiliary} variables
}.
\begin{code}
data OClass = Model | Script deriving (Eq,Ord,Show)

type ObsKind = (Variable,OClass,Type)
\end{code}

\subsubsection{Change Marker}
\begin{code}
data ChgMrk = Chgd | NoChg deriving (Eq,Show)

chgmrg Chgd _ = Chgd
chgmrg _ Chgd = Chgd
chgmrg _    _ = NoChg

chgmap f [] = ([],NoChg)
chgmap f (x:xs)
 = let (x',xchgd) = f x
       (xs',xschgd) = chgmap f xs
   in (x':xs',xchgd `chgmrg` xschgd)
\end{code}

\newpage
\subsection{Single Recursion Boilerplate}

The following routines ignore the mutual recursion,
and only cover a subset of most cases.

\subsubsection{Type Single Recursion}

\begin{code}
typeRec merge spec base ty
 = case spec ty of
     (Just res)  ->  res
     Nothing     ->  tRecurse ty
 where

  typerec = typeRec merge spec base

  tRecurse (Tfree _ fs) = merge $ map typerec $ concat $ map snd fs
  tRecurse (TApp _ ts) = merge $ map typerec ts
  tRecurse (Tfun ty1 ty2) = merge $ map typerec [ty1,ty2]
  tRecurse _ = base
\end{code}

\subsubsection{\texttt{Expr} Single Recursion}

\begin{code}
exprRec merge spec base ex
 = case spec ex of
     (Just res)  ->  res
     Nothing     ->  eRecurse ex
 where

  exprrec = exprRec merge spec base
  exprrec2 (de,re) = merge $ map exprrec [de,re]

  eRecurse (App _ exs) = merge $ map exprrec exs
  eRecurse (Abs _ _ _ exs) = merge $ map exprrec exs
  eRecurse (ESub ex ssub)
    = merge $ map exprrec (ex : getSubstObjs ssub)
  eRecurse _ = base
\end{code}

\subsubsection{\texttt{Pred} Single Recursion}

The use of this function is not currently recommended
when predicate-sets
are present.
\begin{code}
predRec merge spec base pr
 = case spec pr of
     (Just res)  ->  res
     Nothing     ->  pRecurse pr
 where

  predrec = predRec merge spec base

  pRecurse (Sub pr _) = predrec pr
  pRecurse (PAbs _ _ _ prs) = merge $ map predrec prs
  pRecurse (PApp _ prs) = merge $ map predrec prs
  pRecurse _ = base
\end{code}

\subsection{Mutual Recursion Boilerplate}

We shall describe the key concepts using the follow (singly-)recursive
datatype:
\begin{eqnarray*}
  D &::=&  K_0 | K_1 D | K_2 D^*
\end{eqnarray*}
where $K_i$ are the constructors (tags).

Over this datatype we may want to recursively define functions
with signatures as follows:
\begin{itemize}
  \item $D \fun A$
    \\ A straight recursive \emph{fold}.
  \item $D \fun D$
    \\ A straight recursive \emph{map}.
  \item $A \fun D \fun (D,A)$
    \\ A fusion of fold and map with an accumulator (\emph{accfuse}).
    \\ This can operate in two modes:
    \begin{itemize}
      \item parallel --- the $A$ parameter is passed identically to all
      sub-components, and the returned $A$ values are then merged (\emph{accpar})
      \item sequential --- the $A$ parameter is
          threaded in sequence through sub-componets
          with the final value being returned
          (\emph{accseq})
    \end{itemize}
\end{itemize}

\subsubsection{Recursion boilerplate: \emph{map}}

We want to define
\begin{eqnarray*}
   f &:& D \fun D
\\ f~K_0 &\defs& g~K_0
\\ f~(K_1~d) &\defs& K_1~(f~d)
\\ f~(K_2~\delta) &\defs& K_2~(f^*~\delta)
\end{eqnarray*}
The boilerplate:
\begin{eqnarray*}
   map~g~K_0 &\defs& g~K_0
\\ map~g~(K_1~d) &\defs& K_1~(map~g~d)
\\ map~g~(K_2~\delta) &\defs& K_2~((map~g)^*~\delta)
\end{eqnarray*}
We can write $f$ as:
\begin{eqnarray*}
  f &\defs& map~g
\end{eqnarray*}

\newpage
In practice we have two mutually recursive types,
\texttt{Pred} and \texttt{Expr},
so we pass in two functions, one for each datatype:
\begin{code}
mapPf :: (Pred -> (Pred,Bool), Expr -> (Expr,Bool)) -> Pred -> (Pred,Bool)
mapEf :: (Pred -> (Pred,Bool), Expr -> (Expr,Bool)) -> Expr -> (Expr,Bool)

run f e = f e

mapPf (fp,fe) (PExpr e) = (PExpr e', dif)
  where (e', dif) = fe e
mapPf (fp,fe) (Sub pr (vas, lvs)) = (Sub pr' (vas', lvs), dif1 || dif2)
  where
    (pr', dif1) = fp pr
    (vas', dif2) = mapSf fe vas

mapPf (fp,fe) (PAbs s ttts vs prs) = (PAbs s ttts vs prs', or difs)
  where (prs', difs) = unzip $ map (mapPf (fp,fe)) prs

mapPf (fp,fe) pr = (pr, False)

mapEf (fp,fe) (App s es) = (App s es', or difs)
  where (es',difs) = unzip $ map fe es
mapEf (fp,fe) (Abs s ttts qs es) = (Abs s ttts qs es', or difs)
  where (es',difs) = unzip $ map fe es
mapEf (fp,fe) (ESub e (vas, lvs)) = (ESub e' (vas', lvs), dif1 || dif2)
  where
    (vas', dif1) = mapSf fe vas
    (e', dif2) = fe e

mapEf (fp,fe) e = (e, False)

mapSf f vas = (vas', or dif)
  where (vas', dif) = unzip $ map (appSf f) vas

appSf f (v, a) =  ((v, a'), dif) where (a', dif) = f a
\end{code}

The intended usage is for the two functions
to handle the specific cases,
and then call \texttt{mapP}/\texttt{mapE} as appropriate
\begin{verbatim}
myPredMap TRUE = ...
myPredMap (Exists ...) = ...
myPredMap pr = mapP (myPredMap,myExprMap) pr
\end{verbatim}

Now the \texttt{mapP}/\texttt{E} boilerplate:
\begin{code}
mapP :: (Pred -> Pred,Expr -> Expr) -> Pred -> Pred
mapE :: (Pred -> Pred,Expr -> Expr) -> Expr -> Expr

mapP (fp,fe) (PExpr e) = PExpr (fe e)
mapP (fp,fe) (Sub pr (vas,lvs)) = Sub (fp pr) (mapsnd fe vas, lvs)

mapP (fp,fe) pr = pr

mapE (fp,fe) (App s es)    = App s (map fe es)
mapE (fp,fe) (Abs s ttts qs es) = Abs s ttts qs (map fe es)
mapE (fp,fe) (ESub e (vas, lvs))  = ESub (fe e) (mapsnd fe vas, lvs)
\end{code}

\newpage
\subsubsection{Recursion boilerplate: \emph{fold}}

We want to define
\begin{eqnarray*}
   f &:& D \fun A
\\ f~K_0 &\defs& g_0~K_0
\\ f~(K_1~d) &\defs& g_1~(f~d)
\\ f~(K_2~\delta) &\defs& g_2(f^*~\delta)
\end{eqnarray*}
The boilerplate:
\begin{eqnarray*}
   fold (g_0,g_1,g_2) K_0 &\defs& g_0~K_0
\\ fold (g_0,g_1,g_2) (K_1~d) &\defs& g_1~(fold (g_0,g_1,g_2)~d)
\\ fold (g_0,g_1,g_2) (K_2~\delta) &\defs& g_2~((fold(g_0,g_1,g_2))^*~\delta)
\end{eqnarray*}
We can write $f$ as:
\begin{eqnarray*}
  f &\defs& fold(g_0,g_1,g_2)
\end{eqnarray*}
In many cases we will have $g_1(a) = g_2\seqof a$.

As above, we have mutually recursive Pred and Expr to handle
so we need two function quadruples:
\begin{code}
type PFold a = (a,Pred -> a,a -> a,[a]->a)
type EFold a = (a,Expr -> a,a -> a,[a]->a)
foldP :: (PFold a,EFold a) -> Pred -> a
foldE :: (PFold a,EFold a) -> Expr -> a
\end{code}

Folding over predicates:
\begin{code}
foldP pef@((pa,f0,f1,f2),(ea,g0,g1,g2)) pr
 = f pr
 where
  f (PApp s prs) = f2 $ map f0 prs
  f (PAbs s ttts qvs prs) = f2 $ map f0 prs
  f (PExpr e) = f1 $ g0 e
  f (Sub p (avs, _)) = f2 (f0 p : map (g0 . snd) avs)

  f pr = pa -- recursion must stop here !
\end{code}

Folding over Expressions:
\begin{code}
foldE pef@((pa,f0,f1,f2),(ea,g0,g1,g2)) e
 = f e
 where
  f (App s es) = g2 $ map g0 es
  f (Abs s ttts qvs es) = g2 $ map g0 es
  f (ESub e (avs, _)) = g2 (g0 e : map (g0 . snd) avs)

  f e = ea -- recursion must stop here !
\end{code}

\subsubsection{Debugging}

\begin{code}
instance Dshow Pred  where dshow = debugPshow
instance Dshow Expr  where dshow = debugEshow
instance Dshow Type  where dshow = debugTshow
instance Dshow SideCond where dshow sc = "SC"

instance (Dshow a,Dshow b) => Dshow (a,b) where
 dshow (a,b) = "FIRST:\n"++dshow a++"\nSECOND\n"++dshow b

debugPshow pr = dbgPshow 0 pr

debugEshow  =  dbgEshow 0

debugTshow  =  dbgTshow 0

debugLshow (LangSpec ss)
 =  "LANGSPEC"
    ++ concat (map (dbgSSshow 1) ss)

debugAshow (pr,sc)
 = "ASSERTION"
    ++ dbgPshow 3 pr
    ++ dbgSCshow 1 sc

hdr i  = '\n':(replicate i ' ')

dbgPshow i  TRUE     = hdr i ++ "TRUE"
dbgPshow i  FALSE    = hdr i ++ "FALSE"
dbgPshow i  (PVar pv) = hdr i ++ "PVAR "++dbgVshow pv
dbgPshow i  (PExpr e)  = hdr i ++ "PEXPR " ++ dbgEshow (i+1) e
dbgPshow i  (TypeOf e t)
 = hdr i ++ "TYPEOF " ++ dbgEshow (i+1) e ++ dbgTshow (i+1) t
dbgPshow i  (PApp nm prs)
 = hdr i ++ "PAPP " ++ nm ++ concat (map (dbgPshow (i+1)) prs)
dbgPshow i  (PAbs nm tts qs prs)
 = hdr i ++ "PABS " ++ nm ++ show tts
   ++ dbgQSshow (i+1) qs
   ++ concat (map (dbgPshow (i+1)) prs)
dbgPshow i  (Sub pr sub)
 = hdr i ++ "SUB" ++ dbgPshow (i+1) pr ++ dbgESshow (i+1) sub
dbgPshow i  (P2 nm lv1 lv2)
 = hdr i ++ "P2 " ++ nm ++ ' ':dbgLVshow lv1 ++ ' ':dbgLVshow lv2

dbgSSshow i SSNull      = hdr i ++ "SSNULL"
dbgSSshow i (SSTok s)   = hdr i ++ "SSTOK "  ++ s
dbgSSshow i (SSSep s)   = hdr i ++ "SSSEP "  ++ s

dbgEshow i (Num n)         = hdr i ++ "NUM "++show n
dbgEshow i (Var v)         = hdr i ++ "VAR " ++ dbgVshow v
dbgEshow i (App s es)
 = hdr i ++ "APP "++s++concat (map (dbgEshow (i+1)) es)
dbgEshow i (Abs s tts qs es)
 = hdr i ++ "ABS "++s++" "++show tts
   ++ dbgQSshow (i+1) qs
   ++ concat (map (dbgEshow (i+1)) es)
dbgEshow i (ESub e sub)
 = hdr i ++ "ESUB "  ++ dbgEshow (i+1) e ++ dbgESshow (i+1) sub
dbgEshow i  (EPred pr)  = hdr i ++ "EPRED " ++ dbgPshow (i+1) pr

dbgKshow VObs = "VOBS"
dbgKshow VExpr = "VEXP"
dbgKshow VPred = "VPRD"
dbgKshow VScript = "VSCRPT"

dbgRshow VStatic = "VSTATIC"
dbgRshow VPre = "VPRE"
dbgRshow VPost = "VPOST"
dbgRshow VRel = "VREL"
dbgRshow (VInter s) = "VINTER "++s

dbgVshow (n,k,r) = dbgKshow k
                   ++ ' ':n
                   ++ ' ':dbgRshow r

dbgVSshow vs = "<"
               ++ (concat $ intersperse ">, <" $ map dbgVshow vs)
               ++ ">"

debugQSshow :: VarList -> String
debugQSshow = dbgQSshow 0

dbgQSshow i ( [])  = hdr i ++ "VARS(empty)"
dbgQSshow i ( qs)
 = hdr i ++ "VARS:"
   ++ (concat $ map ( (hdr (i+1) ++) . dbgGVshow ) qs)

dbgGVshow (V v) = "V " ++ dbgVshow v
dbgGVshow (L lv) = "L " ++ dbgLVshow lv

dbgLVshow (v, ns) = '[':dbgVshow v ++ " LESS " ++ show ns ++ "]"

dbgMshow i (x,y) = hdr i ++ "DOM" ++ dbgEshow (i+1) x ++ hdr i ++ "RNG" ++ dbgEshow (i+1) y

dbgESshow :: Int -> ESubst -> String
dbgESshow i (vas, lvs)
  = hdr i ++ "E-VAS"
      ++ dbgPAIRSshow dbgVshow (dbgEshow (i+1)) (i+1) vas
      ++ hdr i ++ "E-LVS"
      ++ dbgPAIRSshow dbgLVshow dbgLVshow (i+1) lvs

dbgPAIRSshow :: (a -> String)
         -> (b -> String )
         -> Int -> [(a,b)]
         -> String
dbgPAIRSshow sha shb i  [] = ""
dbgPAIRSshow sha shb i  ((a,b):rest)
 = hdr i ++ sha a ++ " |-> " ++ shb b
   ++ dbgPAIRSshow sha shb i rest

dbgTshow i Tarb = hdr i ++ "TARB"
dbgTshow i (Tvar s) = hdr i ++ "TVAR "++s
dbgTshow i (TApp s ts) = hdr i ++ "TAPP "++s ++ concat(map (dbgTshow (i+1)) ts)
dbgTshow i (Tfree s cs) = hdr i ++ "TFREE "++s ++ concat(map (dbgFshow (i+1)) cs)
dbgTshow i (Tfun t1 t2) = hdr i ++ "TFUN" ++ dbgTshow (i+1) t1 ++ dbgTshow (i+1) t2
dbgTshow i Tenv = hdr i ++ "TENV"
dbgTshow i Z = hdr i ++ "TINT"
dbgTshow i B = hdr i ++ "TBOOL"
dbgTshow i (Terror s t) = hdr i ++ "TERROR "++s++dbgTshow (i+1) t

dbgFshow i (s,ts) = hdr i ++ "CONS "++s++concat(map (dbgTshow (i+1)) ts)

dbgSCshow i SCtrue
  =  hdr i ++ "SC-TRUE"
dbgSCshow i (SCisCond mtyp str)
  =  hdr i ++ "SC-ISCOND "++show mtyp++" "++str
dbgSCshow i (SCnotFreeIn mtyp qs str)
  =  hdr i ++ "SC-NOTFREEIN "++show mtyp++" "++dbgVSshow qs++" "++str
dbgSCshow i (SCareTheFreeOf mtyp qs str)
  =  hdr i ++ "SC-ARETHEFREEOF "++show mtyp++" "++dbgVSshow qs++" "++str
dbgSCshow i (SCcoverTheFreeOf mtyp qs str)
  =  hdr i ++ "SC-COVERTHEFREEOF "++show mtyp++" "++dbgVSshow qs++" "++str
dbgSCshow i (SCfresh mtyp str)
  =  hdr i ++ "SC-FRESH "++show mtyp++" "++dbgVshow str
dbgSCshow i (SCAnd scs)
  =  hdr i ++ "SC-AND" ++ concat(map (dbgSCshow (i+1)) scs)
\end{code}


\newpage
\subsection{Side-Conditions}

A side-condition is a syntactic property,
and therefore in principle ought to be statically checkable.
\begin{code}
data MType = ObsM | TypeM | ExprM | PredM deriving (Eq,Ord)

instance Show MType where
  show ObsM = "O"
  show TypeM = "T"
  show ExprM = "E"
  show PredM = "P"

data SideCond
 = SCtrue
 | SCisCond MType String                     -- Mvar
 | SCnotFreeIn MType [Variable] String       -- Qvars, Mvar
 | SCareTheFreeOf MType [Variable] String    -- Qvars, Mvar
 | SCcoverTheFreeOf MType [Variable] String  -- Qvars, Mvar
 | SCfresh MType Variable                    -- ObsM for now
 | SCAnd [SideCond]
 deriving (Eq,Ord,Show)
