\chapter{Abstract Syntax}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017-2024

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module AST ( Type
           , isAtmType
           , bool, arbpred
           , pattern ArbType,  pattern TypeVar, pattern TypeCons
           , pattern AlgType, pattern FunType, pattern GivenType
           , pattern BottomType
           , isPType, isEType
           , isSubTypeOf
           , Value, pattern Boolean, pattern Integer
           , TermSub, TermSubs, LVarSub, LVarSubs
           , Substn, pattern Substn, substn, substnxx
           , pattern TermSubs, pattern LVarSubs
           , setVTWhen, setLVLVWhen
           , subVarLookup, subLVarLookup, isNullSubstn, subTargets
           , Term, Subable, readTerm
           , pattern Val, pattern Var, pattern Cons
           , pattern Bnd, pattern Lam, pattern Cls
           , pattern Sub, pattern Iter, pattern Typ
           , var,  eVar,  pVar
           , bnd, eBnd, pBnd
           , lam,  eLam,  pLam
           , binderClass
           , termtype, settype
           , isVar, isExpr, isPred, isAtomic
           , theVar, theGVar, varAsTerm, termAsVar
           , icomma, lvarCons
           , assignmentId
           , assignVar, isAssignVar, theAssignment, isAssignment
           , subTerms
           , mentionedVars, mentionedVarLists, mentionedVarSets
           , onlyTrivialQuantifiers, anyTrivialSubstitution
           , termSize
           -- test only below here
           , int_tst_AST
           , jSub, jVar, jBnd, jLam, jeVar, jpVar, jSubstn, xSubstn
           ) where
import Data.Char
import Data.List
import Data.Maybe (fromJust)
import Data.Set(Set)
import qualified Data.Set as S
import Data.Map(Map)
import qualified Data.Map as M

import Utilities
import LexBase
import Variables

import Test.HUnit
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
--import Test.Framework.Providers.QuickCheck2 (testProperty)

import Debugger
\end{code}

\section{AST Introduction}

We implement a abstract syntax tree for a notion of ``terms''
that cover both expressions and predicates.
We also provide a side-condition language.

\newpage
\section{Types}

Types are a restrictive form of terms,
whose main reason here is to prevent large numbers of spurious matches
occurring with expressions.

\begin{code}
data Type -- most general types first
 = T  -- arbitrary type -- top of sub-type relation
 | TV Identifier -- type variable
 | TC Identifier [Type] -- type constructor, applied
 | TA Identifier [(Identifier,[Type])] -- algebraic data type
 | TF Type Type -- function type
 | TG Identifier -- given type
 | TB -- bottom type,  bottom of sub-type relation
 deriving (Eq, Ord, Show, Read)

isAtmType :: Type -> Bool
isAtmType T       =  True
isAtmType (TV _)  =  True
isAtmType (TG _)  =  True
isAtmType TB      =  True
\end{code}
The ordering of data-constructors here is important,
as type-matching relies on it.


\begin{code}
pattern ArbType = T
pattern TypeVar i  = TV i
pattern TypeCons i ts = TC i ts
pattern AlgType i fs = TA i fs
pattern FunType tf ta = TF tf ta
pattern GivenType i = TG i
pattern BottomType = TB

bool  = TG $ jId $ "B"
arbpred = TF TB bool

-- isPtype t if t has shape  t1 -> t2 -> ... -> tn -> bool
-- which is really t1 -> (t2 -> (... -> (tn -> bool)...))
lasttype (TF _ ta)  =  lasttype ta
lasttype t          =  t

isPType (TF _ t)  =  lasttype t == bool
isPType _         =  False
isEType           =  not . isPType
\end{code}

\subsection{Sub-Typing}

We want a pattern of type $\bot \fun \Bool$
to match a candidate of type $t \fun (\Set t \fun \Bool)$.
We might try asking is the candidate a subtype of the pattern?
$$ t \fun (\Set t \fun \Bool)  \subseteq \bot \fun \Bool$$
However a simple contravariant test won't work.
as it as it requires:
$$ \bot \subseteq t 
   \quad\land\quad
   (\Set t \fun \Bool)  \subseteq \Bool
$$
The first test always succeeds, but the second does not in this case.
What we want is that any function-type whose "last" input is boolean,
can match a pattern of type $\bot \fun \Bool$.
We can generalise $\Bool$ to be any type.

So, given a function $\bot \fun t$ we define "sub-typing" as follows:
$$
t_1 \fun t_2 \fun \dots \fun t_n \fun t'
\subseteq
\bot \fun t, \qquad \IF \quad t' \subseteq t
$$
Here neither $t$ nor $t'$ are function types.


\begin{code}
isSubTypeOf :: Type -> Type -> Bool
isSubTypeOf (TF tf1 ta1) (TF TB ta2)   =  lasttype ta1 `isSTOf` ta2
isSubTypeOf t1           t2            =  t1 `isSTOf` t2

isSTOf :: Type -> Type -> Bool
-- normal subtyping
-- true outcomes first, to catch t==t case

_       `isSTOf` T        =  True
T       `isSTOf` _        =  False
TB      `isSTOf` _        =  True
_       `isSTOf` TB       =  False

_       `isSTOf` (TV _)   =  True
(TG i1) `isSTOf` (TG i2)  =  i1 == i2

(TC i1 ts1) `isSTOf` (TC i2 ts2) | i1==i2 = ts1 `areSTOf` ts2
(TA i1 fs1) `isSTOf` (TA i2 fs2) | i1==i2 = fs1 `areSFOf` fs2

(TF tf1 ta1) `isSTOf` (TF tf2 ta2)  
                             =  tf2 `isSTOf` tf1 && ta1 `isSTOf` ta2

_ `isSTOf` _       = False
\end{code}


\begin{code}
areSTOf :: [Type] -> [Type] -> Bool -- are SubTypesOf
[]       `areSTOf` []        =  True
(t1:ts1) `areSTOf` (t2:ts2)  =  t1 `isSTOf` t2 && ts1 `areSTOf` ts2
_        `areSTOf` _         =  False
\end{code}

\begin{code}
-- areSubFieldsOf
areSFOf :: [(Identifier,[Type])] -> [(Identifier,[Type])] -> Bool
[] `areSFOf` []  =  True
((i1,ts1):fs1) `areSFOf` ((i2,ts2):fs2)
 | i1 == i2             =  ts1 `areSTOf` ts2 && fs1 `areSFOf` fs2
_ `areSFOf` _    =  False
\end{code}

\newpage
\section{Substitutions}

Substitutions associate a list of terms (types,expressions,predicates)
with some variables.
We also want to allow list-variables of the appropriate kind
to occur for things, but only when the target variable is also
a list variable.
\begin{code}
type TermSub  = (Variable,Term) -- target, then replacememt 
type TermSubs = Set TermSub
type LVarSub  = (ListVar,ListVar) -- target, then replacement
type LVarSubs = Set LVarSub
data Substn --  pair-sets below are unique in fst part
  = SN TermSubs LVarSubs
  deriving (Eq,Ord,Show,Read)
\end{code}

Patterns:
\begin{code}
pattern Substn ts lvs  <-  SN ts lvs
pattern TermSubs ts     <-  SN ts _
pattern LVarSubs lvs    <-  SN _  lvs
\end{code}

Builders: we have two variants, one (\verb"substn"), the most generally useful, 
removes trivial substitutions ($[x/x]$),
while another (\verb"substnxx"), for special situations, retains them.
\begin{code}
substn :: MonadFail m => [(Variable,Term)] -> [(ListVar,ListVar)]
       -> m Substn
substn ts lvs
 | null ts && null lvs  =  return $ SN S.empty S.empty
 | dupKeys ts'          =  fail "Term substitution has duplicate variables."
 | dupKeys lvs'         =  fail "List-var subst. has duplicate variables."
 | otherwise            =  return $ SN (S.fromList ts') (S.fromList lvs')
 where  
  ts'  = filter nontrivial     $ sort ts
  lvs' = filter (uncurry (/=)) $ sort lvs

substnxx :: MonadFail m => [(Variable,Term)] -> [(ListVar,ListVar)]
       -> m Substn
substnxx ts lvs
 | null ts && null lvs  =  return $ SN S.empty S.empty
 | dupKeys $ sort ts    =  fail "Term substitution has duplicate variables."
 | dupKeys $ sort lvs   =  fail "List-var subst. has duplicate variables."
 | otherwise            =  return $ SN (S.fromList ts) (S.fromList lvs)

nontrivial :: (Variable,Term) -> Bool
nontrivial (v,Var _ v')  =  v /= v'
nontrivial _             =  True

dupKeys :: Eq a => [(a,b)] -> Bool
-- assumes list is ordered
dupKeys ((a1,_):next@((a2,_):_))  =  a1 == a2 || dupKeys next
dupKeys _                         =  False
\end{code}

Use carefully:
\begin{code}
jSubstn ts lvs = fromJust $ substn ts lvs
xSubstn ts lvs = fromJust $ substnxx ts lvs
\end{code}

Queries:
\begin{code}
subVarLookup :: MonadFail m => Substn -> Variable -> m Term
subVarLookup (SN ts _) v  = alookup v $ S.toList ts

subLVarLookup :: MonadFail m => Substn -> ListVar -> m ListVar
subLVarLookup (SN _ lvs) lv  = alookup lv $ S.toList lvs

isNullSubstn :: Substn -> Bool
isNullSubstn (SN ts lvs) = S.null ts && S.null lvs

subTargets :: Substn -> VarSet
subTargets (SN ts lvs)
  = S.map (StdVar . fst) ts
    `S.union`
    S.map (LstVar .fst) lvs
\end{code}

Setters:
\begin{code}
setVTWhen :: VarWhen -> (Variable,Term) -> (Variable,Term)
setVTWhen vw (tv,Var typ rv)  =  (setVarWhen vw tv, jVar typ $ setVarWhen vw rv)
setVTWhen _ (tv,rt)          =  error ("setVTWhen: term is not a variable.")

setLVLVWhen :: VarWhen -> (ListVar,ListVar) -> (ListVar,ListVar)
setLVLVWhen vw (tlv,rlv)  =  (setLVarWhen vw tlv, setLVarWhen vw rlv)
\end{code}

Tests for substitution construction:
\begin{code}
i_a = fromJust $ ident "a"
i_b = fromJust $ ident "b"
i_e = fromJust $ ident "e"
i_f = fromJust $ ident "f"
i_v = fromJust $ ident "v"
i_P = fromJust $ ident "P"
i_Q = fromJust $ ident "Q"

lva = ObsLVar  Before (i_a) [] []
lvb = ObsLVar  After  (i_b) [] []
lve = ExprLVar Before (i_e) [] []
lvf = ExprLVar Before (i_f) [] []

lvs_ord_unq = [(lva,lvf),(lvb,lve)]
test_substn_lvs_id = testCase "LVarSubs ordered, unique"
 ( substn [] lvs_ord_unq  @?= Just (SN S.empty (S.fromList lvs_ord_unq)) )

lvs_unord_unq = [(lvb,lve),(lva,lvf)]

test_substn_lvs_sort = testCase "LVarSubs unordered, unique"
 ( substn [] lvs_unord_unq  @?= Just (SN S.empty (S.fromList lvs_ord_unq)) )

lvs_unord_dup = [(lva,lva),(lvb,lve),(lva,lvf)]

test_substn_lvs_dup = testCase "LVarSubs with duplicates"
 ( substn [] lvs_unord_dup  @?= Nothing )

substnTests = testGroup "AST.substn"
               [ test_substn_lvs_id
               , test_substn_lvs_sort
               , test_substn_lvs_dup
               ]
\end{code}


\newpage
\section{Terms}

We want to implement a collection of terms that include
expressions and predicates defined over a range of variables
that can stand for behaviour observations, terms and program variables.


We consider a term as having the following forms:
\begin{description}
  \item [K] A constant value of an appropriate type:
    $\K k$ or $\kk k$.
  \item [V] A variable:
    $\V v$ or $\vv v$.
  \item [C] A constructor that builds a term out of zero or more sub-terms:
    $\C n {ts}$, $\cc n {ts}$,
    $\C {\!\oplus\!} {ts}$ or $t_1 \oplus t_2 \oplus \dots \oplus t_n$.
  \item [B] A binding construct that introduces sets of local variables:
    $\B n {v^+} t$ or $\bb n {v^+} t$.
  \item [L] A binding construct that introduces lists of local variables:
    $\L n {v^+} t$ or $\ll n {v^+} t$.
  \item [X] A closure construct that hides all free variables:
    $\X n t$ or $\xx n t$.
  \item [S] A term with an explicit substitution of general variables
  by replacement items. Standard variables get replaced by terms,
  while List variables get replaced by set or lists of general variables.
    $\S t v r$, $\ss t {v^n} {r^n}$ or $t\sigma$.
  \item [I] An iteration of a term over a sequence of list-variables:
    $\I \oplus n {lv^+}$ or $\ii \bigoplus n {lvs}$.
  \item [T] An embedding of Types: $\T \tau$ or $\tt\tau$.
\end{description}

\begin{eqnarray*}
   k &\in& Value
\\ n &\in& Name
\\ \tau &\in& Type
\\ v &\in& Var = \dots
\\ t \in T  &::=&  \K k
                ~|~ \V v
                ~|~ \C n {t^*}
                ~|~ \B n {v^+} T
                ~|~ \L n {v^+} T
                ~|~ \S t V R
                ~|~ \X n t
                ~|~ \I \oplus n {lv^+}
                ~|~ \T \tau
\\ &=& \kk k
     ~|~ \vv v
     ~|~ \cc n {ts}
     ~|~ \bb n {v^+} t
     ~|~ \ll n {v^+} t
     ~|~ \ss t {v^n} {r^n}
     ~|~ \xx n t
     ~|~ \ii \bigoplus n {lvs}
     ~|~ \tt \tau
\end{eqnarray*}
We need to distinguish between predicate terms and expression terms.
The key difference is that predicates are all of ``type'' $Env \fun \Bool$,
whereas expressions can have different types.
This means that expression matching requires type information,
while that for predicates does not.


\subsection{Values}

For predicates,
the only constants we require are $\True$ and $\False$.
For expressions, the situation is more complicated,
at least as far as `basic' values are concerned.
With the types as proposed (esp. \verb"TA"),
and the term constructors and bindings,
we could develop values from the ground up,
but we would much prefer to have some built-in,
like numbers of various kinds, and maybe characters?
For now we start with booleans and integers.
\begin{code}
data Value
  = VB Bool
  | VI Integer
  deriving (Eq, Ord, Show, Read)

pattern Boolean b  =  VB b
pattern Integer i  =  VI i
\end{code}


\subsection{Expressions vs. Predicates}

Do we have mutually recursive datatypes or an explicit tag?

With mutually recursive types
we know which we are handling and just match the appropriate patterns,
except,
we need to embed each in the other,
so there always has to be a case which looks for such an embedding
and handles it.

With one recursive type we need to check the expr/predicate tag,
but no longer know that we have one kind of term or the other.

From a coding point of view, given pattern synonyms in particular,
there is little to differentiate the two approaches.
The one exception is the ``zipper'' used to focus in on sub-predicates
and sub-expressions.
This is much simplified by having a unified notion of ``term''.
We identify predicates as terms whose type has the form $t \fun \Bool$.

\newpage
\subsection{Terms}

We have a single term type (\verb"Term"),
with an predicate/expression annotation.
\begin{code}
data Term
 = K Type Value                      -- Value
 | V Type Variable                   -- Variable
 | C Type Subable Identifier [Term]  -- Constructor
 | B Type Identifier VarSet Term     -- Binder (unordered)
 | L Type Identifier VarList Term    -- Binder (ordered)
 | X Identifier Term                     -- Closure (always a predicate)
 | S Type Term Substn                -- Substitution
 | I Type                            -- Iterator
     Subable Identifier  -- top grouping constructor
     Subable Identifier  -- component constructor, with arity a
     [ListVar]   -- list-variables, same length as component arity
 | ET Type                               -- Embedded TypeVar
 deriving (Eq, Ord, Show, Read)

type Subable = Bool  -- True if we can substitute into sub-terms

readTerm :: String -> Term
readTerm = read
\end{code}

We  need to have a correlation between some terms
and the variables they use.
In particular the \texttt{Type} of a \texttt{V} \texttt{Term}
will have to correspond to the \texttt{VarClass} value of the variable.
Also, in binding constructs,
all the general variables being bound will have to agree on \texttt{VarClass}.

Neutral patterns:
\begin{code}
pattern Val  typ k                =   K typ k
pattern Var  typ v                <-  V typ v
pattern Cons typ sb n ts          =   C typ sb n ts
pattern Bnd  typ n vs tm          <-  B typ n vs tm
pattern Lam  typ n vl tm          <-  L typ n vl tm
pattern Cls      n    tm          =   X n tm
pattern Sub  typ      tm s        =   S typ tm s
pattern Iter typ sa na si ni lvs  =   I typ sa na si ni lvs
pattern Typ  typ                  =   ET typ
\end{code}



Smart constructors for variables and binders.

Variable must match term-class.
\begin{code}
var :: MonadFail m => Type -> Variable -> m Term
var tp@(TF _ t) v | t == bool && isPredVar v  =  return $ V tp v
var typ       v   | not $ isPredVar v         =  return $ V typ v
var _       _   =   fail "var: Type/VarClass mismatch"
eVar t v = var t v
pVar t v = var arbpred v
\end{code}

\newpage
All variables in a binder variable-set must have the same class.
\begin{code}
bnd typ n vs tm
 | S.null vs  =  return tm  -- vacuous binder
 | uniformVarSet vs  =  return $ B typ n vs tm
 | otherwise = fail "bnd: var.-set has mixed variables."

eBnd typ n vs tm  =  bnd typ n vs tm
pBnd     n vs tm  =  bnd arbpred       n vs tm
\end{code}

All variables in a lambda variable-list must have the same class.
\begin{code}
lam typ n vl tm
 | null vl  =  return tm  -- vacuous binder
 | uniformVarList vl  =  return $ L typ n vl tm
 | otherwise = fail "lam: var.-list has mixed variables."

eLam typ n vl tm  =  lam typ n vl tm
pLam     n vl tm  =  lam arbpred       n vl tm
\end{code}

\begin{code}
uniformVarSet s = uniformVarList $ S.toList s

uniformVarList [] = True
uniformVarList [_] = True
uniformVarList (gv:vl) = uvl (whatGVar gv) vl
 where
   uvl _ [] = True
   uvl what (gv:vl)
     | whatGVar gv == what  =  uvl what vl
     | otherwise            =  False
\end{code}

It will also be good to enquire the class of a binder:
\begin{code}
binderClass :: MonadFail m => Term -> m VarClass
binderClass (L _ _ (gv:_) _)  =  return $ whatGVar gv
binderClass (B _ _ gvs    _)  =  return $ whatGVar $ S.elemAt 0 gvs
binderClass _ = fail "binderClass: not a binding term."
\end{code}


It can help to test if a term is an variable, expression or predicate:
\begin{code}
termtype :: Term -> Type
termtype (Val typ k)                 =  typ
termtype (Var typ v)                 =  typ
termtype (Cons typ sb n ts)          =  typ
termtype (Bnd typ n vl tm)           =  typ
termtype (Lam typ n vs tm)           =  typ
termtype (Cls i _)                   =  arbpred
termtype (Sub typ tm s)              =  typ
termtype (Iter typ sa na si ni lvs)  =  typ

settype :: Type -> Term -> Term
settype typ (Val _ k)                 =  (Val typ k)
settype typ (Var _ v)                 =  fromJust $ var typ v
settype typ (Cons _ sb n ts)          =  (Cons typ sb n ts) 
settype typ (Bnd _ n vs tm)           =  fromJust $ bnd typ n vs tm 
settype typ (Lam _ n vl tm)           =  fromJust $ lam typ n vl tm 
settype typ (Sub _ tm s)              =  (Sub typ tm s)     
settype typ (Iter _ sa na si ni lvs)  =  (Iter typ sa na si ni lvs)
settype _ t                          =  t

isVar, isExpr, isPred, isAtomic :: Term -> Bool
isVar (Var _ _) = True ; isVar _ = False
isExpr t
  = case termtype t of 
     (TF _ t) | t == bool -> False
     _                    -> True
isPred = not . isExpr
isAtomic (K _ _)  =  True
isAtomic (V _ _)  =  True
isAtomic _        =  False
\end{code}

Pulling out variables:
\begin{code}
theVar :: Term -> Variable
-- pre-theVar t  =  isVar t
theVar (V _ v)  =  v
theGVar :: Term -> GenVar
theGVar = StdVar . theVar
\end{code}

Lifting a variable to a term:
\begin{code}
varAsTerm :: Variable -> Term
varAsTerm v@(PredVar _ _)  =  V arbpred     v
varAsTerm v                =  V T v
\end{code}

Dropping a term (safely) to a variable:
\begin{code}
termAsVar :: MonadFail m => Term -> m Variable
termAsVar (V _ v) = return v
termAsVar t = fail ("termAsVar: not a variable - "++show t)
\end{code}

Using \texttt{Iter} for a construct built from a list of list-variables
\begin{code}
icomma = jId ","
lvarCons typ ni lvs = Iter typ True icomma True ni lvs
\end{code}

In \cite{UTP-book} we find the notion of texts, in chapters 6 and 10.
This has yet to be addressed.

\subsection{Assignment}

We represent (simultaneous) assignment (e.g $x,\lst y := e,\lst f$)
using the substitution form, 
\\ as $(:=)[e,\lst f/x,\lst y]$.

\begin{code}
assignmentId             =  jId ":="
assignVar                =  ScriptVar assignmentId 
isAssignVar (Vbl i _ _)  =  i == assignmentId
theAssignment            =  varAsTerm $ PredVar assignmentId Static
isAssignment (Var _ v)   =  isAssignVar v
isAssignment _           =  False
\end{code}

\subsection{Term Tests}

Test values:
\begin{code}
lv_a = ObsLVar  Static i_a [] []
lv_b = VarLVar         i_b [] []
lv_e = ExprLVar Static i_e [] []
lv_P = PredLVar Static i_P [] []

t42 = Val ArbType $ VI 42
n = fromJust $ ident "n"
\end{code}

We need to test the variable and binder smart constructors
\begin{code}
v_P  = PreCond  i_P
v_Q' = PostCond i_Q
v_a =  PreVar    $ i_a
v_b =  PreVar    $ i_b
v_v =  ScriptVar $ i_v
v_a' = PostVar   $ i_a
v_b' = PostVar   $ i_b

varConstructTests  = testGroup "AST.var,eVar,pVar"
 [ testCase "var arbpred arbpred (Ok)"
   ( var arbpred v_P  @?= Just (V arbpred (PreCond i_P) ))
 , testCase "var ArbType arbpred (Fail)"
   ( var ArbType v_P  @?= Nothing )
 , testCase "var arbpred a (Fail)"
   ( var arbpred v_a  @?= Nothing )
 , testCase "var ArbType a (Ok)"
   ( var ArbType v_a
      @?= Just (V ArbType (PreVar i_a )) )
 , testCase "eVar tarb arbpred (Fail)" ( eVar ArbType v_P  @?= Nothing )
 , testCase "eVar tarb a (Ok)"
   ( eVar ArbType v_a @?= Just (V ArbType (PreVar i_a ) ) )
 , testCase "pVar a (Fail)" ( pVar T v_a  @?= Nothing )
 , testCase "pVar arbpred (Ok)"
   ( pVar T v_P @?= Just (V arbpred (PreCond i_P) ) )
 ]

gv_a =  StdVar v_a
gv_b =  StdVar v_b
gv_v =  StdVar v_v
gv_a' = StdVar v_a'
gv_b' = StdVar v_b'

bindConstructTests  =  testGroup "AST.bnd"
 [ testCase "bnd arbpred n {} t42 (Ok)"
   ( bnd arbpred n S.empty t42 @?= Just t42 )
 , testCase "bnd arbpred n {a} t42 (Ok)"
   ( bnd arbpred n (S.fromList [gv_a]) t42
     @?= Just (B arbpred n (S.fromList [gv_a]) t42) )
 , testCase "bnd arbpred n {a$} t42 (Ok)"
   ( bnd arbpred n (S.fromList [LstVar lv_a]) t42
     @?= Just (B arbpred n (S.fromList [LstVar lv_a]) t42) )
 , testCase "bnd arbpred n {a,a$} t42 (Ok)"
   ( bnd arbpred n (S.fromList [gv_a,LstVar lv_a]) t42
     @?= Just (B arbpred n (S.fromList [gv_a,LstVar lv_a]) t42) )
 , testCase "bnd arbpred n {a,e$} t42 (Fail)"
   ( bnd arbpred n (S.fromList [gv_a,LstVar lv_e]) t42 @?= Nothing )
 , testCase "bnd arbpred n {e$,a} t42 (Fail)"
   ( bnd arbpred n (S.fromList [LstVar lv_e,gv_a]) t42 @?= Nothing )
 , testCase "bnd arbpred n {a,b,e$} t42 (Fail)"
   ( bnd arbpred n (S.fromList [gv_a,gv_b,LstVar lv_e]) t42 @?= Nothing )
 ]

lamConstructTests  =  testGroup "AST.lam"
 [ testCase "lam arbpred n [] t42 (Ok)"
   ( lam arbpred n [] t42 @?= Just t42 )
 , testCase "lam arbpred n [a] t42 (Ok)"
   ( lam arbpred n [gv_a] t42 @?= Just (L arbpred n [gv_a] t42) )
 , testCase "lam arbpred n [a$] t42 (Ok)"
   ( lam arbpred n [LstVar lv_a] t42
     @?= Just (L arbpred n [LstVar lv_a] t42) )
 , testCase "lam arbpred n [a,a$] t42 (Ok)"
   ( lam arbpred n [gv_a,LstVar lv_a] t42
     @?= Just (L arbpred n [gv_a,LstVar lv_a] t42) )
 , testCase "lam arbpred n [a,e$] t42 (Fail)"
   ( lam arbpred n [gv_a,LstVar lv_e] t42 @?= Nothing )
 , testCase "lam arbpred n [e$,a] t42 (Fail)"
   ( lam arbpred n [LstVar lv_e,gv_a] t42 @?= Nothing )
 , testCase "lam arbpred n [a,b,e$] t42 (Fail)"
   ( lam arbpred n [gv_a,gv_b,LstVar lv_e] t42 @?= Nothing )
 ]

termConstructTests  =  testGroup "Term Smart Constructors"
  [ varConstructTests, bindConstructTests,lamConstructTests ]
\end{code}


\newpage
\section{Parts of Terms}

Sometimes we want lists of all term components
of a given type (terms/variables/list-variables/variable-sets/variable-lists)

\subsection{Sub-Terms}

\begin{code}
subTerms :: Term -> [Term]
subTerms t@(C _ _ _ ts)  =  t : nub (concat $ map subTerms ts)
subTerms t@(B _ _ _ t')  =  t : subTerms t'
subTerms t@(L _ _ _ t')  =  t : subTerms t'
subTerms t@(X _ t')      =  t : subTerms t'
subTerms t@(S _ t' (SN tsub _))
  = t : nub (concat $ map subTerms (t':map snd (S.toList tsub)))
subTerms t               =  [t]
-- t = head $ subTerms t !!
\end{code}

\subsection{Trivial Quantifiers}

A quantifier match is trivial if all its list-variables
are bound to empty sets or lists.


\begin{code}
onlyTrivialQuantifiers :: Term -> Bool
onlyTrivialQuantifiers term = all trivialQuantifier $ subTerms term

trivialQuantifier :: Term -> Bool
trivialQuantifier (B _ _ vs _)  =  S.null vs
trivialQuantifier (L _ _ vl _)  =    null vl
trivialQuantifier _ = False
\end{code}


\subsection{Trivial Substitution}

A substitution is trivial if both its substitution lists are null.

\begin{code}
anyTrivialSubstitution :: Term -> Bool
anyTrivialSubstitution term = any trivialSubst $ subTerms term

trivialSubst :: Term -> Bool
trivialSubst (S _ _ (SN ts lvs))  =  S.null ts && S.null lvs
trivialSubst _                    =  False
\end{code}




\subsection{(General) Variables}

Here we return all variables mentioned in a term,
regardless of whether or not they are free or bound.

\begin{code}
mentionedVars :: Term -> VarSet
mentionedVars (V _ v)            =  S.singleton $ StdVar v
mentionedVars (C _ _ _ ts)       =  S.unions $ map mentionedVars ts
mentionedVars (B _ _ vs t)       =  mentionedVars t `S.union` vs
mentionedVars (L _ _ vl t)       =  mentionedVars t `S.union` (S.fromList vl)
mentionedVars (X _ t)            =  mentionedVars t
mentionedVars (S _ t (SN tsub lvsub))
  = (mentionedVars t `S.union` tvs) `S.union` rvs
  where
     (tsvl,rtl) = unzip $ S.toList tsub
     (tlvl,rlvl) = unzip $ S.toList lvsub
     tvs = S.fromList (map StdVar tsvl ++ map LstVar tlvl)
     rvs = S.unions (map mentionedVars rtl)
           `S.union`
           (S.map LstVar $ S.fromList rlvl)
mentionedVars (I _ _ _ _ _ lvs)  =  S.fromList $ map LstVar lvs
mentionedVars _                  =  S.empty
\end{code}

\newpage
\subsection{Variable Collections}

\begin{code}
mentionedVarLists :: Term -> [VarList]
mentionedVarLists (C _ _ _ ts)       =  concat $ map mentionedVarLists ts
mentionedVarLists (B _ _ _ t)        =  mentionedVarLists t
mentionedVarLists (L _ _ vl t)       =  vl : mentionedVarLists t
mentionedVarLists (X _ t)            =  mentionedVarLists t
mentionedVarLists (S _ t (SN tsub lvsub))
  = mentionedVarLists t ++ concat (map mentionedVarLists rtl)
  where rtl = map snd $ S.toList tsub
mentionedVarLists (I _ _ _ _ _ lvs)  =  [map LstVar lvs]
mentionedVarLists _                  =  []
\end{code}

Here we include the implicit variable-sets induced by substitution targets.
\begin{code}
mentionedVarSets :: Term -> [VarSet]
mentionedVarSets (C _ _ _ ts)             =  concat $ map mentionedVarSets ts
mentionedVarSets (B _ _ vs t)             =  vs : mentionedVarSets t
mentionedVarSets (L _ _ _ t)              =  mentionedVarSets t
mentionedVarSets (X _ t)                  =  mentionedVarSets t
mentionedVarSets (S _ t (SN tsub lvsub))  = mentionedVarSets t ++ tvs ++ rvs
  where
     (tsvl,rtl) = unzip $ S.toList tsub
     (tlvl,rlvl) = unzip $ S.toList lvsub
     tsvs  = S.fromList (map StdVar tsvl)
     tlvs  = S.fromList (map LstVar tlvl)
     tvs   = [tsvs,tlvs,tsvs `S.union` tlvs]
     rtvs  = S.unions (concat (map mentionedVarSets rtl))
     rlvvs = S.fromList (map LstVar rlvl)
     rvs   = [rtvs,rlvvs,rtvs `S.union` rlvvs]
mentionedVarSets (I _ _ _ _ _ lvs)        =  [S.fromList $ map LstVar lvs]
mentionedVarSets _                        =  []
\end{code}


Term Sizes
\begin{code}
termSize :: Term -> Int
termSize (Val _ _)            =  1
termSize (Var _ _)            =  1
termSize (Cons _ _ _ ts)      =  1 + sum (map termSize ts)
termSize (Bnd _ _ vs t)       =  1 + S.size vs + termSize t
termSize (Lam _ _ vl t)       =  1 + length vl + termSize t
termSize (Cls _ t)            =  1 + termSize t
termSize (Sub _ t subs)       =  1 + termSize t + subsSize subs
termSize (Iter _ _ _ _ _ vl)  =  3 + length vl
termSize (Typ _)              =  2

subsSize (Substn ts lvs)      =  3 * S.size ts + 2 * S.size lvs
\end{code}



\newpage



\section{Exported Test Group}
\begin{code}
jSub ts lvs  =  fromJust $ substn ts lvs

jVar :: Type -> Variable -> Term
jVar typ v        =  fromJust $ var typ v
jBnd typ n vs tm  =  fromJust $ bnd typ n vs tm
jLam typ n vl tm  =  fromJust $ lam typ n vl tm

jeVar v = fromJust $ eVar ArbType v
jpVar v = fromJust $ pVar T v


int_tst_AST :: [TF.Test]
int_tst_AST
 = [ testGroup "\nAST Internal"
     [ substnTests
     , termConstructTests
     ]
{-  , testGroup "QuickCheck Ident"
     [
       testProperty "Idents Always" prop_ident
     ] -}
   ]
\end{code}
