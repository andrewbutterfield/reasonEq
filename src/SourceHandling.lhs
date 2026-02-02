\chapter{Theory Load and Generate}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2018-25

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module SourceHandling (
  term_syntax
, loadTheory, genTheory
-- ,loadTerm, genTerm, loadType, genType, loadSideCond, genSideCond
, compareIPTheories
)
where

import Data.Maybe(fromJust)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import Data.List 
import Data.Char

import NotApplicable
import YesBut
import Control
import Utilities
import Symbols
import LexBase
import Variables
import Types
import AST
import SideCond
import Laws
import VarData
import Assertions
import Theories
import REQ.Abs
import REQ.Par (myLexer,pThry)
import REQ.Print (printTree)
import TestRendering
import StdTypeSignature
import StdSignature

-- We really need more XSignature files in builtin
import Lists
import Arithmetic

import Debugger
\end{code}


\section{Load-Generate Intro.}

We provide a grammar for theory files defined using LBNF (\h{BNFC/UTP}).
The plan is that we will use this as the main way 
to create new/edit existing theories,
so we don't have to use Haskell modules for this purpose.

Parsers and prettyprinters are already implemented, 
for theories, terms, types and side-conditions.
All we have to provide here are mapping functions 
between the LBNF abstract types and the concrete \reasonEq\ types,
as well as relevant file handling.

\begin{code}
term_syntax = ["see reasonEq/bnfc/REQ.lbnf"]

loadTheory :: MonadFail mf => TheoryDAG -> String -> mf Theory
loadTheory thrys text 
  = case pThry (myLexer text) of
      Left err    ->  fail $ unlines ["loadTheory failed",err]
      Right thry  ->  thry2theory thry
\end{code}

\begin{code}
genTheory :: Theory -> String
genTheory theory = printTree $ theory2thry theory
\end{code}



\section{Conversions}

Here we provide bidirectional conversions between the native \reasonEq\ types
and those used in \h{bnfc/REQ}.
We start with theories, because the known variable data is needed to resolve
a range of ambiguous situations.
This requires passing this known data down to the conversions 
for the sub-components: terms, types, side-conditions, and variables.

\newpage
\subsection{Variable Handling}

Due to the limitations of what can be expressed using LBNF,
we have a specific way of encoding \reasonEq\ \h{Variable}s.
The \h{VarClass} type is a straightforward match against \h{VClass}.
However, we use a \h{DynVar} to encode both the \h{Identifier}
and the \h{VarWhen} component, as follows 
(assume here that $v$ contains only alphanumeric characters):
\begin{eqnarray*}
    v & v &  \text{Static}
\\ \_v & 'v & \text{Before}
\\ v\_ & v' & \text{After}
\\ v\_d & v_d & \text{During}
\end{eqnarray*}
We don't handle textual variables just yet.

\begin{code}
dynvar2idwhen :: DynVar -> (Identifier,VarWhen)
dynvar2idwhen (DynVar "") = (jId "null_variable",Static)
dynvar2idwhen (DynVar "_") = (jId "null_variable",Before)
dynvar2idwhen (DynVar ('_':rest)) = (jId rest,Before)
-- look for last of the remaining underscores, if any
dynvar2idwhen (DynVar dv)
  = case findlast (== '_') dv of
      Nothing  ->  (jId dv,Static)
      Just (before,[])  -> (jId before,After)
      Just (before,d)   -> (jId before,During d)
\end{code}

\begin{code}
idwhen2dynvar :: String -> VarWhen -> DynVar
idwhen2dynvar i Static      =  DynVar i
idwhen2dynvar i Before      =  DynVar ('_':i)
idwhen2dynvar i After       =  DynVar (i++['_'])
idwhen2dynvar i (During d)  = DynVar (i++('_':d))
\end{code}

\newpage
\subsection{Thry to Theory}

\begin{code}
thry2theory :: MonadFail mf => Thry -> mf Theory
thry2theory (Thr thNm deps items)
  = items2theory items $
    thName_ (dyn2str thNm) $
    thDeps_ (map dyn2str deps) $
    nullTheory

dyn2str (DynVar str) = str

items2theory :: MonadFail mf => [Item] -> Theory -> mf Theory
items2theory items thry = do
  let (defs,rest) = partition isDefItem items
  let (decls,asserts) = partition isDeclItem rest
  let defaults = defs2defaults initialDefaults defs
  ctxt@(_,knwn) 
    <- decls2vartable decls (defaults, newNamedVarTable $ thName thry)
  (lws,cnjs) <- asserts2asns ctxt asserts 
  return $ conjs_ cnjs $ laws_ lws $ known_ knwn thry
\end{code}

\subsubsection{Default Variable Attributes}

Given a variable represented using a \h{DynVar} ($x, \_x, x\_, x\_d $), 
we can easily determine the temporality of the variable, 
but not its class.
For variable identifiers that are a single character,
we define defaults for the class, 
based on common usage in UTP material, 
as evidenced in the book\cite{UTP-book}:

\begin{tabular}{|c|l|}
\hline
   A--L,N,P--R,T--Z & Predicate, Static, bool (!)
\\ M,S,O & Obs, Dynamic  -- model/script/all observations
\\ a--h & Expr, Static
\\ i--n & Obs, Static
\\ p--s & Pred, Before  
\\ u--z & Obs, Dynamic
\\ \multicolumn{2}{|c|}{not sure about o or t}
\\\hline
\end{tabular}


For longer variables we use the above table with their first character.
\begin{code}
mkDefault :: [(String,a)] -> Map Char a
mkDefault sas = M.fromList $ concat $ map twiddle sas

twiddle :: ([a],b) -> [(a,b)]
twiddle (xs,y) = map (\x -> (x,y)) xs

chkDefault :: a -> Map Char a -> String -> a
chkDefault dd defMap "" = dd
chkDefault dd defMap (c:_)
  = case M.lookup c defMap of
      Nothing -> dd
      Just d  -> d

defaultClasses :: Map Char VarClass
defaultClasses = mkDefault
  [(['A'..'L']++['N']++['P'..'R']++['T'..'Z'],PredV)
  ,("MSO",ObsV)
  ,("abcdefgh",ExprV),("ijklmn",ObsV),("pqrs",PredV),("uvwxyz",ObsV)]

defaultTypes :: Map Char Type
defaultTypes = mkDefault
  [(['A'..'L']++['N']++['P'..'R']++['T'..'Z'],bool)
  ,("MSO",ArbType)
  ,("abcdefgh",ArbType),("ijklmn",ArbType),("pqrs",bool),("uvwxyz",ArbType)]

defaultWhen :: Map Char VarWhen
defaultWhen = mkDefault
  [(['A'..'L']++['N']++['P'..'R']++['T'..'Z'],Static)
  ,("MSO",During "")
  ,("abcdefghijklmn",Static),("pqrs",Before),("uvwxyz",During "")]

-- ! keep domain of above maps the same !!!!!!!!

type Defaults = Map Char (Type,VarClass,VarWhen)
initialDefaults :: Defaults
initialDefaults
  = M.fromList $ map mrgDefaults 
     $ ( zip3 (M.toList defaultTypes) 
              (M.toList defaultClasses) 
              (M.toList defaultWhen) )
mrgDefaults ((c1,w1),(c2,w2),(c3,w3)) =  (c1,(w1,w2,w3))
-- no error checking just now! hope that c1==c2==c3 !
\end{code}
Here \h{During ""} is code for ``any dynamic'' (before,after,during).


The above defaults can be overridden using the default items.
\begin{code}
isDefItem :: Item -> Bool
isDefItem (DefObs _) = True;
isDefItem (DefExpr _) = True;
isDefItem (DefPred _) = True;
isDefItem (DefStatic _) = True;
isDefItem _ = False
\end{code}

\begin{code}
defs2defaults :: Defaults -> [Item] -> Defaults
defs2defaults currentdefs []  = currentdefs
defs2defaults currentdefs (def:defs) 
  = defs2defaults (def2default currentdefs def) defs

def2default :: Defaults -> Item -> Defaults
def2default currdefs (DefObs dynvars)    
                        = changedefs setObs currdefs dynvars
def2default currdefs (DefExpr dynvars)   
                        =  changedefs setExpr currdefs dynvars
def2default currdefs (DefPred dynvars)   
                        =  changedefs setPred currdefs dynvars
def2default currdefs (DefStatic dynvars) 
                        =  changedefs setStatic currdefs dynvars
def2default currdefs _  =  currdefs --shouldn't occur

changedefs chg currdefs [] = currdefs
changedefs chg currdefs (dynvar:dynvars)
  = changedefs chg (changedef chg dynvar currdefs) dynvars

changedef chg dyn currdefs
  = case M.lookup c currdefs of
      Nothing       ->  M.insert c (chg (ArbType,ObsV,vw)) currdefs
      Just currdef  ->  M.insert c (chg currdef)           currdefs
  where
    (Identifier i _,vw) = dynvar2idwhen dyn
    c = head i

setObs    (t, _,vw)  = (t   , ObsV , vw    )
setExpr   (t, _,vw)  = (t   , ExprV, vw    )
setPred   (_, _,vw)  = (bool, PredV, vw    )
setStatic (t,vc,_ )  = (t   , vc   , Static)
\end{code}

\subsubsection{Var-Table Conversions}

We need to include the defaults disucssed above here,
as they are needed to generate terms,
and terms are recorded in \h{VarTables}s.

\begin{code}
type Context = (Defaults,VarTable)
\end{code}

\begin{code}
isDeclItem :: Item -> Bool
isDeclItem (Conj _ _ _)   =  False
isDeclItem (Law _ _ _ _)  =  False
isDeclItem _              =  True
\end{code}

\begin{code}
decls2vartable :: MonadFail mf => [Item] -> Context -> mf Context
decls2vartable [] vtbl = return vtbl
decls2vartable (item:items) vtbl = do
  vtbl' <- decl2vtentry item vtbl
  decls2vartable items vtbl'

decl2vtentry :: MonadFail mf => Item -> Context -> mf Context

decl2vtentry (DeclVar vclass dvar (KV sbbl typ)) (dflts,vtbl) = do
  let vc = vclass2varclass vclass
  let (id,vw) = dynvar2idwhen dvar
  let var = Vbl id vc vw -- dflts ?
  let t = typ2type typ
  vtbl' <- case sbbl of
    Na  ->  addKnownVar var t vtbl
    SB  ->  addKnownConstructor var t True  vtbl
    NS  ->  addKnownConstructor var t False vtbl
  return (dflts,vtbl')

decl2vtentry (DeclDLVar vclass dvar dvars) (dflts,vtbl) = do
  let vc = vclass2varclass vclass
  let (id,vw) = dynvar2idwhen dvar
  let lvar = Vbl id vc vw
  let ids = map dynvar2idwhen dvars
  let gvars = map (StdVar . mkVTableKeyVar vc) ids
  vtbl' <- addKnownVarList lvar gvars vtbl
  return (dflts,vtbl')

decl2vtentry (DeclASet vclass dvar) (dflts,vtbl) = do
  let vc = vclass2varclass vclass
  let (id,vw) = dynvar2idwhen dvar
  let asvar = Vbl id vc vw
  vtbl' <- addAbstractVarSet asvar vtbl
  return (dflts,vtbl')
  
decl2vtentry item (dflts,vtbl) = fail  "decl2vtentry nyfi"

vclass2varclass :: VClass -> VarClass
vclass2varclass VarObs   =  ObsV
vclass2varclass VarExp   =  ExprV
vclass2varclass VarPred  =  PredV

mkVTableKeyVar :: VarClass -> (Identifier,VarWhen) -> Variable
mkVTableKeyVar vc (id,vw) = Vbl id vc vw
\end{code}

\newpage
\subsubsection{Assertion Conversions}

\begin{code}
asserts2asns :: MonadFail mf 
             => Context -> [Item] -> mf ([Law],[NmdAssertion])
asserts2asns ctxt asserts = ass2asns ctxt [] [] asserts
ass2asns ctxt swal sjnoc [] = return (reverse swal,reverse sjnoc)
ass2asns ctxt swal sjnoc (Law ltyp dv tm sc : rest) = do
  ll <- law2Law ctxt ltyp dv tm sc
  ass2asns ctxt (ll++swal) sjnoc rest
ass2asns ctxt swal sjnoc (Conj dv tm sc : rest) = do
  cnj <- conj2Conj ctxt dv tm sc
  ass2asns ctxt swal (cnj:sjnoc) rest

-- we only keep axioms in .utp files !
law2Law :: MonadFail mf 
        => Context -> LawType -> DynVar -> Trm -> SCond -> mf [Law]
law2Law ctxt LAxiom dv tm sc = do
  nasn <- conj2Conj ctxt dv tm sc
  return [(nasn,Axiom)]
law2Law _ _ _ _ _ = return [] -- ignore proofs, and assumptions

conj2Conj :: MonadFail mf 
        => Context -> DynVar -> Trm -> SCond -> mf NmdAssertion
conj2Conj ctxt (DynVar v) trm scond = do
  term <- trm2term ctxt trm
  sidecond <- scond2sidecond ctxt scond
  return (v,mkAsn term sidecond)
\end{code}

\newpage
\subsection{Theory to Thry}

\begin{code}
theory2thry :: Theory -> Thry
theory2thry theory 
  = Thr (DynVar $ thName theory)
        (map DynVar $ thDeps theory)
        (   (known2items $ known theory)
         ++ (concat $ map law2Item $ laws theory)
         ++ (map nmdassn2Item $ conjs theory))
\end{code}

\subsubsection{VarTable to Items}

\begin{code}
known2items :: VarTable -> [Item]
known2items vt
  =    (vtable2items $ vtList vt)
    ++ (stable2items $ stList vt) 
    ++ (stable2items $ dtList vt) -- maps dtable into stable (Before)

vtable2items vtl = map vmr2item  vtl
stable2items stl = map lvmr2item stl

vmr2item (Vbl (Identifier i _) vc vw,vmr)
  = DeclVar (varclass2vclass vc)
            (idwhen2dynvar i vw)
            (vmr2varrole vmr)
-- KnownTerm trm
-- KnownVar typ sub -- implemented
-- GenericVar
-- InstanceVar
-- UnknownVar
vmr2item vmr = error ("NYFI: vmr2item "++show vmr)

vmr2varrole :: VarMatchRole -> VarRole
vmr2varrole (KnownVar typ msub)
  = KV (msubable2sbbl msub) (type2typ typ)
vmr2varrole vmr = error ("NYFI: vmr2varrole "++show vmr)

msubable2sbbl :: Maybe Subable -> SBBL
msubable2sbbl Nothing       =  Na
msubable2sbbl (Just False)  =  NS
msubable2sbbl (Just True)   =  SB

lvmr2item lvmr = error ("NYI: lvmr2item "++show lvmr)
-- KnownVarList vl vars len
-- KnownVarSet  vs vars siz
-- AbstractList
-- AbstractSet -- ipmlemented
-- UnknownListVar

-- DynamicList vis lvis expand len -- implemented
-- DynamicSet vis lvis expand len
-- DynamicAbsList
-- DynamicAbsSet

\end{code}

\subsubsection{Laws to Items}

\begin{code}
law2Item :: Law -> [Item]
-- we only put axioms into .utp files
law2Item ((nm,(Assertion tm sc)),Axiom) 
  = [ Law LAxiom
          (idwhen2dynvar nm Static) 
          (term2trm tm) 
          (sidecond2scond sc) ]
prov2lawtype _ = []
\end{code}

\subsubsection{Conjectures to Items}

\begin{code}
nmdassn2Item :: NmdAssertion -> Item
nmdassn2Item (nm,(Assertion tm sc)) 
  = Conj (idwhen2dynvar nm Static) 
         (term2trm tm) 
         (sidecond2scond sc)
\end{code}

\newpage
\subsection{Trm to Term}

Missing: known variable data.

Also missing - default declarations for common variables
(e.g., ``P'' is typically a static predicate variable).

\begin{code}
trm2term :: MonadFail mf => Context -> Trm -> mf Term
\end{code}

Values

\begin{code}
trm2term _ TTrue     =  return $ Val bool $ Boolean True
trm2term _ TFalse    =  return $ Val bool $ Boolean False
trm2term _ (EInt i)  =  return $ Val int  $ Integer i
\end{code}

Variables

\begin{code}
trm2term ctxt (TmVar dv) = return $ jVar ArbType $ Vbl id vc vw
  where 
    (id,vw) = dynvar2idwhen dv
    vc = determineClass ctxt id vw
\end{code}

Operators

\begin{code}
trm2term ctxt (PEqv trm1 trm2) = binop2term ctxt (===) trm1 trm2
trm2term ctxt (PImpl trm1 trm2) = binop2term ctxt (==>) trm1 trm2
trm2term ctxt (POr trm1 trm2) = binop2term ctxt (\/) trm1 trm2
trm2term ctxt (PAnd trm1 trm2) = binop2term ctxt (/\) trm1 trm2
--trm2term ctxt (Eql trm1 trm2) = binop2term ctxt op trm1 trm2
--trm2term ctxt (NE trm1 trm2) = binop2term ctxt op trm1 trm2
--trm2term ctxt (Lt trm1 trm2) = binop2term ctxt op trm1 trm2
--trm2term ctxt (LE trm1 trm2) = binop2term ctxt op trm1 trm2
--trm2term ctxt (Gt trm1 trm2) = binop2term ctxt op trm1 trm2
--trm2term ctxt (GE trm1 trm2) = binop2term ctxt op trm1 trm2
trm2term ctxt (LCat trm1 trm2) = binop2term ctxt cat trm1 trm2
trm2term ctxt (LCons trm1 trm2) = binop2term ctxt cons trm1 trm2
trm2term ctxt (EAdd trm1 trm2) = binop2term ctxt add trm1 trm2
trm2term ctxt (EMinus trm1 trm2) = binop2term ctxt sub trm1 trm2
trm2term ctxt (EMul trm1 trm2) = binop2term ctxt mul trm1 trm2
trm2term ctxt (EDiv trm1 trm2) = binop2term ctxt idiv trm1 trm2
trm2term ctxt (EMod trm1 trm2) = binop2term ctxt imod trm1 trm2
\end{code}

Miscellaneous

\begin{code}
--trm2term ctxt (PNot trm) 
--trm2term ctxt ENeg trm
--trm2term ctxt ENil
trm2term ctxt@(dflts,vt) (TCons dv trms) = do
  let  (id,vw) = dynvar2idwhen dv
  let sbbl = lkpSubable (Vbl id ObsV Static) vt
  terms <- sequence $ map (trm2term ctxt) trms 
  return $ Cons ArbType (sbbl==SB) id terms
\end{code}

Substitution

\begin{code}
trm2term ctxt (TSubV trm trms tdvs)     =  mkSubst ctxt trm trms tdvs [] []
trm2term ctxt (TSubLV trm rdlvs tdlvs)   =  mkSubst ctxt trm [] [] rdlvs tdlvs
trm2term ctxt (TSubst trm trms tdvs rdlvs tdlvs)  =  mkSubst ctxt trm trms tdvs rdlvs tdlvs
\end{code}

Not yet implemented!

\begin{code}
trm2term _ trm = fail ("trm2term nyfi\n"++show trm)
\end{code}

\newpage
\subsubsection{Determine Class}

We can get identifier and temporality.
To determine class, we need to search the variable data table,
by working through the different classes 
and searching all three var-table mappings.
\begin{code}
determineClass :: Context -> Identifier -> VarWhen -> VarClass
determineClass (dflts,vt) id vw
  | ifIsVarClass  ObsV   =  ObsV
  | ifIsVarClass  ExprV  =  ExprV
  | ifIsVarClass  PredV  =  PredV
  | ifIsLVarClass ObsV   =  ObsV
  | ifIsLVarClass ExprV  =  ExprV
  | ifIsLVarClass PredV  =  PredV
  | otherwise        
    =  case M.lookup (head $ idName id) dflts of
         Nothing  ->  ObsV  
         Just (_,vc,_)  ->  vc  
  where
   ifIsVarClass  vc  =  lookupVarTable vt (Vbl id vc vw)  /= UnknownVar
   ifIsLVarClass vc  =  lookupLVarTable vt (Vbl id vc vw) /= UnknownListVar


\end{code}

\subsubsection{Binary Operation to Term}

\begin{code}
binop2term :: MonadFail m 
           => Context -> (Term -> Term -> Term) -> Trm -> Trm -> m Term
binop2term ctxt op trm1 trm2 = do
  term1 <- trm2term ctxt trm1
  term2 <- trm2term ctxt trm2
  return (term1 `op` term2)
\end{code}

\subsubsection{Determine Substitutability}

\begin{code}
lkpSubable :: Variable -> VarTable -> SBBL
lkpSubable v vt
  = case lookupVarTable vt v of
      (KnownVar _ subable)  ->  msubable2sbbl subable
      _                     ->  Na
\end{code}

\subsubsection{Substitutions}

\begin{code}
mkSubst :: MonadFail m
        => Context -> Trm -> [Trm] -> [DynVar] -> [DynVar] -> [DynVar] 
        -> m Term
mkSubst ctxt trm trms tdvs rdlvs tdlvs = do
  term   <- trm2term ctxt trm
  terms  <- sequence $ map (trm2term ctxt) trms
  let tvars  = map (dynvar2stdvar ctxt) tdvs
  let rlvars = map (dynvar2lstvar ctxt) rdlvs
  let tlvars = map (dynvar2lstvar ctxt) tdlvs
  return $ Sub ArbType term $ xSubstn (zip tvars terms) (zip tlvars rlvars)
\end{code}
Note the lack of error checking!!!

\subsection{Term to Trm}

\begin{code}
term2trm :: Term -> Trm
term2trm (Val _ (Boolean True)) = TTrue
term2trm (Val _ (Boolean False)) = TFalse
term2trm (Val _ (Integer i)) = EInt i
term2trm (Var _ (Vbl (Identifier i _) vc vw)) 
  = TmVar (idwhen2dynvar i vw)
term2trm (Cons typ sb n ts) = cons2trm sb n ts
-- term2trm (Bnd  typ n vs tm)
-- term2trm (Lam  typ n vl tm)
-- term2trm (Cls      n    tm)
term2trm (Sub typ tm (Substn fvs lvs)) 
  = subs2trm tm (S.toList fvs) (S.toList lvs)
-- term2trm (Iter typ sa na si ni lvs)
-- term2trm (VTyp typ v)
term2trm tm = error ("NYI: term2trm "++show tm)

cons2trm :: Subable -> Identifier -> [Term] -> Trm
-- we ignore subable now but it should be added to TCons
cons2trm sb (Identifier i _) [tm1,tm2]
  | i == "eqv"  =  PEqv   trm1 trm2
  | i == "imp"  =  PImpl  trm1 trm2
  | i == "or"   =  POr    trm1 trm2
  | i == "and"  =  PAnd   trm1 trm2
  | i == "eq"   =  Eql    trm1 trm2
  | i == "ne"   =  NE     trm1 trm2
  | i == "lt"   =  Lt     trm1 trm2
  | i == "le"   =  LE     trm1 trm2
  | i == "gt"   =  Gt     trm1 trm2
  | i == "ge"   =  GE     trm1 trm2
  | i == "cat"  =  LCat   trm1 trm2
  | i == "cons" =  LCons  trm1 trm2
  | i == "add"  =  EAdd   trm1 trm2
  | i == "sub"  =  EMinus trm1 trm2
  | i == "mul"  =  EMul   trm1 trm2
  | i == "div"  =  EDiv   trm1 trm2
  | i == "mod"  =  EMod   trm1 trm2
  where trm1 = term2trm tm1 ; trm2 = term2trm tm2    
cons2trm sb (Identifier i _) ts
  | i == "eqv" = balance PEqv trms
  | otherwise  =  TCons (idwhen2dynvar i Static) trms
  where trms =  map term2trm ts

balance rel [] = ENil
balance rel [trm]  =  trm
balance rel [trm1,trm2] = rel trm1 trm2
balance rel trms = rel (balance rel before) (balance rel after)
  where 
    (before,after) = splitAt ((length trms `div` 2)+1) trms

subs2trm :: Term -> [(Variable,Term)] -> [(ListVar,ListVar)] ->  Trm
subs2trm tm vts lvlvs
  | null vts    =  TSubLV trm rldyn tldyn 
  | null lvlvs  =  TSubV  trm rtdyn tvdyn
  | otherwise   =  TSubst trm rtdyn tvdyn rldyn tldyn
  where
    (tv,rt)   = unzip vts
    (tlv,rlv) = unzip lvlvs
    trm       = term2trm tm
    tvdyn     = map stdvar2dynvar tv
    rtdyn     = map term2trm rt
    rldyn     = map lstvar2dynvar rlv
    tldyn     = map lstvar2dynvar tlv
\end{code}

\subsection{Typ to Type}

At present the only given type is $\Bool$ (\h{GivenType "B"}).
\begin{code}
typ2type :: Typ -> Type
typ2type TArb                    =  ArbType
typ2type TBot                    =  BottomType
typ2type (TVbl (DynVar dv))      =  mkTypVar dv
typ2type (TProd (DynVar dv) [])  =  mkTypVar dv
typ2type (TProd (DynVar dv) ts)  =  TypeCons (jId dv) (map typ2type ts)
typ2type (TRec (DynVar dv) fs)   =  TypeCons (jId dv) (map typ2type fs)
typ2type (TFun t1 t2)            =  FunType (typ2type t1) (typ2type t2)
mkTypVar dv
  | dv == "B"                    =  GivenType $ jId dv
  | otherwise                    =  TypeVar $ jId dv
\end{code}

\subsection{Type to Typ}

\begin{code}
type2typ :: Type -> Typ
type2typ ArbType = TArb
type2typ BottomType = TBot
type2typ (GivenType (Identifier i _)) = TVbl $ idwhen2dynvar i Static
type2typ (TypeVar (Identifier i _)) = TVbl $ idwhen2dynvar i Static
type2typ (FunType td tr) = TFun (type2typ td) (type2typ tr)
type2typ (TypeCons (Identifier i _) ts) 
 = TProd (idwhen2dynvar i Static) (map type2typ ts)
-- type2typ (AlgType i fs)
--  = TRec (idwhen2dynvar i Static) (map type2typ fs)
type2typ typ = error ("NYFI: type2typ "++show typ)
\end{code}

\subsection{SCond to SideCond}

\begin{code}
scond2sidecond :: MonadFail mf => Context -> SCond -> mf SideCond
scond2sidecond _ SCnone = return scTrue
scond2sidecond ctxt (SCVSCs vsconds) 
  = scond2sidecond ctxt (SCFull vsconds $ VSet [])
scond2sidecond ctxt (SCFresh vrset)
  = scond2sidecond ctxt (SCFull [] vrset)
scond2sidecond ctxt (SCFull vsconds (VSet gvars)) = do
  let vscs  = map (vscond2varsidecond ctxt) vsconds
  let fvs = S.fromList $ map (gvar2genvar ctxt) gvars
  mkSideCond vscs fvs
\end{code}

\subsubsection{VSCond to VarSideCond}

\begin{code}
vscond2varsidecond :: Context -> VSCond -> VarSideConds
vscond2varsidecond ctxt (VSCDisj gv gvs) = vscond2VSC ctxt disjfrom gv gvs
vscond2varsidecond ctxt (VSCCovBy gv gvs) = vscond2VSC ctxt coveredby gv gvs
vscond2varsidecond ctxt (VSCDynCov gv gvs) = vscond2VSC ctxt dyncovered gv gvs

vscond2VSC :: Context -> (GenVar -> VarSet -> VarSideConds)
           -> GVar ->  VrSet -> VarSideConds
vscond2VSC ctxt op gv (VSet gvs)
  = gvar2genvar ctxt gv `op` (S.fromList $ map (gvar2genvar ctxt) gvs)
\end{code}

\subsection{SideCond to SCond}

\begin{code}
sidecond2scond :: SideCond -> SCond
sidecond2scond ([],fvs)
  | S.null fvs  =  SCnone
  | otherwise   =  SCFresh $ VSet $ map genvar2dynvar $ S.toList fvs
sidecond2scond (vscs,fvs)
  | S.null fvs  =  SCVSCs $ concat $ map varsidecond2vscond vscs
  | otherwise   =  SCFull (concat $ map varsidecond2vscond vscs)
                          (VSet $ map genvar2dynvar $ S.toList fvs)

varsidecond2vscond :: VarSideConds -> [VSCond]
varsidecond2vscond (VSC gv nvsD nvsC nvsCd)
  =     mkDisj   gv nvsD
     ++ mkCovby  gv nvsC 
     ++ mkDynCon gv nvsCd

mkDisj _  NA        =  []
mkDisj gv (The vsD) 
  =  [VSCDisj (genvar2dynvar gv) (varset2vset vsD) ]

mkCovby _ NA = []
mkCovby gv (The vsC)   
  =  [VSCCovBy (genvar2dynvar gv) (varset2vset vsC) ]

mkDynCon _ NA = []
mkDynCon gv (The vsCd)  
  =  [VSCDisj (genvar2dynvar gv) (varset2vset vsCd) ]

varset2vset :: VarSet -> VrSet
varset2vset vs = VSet $ map genvar2dynvar $ S.toList vs
\end{code}

\subsection{DynVar to GenVar}

\begin{code}
dynvar2stdvar :: Context -> DynVar -> Variable
dynvar2stdvar ctxt dyn = Vbl id vc vw where
  (id,vw) = dynvar2idwhen dyn
  vc = determineClass ctxt id vw
\end{code}

\begin{code}
dynvar2lstvar :: Context -> DynVar -> ListVar
dynvar2lstvar ctxt dyn = LVbl (dynvar2stdvar ctxt dyn) [] []
\end{code}

\begin{code}
gvar2genvar :: Context -> GVar -> GenVar
gvar2genvar ctxt (SVar dyn) = StdVar $ dynvar2stdvar ctxt dyn
gvar2genvar ctxt (LVar dyn) = LstVar $ dynvar2lstvar ctxt dyn
\end{code}

\subsection{GenVar to DynVar}

\begin{code}
genvar2dynvar :: GenVar -> GVar
genvar2dynvar (StdVar v)   =  SVar $ stdvar2dynvar  v
genvar2dynvar (LstVar lv)  =  LVar $ lstvar2dynvar lv
\end{code}

\begin{code}
lstvar2dynvar :: ListVar -> DynVar
lstvar2dynvar (LVbl v [] []) = stdvar2dynvar v
lstvar2dynvar lvar 
  = error ("NYI: cannot handle listvar 'less' lists: "++show lvar)
\end{code}

\begin{code}
stdvar2dynvar :: Variable -> DynVar
stdvar2dynvar (Vbl (Identifier i _) _ vw) = idwhen2dynvar i vw
\end{code}

\begin{code}
varclass2vclass :: VarClass -> VClass
varclass2vclass ObsV  = VarObs
varclass2vclass ExprV = VarExp
varclass2vclass PredV = VarPred
\end{code}

\newpage
\section{Comparisons}

It helps to be able to compare a theory just parsed from a UTP file
with the installed theory. 
Ideally these should be identical, 
modulo the fact that some conjectures in the installed theory 
may have been proven, assumed, or deemed to be suspect.

\subsection{Compare Theories}

We are going to compare an Installed theory with a Parsed theory:
\begin{code}
compareIPTheories :: Theory -> Theory ->  String
compareIPTheories iTheory pTheory
  | iName /= pName  =  unlines' mismatch
  | otherwise       =  compIPDeps [] iTheory pTheory
  where
    iName = thName iTheory ; pName = thName pTheory
    mismatch 
      = [ "Installed: "++iName
        , "Parsed:    "++pName
        , "Different Theories!", "EXIT", "" ]
\end{code}

\subsection{Compare Dependencies}

Names are the same, so next we check dependencies,
but also start accumulating discrepancy reports:
\begin{code}
compIPDeps :: [String] -> Theory -> Theory ->  String
compIPDeps sffid iTheory pTheory
  | iDeps /= pDeps  =  compIPVarTables (mismatch++sffid) iTheory pTheory
  | otherwise       =  compIPVarTables sffid iTheory pTheory
  where
    iDeps = thDeps iTheory ; pDeps = thDeps pTheory
    mismatch 
      = [ "Installed deps. not parsed : "++display (iDeps \\ pDeps)
        , "Parsed deps. not installed : "++display (pDeps \\ iDeps) 
        , "Dependencies differ!", "" ]
    display = intercalate " "
\end{code}

\subsection{Compare Variable Tables}

Here we work through the standard and list variables 
in the parsed \h{VarTable}
comparing them against those in the installed version.
We don't compare the \h{VarData} names as they are not present in .utp files,
and are set equal to the theory name when the theory is built.
\begin{code}
compIPVarTables :: [String] -> Theory -> Theory -> String
compIPVarTables sffid iTheory pTheory
  =  let
       vtErrors = checkVTVars           (vTable pKnown)  (vTable iKnown)
       stErrors = checkSTLVars "lstvar" (lvTable pKnown) (lvTable iKnown)
       dtErrors = checkSTLVars "dynvar" (dvTable pKnown) (dvTable iKnown)
       errors = dtErrors ++ stErrors ++ vtErrors 
       report = if null errors 
                then errors 
                else errors ++ [ "Variable Tables differ!","" ]
     in compIPConjectures (report++sffid) iTheory pTheory
  where iKnown = known iTheory ; pKnown = known pTheory

checkVTVars :: VarRoleMap -> VarRoleMap -> [String]
checkVTVars pvTable ivTable 
  =    errorReport (not $ null pvs_less_ivs) 
          [trVList $ map StdVar pvs_less_ivs,"Parsed vars not installed:"]
    ++ errorReport (not $ null ivs_less_pvs)
             [trVList $ map StdVar ivs_less_pvs,"Installed vars not parsed:"]
    ++ errorReport (not $ null bothMM) 
             [concat $ map showVdiff bothMM,"Differing var entries"]
  where 
    pvs = M.keys pvTable ; ivs = M.keys ivTable
    pvs_less_ivs = pvs \\ ivs 
    ivs_less_pvs = ivs \\ pvs
    both = pvs `intersect` ivs
    bothMM = checkMaps pvTable ivTable both
    showVdiff (var,vmr1,vmr2)
      = trVar var 
        ++ ":\n  parsed    = "++trVarMatchRole vmr1
        ++ "\n  installed = "++trVarMatchRole vmr2

checkSTLVars :: String -> LVarRoleMap -> LVarRoleMap -> [String]
checkSTLVars what plvTable ilvTable 
  =    errorReport (not $ null pvs_less_ivs)
         [trVList $ map StdVar pvs_less_ivs,"Parsed vars not installed:"]
    ++ errorReport (not $ null ivs_less_pvs)
         [trVList $ map StdVar ivs_less_pvs,"Installed vars not parsed:"]
    ++ errorReport (not $ null bothMM) 
         [concat $ map showLVdiff bothMM,"Differing "++what++" entries"]
  where 
    pvs = M.keys plvTable ; ivs = M.keys ilvTable
    pvs_less_ivs = pvs \\ ivs 
    ivs_less_pvs = ivs \\ pvs
    both = pvs `intersect` ivs
    bothMM = checkMaps plvTable ilvTable both
    showLVdiff (var,lvmr1,lvmr2)
      = trVar var 
        ++ ":\n  parsed    = "++trLstVarMatchRole lvmr1
        ++ "\n  installed = "++trLstVarMatchRole lvmr2
\end{code}

\subsection{Compare Conjectures}

Here we work through the parsed conjectures,
comparing them against the installed conjectures and (eventually) laws.
\begin{code}
compIPConjectures :: [String] -> Theory -> Theory -> String
compIPConjectures sffid iTheory pTheory
  = compIPLaws (troper++sffid) iTheory pTheory
  where 
    pCjs = sort $ conjs pTheory
    iCjs = sort $ conjs iTheory
    iLws = sort $ laws  iTheory
    troper = scanConjs [] pCjs iCjs iLws

scanConjs :: [String]            -- reports already generated
              -> [NmdAssertion]       -- parsed conjectures
              -> [NmdAssertion]       -- installed conjectures
              -> [Law]  -- installed laws
              -> [String]            -- updated reports
scanConjs stroper [] iCjs _ 
  | null iCjs  =  stroper
  | otherwise = (("Extra installed conj: "++show (map fst iCjs)):stroper)
scanConjs stroper pCjs@((pnm,_):_) iCjs iLws
  = scanConjs' stroper pCjs (seek fst pnm iCjs) (seek (fst . fst) pnm iLws)
\end{code}

\newpage
\begin{code}
scanConjs' :: [String]            -- reports already generated
                -> [NmdAssertion]       -- pnm
                -> [NmdAssertion]       -- installed conjectures
                -> [Law]  -- installed laws
                -> [String]            -- updated reports

-- scanConjs' preconditions:
--     pCjs@[(pnm,_):_]   -- not null
--     iCjs@[(icnm,_):_]  -- if not null, then icnm >= pnm
--     iLws@[(ilnm,_):_]  -- if not null, then ilnm >= pnm

-- 1. both installed empty
scanConjs' stroper pCjs [] [] 
  = (("Extra parsed conj: "++show (map fst pCjs)):stroper)

-- 2. installed laws empty
scanConjs' stroper pCjs@((pnm,passn):pCjs') 
                   iCjs@((icnm,icassn):iCjs') -- icnm >= pnm
                   []
  | pnm /= icnm  
      = scanConjs (("Extra parsed conj:"++pnm):stroper) pCjs' iCjs []
  | passn /= icassn
      = scanConjs (("Conjectures differ:"++pnm):stroper) pCjs' iCjs' []
  | otherwise = scanConjs stroper pCjs' iCjs' []

-- 3. installed conjectures empty
scanConjs' stroper pCjs@((pnm,passn):pCjs') 
                   [] 
                   iLws@(((ilnm,ilassn),prv):iLws') -- ilnm >= pnm
  | pnm /= ilnm  
     = scanConjs (("Extra parsed conj:"++pnm):stroper) pCjs' [] iLws
  | passn /= ilassn
     = scanConjs (("Conj and law differ:"++pnm):stroper) pCjs' [] iLws'
  | otherwise = scanConjs stroper pCjs' [] iLws'

-- 4. both installed present
-- we would not expect icnm == ilnm -- this is a serious issue
scanConjs' stroper pCjs@((pnm,passn):pCjs')
                   iCjs@((icnm,icassn):iCjs')       -- icnm >= pnm
                   iLws@(((ilnm,ilassn),prv):iLws') -- ilnm >= pnm
  | icnm == ilnm
     =  (("Same Name '"++ilnm++"' in installed conjecture and law!"):stroper)
  | pnm == icnm  -- ilnm > pnm
     = scanConjs 
        (foundBoth ("Both conjectures - "++pnm) passn icassn ++ stroper)  
        pCjs' iCjs' iLws
  | pnm == ilnm -- icnm > pnm
     = scanConjs 
         (foundBoth ("Conjecture and Law - "++pnm) passn ilassn ++ stroper)
         pCjs' iCjs iLws'
  | otherwise = scanConjs stroper pCjs' iCjs' iLws'
\end{code}

\begin{code}
foundBoth :: String -> Assertion -> Assertion -> [String]
foundBoth header pAssn iAssn
  | pAssn == iAssn  =  [] -- nothing to see here....
  | otherwise
      = [ "  installed assertion: " ++ trAsn iAssn
        , "  parsed assertion:    " ++ trAsn pAssn
        , header
        ]
\end{code}

\subsection{Compare Laws}

Here we work through the parsed laws,
comparing them against the installed laws and (eventually) conjectures.
\begin{code}
compIPLaws :: [String] -> Theory -> Theory -> String
compIPLaws sffid iTheory pTheory
  = compFinish (troper++sffid)
  where 
    pLws = sort $ laws  pTheory
    iLws = sort $ laws  iTheory
    iCjs = sort $ conjs iTheory
    troper = scanLaws [] pLws iLws iCjs

scanLaws :: [String] -> [Law] -> [Law] -> [NmdAssertion] -> [String]
scanLaws stroper [] iLws _
  | null iLws  =  stroper
  | otherwise 
      = (("Extra installed laws: "++show (map (fst .fst) iLws)):stroper)
scanLaws stroper pLws@(((pnm,_),_):_) iLws iCjs
  = scanLaws' stroper pLws (seek (fst . fst) pnm iLws) (seek fst pnm iCjs)
\end{code}

\begin{code}
scanLaws' :: [String] -> [Law] -> [Law] -> [NmdAssertion] -> [String]

-- 1. both installed empty
scanLaws' stroper pLws [] []
  = (("Extra parsed laws: "++show (map (fst . fst) pLws)):stroper)

-- 2. installed conjectures empty
scanLaws' stroper pLws@(((pnm,passn),_):pLws')
                  iLws@(((ilnm,ilassn),_):iLws')  -- ilnm >= pnm
                  []
  | pnm /= ilnm
      = scanLaws (("Extra parsed laws"++pnm):stroper) pLws' iLws []
  | passn /= ilassn
      = scanLaws (("Laws differ:"++pnm):stroper) pLws' iLws' []
  | otherwise = scanLaws stroper pLws' iLws' []

-- 3. installed laws empty
scanLaws' stroper pLws@(((pnm,passn),_):pLws')
                  []
                  iCjs@((icnm,icassn):iCjs')   -- icnm >= pnm
  | pnm /= icnm
      = scanLaws (("Extra parsed laws"++pnm):stroper) pLws' [] iCjs'
  | passn /= icassn
      = scanLaws (("Law and Conj differ:"++pnm):stroper) pLws' [] iCjs'
  | otherwise = scanLaws stroper pLws' [] iCjs'

-- 4. both installed present
scanLaws' stroper pLws@(((pnm,passn),_):pLws')
                  iLws@(((ilnm,ilassn),_):iLws')  -- ilnm >= pnm
                  iCjs@((icnm,icassn):iCjs')    -- icnm >= pnm
  | icnm == ilnm
     = (("Same Name '"++ilnm++"' in installed law and conjecture!"):stroper)
  | pnm == ilnm -- icnm > pnm
     = scanLaws 
         (foundBoth ("Both laws - "++pnm) passn ilassn ++ stroper)  
         pLws' iLws' iCjs
  | pnm == icnm -- ilnm > pnm
     = scanLaws 
         (foundBoth ("Law and Conjecture - "++pnm) passn icassn ++ stroper)  
         pLws' iLws iCjs'
  | otherwise = scanLaws stroper pLws' iLws' iCjs'
\end{code}

\subsection{Finish}


\begin{code}
compFinish :: [String] -> String
compFinish sffid 
  = unlines' 
     $ reverse ("Installed vs. Parse Theory check complete.":"":sffid)
\end{code}

\section{Generic Comparison Code}

\subsection{Seeking}

Looking for the first component in an ordered list greater that or equal to a specified target, where order is determined by a sub-component.
\begin{code}
-- expects xs to be ordered
seek :: Ord a => (as -> a) -> a -> [as] -> [as]
seek get nm [] = []
seek get nm xs@(x:xs')
  | nm > get x  =  seek get nm xs'
  | otherwise   =  xs  -- hd xs (if it exists) is >= nm
\end{code}

\subsection{Anomaly Reporting}

This takes a boolean parameter that when true indicates a mismatch of some 
kind between installed and parsed theories.
It simplifies generating reports that have a heading plus a list of errors.
\begin{code}
errorReport :: Bool -> [String] -> [String] -- mismatch report
errorReport True  strs = strs
errorReport False strs = []
\end{code}

\subsection{Comparing Map Entries}

This is intended used with keys that are common to both maps.
\begin{code}
checkMaps :: (Ord a, Eq c) => Map a c -> Map a c -> [a] -> [(a, c, c)]
checkMaps map1 map2 keys = concat $ map (checkEntries map1 map2) keys

checkEntries :: (Ord a, Eq c) => Map a c -> Map a c -> a -> [(a, c, c)]
checkEntries map1 map2 key
  = case (lkp1,lkp2) of
      (Just elem1,Just elem2) ->
        if elem1 == elem2 
        then []
        else [(key,elem1,elem2)]
      _ -> []  -- shouldn't happen, but fail silently anyway
  where lkp1 = M.lookup key map1 ; lkp2 = M.lookup key map2
\end{code}