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
import Data.List (nub, sort, (\\), intercalate, stripPrefix, partition)
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
  knwn <- decls2vartable decls newVarTable
  (lws,cnjs) <- asserts2asns knwn asserts 
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
   A--L,N,P--R,T--Z & Predicate, Static
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
defaultWhen :: Map Char VarWhen
defaultWhen = mkDefault
  [(['A'..'Z'],Static),
  ("abcdefghijklmn",Static),("pqrs",Before),("uvwxyz",During "")]
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

\subsubsection{Var-Table Conversions}

\begin{code}
isDeclItem :: Item -> Bool
isDeclItem (Conj _ _ _)   =  False
isDeclItem (Law _ _ _ _)  =  False
isDeclItem _              =  True
decls2vartable :: MonadFail mf => [Item] -> VarTable -> mf VarTable
decls2vartable [] vtbl = return vtbl
decls2vartable (item:items) vtbl = do
  vtbl' <- decl2vtentry item vtbl
  decls2vartable items vtbl'

decl2vtentry :: MonadFail mf => Item -> VarTable -> mf VarTable

decl2vtentry (DeclVar vclass dvar (KV sbbl typ)) vtbl = do
  let vc = vclass2varclass vclass
  let (id,vw) = dynvar2idwhen dvar
  let var = Vbl id vc vw
  let t = typ2type typ
  case sbbl of
    Na  ->  addKnownVar var t vtbl
    SB  ->  addKnownConstructor var t True  vtbl
    NS  ->  addKnownConstructor var t False vtbl

decl2vtentry (DeclDLVar vclass dvar dvars) vtbl = do
  let vc = vclass2varclass vclass
  let (id,vw) = dynvar2idwhen dvar
  let lvar = Vbl id vc vw
  let ids = map dynvar2idwhen dvars
  let gvars = map (StdVar . mkVTableKeyVar vc) ids
  addKnownVarList lvar gvars vtbl

decl2vtentry (DeclASet vclass dvar) vtbl = do
  let vc = vclass2varclass vclass
  let (id,vw) = dynvar2idwhen dvar
  let asvar = Vbl id vc vw
  addAbstractVarSet asvar vtbl
  
decl2vtentry item vtbl = fail  "decl2vtentry nyfi"

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
             => VarTable -> [Item] -> mf ([Law],[NmdAssertion])
asserts2asns knwn asserts = ass2asns knwn [] [] asserts
ass2asns knwn swal sjnoc [] = return (reverse swal,reverse sjnoc)
ass2asns knwn swal sjnoc (Law ltyp dv tm sc : rest) = do
  ll <- law2Law knwn ltyp dv tm sc
  ass2asns knwn (ll++swal) sjnoc rest
ass2asns knwn swal sjnoc (Conj dv tm sc : rest) = do
  cnj <- conj2Conj knwn dv tm sc
  ass2asns knwn swal (cnj:sjnoc) rest

-- we only keep axioms in .utp files !
law2Law :: MonadFail mf 
        => VarTable -> LawType -> DynVar -> Trm -> SCond -> mf [Law]
law2Law knwn LAxiom dv tm sc = do
  nasn <- conj2Conj knwn dv tm sc
  return [(nasn,Axiom)]
law2Law _ _ _ _ _ = return [] -- ignore proofs, and assumptions

conj2Conj :: MonadFail mf 
        => VarTable -> DynVar -> Trm -> SCond -> mf NmdAssertion
conj2Conj knwn (DynVar v) trm scond = do
  term <- trm2term knwn trm
  sidecond <- scond2sidecond knwn scond
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
trm2term :: MonadFail mf => VarTable -> Trm -> mf Term
\end{code}

Values

\begin{code}
trm2term _ TTrue     = return $ Val bool $ Boolean True
trm2term _ TFalse    = return $ Val bool $ Boolean False
trm2term vt (EInt i) = return $ Val int  $ Integer i
\end{code}

Variables

\begin{code}
trm2term vt (TmVar dv) = return $ jVar ArbType $ Vbl id vc vw
  where 
    (id,vw) = dynvar2idwhen dv
    vc = determineClass vt id vw
\end{code}

Operators

\begin{code}
trm2term vt (PEqv trm1 trm2) = binop2term vt (===) trm1 trm2
trm2term vt (PImpl trm1 trm2) = binop2term vt (==>) trm1 trm2
trm2term vt (POr trm1 trm2) = binop2term vt (\/) trm1 trm2
trm2term vt (PAnd trm1 trm2) = binop2term vt (/\) trm1 trm2
--trm2term vt (Eql trm1 trm2) = binop2term vt op trm1 trm2
--trm2term vt (NE trm1 trm2) = binop2term vt op trm1 trm2
--trm2term vt (Lt trm1 trm2) = binop2term vt op trm1 trm2
--trm2term vt (LE trm1 trm2) = binop2term vt op trm1 trm2
--trm2term vt (Gt trm1 trm2) = binop2term vt op trm1 trm2
--trm2term vt (GE trm1 trm2) = binop2term vt op trm1 trm2
trm2term vt (LCat trm1 trm2) = binop2term vt cat trm1 trm2
trm2term vt (LCons trm1 trm2) = binop2term vt cons trm1 trm2
trm2term vt (EAdd trm1 trm2) = binop2term vt add trm1 trm2
trm2term vt (EMinus trm1 trm2) = binop2term vt sub trm1 trm2
trm2term vt (EMul trm1 trm2) = binop2term vt mul trm1 trm2
trm2term vt (EDiv trm1 trm2) = binop2term vt idiv trm1 trm2
trm2term vt (EMod trm1 trm2) = binop2term vt imod trm1 trm2
\end{code}

Miscellaneous

\begin{code}
--trm2term vt (PNot trm) 
--trm2term vt ENeg trm
--trm2term vt ENil
trm2term vt (TCons dv trms) = do
  let  (id,vw) = dynvar2idwhen dv
  let sbbl = lkpSubable (Vbl id ObsV Static) vt
  terms <- sequence $ map (trm2term vt) trms 
  return $ Cons ArbType (sbbl==SB) id terms
\end{code}

Substitution

\begin{code}
trm2term vt (TSubV trm trms tdvs)     =  mkSubst vt trm trms tdvs [] []
trm2term vt (TSubLV trm rdlvs tdlvs)  =  mkSubst vt trm [] [] rdlvs tdlvs
trm2term vt (TSubst trm trms tdvs rdlvs tdlvs)
                                      =  mkSubst vt trm trms tdvs rdlvs tdlvs
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
determineClass :: VarTable -> Identifier -> VarWhen -> VarClass
determineClass vt id vw
  | ifIsVarClass  ObsV   =  ObsV
  | ifIsVarClass  ExprV  =  ExprV
  | ifIsVarClass  PredV  =  PredV
  | ifIsLVarClass ObsV   =  ObsV
  | ifIsLVarClass ExprV  =  ExprV
  | ifIsLVarClass PredV  =  PredV
  | otherwise        
    =  case M.lookup (head $ idName id) defaultClasses of
         Nothing  ->  ObsV  -- o or t
         Just vc  ->  vc  
  where
   ifIsVarClass  vc  =  lookupVarTable vt (Vbl id vc vw)  /= UnknownVar
   ifIsLVarClass vc  =  lookupLVarTable vt (Vbl id vc vw) /= UnknownListVar


\end{code}

\subsubsection{Binary Operation to Term}

\begin{code}
binop2term :: MonadFail m 
           => VarTable -> (Term -> Term -> Term) -> Trm -> Trm -> m Term
binop2term vt op trm1 trm2 = do
  term1 <- trm2term vt trm1
  term2 <- trm2term vt trm2
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
        => VarTable -> Trm -> [Trm] -> [DynVar] -> [DynVar] -> [DynVar] 
        -> m Term
mkSubst vt trm trms tdvs rdlvs tdlvs = do
  term   <- trm2term vt trm
  terms  <- sequence $ map (trm2term vt) trms
  let tvars  = map (dynvar2stdvar vt) tdvs
  let rlvars = map (dynvar2lstvar vt) rdlvs
  let tlvars = map (dynvar2lstvar vt) tdlvs
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
typ2type TArb  =  ArbType
typ2type TBot  =  BottomType
typ2type (TVbl (DynVar dv))  
  | dv == "B"  =  GivenType $ jId dv
  | otherwise  =  TypeVar $ jId dv
typ2type (TFun t1 t2)        
  =  FunType (typ2type t1) (typ2type t2)
typ2type (TProd (DynVar dv) ts)  
  =  TypeCons (jId dv) (map typ2type ts)
typ2type (TRec (DynVar dv) fs)   
  =  TypeCons (jId dv) (map typ2type fs)
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
scond2sidecond :: MonadFail mf => VarTable -> SCond -> mf SideCond
scond2sidecond _ SCnone = return scTrue
scond2sidecond vt (SCVSCs vsconds) 
  = scond2sidecond vt (SCFull vsconds $ VSet [])
scond2sidecond vt (SCFresh vrset)
  = scond2sidecond vt (SCFull [] vrset)
scond2sidecond vt (SCFull vsconds (VSet gvars)) = do
  let vscs  = map (vscond2varsidecond vt) vsconds
  let fvs = S.fromList $ map (gvar2genvar vt) gvars
  mkSideCond vscs fvs
\end{code}

\subsubsection{VSCond to VarSideCond}

\begin{code}
vscond2varsidecond :: VarTable -> VSCond -> VarSideConds
vscond2varsidecond vt (VSCDisj gv gvs) = vscond2VSC vt disjfrom gv gvs
vscond2varsidecond vt (VSCCovBy gv gvs) = vscond2VSC vt coveredby gv gvs
vscond2varsidecond vt (VSCDynCov gv gvs) = vscond2VSC vt dyncovered gv gvs

vscond2VSC :: VarTable -> (GenVar -> VarSet -> VarSideConds)
           -> GVar ->  VrSet -> VarSideConds
vscond2VSC vt op gv (VSet gvs)
  = gvar2genvar vt gv `op` (S.fromList $ map (gvar2genvar vt) gvs)
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
dynvar2stdvar :: VarTable -> DynVar -> Variable
dynvar2stdvar vt dyn = Vbl id vc vw where
  (id,vw) = dynvar2idwhen dyn
  vc = determineClass vt id vw
\end{code}

\begin{code}
dynvar2lstvar :: VarTable -> DynVar -> ListVar
dynvar2lstvar vt dyn = LVbl (dynvar2stdvar vt dyn) [] []
\end{code}

\begin{code}
gvar2genvar :: VarTable -> GVar -> GenVar
gvar2genvar vt (SVar dyn) = StdVar $ dynvar2stdvar vt dyn
gvar2genvar vt (LVar dyn) = LstVar $ dynvar2lstvar vt dyn
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
  = error ("NYI cannot handle listvar 'less' lists: "++show lvar)
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

\section{Comparisons}

It helps to be able to compare a theory just parsed from a UTP file
with the installed theory. 
Ideally these should be identical, 
modulo the fact that some conjectures in the installed theory 
may have been proven, assumed, or deemed to be suspect.

We are going to compare an Installed theory with a Parsed theory:
\begin{code}
compareIPTheories :: Theory -> Theory ->  String
compareIPTheories iTheory pTheory
  | iName /= pName  =  "Different theories '"++iName++"'/'"++pName++"'"
  | otherwise  =  compIPDeps [] iTheory pTheory
  where
    iName = thName iTheory ; pName = thName pTheory
\end{code}

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
      = [ "Installed deps not parsed.   : "++display (iDeps \\ pDeps)
        , "Installed parsed not in deps : "++display (pDeps \\ iDeps) ]
    display = intercalate " "
\end{code}

Check both theories \h{VarTables}:
\begin{code}
compIPVarTables :: [String] -> Theory -> Theory -> String
compIPVarTables sffid iTheory pTheory
  | iKnown /= pKnown  =  compIPNext (mismatch++sffid) iTheory pTheory
  | otherwise  =  compIPNext sffid iTheory pTheory
  where 
    iKnown = known iTheory ; pKnown = known pTheory
    -- we should do this variable by variable
    mismatch
      = [ "Installed known:\n" ++ show iKnown
        , "Parsed known:\n"    ++ show pKnown ]
\end{code}

Leftover:
\begin{code}
compIPNext :: [String] -> Theory -> Theory -> String
compIPNext sffid iTheory pTheory
  = unlines $ reverse ("More as yet unchecked":sffid)
\end{code}