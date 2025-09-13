\chapter{Theory Load and Generate}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2018-25

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module SourceHandling (
  mkLawName
, term_syntax
, renderToken'
, loadTheory, genTheory
, loadTerm
)

where

import Data.Maybe(fromJust)
-- import Data.Map as M (fromList,assocs)
import qualified Data.Set as S
import qualified Data.Map as M
import Data.List (nub, sort, (\\), intercalate, stripPrefix)
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
import TestRendering
import StdTypeSignature

import Debugger
\end{code}

\section{Load-Generate Intro.}

We provide a simple, clunky way to read and write theory objects
using a simple grammar mostly using prefix-based constructs.

The plan is that we will use this as the main way to create
new theories,
so we don't have to use Haskell modules.

For now we have simple literals,
composites done as prefix-functions applied to delimited lists of sub-terms,
and binders in standard mixfix style.


\newpage
\section{Theories}

We start here with code to load and save \emph{entire} theories
We will gradually flesh this out.

For now we concern ourselves with theory names, dependencies, knowns, laws,
and conjectures.
Proofs are complex, and only arise by running \reasonEq,
and we will rely on save and restore to handle them.
The automatic laws can be re-generated once the theory is loaded.

Lesson 1 : Don't base it on blocks like Laws \dots Done.
Instead: allow arbitrary interleaving on input,
with each item flagged by a leading keyword (.eg. Law),
and terminated by End.

Here is a second cut for a theory:
\begin{verbatim}
Theory <TheoryName>
DependsOn 
  <DepThryName>  ... 
  <DepThryName>  ...
Done
( KnownVariable <entry> end | Law <law> end | Conjecture <conj> end)+
\end{verbatim}
The theory name and dependencies should be first,
while all the other items
can occur in any order, and multiple times.
Their contents are gathered and kept in sequence.
When we output theories like this, 
all the items in the same category will appear together.

Keywords:
\begin{code}
kTheory = "Theory"
kNeeds = "Needs"
kKnown = "Known"
kLaw = "Law"
kConjecture = "Conjecture"
kBegin = "BEGIN"
kEnd = "END"
\end{code}

\subsection{Load Theory}

Theory names become filenames,
so they are restricted to the ``safe'' character set 
less the extension dot: \verb"[a-zA-Z0-9-_]",
\begin{code}
validFileName name = all validFileChar name
validFileChar c = c `elem` validFileChars
validFileChars = ['a'..'z'] ++ ['A'..'Z'] ++ "_-"
\end{code}


\begin{code}
loadTheory :: MonadFail mf => String -> mf Theory
loadTheory text  =  loadTheoryParts nullTheory $ tlex $ prepare text


loadTheoryParts :: MonadFail mf  => Theory -> [Token] -> mf Theory
loadTheoryParts thry [] = fail "Empty theory file!"
loadTheoryParts thry ( (lno,TVar key Static)
                   :(_,TVar name Static):rest)
  | key == kTheory && validFileName name = do
        (thry',rest') <- loadDependencies (thName_ name thry) rest 
        loadDefinitions thry' rest'   
  | otherwise  =  fail $ unlines  
      [ "loadTheory headline parse error at line " ++ show lno 
      , "  expected: "++kTheory++" theoryname"
      , "  got: " ++ key ++ " " ++ name ]

loadDependencies :: MonadFail mf 
                   => Theory -> [Token] 
                   -> mf (Theory,[Token])
loadDependencies thry []  =  return (thry,[])
loadDependencies thry nlines@((lno,TVar  needs Static):rest)
  | needs == kNeeds  =  loadDeps thry [] rest
  | otherwise = return (thry,nlines) -- no dependencies is fine

loadDeps thry sped []  =  premAfter [ kNeeds ]

loadDeps thry sped ((lno,TVar close _):rest) 
  | close == kEnd  
     =  return ((thDeps__ (++(reverse sped)) thry), rest)

loadDeps thry sped ((lno,TVar i Static):rest) 
  | validFileName i = loadDeps thry (i:sped) rest 

loadDeps thry sped (tok@(lno,_):rest) 
  = fail $ unlines
      [ "invalid dependency at line "++show lno
      , "  saw "++renderToken tok ]

-- loadDepLine thry sped rest lno [] = loadDeps thry sped rest
-- loadDepLine thry sped rest lno ((_,TVar  dep Static):deps)
--   | validFileName dep = loadDepLine thry (dep:sped) rest lno deps
--   | otherwise = 


loadDefinitions :: MonadFail mf => Theory -> [Token] -> mf Theory  
loadDefinitions thry []  =  return thry
loadDefinitions thry ((lno,TVar category Static)
                       :(_,TVar name Static):rest)
  | category == kConjecture = do
      (conj',rest') <- loadConjecture name rest
      loadDefinitions (conjs__ (++[conj']) thry) rest'
  | category == kLaw = do
      (law',rest') <- loadLaw name rest
      loadDefinitions (laws__ (++[law']) thry) rest'
loadDefinitions thry ((lno,TVar category Static):rest)
  | category == kKnown = do
      (known',rest') <- loadKnown (known thry) rest
      loadDefinitions (known_ known' thry) rest'
loadDefinitions thry (tok@(lno,_):_)
  = fail $ unlines [ "loadTheory expected known/law/conj at " 
                        ++ show lno
                   , "but got: "++renderToken tok
                   ] 
\end{code}


\subsection{Generate Theory}

\begin{code}
genTheory :: Theory -> String
genTheory theory = unlines (
  (kTheory ++ " " ++ thName theory)
   : ( genDeps (thDeps theory) ++
       ["",genVarTable (known theory)] ++
       ["",genLaws (laws theory)] ++
       [genConjectures (conjs theory)] ) )

genDeps [] = []
genDeps deps = 
  [ kNeeds , genIndentedNameList 2 80 deps , kEnd] 
\end{code}

\newpage
\section{VarTables}

\subsection{Load VarTable}

Seen \h{kKnown}:
\begin{code}
loadKnown :: MonadFail mf => VarTable -> [Token] -> mf (VarTable,[Token])
loadKnown vt [] = return (vt,[])
loadKnown vt toks@((lno,TVar var vw):rest) = loadKVar vt lno var vw rest
loadKnown vt toks@((lno,TLVar var vw):rest) = loadKLVar vt lno var vw rest
loadKnown name (tok:rest) 
  = fail ("loadVarData NYfI - tok:"++show tok)

dot = "."
dotTok = TSym dot  -- used to terminate var data type entries
kInstanceOf = "instanceof"
\end{code}

\subsubsection{Load Known Variable}

\begin{verbatim}
Known v : <type> .
Known t = BEGIN <term> END
Known g :: generic
Known i instanceof g
\end{verbatim}

Seen \h{Known var}
\begin{code}
loadKVar :: MonadFail mf 
           => VarTable -> Int -> String -> VarWhen -> [Token] 
           -> mf (VarTable,[Token])
loadKVar vt _ var vw ((lno,TSym ":"):rest) 
                                  =  loadKVarOfType vt lno var vw rest
loadKVar vt _ var vw ((lno,TSym "="):rest)  
                                  =  loadKVarIsConst vt lno var vw rest
loadKVar vt _ var vw ((lno,TSym "::"):rest)  
                                  =  loadKVarIsGeneric vt lno var vw rest
loadKVar vt _ var vw ((lno,TVar iof _):rest)
  | iof == kInstanceOf  =  loadKVarInstance vt lno var vw rest
loadKVar vt _ var vw ((lno,ttyp):_)
  = fail ( "loadKVar: unexpected token "
           ++show ttyp++" at line "++show lno )
loadKVar vt lno var vw []  =  premImport "known var" var lno 
\end{code}

Seen \h{Known var :}, expect a type terminated by \h{.}
\begin{code}
loadKVarOfType :: MonadFail mf 
                 => VarTable -> Int -> String -> VarWhen -> [Token] 
                 -> mf (VarTable,[Token])
loadKVarOfType vt lno var vw []  =  premImport "type" var lno
loadKVarOfType vt lno var vw rest = do
  (typ,rest') <- loadType rest
  rest'' <- expectToken "loadKVarOfType" dotTok rest'
  vt' <- addKnownVar (Vbl (jId var) ObsV vw) typ vt
  return (vt',rest'')
\end{code}

Seen \h{Known var =}, expect a term wrapped with \h{BEGIN \dots END}
\begin{code}
loadKVarIsConst :: MonadFail mf 
                  => VarTable -> Int -> String -> VarWhen -> [Token] 
                  -> mf (VarTable,[Token])
loadKVarIsConst vt lno var vw tokens = do
  (block,beyond) <- getBlock beBlock tokens
  (term,rest) <- parseTerm block
  if null rest 
  then do
    vt' <- addKnownConst (Vbl (jId var) ExprV Static) term vt
    return (vt',beyond)
  else fail $ unlines'
        [ "loadKVarIsConst("++var++")"
        , "after term: "++trTerm 0 term
        , "has junk "++renderTokTyp (snd (head rest))
        , "at line no "++show (fst (head rest)) ]
\end{code}

Seen \h{Known var ::}, expect keyword \h{generic}
\begin{code}
loadKVarIsGeneric :: MonadFail mf 
                  => VarTable -> Int -> String -> VarWhen -> [Token] 
                  -> mf (VarTable,[Token])
loadKVarIsGeneric vt lno var vw []  =  premImport "generic" var lno
loadKVarIsGeneric vt lno var vw ((lno',TVar "generic" _):rest) = do
  vt' <- addGenericVar (Vbl (jId var) ExprV Static) vt
  return (vt',rest)
loadKVarIsGeneric vt lno var vw ((lno',tok):rest)
  = fail ( "loadKVarGeneric("++var++"): unexpected token "
           ++renderTokTyp tok++" at line "++show lno' )
\end{code}

Seen \h{Known var instanceof}, expect (generic) variable.
\begin{code}
loadKVarInstance :: MonadFail mf 
                  => VarTable -> Int -> String -> VarWhen -> [Token] 
                  -> mf (VarTable,[Token])
loadKVarInstance vt lno var vw []  =  premImport "instance" var lno
loadKVarInstance vt lno var vw ((lno',TVar gvar _):rest) = do
  vt' <- addInstanceVar (Vbl (jId var) ExprV Static) 
           (Vbl (jId gvar) ExprV Static) vt
  return (vt',rest)
loadKVarInstance vt lno var vw ((lno',tok):rest)
  = fail ( "loadKVarInstance("++var++"): unexpected token "
           ++renderTokTyp tok++" at line "++show lno' )
\end{code}

\subsubsection{Load Known List-Variable}

\begin{verbatim}
Known al$ :: list
Known as$ :: set
Known lst$ = '<' gv1 , ... , gvn '>'
Known set$ = { gv1 , ... , gvn }
\end{verbatim}

Seen \h{Known var\$}
\begin{code}
loadKLVar :: MonadFail mf 
           => VarTable -> Int -> String -> VarWhen -> [Token] 
           -> mf (VarTable,[Token])
loadKLVar vt _ lvar vw ((lno,TSym "="):rest)  
                              =  loadKLVarIsContainer vt lno lvar vw rest
loadKLVar vt _ lvar vw ((lno,TSym "::"):rest)  
                          =  loadKLVarIsAbsContainer vt lno lvar vw rest
loadKLVar vt _ lvar vw ((lno,ttyp):_)
  = fail ( "loadKLVar: unexpected token "
           ++show ttyp++" at line "++show lno )
loadKLVar vt lno lvar vw []  =  premImport "known list-var" lvar lno 
\end{code}

Seen \h{Known var\$ =}, 
expect a list enumeration wrapped with \h{< \dots >},
or a set enumeration wrapped with \h{\{ \dots \}}
\begin{code}
listOpen = TSym "<"; listClose = TSym ">"; listBlock = (listOpen,listClose)
setOpen = TOpen "{"; setClose = TClose "}"; setBlock = (setOpen,setClose)

loadKLVarIsContainer :: MonadFail mf 
                  => VarTable -> Int -> String -> VarWhen -> [Token] 
                  -> mf (VarTable,[Token])
loadKLVarIsContainer vt lno lvar vw [] = premAfter ["Known",lvar,show lno]
loadKLVarIsContainer vt _   lvar vw tokens@((lno,tok):_)
  | tok == listOpen  = do
      (block,beyond) <- getBlock listBlock tokens
      (list,rest) <- loadSepList (TSep ",") loadGenVar block
      vt' <- addKnownVarList (Vbl (jId lvar) ObsV vw) list  vt
      return (vt',beyond)
  | tok == setOpen  = do
      (block,beyond) <- getBlock setBlock tokens
      (list,rest) <- loadSepList (TSep ",") loadGenVar block
      vt' <- addKnownVarSet (Vbl (jId lvar) ObsV vw) (S.fromList list)  vt
      return (vt',beyond)
  | otherwise = fail $ unlines'
      [ "loadKLVarIsContainer: expected '<' or '{'"
      , "but got "++renderTokTyp tok++" at line "++show lno ]
\end{code}


Seen \h{Known var\$ ::}, expect keyword \h{list} or \h{set}.
\begin{code}
loadKLVarIsAbsContainer :: MonadFail mf 
                  => VarTable -> Int -> String -> VarWhen -> [Token] 
                  -> mf (VarTable,[Token])
loadKLVarIsAbsContainer vt lno lvar vw []  =  premImport "list or set" lvar lno
loadKLVarIsAbsContainer vt lno lvar vw ((lno',TVar abstract _):rest)
  | abstract == "list" = do
      vt' <- addAbstractVarList (Vbl (jId lvar) ExprV vw) vt
      return (vt',rest)
  | abstract == "set" = do
      vt' <- addAbstractVarSet (Vbl (jId lvar) ExprV vw) vt
      return (vt',rest)
loadKLVarIsAbsContainer vt lno lvar vw ((lno',tok):rest)
  = fail ( "loadKLVarIsAbsContainer("++lvar++"): unexpected token "
           ++renderTokTyp tok++" at line "++show lno' )
\end{code}


\subsection{Generate VarTable}


We start every entry with the ``Known'' keyword:
\begin{code}
genVarTable :: VarTable -> String
genVarTable (VarData (vtname,vtable,stable,dtable))
  = '\n':showTable genKnownVar (M.assocs vtable) ++
    '\n':showTable genKnownLstVar (M.assocs stable) ++
    '\n':showTable genKnownDynamic (M.assocs dtable)
  where showTable showMapping alist  
          =  unlines' $ map ( ((kKnown++" ")++) . showMapping ) alist 

genKnownVar :: (Variable,VarMatchRole) -> String
genKnownVar (v,KnownConst trm) = genVariable v ++ " = " 
  ++ kBegin ++ " " ++ genTerm trm ++ " " ++ kEnd
genKnownVar (v,KnownVar typ) = genVariable v ++ " : " ++ genType 4 typ ++ " ."
genKnownVar (gv,GenericVar) = genVariable gv ++ " :: generic"
genKnownVar (iv,InstanceVar gv) 
  = genVariable iv ++ " "++kInstanceOf++" " ++ genVariable gv
genKnownVar (v,vmr) = "" -- unknown variable

-- static list variables
genKnownLstVar :: (Variable,LstVarMatchRole) -> String
genKnownLstVar (lv,KnownVarList vl _ _) 
  = genVariable lv ++ "$ = < " ++ intercalate "," (map trGVar vl) ++ " >"
genKnownLstVar (lv,KnownVarSet vs _ _) 
  = genVariable lv ++ "$ = {" 
    ++ intercalate "," (S.toList (S.map trGVar vs)) ++ "}"
genKnownLstVar (lv,AbstractList) 
  = genVariable lv ++ "$ :: list"
genKnownLstVar (lv,AbstractSet) 
  = genVariable lv ++ "$ :: set"
genKnownLstVar (lv,lvmr) = ""


genKnownDynamic :: (IdAndClass,DynamicLstVarRole) -> String
genKnownDynamic ((id,vc),DynamicList vl lvl _ _) 
-- we can infer vc from the classes of vl and lvl 
-- which should also be known-var
-- we render using before-variables:  'lst$ = .. 'v ... 'lv$
  =  "'" ++ trId id ++ "$ = < "
    ++ intercalate "," (map (("'"++) . idName) vl)
    ++ (if length vl > 0 && length lvl > 0 then "," else "")
    ++ intercalate "," (map (("'"++) . (++"$") . idName) lvl)
    ++ " >"
genKnownDynamic ((id,vc),DynamicSet vs lvs _ _) 
  =  "'" ++ trId id ++ "$ = {"
    ++ intercalate "," (S.toList (S.map (("'"++) . idName) vs))
    ++ (if S.size vs > 0 && S.size lvs > 0 then "," else "")
    ++ intercalate "," (S.toList (S.map (("'"++) . (++"$") . idName) lvs))
    ++ "}"
genKnownDynamic ((id,vc),DynamicAbsList) =  trId id ++"$' :: list "
genKnownDynamic ((id,vc),DynamicAbsSet) =  trId id ++"$' :: set "
genKnownDynamic ((id,vc),dlvr) = ""
\end{code}

\newpage
\section{Blocks}

We have a notion of blocks
which are a contiguous run of text bracketed by `BEGIN` and `END`.

\begin{code}
getBlock :: MonadFail mf 
         => (TokenType,TokenType) -> [Token] -> mf ([Token],[Token])
getBlock _ [] = fail "no block"
getBlock (tBegin,tEnd) ((lno,tok):rest)
  | tok == tBegin  =  scanBlock tEnd [] rest
getBlock (tBegin,tEnd) (tok@(lno,_):_)
  = fail $ unlines' [ "getBlock: "++renderTokTyp tBegin++" expected"
                    , "but "++renderToken tok++" found at line "++show lno
                    ]

-- 
scanBlock :: MonadFail mf 
             => TokenType -> [Token] -> [Token] -> mf ([Token],[Token])
scanBlock _ sofar []  =  premDuring ["scanning block"]
scanBlock tEnd sofar ((lno,tok):rest)
  | tok == tEnd           =  return (reverse sofar, rest)
scanBlock tEnd sofar (tok:rest)  =  scanBlock tEnd (tok:sofar) rest
\end{code}

Laws, Conjectures and know Terms use \h{BEGIN} \dots \h{END} blocks:
\begin{code}
beBlock = (TVar "BEGIN" Static,TVar "END" Static)
\end{code}

\newpage
\section{Laws}

\subsection{Load Law}

A law starts on a new line,
but can also involve many lines.
The format is:
\begin{verbatim}
Law conj_name BEGIN
  provenance
, <term-text>
, <side-cond>
END
\end{verbatim}

\begin{code}
loadLaw :: MonadFail mf 
          => String -> [Token] 
          -> mf (Law,[Token])
loadLaw lawname []  =  premAfter [kLaw,lawname,kBegin]
loadLaw lawname tokens = do
  (block,beyond) <- getBlock beBlock tokens
  (provenance,rest1) <- loadProvenace block
  case rest1 of
    []  ->  premAfter [kLaw,show provenance ]
    ((_,TSep ","):rest2) -> do
      (term,rest3) <- parseTerm rest2
      case rest3 of
        [] -> return (((lawname,(mkAsn term scTrue)),provenance),beyond)
        ((_,TSep ","):rest4) -> do
          (sc,rest5) <- loadSideCond rest4
          return (((lawname,(mkAsn term sc)),provenance),beyond)
        (tok@(lno,_):_) -> fail $ unlines'
          [ "loadLaw: unexpected token after provenance"
          , renderToken tok ++ " at line "++show lno ]
    (tok@(lno,_):_) -> fail $ unlines'
      [ "loadLaw: unexpected token after provenance"
      , renderToken tok ++ " at line "++show lno ]

loadProvenace :: MonadFail mf => [Token] -> mf (Provenance,[Token])
loadProvenace []  =  premAfter [kBegin]
loadProvenace ((_,TVar  "axiom" Static):rest) 
  = return (Axiom,rest)
loadProvenace ((_,TVar  "assumed" Static):rest) 
  = return (Assumed,rest)
loadProvenace ((_,TVar  "proven" Static)
                :(_,TVar i Static):rest) 
  = return (Proven i,rest)
loadProvenace ((_,TVar  "suspect" Static)
                :(_,TVar i Static):rest) 
  = return ((Suspect i),rest)
loadProvenace (tok@(lno,_):_)
  = fail $ unlines'
      [ "loadProvenace: unexpected token after "++kBegin 
      , renderToken tok ++ "at line " ++ show lno ]
\end{code}

\subsection{Generate Laws}


\begin{code}
genLaws :: [Law] -> String
genLaws laws  =  unlines' $ map genLaw laws

genLaw :: Law -> String
genLaw ((name,Assertion tm sc),provenance)
  = unlines' ( [ "", kLaw ++ " " ++ name ++ " " ++ kBegin
               , " " ++ genProv provenance
               , " ," , genTerm tm ]
               ++ (if isTrivialSC sc then [] else [",",genSideCond sc])
               ++ [ kEnd ] )

genProv Axiom            =  "axiom"
genProv (Proven proof)   =  "proven " ++ proof
genProv (Suspect proof)  =  "suspect " ++ proof
genProv Assumed          =  "assumed"
\end{code}


\subsection{Load Conjecture}

A conjecture starts on a new line,
but can also involve many lines.
The format is
\begin{verbatim}
Conjecture conj_name
BEGIN
  <term-text>
, 
  <sc-text>
END
\end{verbatim}

\begin{code}
loadConjecture :: MonadFail mf 
                 => String -> [Token] 
                 -> mf (NmdAssertion,[Token])
loadConjecture conjname []  =  premAfter [kConjecture,conjname]
loadConjecture conjname tokens = do
  (block,beyond) <- getBlock beBlock tokens
  (term,rest2) <- parseTerm block
  case rest2 of
    [] -> return ( ( conjname, mkAsn term scTrue ), beyond )
    ((_,TSep ","):rest3) -> do
      (sc,rest4) <- loadSideCond rest3
      return ( ( conjname, mkAsn term sc ), beyond )
    (tok@(lno,_):_) -> 
      fail $ unlines
        [ "loadConjecture: unexpected token after term"
        , renderToken tok ++ " at line "++show lno ]
\end{code}

\subsection{Generate Conjectures}

\begin{code}
genConjectures :: [NmdAssertion] -> String
genConjectures nmdassns  =  unlines' $ map genConjecture nmdassns
\end{code}
\begin{code}

genConjecture :: NmdAssertion -> String
genConjecture (name,Assertion tm sc)
  = unlines'  ( [ "", kConjecture ++ " " ++ name ++ " " ++ kBegin 
                , "  " ++ genTerm tm ]
                ++ (if isTrivialSC sc then [] else [", " ++ genSideCond sc])
                ++ [ kEnd ] )
\end{code}

\newpage
\section{Terms}

The abstract syntax:
\begin{eqnarray*}
   b &\in& Bool
\\ n &\in& Num
\\ i &\in& Ident
\\ s &\in& \setof{nonsub,cansub}
\\ v &\in& Var = Ident \times VarWhen
\\ \lst v &\in& LVar = Var \times Less
\\ g &\in& GVar =  Var \uplus LVar
\\ gs &\in& GVarList = GVar^*
\\ T &\in& Type
\\ t &\in& Term ::= b
               \mid n
               \mid v
               \mid i~s~(t_1,\dots,t_n)
               \mid \mathcal Q ~i ~gs \bullet t
               \mid \mathcal X ~i ~t
               \mid v : T
\\ && \quad \mid t [t_1,\dots,t_n/g_1,\dots,g_n]
\\ && \quad \mid \mathcal I ~i_{top} ~ s_{top} ~i_{ix} ~ s_{ix} 
                    ~(\lst v_1,\dots,\lst v_n)
\\ && \quad \mid (~t~)
\end{eqnarray*}

The concrete syntax (non-terminals in \verb@<..>@).
First, the bits and pieces, then the term syntax,
and finally the key words and symbols.
\begin{code}
syntax_bits
 = [ "** Lexical Tokens:"
   , "n : int with optional leading minus"
   , "i : reasonEq identifier"
   , "s : substitutability non(N) can(S))"
   , "** Variable Syntax:"
   , "<v> ::= i | 'i | i' | i'i"
   , "by default lowercase i are ObsVar, uppercase are TermVar"
   , "we could have more nuanced defaults"
   , "we could declare variables seperately and post-process them"
   , "should the known variables (so far) be passed as a parameter?"
   , "<lv> ::= <v>$"
   , "<gv> ::=  <v> | <lv>"
   ]
\end{code}
\begin{code}
term_definition
 = [ "** Term Syntax:"
   , "<b> ::= true | false"
   , "<q> ::= QS | QL"
   , "<t> ::= <b>  |  n  | <v>"
   , "     |  i s ( <t> , ... , <t> )"
   , "     |  <q> i <gv> ... <gv> @ <t>"
   , "     |  CLS i <t>"
   , "     |  SUB [ (<v>,<t>)* ]<t> "
   ]
\end{code}

\newpage
The tokens that can start a term are: 
\verb"true false n <v> i <q> CLS SUB (". 
\begin{code}
key_names 
 = [ "** Keywords:   true  false  QS  QL CLS"
   , "** Keysymbols: ?  $  (  ,  )  @"
   ]
kTrue = "true"
kFalse = "false"
kSetBind = "QS"
kListBind = "QL"
kClosure = "CLS"
kSubst = "SUB"
kIter = "ITER"
kCS = "CS"
kNS = "NS"
kLstVar = '$'
kSep = ','
kQBody = "@"
term_syntax = syntax_bits ++ term_definition ++ key_names
\end{code}


\subsection{Generate Term}

\begin{code}
genSBBL s = if s then kCS else kNS

genTerm :: Term -> String
genTerm (Val typ (Boolean b)) = if b then kTrue else kFalse
genTerm (Val typ (Integer i)) = show i
genTerm (Var typ var) = genVariable var
genTerm (Cons typ subable (Identifier i _) terms) 
  = i ++ " " ++ (genSBBL subable) ++ " "
      ++ "("
      ++ (intercalate [kSep] $ map genTerm terms)
      ++ ")"
genTerm (Bnd typ (Identifier quant _) vs term)
  = kSetBind ++ " " ++ quant
    ++ " " ++ intercalate " " (S.toList (S.map genGenVar vs))
    ++ "\n  " ++ kQBody 
    ++ "  " ++ genTerm term
genTerm (Lam typ (Identifier lambda _) vl term)
  = kListBind ++ " " ++ lambda
    ++ " " ++  intercalate " " (map genGenVar vl)
    ++ "\n  " ++kQBody 
    ++ " " ++ genTerm term
genTerm (Cls (Identifier kind _) term) 
  = kClosure ++ " "++kind++"\n  "++genTerm term
genTerm (Sub typ term (Substn vts lvlvs))
  = kSubst ++ " [" ++ genTermVarSubs (S.toList vts) ++ " "
                   ++ genLVarSubs (S.toList lvlvs) ++ "] "
    ++ genTerm term
genTerm (Iter typ sa na si ni lvs)
  = kIter 
    ++ " " ++ genSBBL sa ++ " " ++ idName na
    ++ " " ++ genSBBL si ++ " " ++ idName ni
    ++ " ["++intercalate " " (map genListVariable lvs)++"]"
genTerm (VTyp typ var) = "VT-stuff?"
\end{code}

\begin{code}
genTermVarSubs vts = intercalate " " $ map genTermVarSub vts
genTermVarSub (v,t) = "("++genVariable v++","++genTerm t++")"

genLVarSubs lvlvs = intercalate " " $ map genLVarSub lvlvs
genLVarSub (tlv,rlv) 
  = "("++genListVariable tlv++","++genListVariable rlv++")"
\end{code}


\subsection{Load Term}


Truth builders:
\begin{code}
true = Vbl (fromJust $ ident "true") PredV Static
trueP = fromJust $ pVar ArbType true
false = Vbl (fromJust $ ident "false") PredV Static
falseP = fromJust $ pVar ArbType false
mkTrue n | isUpper $ head n  =  trueP
mkTrue _ =  Val bool $ Boolean True
mkFalse n | isUpper $ head n  =  falseP
mkFalse _  =  Val bool $ Boolean False
\end{code}

Making variables and variable-terms

For now the variable class is determined by the first character
of the identifier.
The simplest is the case, lower being an observable, higher a term.

\begin{code}
mkV id1 vw 
  | isUpper $ head iname  =  Vbl id1 PredV vw
  | otherwise             =  Vbl id1 ObsV  vw
  where iname = idName id1

mkLV id1 vw  = LVbl (mkV id1 vw) [] []

mkVarTerm id1 vw  =  fromJust $ var arbpred $ mkV id1 vw

tok2GVar :: Token -> GenVar
tok2GVar (_,(TVar  nm vw)) = StdVar $ mkV  (jId nm) vw
tok2GVar (_,(TLVar nm vw)) = LstVar $ mkLV (jId nm) vw
\end{code}

Subability:
\begin{code}
loadSBBL str
  | str == kCS  =  return True
  | str == kNS  =  return False
  | otherwise = fail 
     ( "load-subability: expected "++kCS++" or "++kNS ++ "but got "++str )
\end{code}


\newpage

\subsection{Term Parser}

\begin{code}
parseTerm :: MonadFail m => [Token] -> m (Term, [Token])
parseTerm [] =  fail "parseTerm: nothing to parse"
\end{code}

\paragraph{Numbers}~

\begin{code}
parseTerm ((_,TNum n):tts) = return ( Val int $ Integer n, tts)
\end{code}

\paragraph{Symbols}

Symbols are valid identifiers

\begin{code}
parseTerm ((_,TSym consName):(_,TVar subable Static ):(_,TOpen "("):tts)
  | subable == "N" = parseCons cons False [] tts
  | subable == "S" = parseCons cons True  [] tts
  where cons = jId consName
parseTerm ((_,TSym sym):tts) = return (mkVarTerm (jId sym) Static, tts)
\end{code}

\paragraph{Constructions}

Important: we must check for constructions before we
check for lone identifiers.

\paragraph{Identifiers}

We check for constructions first \dots

\begin{code}
parseTerm ((_,TVar consName vw):(_,TVar subable Static ):(_,TOpen "("):tts)
  | subable == kNS = parseCons cons False [] tts
  | subable == kCS = parseCons cons True  [] tts
  where 
    cons = jId consName
parseTerm ((_,TVar nm vw):tts)
  | nm == kTrue      =  return ( mkTrue nm,  tts)
  | nm == kFalse     =  return ( mkFalse nm, tts)
  | nm == kSetBind   =  parseSetQ tts
  | nm == kListBind  =  parseListQ tts
  | nm == kClosure   =  parseClosure tts
  | nm == kSubst     =  parseSubstn tts
  | nm == kIter      =  parseIter tts
  | otherwise        =  return (mkVarTerm (jId nm) vw, tts)
\end{code}

\paragraph{Bad Start}~


\begin{code}
parseTerm (tt:tts)  = fail ("parseTerm: unexpected token: "++renderToken tt)
\end{code}

\subsection{Term Helpers}

Seen identifier and opening parenthesis.
$$ i(~~~t_1,\dots,t_n) $$
Look for sub-term, or closing parenthesis.
\begin{code}
parseCons :: MonadFail mf 
          => Identifier -> Bool -> [Term] -> [Token]-> mf (Term,[Token])
parseCons id1 subable smretbus ((_,TClose ")") : tts)
  = return ( Cons arbpred subable id1 $ reverse smretbus, tts)
parseCons id1 subable smretbus tts
  = do (tsub',tts') <- parseTerm tts
       parseCons' id1 subable (tsub':smretbus) tts'
\end{code}

\newpage
Seen (sub-) term.
Looking for comma or closing parenthesis
\begin{code}
parseCons' :: MonadFail mf 
           => Identifier -> Bool -> [Term] -> [Token]-> mf (Term,[Token])
parseCons' id1 subable smretbus ((_,TSep ",") : tts)
  =  parseCons id1 subable smretbus tts
parseCons' id1 subable smretbus ((_,TClose ")") : tts)
  =  return ( Cons arbpred subable id1 $ reverse smretbus, tts)
parseCons' id1 subable smretbus tts
  =  fail $ unlines'
       [ "parseCons': expected ',' or ')'"
       , "got "++show (take 3 tts)++" ..." ]
\end{code}


\paragraph{Quantifiers}~

Seen \texttt{QS}, 
$$ QS~~~i~g_1 \dots g_n \bullet t $$
parse the quantifier:
\begin{code}
parseSetQ :: MonadFail mf => [Token] -> mf (Term,[Token])
parseSetQ []  =  premDuring ["parseSetQ"]
parseSetQ ((_,TVar nm Static) : tts) = do
  let i = jId nm
  (i,sg,term,tts') <- parseQVars i [] tts
  qsterm <- pBnd i (S.fromList $ map tok2GVar sg) term
  return (qsterm,tts')
parseSetQ (tok:_) = fail ("parseSetQ: exp. ident, found: "++renderToken tok)
\end{code}

Seen \texttt{QL}, 
$$ QL~~~i~g_1 \dots g_n \bullet t $$
parse the quantifier:
\begin{code}
parseListQ :: MonadFail mf => [Token] -> mf (Term,[Token])
parseListQ []  = premDuring ["parseListQ"]
parseListQ ((_,TVar nm Static) : tts) = do
  let i = jId nm
  (i,sg,term,tts') <- parseQVars i [] tts
  lsterm <- pLam i (reverse $ map tok2GVar sg) term
  return (lsterm,tts')
parseListQ (tok:_) = fail ("parseListQ: exp. ident, found: "++renderToken tok)
\end{code}

Seen \texttt{Qx i}, and zero or more \texttt{g\_i}:
$$ Qx~i~g_1 \dots g_i ~~~~~ g_{i+1} \dots g_n \bullet t $$
parse the quantifier:
\begin{code}
parseQVars i _ []  =  premDuring ["parseQVars:",trId i]
parseQVars i sg ((_,TSym sym) : tts)
  | sym == kQBody  =  parseQBody i sg tts
parseQVars i sg (v@(_,TVar _ _)    : tts)   =  parseQVars i (v:sg) tts
parseQVars i sg (lv@(_,TLVar _ _) : tts)   =  parseQVars i (lv:sg) tts
parseQVars i sg ((lno,ttyp) : _)  
  = fail ( "parseQVars: unexpected token "++renderTokTyp ttyp
           ++" at line "++show lno)
\end{code}

Seen \texttt{Qx i g\_1 .. g\_n @}, 
$$ Qx~i~g_1 \dots g_n \bullet ~~~ t $$
parse the body term
\begin{code}
parseQBody i _ [] = fail ("parseQVars: "++trId i++" (missing body)")
parseQBody i sg tts = do
  (term,toks) <- parseTerm tts
  return (i,sg,term,toks)
\end{code}


\paragraph{Closure}~

Seen \texttt{CLS}.
\begin{code}
parseClosure [] = premDuring ["parseClosure"]
parseClosure ((lno,TVar nm _):rest1) = do
  (term,rest2) <- parseTerm rest1
  return (Cls (jId nm) term,rest2)
parseClosure ((lno,ttyp):rest) = fail $ unlines'
  [ "parseClosure: expected name"
  , "but got "++renderTokTyp ttyp++" at line "++show lno]
  
\end{code}


\paragraph{Substitution}~

Seen \texttt{SUB}.
\begin{code}
parseSubstn [] = premDuring ["parseSubstn"]
parseSubstn ((lno,TOpen open):rest1)
  | open == "["  =  do
     ((vts,lvlvs),rest2) <- parseSubPairs [] [] rest1
     rest3 <- expectToken "parseSubstn" (TClose "]") rest2
     (term,rest4) <- parseTerm rest3
     sub <- substn vts lvlvs
     return (Sub (termtype term) term sub,rest4)
parseSubstn ((lno,ttyp):rest) = fail $ unlines'
  [ "parseSubstn: expected '['"
  , "but got "++renderTokTyp ttyp++" at line "++show lno]

parseSubPairs vts lvlvs []                      = return ((vts,lvlvs),[])
parseSubPairs vts lvlvs toks@((_,TClose "]"):_) = return ((vts,lvlvs),toks)

parseSubPairs vts lvlvs
   ((lno,TOpen "(")
   :vart@(_,TVar v _)
   :(_,TSep ","):rest1) = do
     (term,rest2) <- parseTerm rest1
     rest3 <- expectToken "parseSubPairs" (TClose ")") rest2
     parseSubPairs ((var,term):vts) lvlvs rest3
  where 
       (var,_) = fromJust $ loadVariable [vart]
       -- (term,_) = fromJust $ parseTerm [tt]

parseSubPairs vts lvlvs
   ((lno,TOpen "(")
   :lvart@(_,TLVar v _)
   :(_,TSep ",")
   :lvarr@(_,TLVar t _)
   :(_,TClose ")"):rest1) = parseSubPairs vts ((tlv,rlv):lvlvs) rest1
 where 
       (tlv,_) = fromJust $ loadListVariable [lvart]
       (rlv,_) = fromJust $ loadListVariable [lvarr]

parseSubPairs vts lvlvs toks = fail $ unlines'
  [ "parseSubPairs: expecting zero or more (v,t) or (tv$,rv$)" 
  , " but got "++show (take 5 toks)]
\end{code}

\paragraph{Iteration}

Seen \h{ITER}.
Expect subable,identifier,subable,identifier,list-variable list. 
\begin{code}
parseIter [] = premDuring ["parseIter"]
parseIter 
  ( (lno,TVar sa _) : (_,TVar na _) :
    (_,TVar si _) : (_,TVar ni _) : (_,TOpen "[") : rest1 ) = do
      asub <- loadSBBL sa
      isub <- loadSBBL si
      (lvars,rest2) <- loadListVariables "]" rest1
      return ( Iter ArbType asub (jId na) isub (jId ni) lvars
             , rest2 )
parseIter ((lno,ttyp):rest) = fail $ unlines'
  [ "parseIter: expected subable indicator"
  , "but got "++renderTokTyp ttyp++" at line "++show lno]
\end{code}

\subsubsection{Top-Level Term Reader}

\begin{code}
loadTerm :: MonadFail mf => String -> mf (Term, [Token])
loadTerm = parseTerm . tlex . prepare
\end{code}


\section{Side-Conditions}

\begin{code}
sidecond_definition
 = [ "<sc>     ::= NONE"
   , "          | opt( <vsc>+ )  opt( FREE <fvs> )"
   , "<vsc>    ::= VREL (opt( <disj>) | opt( <cov> )|  opt( <dyncov> ))"
   , "<fvs>    ::= (<v>)+"
   , "<disj>   ::= ( DISJ <v> FROM <v>+)"
   , "<cov>    ::= ( COV <v> BY <v>+)"
   , "<dyncov> ::= ( DYNCOV <v> BY <v>+)"
  ]

kNone = "NONE"
kFree = "FREE"
kVRel = "VREL"
kDisj = "DISJ"
kCovBy = "COV"
kDynCov = "DYNCOV"
kFrom = "FROM"
kBy = "BY"
\end{code}


\subsection{Generate Side-Condition}

\begin{code}
genSideCond :: SideCond -> String
genSideCond ([],fvs) | S.null fvs  =  "true"
genSideCond (vscs,fvs)  
  =  genVSCs vscs ++ genFVs (null vscs) fvs

genVSCs [] = ""
genVSCs vscs = kVRel ++ " " ++ (intercalate " " $ map genVSC vscs)

genVSC (VSC gv nvsD nvsC nvsCd) 
  = intcalNN " " [genD gv nvsD, genC gv nvsC, genCd gv nvsCd]

genD _ NA = ""
genD gv (The vs) = "("++kDisj++" "++genGenVar gv++" FROM "++genVS vs++")"

genC _ NA = ""
genC gv (The vs)  = "("++kCovBy++" "++genGenVar gv++" BY "++genVS vs++")"

genCd _ NA = ""
genCd gv (The vs) = "("++kDynCov++" "++genGenVar gv++" BY "++genVS vs++")"

genFVs noVSC fvs
  | S.null fvs  =  ""
  | otherwise   =  start ++ kFree++" " ++ genVS fvs
  where start = if noVSC then "" else "\n  "

genVS vs = intercalate " " $ map genGenVar $ S.toList vs
\end{code}

\subsection{Load Side-Condition}

Expecting on of \texttt{NONE}, \texttt{VREL}, and \texttt{FREE}.
\begin{code}
loadSideCond :: MonadFail mf => [Token] -> mf (SideCond, [Token])
loadSideCond [] = premDuring [ "loadSideCond" ]
loadSideCond toks@(tok@(lno,TVar nm _):rest)
  | nm == kNone  =  return (scTrue,rest)
  | nm == kVRel  =  parseVRel [] rest
  | nm == kFree  =  parseFree [] [] rest
loadSideCond ((lno,ttyp):_) = fail $ unlines'
  [ "loadSideCond: expected "++kNone++", "++kVRel++", "++kFree
  , " got "++renderTokTyp ttyp++" at line "++show lno ]
\end{code}

Seen \texttt{VREL}, zero or more \texttt{(\dots)},
expecting \texttt{(}, \texttt{FREE}, 
ended by \texttt{END}.
\begin{code}
parseVRel :: MonadFail mf 
          => [VarSideConds] -> [Token] -> mf (SideCond,[Token])
parseVRel vscs []  =  checkSC vscs [] []
parseVRel vscs toks@((lno,TVar nm _):rest)
  |  nm == kEnd  =  checkSC vscs [] toks
  |  nm == kFree  = parseFree vscs [] rest
parseVRel vscs ((lno,TOpen open):rest)
  | open == "("  =  parseVSC vscs rest  
parseVRel _ ((lno,ttyp):_) = fail $ unlines'
  [ "parseVRel: expected var-sidecond '(...)'"
  , " got "++renderTokTyp ttyp++" at line "++show lno ]
\end{code}

Seen \texttt{(}, expected \texttt{DISJ}, \texttt{COV}, \texttt{DYNCOV},
followed by gen-var, \texttt{FROM} or \texttt{BY}, gen-vars, and \texttt{)}.
\begin{code}
parseVSC :: MonadFail mf 
          => [VarSideConds] -> [Token] -> mf (SideCond,[Token])
parseVSC vscs [] = premDuring ["parseVRel"]
parseVSC vscs ((lno,TVar nm _):rest)
  | nm == kDisj    = parseSCRel1 kFrom disjfrom   vscs rest
  | nm == kCovBy   = parseSCRel1 kBy   coveredby  vscs rest
  | nm == kDynCov  = parseSCRel1 kBy   dyncovered vscs rest
parseVSC _ ((lno,ttyp):_) = fail $ unlines'
  [ "parseVSC: expected DISJ, COV, DYNCOV"
  , " got "++renderTokTyp ttyp++" at line "++show lno ]
\end{code}


Seen \texttt{(} and one of texttt{DISJ}, \texttt{COV}, or \texttt{DYNCOV}.
Expecting a general variable \dots
\begin{code}
parseSCRel1 :: MonadFail mf
            => String 
            -> (GenVar -> VarSet -> VarSideConds) 
            -> [VarSideConds]
            -> [Token]
            -> mf (SideCond,[Token])
parseSCRel1 sepk makesc vscs [] = premDuring ["parseSCRel1"]

parseSCRel1 sepk makesc vscs toks@((_,TVar nm _):_) = do
  (var,rest1) <- loadVariable toks
  rest2 <- expectToken "parseSCRel1-var" (TVar sepk Static) rest1
  parseSCRel2 makesc vscs (StdVar var) [] rest2

parseSCRel1 sepk makesc vscs toks@((_,TLVar nm _):_) = do
  (lvar,rest1) <- loadListVariable toks
  rest2 <- expectToken "parseSCRel1-lvar" (TVar sepk Static) rest1
  parseSCRel2 makesc vscs (LstVar lvar) [] rest2

parseSCRel1 sepk _ _ ((lno,ttyp):_) = fail $ unlines'
  [ "parseSCRel1: expected gv "++sepk++"varlist"
  , " got "++renderTokTyp ttyp++" at line "++show lno ]
\end{code}

Seen \texttt{( what gvar sepk}. 
Expecting a list of general variables followed by \texttt{)}.
\begin{code}
parseSCRel2 :: MonadFail mf
            => (GenVar -> VarSet -> VarSideConds) 
            -> [VarSideConds]
            -> GenVar
            -> [GenVar]
            -> [Token]
            -> mf (SideCond,[Token])
parseSCRel2 makesc vscs gv gvs [] = premDuring ["parseSCRel2"]

parseSCRel2 makesc vscs gv gvs ((lno,TClose ")"):rest)
  = parseVRel (makesc gv (S.fromList gvs):vscs) rest

parseSCRel2 makesc vscs gv gvs toks@((lno,TVar nm _):_) = do
  (var,rest1) <- loadVariable toks
  parseSCRel2 makesc vscs gv (StdVar var:gvs) rest1

parseSCRel2 makesc vscs gv gvs toks@((lno,TLVar nm _):_) = do
  (lvar,rest1) <- loadListVariable toks
  parseSCRel2 makesc vscs gv (LstVar lvar:gvs) rest1

parseSCRel2 sepk _ _ _ ((lno,ttyp):_) = fail $ unlines'
  [ "parseSCRel2: expected varlist"
  , " got "++renderTokTyp ttyp++" at line "++show lno ]
\end{code}


Seen \texttt{FREE}, zero or more \texttt{genvar},
expecting \texttt{genvar}, 
ended by \texttt{END}.
\begin{code}
parseFree :: MonadFail mf 
          => [VarSideConds] -> VarList -> [Token] -> mf (SideCond,[Token])
parseFree vscs gvs []  =  checkSC vscs gvs []
parseFree vscs gvs toks@((lno,TVar nm _):rest)
  |  nm == kEnd  =  checkSC vscs gvs toks
  |  otherwise   =  do
       (var,rest) <- loadVariable toks
       parseFree vscs (StdVar var:gvs) rest
parseFree vscs gvs toks@((lno,TLVar nm _):rest)
  |  nm == kEnd  =  checkSC vscs gvs toks
  |  otherwise   =  do
       (lvar,rest) <- loadListVariable toks
       parseFree vscs (LstVar lvar:gvs) rest
parseFree _ _ ((lno,ttyp):_) = fail $ unlines'
  [ "parseFree: expected gen-var"
  , " got "++renderTokTyp ttyp++" at line "++show lno ]
\end{code}

\begin{code}
checkSC :: MonadFail mf 
        => [VarSideConds] -> VarList -> [Token] -> mf(SideCond,[Token])
checkSC vscs gvs rest = do
  vscs' <- mergeVarConds vscs
  return ((vscs',S.fromList gvs),rest)
\end{code}

\section{Variables}

\subsection{Generate General Variable}

\begin{code}
genGenVar :: GenVar -> String
genGenVar (StdVar v) = genVariable v
genGenVar (LstVar lv) = genListVariable lv
\end{code}

\subsection{Load General Variable}


\begin{code}
loadGenVar :: MonadFail mf => [Token] -> mf (GenVar,[Token])
loadGenVar [] = premDuring ["loadGenVar"]
loadGenVar toks@((lno,TVar nm vw):_) = do
  (var,rest) <- loadVariable toks
  return (StdVar var,rest)
loadGenVar toks@((lno,TLVar nm vw):_) = do
  (lvar,rest) <- loadListVariable toks
  return (LstVar lvar,rest)
loadGenVar ((lno,tok):_) = fail $ unlines'
  [ "loadGenVar: expecting standard or list variable"
  , "but got "++renderTokTyp tok++" at line "++show lno]
\end{code}

\subsection{Generate List Variable}

\begin{code}
genListVariable :: ListVar -> String
genListVariable (LVbl (Vbl i vc Before) is js) 
  = '\'' : idName i ++ "$"
genListVariable (LVbl (Vbl i vc (During d)) is js)  
  =  idName i ++ "$" ++ '\'' : d
genListVariable (LVbl (Vbl i vc After) is js)       
  = idName i ++ "$" ++ "\'"
genListVariable (LVbl (Vbl i vc _) is js)           
  = idName i ++ "$" 
\end{code}

\subsection{Load List Variable}

\begin{code}
loadListVariable :: MonadFail mf => [Token] -> mf (ListVar,[Token])
loadListVariable [] = premDuring ["loadListVariable"]
loadListVariable ((lno,TLVar nm vw):rest) 
  = return (LVbl (Vbl (jId nm) ObsV vw) [] [],rest)
loadListVariable ((lno,tok):_) = fail $ unlines'
  [ "loadListVariable: expecting list variable"
  , "but got "++renderTokTyp tok++" at line "++show lno]

loadListVariables :: MonadFail mf 
                  => String -> [Token] -> mf ([ListVar],[Token])
loadListVariables close [] 
  = premDuring ["loadListVariables",close]
loadListVariables close ((lno,TClose str):rest)
  | str == close  =  return ([],rest)
loadListVariables close toks = do
  (lvar,rest1) <- loadListVariable toks
  (lvars,rest2) <- loadListVariables close rest1
  return (lvar:lvars,rest2)
\end{code}

\subsection{Generate Variable}

\begin{code}
genVariable :: Variable -> String
genVariable (Vbl i vc Before)      = '\'' : idName i
genVariable (Vbl i vc (During d))  =  idName i ++ '\'' : d
genVariable (Vbl i vc After)       = idName i ++ "\'"
genVariable (Vbl i vc _)           = idName i 
\end{code}

\subsection{Load Variable}

The Identifier datatype, enforced by \h{validIdent} includes decorations, 
like dashes and dollars,
and can also have symbols and trailing spaces.
\begin{code}
validVarRoot (c:rest)
  | isAlpha c  =  all validVarChar rest
validVarRoot _ = False
validVarChar '_' = True
validVarChar c  =  isAlphaNum c
\end{code}

For UTP variables we need to tighten this up a bit.

Here, for now, we simply make observation variables,
and let post-processing sort things out.
\begin{code}
loadVariable :: MonadFail mf => [Token] -> mf (Variable,[Token])
loadVariable [] = premDuring ["loadVariable"]
loadVariable ((lno,TVar nm vw):rest) = return (Vbl (jId nm) ObsV vw,rest)
loadVariable ((lno,tok):_) = fail $ unlines'
  [ "loadVariable: expecting standard variable"
  , "but got "++renderTokTyp tok++" at line "++show lno]
\end{code}

\newpage
\section{Types}

\subsection{Type Grammar}

Experimentation makes it clear that keywords are too heavy,
so we use parentheses a lot!
\def\typestart{Tokens that can start a type:  $id~($}
\def\typefollow{Tokens that can follow and continue a type: $\fun~id~(~$}
\def\typeopenfollow{(The) Token that can follow ( or $<$ is: $id$}
\def\typeidfollow{Tokens that can follow a name and continue a type: $id~(~<$}
\def\typeover{Tokens that can \emph{end} a type: $)$}
\def\varstart{Tokens that can start a variant:  $<$}
\def\varover{Tokens that can \emph{end} a variant: $>$}
\def\typegrammar{
\begin{eqnarray*}
\lefteqn{t \in Type}
\\ &::=&  name
\\ &\mid& \mathbf{(} ~t~ \fun ~t~\mathbf{)}
\\ &\mid& \mathbf{(}~name~t~\dots~t~\mathbf{)}
\\ &\mid& \mathbf{(}~name~v^*~\mathbf{)}
\\\lefteqn{v \in Variant}
\\ &::=& \mathbf{<}~name~~t~\dots~t~\mathbf{>}
\end{eqnarray*}
}
\typegrammar
\newline\typestart
\newline\typefollow 
\newline\typeopenfollow
\newline\typeidfollow
\newline\typeover
\newline\varstart
\newline\varover

\subsection{Generate Type}

\begin{code}
arbTypeString = "T"
bottomTypeString = "_"
funArrow = "->"
startCompType = "(" ; endCompType = ")"
startVariant = "<" ; endVariant = ">"
typeKeys = [ arbTypeString, bottomTypeString, funArrow
           , startCompType, endCompType, startVariant, endVariant ]

genType :: Int -> Type -> String
genType _ ArbType          = arbTypeString
genType _ BottomType       = bottomTypeString
genType _ (TypeVar i)      = idName i
genType _ (GivenType i)    = idName i
genType i (FunType td tr)  
  = startCompType++" "++genType (i+2) td++" "++
    funArrow++" "++genType (i+2) tr++" "++endCompType
genType _ (TypeCons i [])  = idName i  -- degen, GivenType?
genType i (TypeCons consi ts)  
  = startCompType ++ " " ++ genCons (i+2) (consi,ts) ++ " " ++ endCompType
genType i (AlgType algi fs)   
  = nl i startCompType ++" "++idName algi ++ 
    intercalate "" (map (genVariant (i+2)) fs) ++ nl i endCompType

type Variant = (Identifier,[Type])

genCons :: Int -> Variant -> String
genCons i (consi,ts) 
  = idName consi ++ " " ++ (intercalate " " (map (genType i) ts))

genVariant :: Int -> Variant -> String
genVariant i its
  = nl i startVariant ++ " " ++ genCons (i+2) its ++" "++endVariant

\end{code}

\newpage
\subsection{Load Type}

\typegrammar

Once parsing is complete we post-process 
names to pull out $\top$ and $\bot$ types.

\begin{code}
loadType :: MonadFail mf => [Token] -> mf (Type,[Token])
loadType [] = premDuring ["loadType"]
loadType ((lno,TVar name _):rest) = return (TypeVar $ jId name,rest)
loadType ((lno,TOpen open):rest)
  | open == startCompType   =  loadCompositeType rest
loadType toks = fail ("loadType: invalid start "++show (take 5 toks))
\end{code}

\typeopenfollow

Seen: \textbf{(}.
Expects an initial name, then looks at second token to determine what follows.
\begin{code}
loadCompositeType [] = premDuring ["loadCompositeType"]
loadCompositeType ((lno,TVar name _):rest1) 
  = loadCompType2 (TypeVar $ jId name) rest1
loadCompositeType toks@((lno,TOpen open):_)
  | open == startCompType = do
      (typ,rest1) <- loadType toks
      loadCompType2 typ rest1
loadCompositeType toks
  = fail ("loadCompositeType: invalid start "++show (take 5 toks))
\end{code}

Seen: \textbf{( type1} (a.k.a the ``head type'' \textbf).
Now looking for:
\\ (1) \textbf{)} ---result: \textbf{type1}.
\\ (2) \textbf{$\mathbf{\fun}$ type2)}  
---result: $\mathbf{type1 \fun type2}$.
\\ (3) \textbf{$\{\mathbf{<}$ nm $\mathbf{type^*}~>\}^*~\mathbf{)}$}
--- result: \textbf{name}~$\{\mathbf{<}$ nm $\mathbf{type^*}~>\}^*$,
only valid if head type is \textbf{name}.
\\ (4) \textbf{$\mathbf{type^+}$)} 
---result: $\mathbf{name(type^+)}$, 
only valid if head type is \textbf{name}.

\begin{code}
loadCompType2 htype [] = premDuring["loadCompType2",show htype]
-- (1)   ?  )
loadCompType2 head toks@((_,TClose close):rest1) = return (head,rest1)
-- (2)   ?  -> 
loadCompType2 dtyp toks@((_,TSym sym):rest1)
  | sym == funArrow  = do
      (rtyp,rest2) <- loadType rest1
      rest3 <- expectToken "loadCompType2 ->" (TClose endCompType) rest2
      return (FunType dtyp rtyp,rest3)
-- (3)   ?  <
loadCompType2 (TypeVar tid) toks@((_,TSym sym):_)
  | sym == startVariant  =  do
      (variants,rest1) <- loadVariants [] toks
      rest2 <- expectToken "loadCompType2 <" (TClose endCompType) rest1
      return (AlgType tid variants,rest2)
-- (4)   ?  terms
loadCompType2 (TypeVar tid) toks = loadProdType tid [] toks
-- ???
loadCompType2 typ toks = fail 
    ("loadCompType2  expected ')' \"->\" type '<',  got "++show (take 5 toks))
\end{code}

Seen: \textbf{( name $t^*$}.
Expecting a type or \textbf{)}.
\begin{code}
loadProdType pid _ [] = premDuring ["loadProdType",idName pid]
loadProdType pid sepyt ((lno,TClose close):rest1)
  | close == endCompType  
     -- we need to check below for function arrows
     =  return (TypeCons pid (reverse sepyt),rest1)
loadProdType pid sepyt toks = do
  (typ,rest1) <- loadType toks
  loadProdType pid (typ:sepyt) rest1
\end{code}


Seen \textbf{sum sumname}, 
called from top-level knowning that the next token is $\mathbf{<}$.
\begin{code}
loadVariants :: MonadFail mf 
               => [Variant] -> [Token] -> mf ([Variant],[Token])
loadVariants stnairav toks@[] = return (reverse stnairav,toks)
loadVariants stnairav toks@(tok@(lno,TClose close):rest1)
  | close == endCompType  =  return (reverse stnairav,toks)
loadVariants stnairav toks@(tok@(lno,TSym str):_)
 | str /= startVariant  
     = fail ("loadVariants: expecting '<' but got "++show tok)
 | otherwise = do
      (variant,rest1) <- loadVariant toks
      case rest1 of 
        [] -> premDuring ["loadVariants",endVariant]
        _ -> loadVariants (variant:stnairav) rest1
loadVariants stnairav toks = fail $ unlines'
  [ "loadVariants("++show (length stnairav)++" so far):  expected ')' or '<'"
  , "but got "++show (take 5 toks) ]
\end{code}

Looks for $\mathbf{<}~name~t_1~t_2~\dots~t_n~\mathbf{>}$
\begin{code}
loadVariant [] = premDuring ["loadVariant"]
loadVariant ((lno,TSym sym):rest1)
  | sym == startVariant  = do
      (Vbl vid _ _,rest2) <- loadVariable rest1
      (types,rest3) <- loadTypes [] rest2
      rest4 <- expectToken "loadVariant" (TSym endVariant) rest3
      return ((vid,types),rest4)
loadVariant toks = fail $ unlines'
  [ "loadVariant: expecting '<'"
  , "but saw "++show (take 5 toks) ]
\end{code}


Expecting a list of zero or more types, ended by \textbf{endp} or \textbf{endv}.
\begin{code}
loadTypes :: MonadFail mf => [Type] -> [Token] -> mf ([Type],[Token])
loadTypes sepyt toks@[]            = return (reverse sepyt,toks)
loadTypes sepyt toks@((lno,TClose end):rest)
  | end == endCompType  =  return (reverse sepyt,toks)
loadTypes sepyt toks@((lno,TSym end):rest)
  | end == endVariant  =  return (reverse sepyt,toks)
loadTypes sepyt toks = do
  (typ',rest1) <- loadType toks
  loadTypes (typ':sepyt) rest1
\end{code}

\typestart

\begin{code}
typeStart :: Token -> Bool
typeStart (_,TVar _ _)                            =  True
typeStart (_,TSym _)                              =  True
--typeStart (_,TOpen open) | open == openParString  =  True
typeStart _                                       =  False
\end{code}

\typeover

\begin{code}
typeOver :: Token -> Bool
typeOver (_,TSym sym)     | sym   == dot             =  True
-- typeOver (_,TClose close) | close == closeParString  =  True
typeOver _                                           =  False
\end{code}


\section{Load Separated List}

Called to parse a list of items with a separator symbol,
and consumes entire input.
\begin{code}
loadSepList :: MonadFail m 
            => TokenType -> ([Token] -> m (a, [Token])) -> [Token] 
            -> m ([a], [Token])
loadSepList sep objparser [] = return ([],[])
loadSepList sep objparser tokens = do
  (obj,rest1) <- objparser tokens
  case rest1 of
    [] ->  return ([obj],rest1)
    _  -> do
      rest2 <- expectToken "loadSepList" sep rest1
      (objs,rest3) <- loadSepList sep objparser rest2
      return (obj:objs,rest3)
\end{code}

\section{Indentation}

We need to keep things readable, using indentation when we generate sources.

Indenting occurs immediately after a newline,
so we define an indentation-aware newline function,
that takes an indent and string as parameters:
\begin{code}
nl :: Int -> String -> String
nl i s = '\n':replicate i ' ' ++ s
\end{code}


\section{Lexical Basics}

We limit everything to the ASCII subset,
simply because UTF8 Unicode is a mess
(and it's the nicest one!).

In general we will take a text file,
and add line numbers, and remove blank lines before processing.



\begin{code}
type NumberedLine = (Int,String)
prepare :: String -> [NumberedLine]
prepare 
  = filter nonNull . zip [1..] . lines
  where nonNull (_,string) = not $ all isSpace string
\end{code}


\subsection{Tokens}

We have the following token classes:
\begin{description}
  \item [Numbers]~
    Just integers for now,
    with a minus-sign to start if negative,
    with no whitespace between it and the one or more (decimal) digits.
  \item [Identifiers]~
    These start with an alpha, 
    and can follow with alpha, numeric, and underscore
    (\h{Lexbase.validIdent} is too liberal).
    with added decoration for UTP variable classification.
    \textbf{Keywords} form a subset of these.
    We expect identifiers to have one of the following concrete forms:
      \textsf{ident}%
    , \texttt{?}\textsf{ident}%
    , \textsf{ident}\texttt{?}%
    , \textsf{ident}\texttt{?}\textsf{alphas}.
  \item [Delimiters]~
    Small tokens used for general punctuation,
    further classified into: matched (Open/Close) bracketing; and separators.
  \item [Symbols]~
    Tokens assembled from everything else,
    provided they satisfy \texttt{LexBase.validIdent}.
\end{description}
We shall use the dash/prime character as a decoration to indicate variable temporality.
\begin{code}
beforeChar = '\'' -- backquote is visually disruptive
afterChar = '\''
lstvChar = '$'
\end{code}

\begin{tabular}{|l|c|l|}
\hline
  Temp. & Math. & Script 
\\\hline
  Static & $v$ & \texttt{v}
\\\hline
  Before & $v$ & \verb"'v"
\\\hline
  During & $v_m$ & \verb"v'm"
\\\hline
  After & $v'$ & \verb"v'"
\\\hline
\end{tabular}

If any of the above is immediately followed by `\$',
then it denotes the corresponding list-variable.

\subsection{Token Data Type}

\begin{code}
data TokenType
  =  TNum   Integer
  |  TVar   String VarWhen  -- v 'v v'm v'
  |  TLVar  String VarWhen  -- v$ 'v$ v$'m v$'
  |  TOpen  String
  |  TClose String
  |  TSep   String
  |  TSym   String
  |  TErr   String
  deriving (Eq,Show)
type Token = (Int,TokenType)
\end{code}

We provide some rendering code, mostly for error reporting:
\begin{code}
renderTokTyp :: TokenType -> String
renderTokTyp (TNum i) = show i
renderTokTyp (TVar  nm Static)     = nm
renderTokTyp (TVar  nm Before)     = beforeChar : nm
renderTokTyp (TVar  nm (During d)) = nm ++ afterChar : d
renderTokTyp (TVar  nm After)      = nm ++ [afterChar]
renderTokTyp (TLVar nm Static)     = nm ++ "$"
renderTokTyp (TLVar nm Before)     = beforeChar : nm ++ "$"
renderTokTyp (TLVar nm (During d)) = nm ++ '$' : afterChar : d
renderTokTyp (TLVar nm After)      = nm ++ ['$',afterChar]
renderTokTyp (TOpen str) = str
renderTokTyp (TClose str) = str
renderTokTyp (TSep str) = str
renderTokTyp (TSym sym) = sym
renderTokTyp (TErr str) = str

renderToken (lno,toktyp) = renderTokTyp toktyp
-- useful for lists

renderToken' tok = ' ' : renderToken tok
\end{code}


\subsection{Character Classes}

We shall predefine delimiters as constant for now.
Later on these will be parameters to the whole parsing process.
\begin{code}
openings  =  "([{"
closings  =  "}])"
separators = ","  -- really don't want too many of these (definitely not ';' !)
\end{code}

Anything else is a symbol (for now.)
\begin{code}
issymbol c
  | isSpace c  =  False
  | isDigit c  =  False
  | isAlpha c  =  False
  | c `elem` beforeChar : afterChar : openings ++ closings ++ separators
               =  False
  | otherwise  =  True
\end{code}

\subsection{Word Classes}

Making symbols and identifiers:
\begin{code}
mkSym str
  | validIdent str  =  TSym str
  | str == "."      =  TSym str
  | otherwise =  TErr ("mkSym: invalid symbol "++str)

mkName tcons str
  = let (root,temp) = extractTemporality str
    in if validIdent root 
        then tcons root temp
        else TErr ("mkSym: invalid name "++str)

mkId str   = mkName TVar str

mkLVar str = mkName TLVar str

-- v 'v v'm v'
-- v$ 'v$ v$'m v$'
extractTemporality cs -- non-empty
 | c1 == beforeChar      =  ( tail cs, Before) --  ' v    ' v$
 | last cs == afterChar  =  ( init cs, After ) --  v '    v$ '
 -- remaining: v v$ v'm  v$'m

-- NEED TO REWORK BELOW

 --    nm       nm$    nm'$    nm'subscr    nm'subscr$
 --     v        v      v         v             v
 --   (nm,S) (nm$,S) (nm$,A) (nm,D subscr) (nm$,D subscr)
 | null rest = ( cs, Static )  -- nm ,  nm$
 | last subscr == lstvChar && null (init subscr)   -- nm'$
                         =  ( root++[lstvChar], After) 
 | have root && have subscr && all isAlphaNum subscr -- nm'subscr
                         =  ( root,    During subscr )
 | have root && have subscr && last subscr == lstvChar  -- nm'subscr$
                         =  ( root++[lstvChar], During $ init subscr )
 | otherwise = ( cs, Static )
 where
    c1 = head cs
    (root,rest) = break (== afterChar) cs
    have [] = False ; have _ = True
    subscr = ttail rest
 

-- tail recursion often requires reversal at end of accumulated lists
mkMys  =  mkSym . reverse   ;   mkDi   =  mkId . reverse
mkRavL = mkLVar . reverse
\end{code}

\subsection{Law Name Reader}

\begin{code}
mkLawName :: [String] -> String
mkLawName ss
  = intercalate "_" $ map showTTok $ concat $ map (tlex . prepare) ss
  where
    showTTok (_,(TNum n))     =  show n
    showTTok (_,(TVar nm _))  =  nm
    showTTok (_,(TSym nm))    =  nm
    showTTok ttok             =  _redQ
\end{code}

\newpage 
\subsection{Lexer}
Now we define the lexer:
\begin{code}
tlex :: [NumberedLine] -> [Token]
tlex []                    = []
tlex ((lno,""):rest)       =  tlex rest
tlex ((lno,str@(c:cs)):rest)
  | isSpace c              =  tlex ((lno,cs):rest)
  | isDigit c              =  tlexNum lno rest [c] cs
  | c == '-'               =  tlexMinus lno rest cs
  | isAlpha c || c == '_'  =  tlexVar lno rest [c] cs
  | c == beforeChar        =  tlexBeforeId lno rest cs
  | c `elem` openings      =  (lno,TOpen [c])  : tlex ((lno,cs):rest)
  | c `elem` closings      =  (lno,TClose [c]) : tlex ((lno,cs):rest)
  | c `elem` separators    =  (lno,TSep [c])   : tlex ((lno,cs):rest)
  | otherwise              =  tlexSym lno rest [c] cs
\end{code}


Seen one or more digits, keep looking for more.
\begin{code}
tlexNum lno rest mun ""  = (lno,mkNum mun) : tlex rest
tlexNum lno rest mun str@(c:cs)
  | isDigit c  =  tlexNum lno rest (c:mun) cs
  | otherwise  =  (lno,mkNum mun) : tlex ((lno,str):rest)

mkNum mun = TNum $ read $ reverse mun
\end{code}

We have seen a minus sign. If followed immediately by a number
it is then merged with it to form a negative literal.
Otherwise it is treated as a (part of a) symbol.
\begin{code}
tlexMinus lno rest "" = [ (lno, mkSym "-") ]
tlexMinus lno rest str@(c:cs)
  | isDigit c  =  tlexNum lno rest [c,'-'] cs
  | otherwise  =  tlexSym lno rest [c,'-'] cs
\end{code}

A \texttt{afterChar} may end an identifier,
or indicate that we expect a During subscript,
provided none exists at the start.
Otherwise it is an error.
Also a subscript appearing when a \texttt{afterChar} is already present
is an error.


\begin{code}
-- seen '  expecting  v v$ 
tlexBeforeId lno rest "" 
  =  (lno,TErr "' found without variable part") : tlex rest
tlexBeforeId lno rest cs@(c:cs')
  | isAlpha c  =  tlexBeforeGVar lno rest [c] cs'
  | otherwise  =  (lno,TErr "' found without variable part") : tlex ((lno,cs):rest) 

--seen 'v   expecting 'v  'v$
tlexBeforeGVar lno rest di "" 
  =  (lno,TVar (reverse di) Before) : tlex rest
tlexBeforeGVar lno rest di cs@(c:cs')
  | isAlpha c  =  tlexBeforeGVar lno rest (c:di) cs'
  | c == '_'   =  tlexBeforeGVar lno rest (c:di) cs'
  | c == '$'   =  (lno,TLVar (reverse di) Before) : tlex ((lno,cs'):rest)
  | otherwise  =  (lno,TVar (reverse di) Before) : tlex ((lno,cs):rest)

-- tlexVar lno rest di cs   (di is non-empty)
--  seen  v  expecting  v  v'  v'm  v$ v$' v$'m
tlexVar lno rest di ""     =  (lno, mkDi di) : tlex rest -- std-var
tlexVar lno rest di cs@(c:cs') 
  | isAlphaNum c    =  tlexVar lno rest (c:di) cs'
  | c == '_'        =  tlexVar lno rest (c:di) cs'
  | c == afterChar  =  tlexLater lno rest (reverse di) TVar "" cs' -- v'
  | c == lstvChar   =  tlexLVar   lno rest (reverse di) cs' -- v$
  | otherwise = (lno,mkDi di) : tlex ((lno,cs):rest)

-- seen v$  expecting v$ v$' v$'m
tlexLVar lno rest var "" = (lno,TLVar var Static) : tlex rest
tlexLVar lno rest var cs@(c:cs')
  | c == afterChar  =  tlexLater lno rest var TLVar "" cs' -- v$'
  | otherwise       =  (lno,TLVar var Static) : tlex ((lno,cs):rest)

-- seen v' v$'   expecting  v' v'm v$' v$'m
tlexLater lno rest var tvar rud ""  -- v'   v$'
  =  (lno,tvar var $ mkLater rud) : tlex rest 
tlexLater lno rest var tvar rud cs@(c:cs')
  | isAlpha c  =  tlexLater lno rest var tvar (c:rud) cs' 
  | isDigit c  =  tlexLater lno rest var tvar (c:rud) cs'
  | otherwise  =  (lno,tvar var $ mkLater rud) : tlex ((lno,cs):rest)

mkLater rud = if null rud then After else During (reverse rud)
\end{code}


If none of the above apply, we gobble up a maximum-munch symbol:
\begin{code}
tlexSym lno rest mys ""  = (lno, mkMys mys) : tlex rest
tlexSym lno rest mys str@(c:cs)
  | issymbol c  =  tlexSym lno rest (c:mys) cs
  | otherwise  =  (lno,mkMys mys) : tlex ((lno,str):rest)
\end{code}

\section{Token Parsing Utilities}

When input ends unexpectedly:
\begin{code}
premAfter strs
  = fail ("premature file end after "++intercalate " " strs)
premDuring strs
  = fail ("premature file end during "++intercalate " " strs)
premImport what got lno 
  = fail ("premature end while loading "++what++" "++got++" at line "++show lno)
\end{code}

Called when a specific token is expected:
\begin{code}
expectToken :: MonadFail mf => String -> TokenType -> [Token] -> mf [Token]
expectToken msg tok [] = fail $ unlines'
  [ "premature end ("++msg++")"
  , "while expecting "++renderTokTyp tok ]
expectToken msg tok toks@((lno,tok'):rest)
  | tok == tok'  =  return rest
  | otherwise    =  fail $ unlines'
                      [ "expectToken("++msg++") error"
                      , "was expecting "++show tok++" at line "++show lno
                      , "but found "++show (take 5 toks)]
\end{code}

Called to parse something inside delimiters.
Called when the opening delimiter has been seen.
\begin{code}
delimitedParse :: MonadFail mf =>
  TokenType -> ([Token] -> mf (a, [Token])) -> [Token] -> mf (a, [Token])
delimitedParse close parser [] 
  = fail ("premature end while parsing before "++renderTokTyp close)
delimitedParse close parser tokens = do
  (thing,rest) <- parser tokens
  rest' <- expectToken "delimitedParse" close rest
  return (thing,rest')
\end{code}


\newpage
\section{Random test/prototype bits}

\begin{code}
showMacro :: String -> IO ()
showMacro macro
 = case findSym macro of
     Nothing -> putStrLn "<nothing found>"
     Just sym -> putStrLn ("found: "++sym)
\end{code}

\begin{code}
tread str 
  = case loadTerm str of
      Yes (term,tokens) 
        | null tokens -> putStrLn $ trTerm 0 term
        | otherwise   -> putStrLn ( "tokens leftover: " ++
                                     concat (map renderToken' tokens) )
      But msgs -> putStrLn $ unlines' msgs
\end{code}


\section{Useful Writers}

\begin{code}
genIndentedNameList  :: Int -> Int -> [String] -> String
genIndentedNameList ind width names
  = let widths = map length names
        actualwidth = width - ind
        partitions = sizepack actualwidth $ zip names widths
        indent = replicate ind ' '
    in unlines' $ map ((indent++) . intercalate " ") partitions

sizepack :: Int -> [(a,Int)] -> [[a]]
-- packed = sizepack w xws ==> max (map (sum . map snd) xws) <= w
sizepack wall [] = []
sizepack wall xws
  = let (xs,xws') = packfst wall 0 [] xws
    in xs : sizepack wall xws'

packfst :: Int -> Int -> [a] -> [(a,Int)] -> ([a],[(a,Int)])
packfst wall _ xs [] = (reverse xs,[])
packfst wall wsofar accum xws@((x,w):xws')
  |  wnext <= wall  =  packfst wall wnext (x:accum) xws' 
  |  otherwise      =  (reverse accum,xws)
  where
    wnext = wsofar + w
\end{code}