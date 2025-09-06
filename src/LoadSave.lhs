\chapter{Theory Load and Save}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2018-25

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module LoadSave (
  mkLawName
, term_syntax
, renderToken'
, loadTheory, saveTheory
, loadTerm
)

where

import Data.Maybe(fromJust)
-- import Data.Map as M (fromList,assocs)
import qualified Data.Set as S
import qualified Data.Map as M
import Data.List (nub, sort, (\\), intercalate, stripPrefix)
import Data.Char


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

\section{Load-Save Intro.}

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
and we will rely on dump and grab (export and import?) to handle them.
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
loadTheory text  =  importTheory nullTheory $ tlex $ prepare text


importTheory :: MonadFail mf  => Theory -> [Token] -> mf Theory
importTheory thry [] = fail "Empty theory file!"
importTheory thry ( (lno,TVar key Static)
                   :(_,TVar name Static):rest)
  | key == kTheory && validFileName name = do
        (thry',rest') <- importDependencies (thName_ name thry) rest 
        importDefinitions thry' rest'   
  | otherwise  =  fail $ unlines  [ "loadTheory headline parse error at line "
                                    ++ show lno 
                                  , "  expected: "++kTheory++" theoryname"
                                  , "  got: " ++ key ++ " " ++ name
                                  ]

importDependencies :: MonadFail mf 
                   => Theory -> [Token] 
                   -> mf (Theory,[Token])
importDependencies thry []  =  return (thry,[])
importDependencies thry nlines@((lno,TVar  needs Static):rest)
  | needs == kNeeds  =  importDeps thry [] rest
  | otherwise = return (thry,nlines) -- no dependencies is fine

importDeps thry sped []  =  premAfter [ kNeeds ]
importDeps thry sped ((lno,TClose close):rest) 
  | close == kEnd  
     =  return ((thDeps__ (++(reverse sped)) thry), rest)
importDeps thry sped ((lno,TVar i Static):rest) 
  | validFileName i = importDeps thry (i:sped) rest 
importDeps thry sped (tok@(lno,_):rest) 
  = fail $ unlines
      [ "invalid dependency at line "++show lno
      , "  saw "++renderToken tok ]

-- importDepLine thry sped rest lno [] = importDeps thry sped rest
-- importDepLine thry sped rest lno ((_,TVar  dep Static):deps)
--   | validFileName dep = importDepLine thry (dep:sped) rest lno deps
--   | otherwise = 


importDefinitions :: MonadFail mf => Theory -> [Token] -> mf Theory  
importDefinitions thry []  =  return thry
importDefinitions thry ((lno,TVar category Static)
                       :(_,TVar name Static):rest)
  | category == kConjecture = do
      (conj',rest') <- importConjecture name rest
      importDefinitions (conjs__ (++[conj']) thry) rest'
  | category == kLaw = do
      (law',rest') <- importLaw name rest
      importDefinitions (laws__ (++[law']) thry) rest'
importDefinitions thry ((lno,TVar category Static):rest)
  | category == kKnown = do
      (known',rest') <- importKnown (known thry) rest
      importDefinitions (known_ known' thry) rest'
importDefinitions thry (tok@(lno,_):_)
  = fail $ unlines [ "loadTheory expected known/law/conj at " 
                        ++ show lno
                   , "but got: "++renderToken tok
                   ] 
\end{code}


\subsection{Save Theory}

\begin{code}
saveTheory :: Theory -> String
saveTheory theory = unlines (
  (kTheory ++ " " ++ thName theory)
   : ( saveDeps (thDeps theory) ++
       ["",saveVarTable (known theory)] ++
       ["",saveLaws (laws theory)] ++
       [saveConjectures (conjs theory)] ) )

saveDeps [] = []
saveDeps deps = 
  [ kNeeds , saveIndentedNameList 2 80 deps , kEnd] 
\end{code}

\newpage
\section{VarTables}

\subsection{Load VarTable}

Seen \h{kKnown}:
\begin{code}
importKnown :: MonadFail mf => VarTable -> [Token] -> mf (VarTable,[Token])
importKnown vt [] = return (vt,[])
importKnown vt toks@((lno,TVar var vw):rest) = importKVar vt lno var vw rest
importKnown vt toks@((lno,TLVar var vw):rest) = importKLVar vt lno var vw rest
importKnown name (tok:rest) 
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
importKVar :: MonadFail mf 
           => VarTable -> Int -> String -> VarWhen -> [Token] 
           -> mf (VarTable,[Token])
importKVar vt _ var vw ((lno,TSym ":"):rest) 
                                  =  importKVarOfType vt lno var vw rest
importKVar vt _ var vw ((lno,TSym "="):rest)  
                                  =  importKVarIsConst vt lno var vw rest
importKVar vt _ var vw ((lno,TSym "::"):rest)  
                                  =  importKVarIsGeneric vt lno var vw rest
importKVar vt _ var vw ((lno,TVar iof _):rest)
  | iof == kInstanceOf  =  importKVarInstance vt lno var vw rest
importKVar vt _ var vw ((lno,ttyp):_)
  = fail ( "importKVar: unexpected token "
           ++show ttyp++" at line "++show lno )
importKVar vt lno var vw []  =  premImport "known var" var lno 
\end{code}

Seen \h{Known var :}, expect a type terminated by \h{.}
\begin{code}
importKVarOfType :: MonadFail mf 
                 => VarTable -> Int -> String -> VarWhen -> [Token] 
                 -> mf (VarTable,[Token])
importKVarOfType vt lno var vw []  =  premImport "type" var lno
importKVarOfType vt lno var vw rest = do
  (typ,rest') <- importType rest
  rest'' <- expectToken dotTok rest'
  vt' <- addKnownVar (Vbl (jId var) ObsV vw) typ vt
  return (vt',rest'')
\end{code}

Seen \h{Known var =}, expect a term wrapped with \h{BEGIN \dots END}
\begin{code}
importKVarIsConst :: MonadFail mf 
                  => VarTable -> Int -> String -> VarWhen -> [Token] 
                  -> mf (VarTable,[Token])
importKVarIsConst vt lno var vw tokens = do
  (block,beyond) <- getBlock beBlock tokens
  (term,rest) <- sTermRead block
  if null rest 
  then do
    vt' <- addKnownConst (Vbl (jId var) ExprV Static) term vt
    return (vt',beyond)
  else fail $ unlines'
        [ "importKVarIsConst("++var++")"
        , "after term: "++trTerm 0 term
        , "has junk "++renderTokTyp (snd (head rest))
        , "at line no "++show (fst (head rest)) ]
\end{code}

Seen \h{Known var ::}, expect keyword \h{generic}
\begin{code}
importKVarIsGeneric :: MonadFail mf 
                  => VarTable -> Int -> String -> VarWhen -> [Token] 
                  -> mf (VarTable,[Token])
importKVarIsGeneric vt lno var vw []  =  premImport "generic" var lno
importKVarIsGeneric vt lno var vw ((lno',TVar "generic" _):rest) = do
  vt' <- addGenericVar (Vbl (jId var) ExprV Static) vt
  return (vt',rest)
importKVarIsGeneric vt lno var vw ((lno',tok):rest)
  = fail ( "importKVarGeneric("++var++"): unexpected token "
           ++renderTokTyp tok++" at line "++show lno' )
\end{code}

Seen \h{Known var instanceof}, expect (generic) variable.
\begin{code}
importKVarInstance :: MonadFail mf 
                  => VarTable -> Int -> String -> VarWhen -> [Token] 
                  -> mf (VarTable,[Token])
importKVarInstance vt lno var vw []  =  premImport "instance" var lno
importKVarInstance vt lno var vw ((lno',TVar gvar _):rest) = do
  vt' <- addInstanceVar (Vbl (jId var) ExprV Static) 
           (Vbl (jId gvar) ExprV Static) vt
  return (vt',rest)
importKVarInstance vt lno var vw ((lno',tok):rest)
  = fail ( "importKVarInstance("++var++"): unexpected token "
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
importKLVar :: MonadFail mf 
           => VarTable -> Int -> String -> VarWhen -> [Token] 
           -> mf (VarTable,[Token])
importKLVar vt _ lvar vw ((lno,TSym "="):rest)  
                              =  importKLVarIsContainer vt lno lvar vw rest
importKLVar vt _ lvar vw ((lno,TSym "::"):rest)  
                          =  importKLVarIsAbsContainer vt lno lvar vw rest
importKLVar vt _ lvar vw ((lno,ttyp):_)
  = fail ( "importKLVar: unexpected token "
           ++show ttyp++" at line "++show lno )
importKLVar vt lno lvar vw []  =  premImport "known list-var" lvar lno 
\end{code}

Seen \h{Known var\$ =}, 
expect a list enumeration wrapped with \h{< \dots >},
or a set enumeration wrapped with \h{\{ \dots \}}
\begin{code}
listOpen = TSym "<"; listClose = TSym ">"; listBlock = (listOpen,listClose)
setOpen = TOpen "{"; setClose = TClose "}"; setBlock = (setOpen,setClose)

importKLVarIsContainer :: MonadFail mf 
                  => VarTable -> Int -> String -> VarWhen -> [Token] 
                  -> mf (VarTable,[Token])
importKLVarIsContainer vt lno lvar vw [] = premAfter ["Known",lvar,show lno]
importKLVarIsContainer vt _   lvar vw tokens@((lno,tok):_)
  | tok == listOpen  = do
      (block,beyond) <- getBlock listBlock tokens
      (list,rest) <- sepListParse (TSym ",") undefined block
      fail ("importKLVarIsContainer(list): NYfI "++show block++" @ "++show lno)
  | tok == setOpen  = do
      (block,beyond) <- getBlock setBlock tokens
      fail ("importKLVarIsContainer(set): NYfI "++show block++" @ "++show lno)
  | otherwise = fail $ unlines'
      [ "importKLVarIsContainer: expected '<' or '{'"
      , "but got "++renderTokTyp tok++" at line "++show lno ]
\end{code}


Seen \h{Known var\$ ::}, expect keyword \h{list} or \h{set}.
\begin{code}
importKLVarIsAbsContainer :: MonadFail mf 
                  => VarTable -> Int -> String -> VarWhen -> [Token] 
                  -> mf (VarTable,[Token])
importKLVarIsAbsContainer vt lno lvar vw []  =  premImport "list or set" lvar lno
importKLVarIsAbsContainer vt lno lvar vw ((lno',TVar abstract _):rest)
  | abstract == "list" = do
      vt' <- addAbstractVarList (Vbl (jId lvar) ExprV vw) vt
      return (vt',rest)
  | abstract == "set" = do
      vt' <- addAbstractVarSet (Vbl (jId lvar) ExprV vw) vt
      return (vt',rest)
importKLVarIsAbsContainer vt lno lvar vw ((lno',tok):rest)
  = fail ( "importKLVarIsAbsContainer("++lvar++"): unexpected token "
           ++renderTokTyp tok++" at line "++show lno' )
\end{code}


\subsection{Save VarTable}


We start every entry with the ``Known'' keyword:
\begin{code}
saveVarTable :: VarTable -> String
saveVarTable (VarData (vtname,vtable,stable,dtable))
  = '\n':showTable saveKnownVar (M.assocs vtable) ++
    '\n':showTable saveKnownLstVar (M.assocs stable) ++
    '\n':showTable saveKnownDynamic (M.assocs dtable)
  where showTable showMapping alist  
          =  unlines' $ map ( ((kKnown++" ")++) . showMapping ) alist 

saveKnownVar :: (Variable,VarMatchRole) -> String
saveKnownVar (v,KnownConst trm) = saveVariable v ++ " = " 
  ++ kBegin ++ " " ++ saveTerm trm ++ " " ++ kEnd
saveKnownVar (v,KnownVar typ) = saveVariable v ++ " : " ++ saveType typ ++ " ."
saveKnownVar (gv,GenericVar) = saveVariable gv ++ " :: generic"
saveKnownVar (iv,InstanceVar gv) 
  = saveVariable iv ++ " "++kInstanceOf++" " ++ saveVariable gv
saveKnownVar (v,vmr) = "" -- unknown variable

-- static list variables
saveKnownLstVar :: (Variable,LstVarMatchRole) -> String
saveKnownLstVar (lv,KnownVarList vl _ _) 
  = saveVariable lv ++ "$ = < " ++ intercalate "," (map trGVar vl) ++ " >"
saveKnownLstVar (lv,KnownVarSet vs _ _) 
  = saveVariable lv ++ "$ = {" 
    ++ intercalate "," (S.toList (S.map trGVar vs)) ++ "}"
saveKnownLstVar (lv,AbstractList) 
  = saveVariable lv ++ "$ :: list"
saveKnownLstVar (lv,AbstractSet) 
  = saveVariable lv ++ "$ :: set"
saveKnownLstVar (lv,lvmr) = ""


saveKnownDynamic :: (IdAndClass,DynamicLstVarRole) -> String
saveKnownDynamic ((id,vc),DynamicList vl lvl _ _) 
-- we can infer vc from the classes of vl and lvl 
-- which should also be known-var
  =  trId id ++ "$' = < "
    ++ intercalate "," (map idName vl)
    ++ (if length vl > 0 && length lvl > 0 then "," else "")
    ++ intercalate "," (map ((++"$") . idName) lvl)
    ++ " >"
saveKnownDynamic ((id,vc),DynamicSet vs lvs _ _) 
  =  trId id ++ "$' = {"
    ++ intercalate "," (S.toList (S.map idName vs))
    ++ (if S.size vs > 0 && S.size lvs > 0 then "," else "")
    ++ intercalate "," (S.toList (S.map ((++"$") . idName) lvs))
    ++ "}"
saveKnownDynamic ((id,vc),DynamicAbsList) =  trId id ++"$' :: list "
saveKnownDynamic ((id,vc),DynamicAbsSet) =  trId id ++"$' :: set "
saveKnownDynamic ((id,vc),dlvr) = ""
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
importLaw :: MonadFail mf 
          => String -> [Token] 
          -> mf (Law,[Token])
importLaw lawname []  =  premAfter [kLaw,lawname,kBegin]
importLaw lawname tokens = do
  (block,beyond) <- getBlock beBlock tokens
  (provenance,rest1) <- importProvenace block
  case rest1 of
    []  ->  premAfter [kLaw,show provenance ]
    ((_,TSep ","):rest2) -> do
      (term,rest3) <- sTermRead rest2
      case rest3 of
        [] -> return (((lawname,(mkAsn term scTrue)),provenance),beyond)
        ((_,TSep ","):rest4) -> do
          (sc,rest5) <- loadSideCond rest4
          return (((lawname,(mkAsn term sc)),provenance),beyond)
        (tok@(lno,_):_) -> fail $ unlines'
          [ "importLaw: unexpected token after provenance"
          , renderToken tok ++ " at line "++show lno ]
    (tok@(lno,_):_) -> fail $ unlines'
      [ "importLaw: unexpected token after provenance"
      , renderToken tok ++ " at line "++show lno ]

importProvenace :: MonadFail mf => [Token] -> mf (Provenance,[Token])
importProvenace []  =  premAfter [kBegin]
importProvenace ((_,TVar  "axiom" Static):rest) 
  = return (Axiom,rest)
importProvenace ((_,TVar  "assumed" Static):rest) 
  = return (Assumed,rest)
importProvenace ((_,TVar  "proven" Static)
                :(_,TVar i Static):rest) 
  = return (Proven i,rest)
importProvenace ((_,TVar  "suspect" Static)
                :(_,TVar i Static):rest) 
  = return ((Suspect i),rest)
importProvenace (tok@(lno,_):_)
  = fail $ unlines'
      [ "importProvenace: unexpected token after "++kBegin 
      , renderToken tok ++ "at line " ++ show lno ]
\end{code}

\subsection{Save Laws}


\begin{code}
saveLaws :: [Law] -> String
saveLaws laws  =  unlines' $ map saveLaw laws

saveLaw :: Law -> String
saveLaw ((name,Assertion tm sc),provenance)
  = unlines' ( [ "", kLaw ++ " " ++ name ++ " " ++ kBegin
               , " " ++ saveProv provenance
               , " ," , saveTerm tm ]
               ++ (if isTrivialSC sc then [] else [",",saveSideCond sc])
               ++ [ kEnd ] )

saveProv Axiom            =  "axiom"
saveProv (Proven proof)   =  "proven " ++ proof
saveProv (Suspect proof)  =  "suspect " ++ proof
saveProv Assumed          =  "assumed"
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
importConjecture :: MonadFail mf 
                 => String -> [Token] 
                 -> mf (NmdAssertion,[Token])
importConjecture conjname []  =  premAfter [kConjecture,conjname]
importConjecture conjname tokens = do
  (block,beyond) <- getBlock beBlock tokens
  (term,rest2) <- sTermRead block
  case rest2 of
    [] -> return ( ( conjname, mkAsn term scTrue ), beyond )
    ((_,TSep ","):rest3) -> do
      (sc,rest4) <- loadSideCond rest3
      return ( ( conjname, mkAsn term sc ), beyond )
    (tok@(lno,_):_) -> 
      fail $ unlines
        [ "importConjecture: unexpected token after term"
        , renderToken tok ++ " at line "++show lno ]
\end{code}

\subsection{Save Conjectures}

\begin{code}
saveConjectures :: [NmdAssertion] -> String
saveConjectures nmdassns  =  unlines' $ map saveConjecture nmdassns
\end{code}
\begin{code}

saveConjecture :: NmdAssertion -> String
saveConjecture (name,Assertion tm sc)
  = unlines'  ( [ "", kConjecture ++ " " ++ name ++ " " ++ kBegin 
                , " " ++ saveTerm tm ]
                ++ (if isTrivialSC sc then [] else [",",saveSideCond sc])
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
   ]
\end{code}
The tokens that can start a term are: \verb"true false n <v> i <q> (". 
\begin{code}
key_names 
 = [ "** Keywords:   true  false  QS  QL"
   , "** Keysymbols: ?  $  (  ,  )  @"
   ]
kTrue = "true"
kFalse = "false"
kSetBind = "QS"
kListBind = "QL"
kLstVar = '$'
kSep = ','
kQBody = "@"
term_syntax = syntax_bits ++ term_definition ++ key_names
\end{code}


\subsection{Save Term}

\begin{code}
saveSBBL s = if s then "CS" else "NS"

saveTerm :: Term -> String
saveTerm (Val typ (Boolean b)) = if b then kTrue else kFalse
saveTerm (Val typ (Integer i)) = show i
saveTerm (Var typ var) = saveVariable var
saveTerm (Cons typ subable (Identifier i _) terms) 
  = i ++ " " ++ (saveSBBL subable) ++ " "
      ++ "("
      ++ (intercalate [kSep] $ map saveTerm terms)
      ++ ")"
saveTerm (Bnd typ n vs term) = "B-stuff?"
saveTerm (Lam typ n vl term) = "L-stuff?"
saveTerm (Cls typ term) = "X-stuff?"
saveTerm (Sub typ term sub) = "S-stuff?"
saveTerm (Iter typ sa na si ni lvs) = "I-stuff?"
saveTerm (VTyp typ var) = "VT-stuff?"
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


\newpage

\subsection{Term Reader}

\begin{code}
sTermRead :: MonadFail m => [Token] -> m (Term, [Token])
sTermRead [] =  fail "sTermRead: nothing to parse"
\end{code}

\paragraph{Numbers}

\begin{code}
sTermRead ((_,TNum n):tts) = return ( Val int $ Integer n, tts)
\end{code}

\paragraph{Symbols}

Symbols are valid identifiers

\begin{code}
sTermRead ((_,TSym consName):(_,TVar subable Static ):(_,TOpen "("):tts)
  | subable == "N" = sAppParse cons False [] tts
  | subable == "S" = sAppParse cons True  [] tts
  where cons = jId consName
sTermRead ((_,TSym sym):tts) = return (mkVarTerm (jId sym) Static, tts)
\end{code}

\paragraph{Constructions}

Important: we must check for constructions before we
check for lone identifiers.

\paragraph{Identifiers}

We check for constructions first \dots

\begin{code}
sTermRead ((_,TVar consName vw):(_,TVar subable Static ):(_,TOpen "("):tts)
  | subable == "NS" = sAppParse cons False [] tts
  | subable == "CS" = sAppParse cons True  [] tts
  where 
    cons = jId consName
sTermRead ((_,TVar nm vw):tts)
  | nm == kTrue      =  return ( mkTrue nm,  tts)
  | nm == kFalse     =  return ( mkFalse nm, tts)
  | nm == kSetBind   =  setQParse tts
  | nm == kListBind  =  listQParse tts
  | otherwise       =  return (mkVarTerm (jId nm) vw, tts)
\end{code}

\paragraph{Bad Start}


\begin{code}
sTermRead (tt:tts)  = fail ("sTermRead: unexpected token: "++renderToken tt)
\end{code}

\subsection{Term Helpers}

Seen identifier and opening parenthesis.
$$ i(~~~t_1,\dots,t_n) $$
Look for sub-term, or closing parenthesis.
\begin{code}
sAppParse :: MonadFail mf 
          => Identifier -> Bool -> [Term] -> [Token]-> mf (Term,[Token])
sAppParse id1 subable smretbus ((_,TClose ")") : tts)
  = return ( Cons arbpred subable id1 $ reverse smretbus, tts)
sAppParse id1 subable smretbus tts
  = do (tsub',tts') <- sTermRead tts
       sAppParse' id1 subable (tsub':smretbus) tts'
\end{code}

\newpage
Seen (sub-) term.
Looking for comma or closing parenthesis
\begin{code}
sAppParse' :: MonadFail mf 
           => Identifier -> Bool -> [Term] -> [Token]-> mf (Term,[Token])
sAppParse' id1 subable smretbus ((_,TSep ",") : tts)
  =  sAppParse id1 subable smretbus tts
sAppParse' id1 subable smretbus ((_,TClose ")") : tts)
  =  return ( Cons arbpred subable id1 $ reverse smretbus, tts)
sAppParse' id1 subable smretbus tts
  =  fail $ unlines'
       [ "sAppParse': expected ',' or ')'"
       , "got "++show (take 3 tts)++" ..." ]
\end{code}


\paragraph{Quantifiers}~

Seen \texttt{QS}, 
$$ QS~~~i~g_1 \dots g_n \bullet t $$
parse the quantifier:
\begin{code}
setQParse :: MonadFail mf => [Token] -> mf (Term,[Token])
setQParse []  =  premDuring ["setQParse"]
setQParse ((_,TVar nm Static) : tts) = do
  let i = jId nm
  (i,sg,term,tts') <- quantread i [] tts
  qsterm <- pBnd i (S.fromList $ map tok2GVar sg) term
  return (qsterm,tts')
setQParse (tok:_) = fail ("setQParse: exp. ident, found: "++renderToken tok)
\end{code}

Seen \texttt{QL}, 
$$ QL~~~i~g_1 \dots g_n \bullet t $$
parse the quantifier:
\begin{code}
listQParse :: MonadFail mf => [Token] -> mf (Term,[Token])
listQParse []  = premDuring ["listQParse"]
listQParse ((_,TVar nm Static) : tts) = do
  let i = jId nm
  (i,sg,term,tts') <- quantread i [] tts
  lsterm <- pLam i (reverse $ map tok2GVar sg) term
  return (lsterm,tts')
listQParse (tok:_) = fail ("listQParse: exp. ident, found: "++renderToken tok)
\end{code}

Seen \texttt{Qx i}, and zero or more \texttt{g\_i}:
$$ Qx~i~g_1 \dots g_i ~~~~~ g_{i+1} \dots g_n \bullet t $$
parse the quantifier:
\begin{code}
quantread i _ []  =  premDuring ["quantread:",trId i]
quantread i sg ((_,TSym sym) : tts)
  | sym == kQBody  =  quantreadBody i sg tts
quantread i sg (v@(_,TVar _ _)    : tts)   =  quantread i (v:sg) tts
quantread i sg (lv@(_,TLVar _ _) : tts)   =  quantread i (lv:sg) tts
quantread i sg (tok : _)  = fail ("quantread: unexpected token "++renderToken tok)
\end{code}

Seen \texttt{Qx i g\_1 .. g\_n @}, 
$$ Qx~i~g_1 \dots g_n \bullet ~~~ t $$
parse the body term
\begin{code}
quantreadBody i _ [] = fail ("quantread: "++trId i++" (missing body)")
quantreadBody i sg tts = do
  (term,toks) <- sTermRead tts
  return (i,sg,term,toks)
\end{code}

\subsubsection{Top-Level Term Reader}

\begin{code}
loadTerm :: MonadFail mf => String -> mf (Term, [Token])
loadTerm = sTermRead . tlex . prepare
\end{code}


\section{Side-Conditions}

\subsection{Save Side-Condition}

\begin{code}
saveSideCond :: SideCond -> String
saveSideCond sc = "saveSideCond NYI"
\end{code}

\subsection{Load Side-Condition}

\begin{code}
loadSideCond :: MonadFail mf => [Token] -> mf (SideCond, [Token])
loadSideCond sc = fail "loadSideCond NYI"
\end{code}


\section{Variables}


\subsection{Save Variable}

\begin{code}
saveVariable :: Variable -> String
saveVariable (Vbl i vc Before)      = '\'' : idName i
saveVariable (Vbl i vc (During d))  =  idName i ++ '\'' : d
saveVariable (Vbl i vc After)       = idName i ++ "\'"
saveVariable (Vbl i vc _)           = idName i 
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
loadVariable :: MonadFail mf => String -> mf Variable
loadVariable ('\'' : string)
    | validVarRoot string  =  return $ Vbl (jId string) ObsV Before
loadVariable string
  | validVarRoot name
    = case post of
       ("\'")    ->  return $ Vbl ident ObsV After
       ('\'':d)  ->  return $ Vbl ident ObsV $ During d
       _         ->  return $ Vbl ident ObsV Static
  where 
    (name,post) = break (=='\'') string
    ident = jId name
loadVariable string = fail ("loadVariable: invalid variable - "++string)
\end{code}

\section{Types}

\subsection{Type Grammar}

Alternate grammar?
\def\typegrammar{
\begin{eqnarray*}
\lefteqn{t \in Type}
\\ &::=&  name
\\ &\mid& \mathbf{fun} ~t~ \mathbf{to} ~t~\mathbf{endf}
\\ &\mid& \mathbf{prod}~name~t~\dots~t~\mathbf{endp}
\\ &\mid& \mathbf{sum}~name~v^*~\mathbf{ends}
\\\lefteqn{v \in Variant}
\\ &::=& \mathbf{variant}~name~~t~\dots~t~\mathbf{endv}
\end{eqnarray*}
}
\def\typestart{Tokens that can start a type:  $id~fun~prod~sum$}
\def\typefollow{Tokens that can follow and continue a type: $\fun~id~($}
\def\typeover{Tokens that can \emph{end} a type: $endf~endp~ends$}


% \def\typegrammar{
% \begin{eqnarray*}
%    Tokens: && id~\fun~|~(~)~.
% \\ t \in Type 
%    &::=& 
%    id \mid \tau_1 \fun t_2
%    \mid id~\tau_1~\tau_2~\dots~\tau_n \mid ~
% \\ && id_0~ `|`~id_1~\tau_{11} \dots \tau_{1k_1} 
%             `|` \dots `|`
%             id_n~\tau_{n1} \dots \tau_{nk_n} 
% \\ \tau \in WrapType
%    &&  id \text{ are rendered as-is}
% \\ &&  \text{non-atomic are enclosed in parentheses}
% \end{eqnarray*}
% }

\typegrammar

\typestart

\typeover

\subsection{Save Type}



\begin{code}
arbTypeString = "T"
bottomTypeString = "_"

startFun = "FUN" ; funArrow = "TO" ; endFun = "ENDF"
startProd = "PROD" ; endProd = "ENDP"
startSum = "SUM" ; endSum = "ENDS"
startVariant = "VARIANT" ; endVariant = "ENDV"

typeKeys = [ arbTypeString, bottomTypeString
           , startFun, funArrow, endFun
           , startProd, endProd
           , startSum, endSum, startVariant, endVariant ]

saveType :: Type -> String
saveType ArbType          = arbTypeString
saveType BottomType       = bottomTypeString
saveType (TypeVar i)      = idName i
saveType (GivenType i)    = idName i
saveType (FunType td tr)  
  = startFun++" "++saveType td++" "++funArrow++" "++saveType tr++" "++endFun
saveType (TypeCons i [])  = idName i  -- degenerate, GivenType?
saveType (TypeCons i ts)  = startProd ++" "++saveCons (i,ts)++" "++endProd
saveType (AlgType i fs)   = startSum ++" "++idName i 
                            ++ '\n' : unlines' (map saveVariant fs)
                            ++ '\n' : endSum

type Variant = (Identifier,[Type])

saveCons :: Variant -> String
saveCons (i,ts) = idName i ++ " " ++ intercalate " " (map saveType ts)

saveVariant :: Variant -> String
saveVariant its
  = "  "++startVariant++" "++saveCons its++" "++endVariant

--saveType (FunType td tr)  = wrapNonAtomic td++funTypeString++saveType tr
-- saveType (TypeCons i ts)  = saveCons (i,ts)
-- saveType (AlgType i fs) 
--  = idName i  ++ "    \n  "++altTypeString++" "++
--     intercalate ("   \n  "++altTypeString++" ") (map saveCons fs)


--saveCons (i,ts) = idName i ++ " " ++ intercalate " " (map wrapNonAtomic ts)

--openParString = "(" ; closeParString = ")"
-- wrapNonAtomic t
--   | isAtmType t = saveType t
--  | otherwise  = openParString++saveType t++closeParString
\end{code}

\newpage
\subsection{Load Type}

\typegrammar

Once parsing is complete we post-process 
names to pull out $\top$ and $\bot$ types.

\begin{code}
importType :: MonadFail mf => [Token] -> mf (Type,[Token])
importType [] = premDuring ["importType"]
importType ((lno,TVar nm _):rest)
  | nm == startFun   =  importFunType rest
  | nm == startProd  =  importProdType rest
  | nm == startSum   =  importSumType rest
  | otherwise  = return (TypeVar (jId nm),rest)
importType (tok:_)
  = fail ("importType: invalid start "++show tok)
\end{code}

Seen: \textbf{fun}.
\begin{code}
importFunType [] = premDuring ["importFunType"]
importFunType toks = do
  (dtype,rest1) <- importType toks
  rest2 <- expectToken (TVar funArrow Static) rest1
  (rtype,rest3) <- importType rest2
  rest4 <- expectToken (TVar endFun Static) rest3
  return (FunType dtype rtype,rest4)
\end{code}

Seen: \textbf{prod}.
\begin{code}
importProdType [] = premDuring ["importProdType"]
importProdType ((lno,TVar nm _):rest1)
  | not( nm `elem` typeKeys) = do
      (types,rest2) <- importTypes [] rest1
      rest3 <- expectToken (TVar endProd Static) rest2
      return (TypeCons (jId nm) types,rest3)
importProdType (tok:_) 
  = fail ("importProdType: invalid name "++show tok)
\end{code}

Seen: \textbf{sum}.
\begin{code}
importSumType [] = premDuring ["importSumType"]
importSumType ((lno,TVar nm _):rest1)
  | not( nm `elem` typeKeys) = do 
      (variants,rest2) <- importVariants (jId nm) [] rest1
      rest3 <- expectToken (TVar endSum Static) rest2
      return (AlgType (jId nm) variants,rest3)
importSumType (tok:_) 
  = fail ("importSumType: invalid name "++show tok)
\end{code}

Seen: \textbf{variant}.
\begin{code}
importVariant [] = premDuring ["importVariant"]
importVariant ((lno,TVar nm _):rest1)
  | not( nm `elem` typeKeys) = do
      (types,rest2) <- importTypes [] rest1
      rest3 <- expectToken (TVar endVariant Static) rest2
      return ((jId nm,types),rest3)
importVariant (tok:_) 
  = fail ("importVariant: invalid name "++show tok)
\end{code}

Seen \textbf{sum} sumname.
Expecting a list of zero or more types, ended by \textbf{endp} or \textbf{endv}.
\begin{code}
importVariants :: MonadFail mf 
               => Identifier -> [Variant] -> [Token] 
               -> mf ([Variant],[Token])
importVariants vid stnairav toks@[] = return (reverse stnairav,toks)
importVariants vid stnairav toks@(tok@(lno,TVar str _):rest1)
  | str == endSum  =  return (reverse stnairav,toks)
  | str /= startVariant  = fail ("importVariants: invalid key "++show tok)
  | otherwise = do
      (variant,rest2) <- importVariant rest1
      case rest2 of 
        [] -> premDuring ["importVariants",endVariant]
        _ -> importVariants vid (variant:stnairav) rest2
\end{code}

Expecting a list of zero or more types, ended by \textbf{endp} or \textbf{endv}.
\begin{code}
importTypes :: MonadFail mf => [Type] -> [Token] -> mf ([Type],[Token])
importTypes sepyt toks@[]            = return (reverse sepyt,toks)
importTypes sepyt toks@((lno,TVar end _):rest)
  | end `elem` [endProd,endVariant]  =  return (reverse sepyt,toks)
importTypes sepyt toks = do
  (typ',rest1) <- importType toks
  importTypes (typ':sepyt) rest1
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



% Tokens that can occur after $id$ are: $.~\fun~|~)~id~($
% If we encounter $.$ or $)$ we leave it in place.
% \begin{code}
% gotTypeFirstName :: MonadFail mf => String -> [Token] -> mf (Type,[Token])
% gotTypeFirstName nm [] = premDuring ["gotTypeFirstName", "'"++nm++"'"]
% gotTypeFirstName nm toks@((lno,TSym sym):rest)
%   | sym == dot                            =  return (vartype,toks)
%   | sym == funTypeString                  =  gotFunArrow vartype rest
%   | sym == altTypeString                  =  gotAltBar nm [] rest
%   where vartype = TypeVar $ jId nm
% gotTypeFirstName nm ((lno,TVar var _):rest) 
%                               =  getProduct (jId nm) [TypeVar (jId var)] rest
% gotTypeFirstName nm toks@((lno,TOpen open):rest)
%   | open == openParString =  do
%      (typ,rest) <- getProduct (jId nm) [] toks
%      rest' <- expectToken (TClose closeParString) rest
%      return (typ,rest')
% gotTypeFirstName nm toks@((lno,TClose close):rest)
%   | close == closeParString               =  return ((TypeVar $ jId nm),toks)
% gotTypeFirstName nm ((lno,tok):rest) = fail $ unlines'
%   [ "gotTypeFirstName \""++nm++"\" NYfI"
%   , "Seeing "++renderTokTyp tok++" at line "++show lno ]
% \end{code}

% Tokens that can occur after $($ are: $id~(~)$
% \begin{code}
% rightParTok = TClose closeParString
% gotTypeLeftPar :: MonadFail mf => [Token] -> mf (Type,[Token])
% gotTypeLeftPar rest = do
%   (typ,rest') <- importType rest
%   rest'' <- expectToken rightParTok rest'
%   -- !!!! now we need to look for -> !!!!
%   return (typ,rest'')
% \end{code}

% Tokens that can occur after $\fun$ are: $id~($
% \begin{code}
% gotFunArrow  :: MonadFail mf => Type -> [Token] -> mf (Type,[Token])
% gotFunArrow dtype rest = do
%   (rtype,rest') <- importType rest
%   -- we should look for more arrows !!!!!
%   return (FunType dtype rtype,rest')
% \end{code}

% Tokens that can occur after $|$ are: $id~$
% \begin{code}
% gotAltBar :: MonadFail mf 
%           => String -> [Variant] -> [Token] 
%           -> mf (Type,[Token])
% gotAltBar sumNm variants []  =  premDuring ["gotAltBar"]
% gotAltBar sumNm variants ((lno,TVar nm _):rest) 
%   = getAltProduct sumNm nm variants [] rest
% gotAltBar sumNm variants ((lno,tok):rest) 
%  = fail $ unlines'
%     [ "importType (sum-of-products) syntax error"
%     , "expected product constructor name"
%     , "but got "++renderTokTyp tok++" at line "++show lno
%     ]
% \end{code}

% When we see $id_0~id_1$ or $id_0~($
% we expect a sequence of types, whose first token is $id_1$ or $($.
% This sequence should end with either $.$ or $|$,
% which we leave in place.
% \begin{code}
% getProduct :: MonadFail mf 
%            => Identifier -> [Type] -> [Token] -> mf (Type,[Token])
% getProduct conid types [] = premDuring ("product":trId conid:map trType types)
% getProduct conid types rest = do
%   (types',rest') <- importTypes types rest
%   return (TypeCons conid (reverse types'),rest')
% \end{code}



% Tokens that can occur after $|~id$ are $id~(~|$
% \begin{code}
% getAltProduct :: MonadFail mf 
%                => String -> String -> [Variant] -> [Type] 
%                -> [Token] -> mf (Type,[Token])
% getAltProduct sumNm prodNm variants [] rest
%   = fail "getAltProduct NYI"
% \end{code}

% Tokens that can occur after $.$ are returned with parsed item.



\newpage
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
  = fail ("premature end while importing "++what++" "++got++" at line "++show lno)
\end{code}

Called when a specific token is expected:
\begin{code}
expectToken :: MonadFail mf => TokenType -> [Token] -> mf [Token]
expectToken tok [] = fail ("premature end while expecting "++renderTokTyp tok)
expectToken tok ((lno,tok'):rest)
  | tok == tok'  =  return rest
  | otherwise    =  fail $ unlines'
                      [ "was expecting "++show tok++" at line "++show lno
                      , "but found "++show tok' ]
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
  rest' <- expectToken close rest
  return (thing,rest')
\end{code}

Called to parse a list of items with a separator symbol,
and consumes entire input.
\begin{code}
sepListParse sep objparser tokens = fail "sepListParser NYI"
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
saveIndentedNameList  :: Int -> Int -> [String] -> String
saveIndentedNameList ind width names
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