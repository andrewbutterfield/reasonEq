\chapter{Hidden Types}

Copyright  Andrew Buttefield \copyright\ 2024

LICENSE: BSD3, see file LICENSE at reasonEq root


Here we keep copies of internal DS definitions
for easy reference when looking at \h{Show} output

\section{Variables}

\begin{code}
data VarClass = VO | VE | VP 
\end{code}

\begin{code}
data VarWhen  = WS | WB | WD Subscript | WA | WT            --  Textual
\end{code}

\begin{code}
data GenVar = GV Variable | GL ListVar  
\end{code}

\section{Abstract Syntax Tree}

\begin{code}
data Type  
 = T | TV Identifier | TC Identifier [Type]
 | TA Identifier [(Identifier,[Type])] | TF Type Type | TG Identifier | TB 
\end{code}

\begin{code}
data Substn = SN TermSubs LVarSubs
\end{code}

\begin{code}
data Value = VB Bool | VI Integer
\end{code}

\begin{code}
data Term
 = K Type Value | V Type Variable | C Type Subable Identifier [Term]
 | B Type Identifier VarSet Term | L Type Identifier VarList Term
 | X Identifier Term | S Type Term Substn     
 | I Type Subable Identifier Subable Identifier [ListVar]  
 | ET Type                               -- Embedded TypeVar
\end{code}

\section{Variable Data}

\begin{code}
data VarMatchRole = KC Term | KV Type | KG | KI Variable | UV    
\end{code}

\begin{code}
data LstVarMatchRole -- ListVar Matching Roles
 = KL VarList        -- Known Variable-List (all known?)
      [Variable]     -- full expansion
      Int            -- length of full expansion
 | KS VarSet         -- Known Variable-Set (all known?)
      (Set Variable) -- full expansion
      Int            -- size of full expansion
 | AL                -- Abstract Known Variable-List
 | AS                -- Abstract Known Variable-Set
 | UL                -- Unknown List-Variable
\end{code}

\begin{code}
data DynamicLstVarRole -- Dynamic ListVar Matching Roles
 = DL [Identifier]      -- Known-list, Variable identifiers
      [Identifier]      -- Known-list, List-Variable identifiers
      [Identifier]      -- full expansion
      Int               -- length of full expansion
 | DS (Set Identifier)  -- Known-set, Variable identifiers
      (Set Identifier)  -- Known-set, List-Variable identifiers
      (Set Identifier)  -- full expnasion
      Int               -- size of full expansion
 | DAL                  -- Abstract Known List
 | DAS                  -- Abstract Known Set
 | UD         -- Unknown Dynamic List-Variable
 deriving (Eq, Ord, Show, Read)
\end{code}

\section{Bindings}

\begin{code}
data VarBind 
  = BI Identifier | BV Variable | BT Term | BLV ListVar
type VarBinding = M.Map (Identifier,VarClass) VarBind
\end{code}

\begin{code}
data LstVarBind
 = BL  VarList
 | BS  VarSet
 | BX  [LVarOrTerm]
 deriving (Eq, Ord, Show, Read)
\end{code}
