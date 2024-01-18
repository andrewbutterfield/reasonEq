\section{Verification Condition Generation}

Given a program and a postcondition, in the presence of a suitable
predicate transformer semantics, we can obtain a total precondition
for the program, along with multiple intermediate verification
conditions.

We will need to repeatedly perform matching of program statement -
postcondition pairs against laws of the transformer semantics. We
need a match context containing \textit{just} the transformer 
semantics to do this, since if we are to avoid having to seek user
input, there must be a single unique match for each statement in
the program theory (otherwise we need to let them choose between
multiple valid preconditions).

\begin{code}
module Verification where
import SaoithinProof

data VCGState = VCGState { progThry :: Theory
                         , transThryName :: String
                         , transMctxt :: MatchContext
                         , pcondition :: Pred
                         }

buildVCG thname pred progthry work
 = do tstack <- extractProofStack thname work
      let matchCtxt = mkMatchContext tstack
      return $ VCGState progthry thname matchCtxt pred

\end{code}
We need to generate the predicate (progP wp pcondP).

For now, in the interests of getting something working,
we can rely on the presence of the theories "X-Thesis"
and "WP-Thesis", but we shouldn't in general.

Can we do this without a DSL? Going through the parser,
we can accomplish it like so:

\begin{code}

mkWp :: Var SaoithinState -> Pred -> Pred -> Either Pred String
mkWp work predA predB
 = do mstk <- getMstk work
      let txtA = show predA
      let txtB = show predB
      let txtwp = txtA ++ " wp " ++ txtB
      return $ parser mstk "auto-wp" txtwp

\end{code}

We need to generate at each step the precondition for
the next, and the postcondition is expanding each time.

Each of these preconditions we insert into the program
theory as a verification condition for the program.
TODO: Investigate how we can manipulate these preconditions.
for example, use law matching to simplify them.

\begin{code}

genVC thryname work pred predname postcond
 = do let precond = mkWp work pred postcond
      case precond of
        Left msg      -> return $ Nothing
        Right (vc,sc) ->
          do let wpredname = "w"++predname
             insertPredicate thryname wpredname vc work
             return $ Just vc

genVCS tname work pcondP [] = do return $ pcondP
genVCS tname work pcondP ((pred,predname):rest)
 = do let vc = genVC tname work pred predname pcondP
      case vc of
        Nothing      -> scream work $ "genVCS parse error - failed to construct wp predicate: "++msg
        Just aPred   -> return $ genVCS tname work aPred rest

{-
runVCG tname work preds
 = do 
 TODO: lookup the postcondition given its name and a theory, call genVCS
-}

\end{code}
