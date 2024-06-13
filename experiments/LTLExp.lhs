\section{LTL Experiment}

\begin{code}
module LTLExp where
type Event = Char
type Trace = [Event]
data LTL
  =  Atm Event
  |  Not LTL
  |  And LTL LTL
  |  Or LTL LTL
  |  Until LTL LTL
  |  Eventually LTL
  |  Always LTL
  deriving (Eq,Ord,Show,Read)
ltlSat :: LTL -> Trace -> Bool
ltlSat alw@(Always ltl) []  =  True
ltlSat _ [] =  False -- not sure about this
ltlSat (Atm a) (e:_)         =  a == e
ltlSat (Not ltl) trace        =  not $ ltlSat ltl trace
ltlSat (And ltl1 ltl2) trace  =  (ltlSat ltl1 trace) && (ltlSat ltl2 trace)
ltlSat (Or ltl1 ltl2) trace   =  (ltlSat ltl1 trace) || (ltlSat ltl2 trace)
ltlSat u@(ltl1 `Until` ltl2) es@(e:es')
  | ltlSat ltl2 es = True
  | otherwise  =  ltlSat ltl1 es && ltlSat u es'
ltlSat alw@(Eventually ltl) es@(_:es')
  | ltlSat ltl es = True
  | otherwise  =  ltlSat alw es'
ltlSat alw@(Always ltl) es@(_:es')  =  ltlSat ltl es && ltlSat alw es'
\end{code}