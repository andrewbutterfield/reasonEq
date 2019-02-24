\section{Control}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2019

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Control where

import Data.Map(Map)
import qualified Data.Map as M
import Control.Monad
\end{code}

We provide general flow-of-control constructs here,
often of a monadic flavour.

\subsection{Matching Controls}

Matching many patterns against many candidates
\begin{code}
type BasicM mp b c p = c -> p -> b -> mp b

type Combine c b b' = [c] -> [c] -> b -> b'

manyToOne :: MonadPlus mp
           => BasicM mp b c p
           -> Combine c b b'
           -> [c] -> p -> b
           -> mp b'
manyToOne bf cf cs p b = manyToOne' bf cf [] p b cs

manyToOne' bf cf sc p b0 []      =  fail "no candidates"
manyToOne' bf cf sc p b0 (c:cs)  =  (do b <- bf c p b0 ; return $ cf sc cs b)
                                    `mplus`
                                    manyToOne' bf cf (c:sc) p b0 cs

manyToMany :: MonadPlus mp
           => BasicM mp b c p
           -> Combine c b b'
           -> [c] -> [p] -> b
           -> mp b'
manyToMany bf cf cs ps b
 = foldr mplus (fail ".") $ map f ps
 where
   f p = manyToOne bf cf cs p b

defCombine :: Combine c b (b,[c])
defCombine sc cs b  = (b, reverse sc ++ cs)
\end{code}
