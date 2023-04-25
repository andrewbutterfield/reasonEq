\section{Control}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2019

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Control  ( mapfst, mapsnd, mappair, mapboth
                , mapaccum
                , BasicM
                , matchPair
                , Combine, defCombine
                , manyToOne
                , manyToMany
                , Extract, defExtract
                , manyToMultiple
)
where

import Data.Map(Map)
import qualified Data.Map as M
import Control.Monad
\end{code}

We provide general flow-of-control constructs here,
often of a monadic flavour.

\subsection{List Controls}

\subsubsection{Mapping Pairs}

\begin{code}
mapfst :: (a -> c) -> [(a,b)] -> [(c,b)]
mapfst f1 [] = []
mapfst f1 ((x,y):xys) = (f1 x,y) : mapfst f1 xys

mapsnd :: (b -> c) -> [(a,b)] -> [(a,c)]
mapsnd f2 [] = []
mapsnd f2 ((x,y):xys) = (x,f2 y) : mapsnd f2 xys

mappair :: (a->c) -> (b->d) -> [(a,b)] -> [(c,d)]
mappair _ _ [] = []
mappair f1 f2 ((x,y):xys) = (f1 x,f2 y) : mappair f1 f2 xys

mapboth :: (a->b) -> [(a,a)] -> [(b,b)]
mapboth _ [] = []
mapboth f ((x,y):xys) = (f x, f y) : mapboth f xys
\end{code}

\subsubsection{Mapping an Accumulator}

\begin{code}
mapaccum :: (a -> t -> (t,a)) -> a -> [t] -> ([t],a)
mapaccum f acc [] = ([],acc)
mapaccum f acc (x:xs)
  = let
      (x',acc') = f acc x
      (xs',acc'') = mapaccum f acc' xs
    in (x':xs',acc'')
\end{code}

\subsection{Matching Controls}

\subsubsection{Matching types}
\begin{description}
  \item [\texttt{mp} :] instance of MonadPlus and MonadFail
  \item [\texttt{b} :]  binding type
  \item [\texttt{c} :] candidate type
  \item [\texttt{p} :] pattern type
\end{description}
We can then describe a standard (basic) match as:
\begin{code}
type BasicM mp b c p = c -> p -> b -> mp b
\end{code}

\subsubsection{Matching pairs}

\begin{code}
matchPair :: (MonadFail mp, MonadPlus mp)
          => BasicM mp b c1 p1 -> BasicM mp b c2 p2
          -> BasicM mp b (c1,c2) (p1,p2)

matchPair m1 m2 (c1,c2) (p1,p2) b  =   m1 c1 p1 b >>= m2 c2 p2
\end{code}

\subsubsection{Matching lists}

When we match lists sometimes we need to return
not just bindings,
but also something built from leftover list fragments
(usually before/after).
\begin{description}
  \item [\texttt{b'} :] binding plus extra stuff
\end{description}
\begin{code}
type Combine c b b' = [c] -> [c] -> b -> b'
\end{code}
In most cases we have the first list being those candidates before the match
(in reverse order, due to tail-recursion),
while the second is those after that match.
We typically want the binding with a single (ordered) list of the leftovers.
\begin{code}
defCombine :: Combine c b (b,[c])
defCombine sc cs b  = (b, reverse sc ++ cs)
\end{code}

\newpage
Matching many candidates against one pattern.
\begin{code}
manyToOne :: (MonadFail mp, MonadPlus mp)
          => BasicM mp b c p
          -> Combine c b b'
          -> [c] -> p -> b
          -> mp b'
manyToOne bf cf [] p b = fail "manyToOne: no candidates"
manyToOne bf cf cs p b = manyToOne' bf cf [] p b cs

manyToOne' bf cf sc p b0 []      =  return $ cf sc [] b0
manyToOne' bf cf sc p b0 [c]     =  (do b <- bf c p b0 ; return $ cf sc [] b)
manyToOne' bf cf sc p b0 (c:cs)  =  (do b <- bf c p b0 ; return $ cf sc cs b)
                                    `mplus`
                                    manyToOne' bf cf (c:sc) p b0 cs
\end{code}

Matching many candidates against many patterns,
looking for one-to-one matches.
\begin{code}
manyToMany :: (MonadFail mp, MonadPlus mp)
           => BasicM mp b c p
           -> Combine c b b'
           -> [c] -> [p] -> b
           -> mp b'
manyToMany bf cf cs [] b  =  return $ cf [] cs b
manyToMany bf cf cs ps b
 = foldr mplus (fail "manyToMany:end-of-list") $ map f ps
 where
   f p = manyToOne bf cf cs p b
\end{code}


Sometimes we need to extract what has been combined:
\begin{code}
type Extract c b b' = b' -> (b,[c])
\end{code}
The counterpart to \texttt{defCombine} is in fact the identity function
\begin{code}
defExtract :: Extract c b (b,[c])
defExtract = id
\end{code}

Matching candidates against many patterns,
looking for many-to-many matches from every pattern to a candidate.
\begin{code}
manyToMultiple :: (MonadFail mp, MonadPlus mp)
               => BasicM mp b c p
               -> Combine c b b'
               -> Extract c b b'
               -> [c] -> [p] -> b
               -> mp b'
manyToMultiple bf cf xt cs [] b  =  return $ cf [] cs b
manyToMultiple bf cf xt cs (p:ps) b
 = do bc <- manyToOne bf cf cs p b
      let (b',cs') = xt bc
      manyToMultiple bf cf xt cs' ps b'
\end{code}
