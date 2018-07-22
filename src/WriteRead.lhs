\section{Writing and Reading}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module WriteRead
 ( readThis, readKey
 , writeMap, readMap
 )
where

import Data.Map (Map)
import qualified Data.Map as M

import Utilities
\end{code}

Here we provide functions to convert various datatypes
to and from text, for saving to and restoring from files.
We could simply use \texttt{show} and \texttt{read},
but this results in files being one-liners,
and hence not very easy to check by eye,
and indigestible by diff tools in version control.

Instead we go for a halfway house:
terms, side-conditions, laws, are all one-liners,
but aggregates of these such as proofs, or theory
will be multiline, so allowing effective version control.


\subsection{Fixed Text}

\begin{code}
readThis :: Monad m => String -> [String] -> m [String]
readThis this [] = fail "readThis: no text."
readThis this (txt:txts)
 | txt == this  =  return txts
 | otherwise
     = fail ("readThis: expected '" ++ this ++
             "', but got '"++ txt ++ "'.")
\end{code}

\subsection{Keyed Text}

\begin{code}
readKey :: Monad m => String -> (String -> a) -> [String] -> m (a,[String])
readKey key _ [] = fail ("readKey '"++key++"': no text.")
readKey key rd (txt:txts)
 | pre == key  =  return (rd post,txts)
 | otherwise
     = fail ("readKey: expected '" ++ key ++
             "', but got '"++ txt ++ "'.")
 where
   (pre,post) = splitAt (length key) txt
\end{code}


\newpage
\subsection{Maps}

\begin{code}
mapping = "MAP"
mapHDR = "BEGIN "++mapping ; mapTRL ="END "++mapping

writeMap :: Show k => String -> (d -> [String]) -> Map k d -> [String]
writeMap title write m
  =  [ mapHDR ++ " " ++ title ] ++
     wmap (M.assocs m) ++
     [ mapTRL ++ " " ++ title ]
  where
    wmap [] = []
    wmap ((k,d):rest) = show k : write d ++ wmap rest
\end{code}

\begin{code}
readMap :: Monad m => String -> (String -> m k) -> ([String] -> m (d,[String]))
        -> [String] -> m (Map k d,[String])
readMap title rdKey rdDat txts
  = fail "readMap NYI"
\end{code}
