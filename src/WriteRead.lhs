\section{Writing and Reading}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module WriteRead
 ( readThis, readKey
 , writePerLine, readPerLine
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

\newpage{Lists}

\begin{code}
list = "LIST"
listHDR ttl  =  "BEGIN " ++ list ++ " " ++ ttl
listTRL ttl  =  "END " ++ list ++ " " ++ ttl

writePerLine :: String -> (a -> String) -> [a] -> [String]
writePerLine ttl write xs  =  listHDR ttl : map write xs ++ [ listTRL ttl]

readPerLine :: Monad m => String -> (String -> a) -> [String]
            -> m ([a],[String])
readPerLine ttl read [] = fail "readPerLine: no text."
readPerLine ttl read (txt:txts)
  | txt /= listHDR ttl  = fail ("readPerLine: not a list - "++txt)
  | otherwise = readPerLine' (listTRL ttl) read [] (txts)

readPerLine' _ _ _ [] = fail "readPerLine: premature text end."
readPerLine' trailer read tsil (txt:txts)
 | txt == trailer  =  return (reverse tsil, txts)
 | otherwise = readPerLine' trailer read (read txt:tsil) txts
\end{code}

\newpage
\subsection{Maps}

\begin{code}
mapping = "MAP"
mapHDR ttl  =  "BEGIN " ++ mapping ++ " " ++ ttl
mapTRL ttl  =  "END " ++ mapping ++ " " ++ ttl

writeMap :: Show k => String -> (d -> [String]) -> Map k d -> [String]
writeMap title write m
  =  [ mapHDR title ] ++
     wmap (M.assocs m) ++
     [ mapTRL title ]
  where
    wmap [] = []
    wmap ((k,d):rest) = show k : write d ++ wmap rest
\end{code}

\begin{code}
readMap :: (Ord k, Monad m)
        => String -> (String -> m k) -> ([String] -> m (d,[String])) -> [String]
        -> m (Map k d,[String])
readMap title rdKey rdDat [] = fail "readMap: no text."
readMap title rdKey rdDat txts
  = do rest <- readThis (mapHDR title) txts
       readMap' (mapTRL title) rdKey rdDat [] rest

readMap' _ _ _ _ [] = fail "readMap: missing entry or trailer."
readMap' trailer rdKey rdDat alist (txt:txts)
 | txt == trailer  =  return (M.fromList alist,txts)
 | otherwise =
     do key <- rdKey txt
        (dat,rest) <- rdDat txts
        readMap' trailer rdKey rdDat ((key,dat):alist) rest
\end{code}
