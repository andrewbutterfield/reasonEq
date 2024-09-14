\section{YesBut Datatype}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017-22

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module YesBut (
  YesBut(..)
)
where

import Control.Applicative
import Control.Monad
\end{code}


\subsection{Datatype: Yes, But \dots}

\begin{code}
data YesBut t
 = Yes t
 | But [String]
 deriving (Eq,Show)
\end{code}

\subsection{Instances}

\begin{code}
instance Functor YesBut where
  fmap f (Yes x)    =  Yes $ f x
  fmap f (But msgs)  =  But msgs

instance Applicative YesBut where
  pure x                   =  Yes x
  Yes f <*> Yes x          =  Yes $ f x
  Yes f <*> But msgs       =  But msgs
  But msgs <*> Yes x       =  But msgs
  But msgs1 <*> But msgs2  =  But (msgs1++msgs2)

instance Monad YesBut where
  Yes x   >>= f   =  f x
  But msgs >>= f  =  But msgs

instance MonadFail YesBut where
  fail msg  =  But $ lines msg

instance Alternative YesBut where
  empty = But []
  But msgs1 <|> But msgs2  =  But (msgs1 ++ msgs2)
  But _     <|> yes2       =  yes2
  yes1      <|> _          =  yes1

instance MonadPlus YesBut where
  mzero = But []
  But msgs1 `mplus` But msgs2  =  But (msgs1 ++ msgs2)
  But _     `mplus` yes2       =  yes2
  yes1      `mplus` _          =  yes1
\end{code}
