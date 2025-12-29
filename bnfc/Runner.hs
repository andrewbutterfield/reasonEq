module Main where

import LexUTP
import ParUTP
import AbsUTP

import ErrM

main = do
  interact calc
  putStrLn ""

calc s = 
  let Ok e = pExp (myLexer s) 
  in ("Input: "++s++"Output: "++show (interpret e)++"\n.")


interpret :: Exp -> Integer
interpret x = case x of
  EAdd exp0 exp  -> interpret exp0 + interpret exp
  ESub exp0 exp  -> interpret exp0 - interpret exp
  EMul exp0 exp  -> interpret exp0 * interpret exp
  EDiv exp0 exp  -> interpret exp0 `div` interpret exp
  EInt n  -> n
