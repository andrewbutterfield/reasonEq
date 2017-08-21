module Main where
import Test.Framework as TF (defaultMain, Test)

import LexBase
import AST
import Syntax
import Builder
import VarDataTest

main = defaultMain tests

tests :: [TF.Test]
tests
 =  int_tst_LexBase
 ++ int_tst_AST
 ++ int_tst_Syntax
 ++ int_tst_Builder
 ++ tst_VarData
