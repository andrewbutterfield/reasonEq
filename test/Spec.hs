module Main where
import Test.Framework as TF (defaultMain, Test)

import LexBase
import AST
import Syntax

main = defaultMain tests

tests :: [TF.Test]
tests
 = int_tst_LexBase ++ int_tst_AST ++ int_tst_Syntax
