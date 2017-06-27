module Main where
import Test.Framework as TF (defaultMain, Test)

import LexBase
import AST

main = defaultMain tests

tests :: [TF.Test]
tests
 = int_tst_LexBase ++ int_tst_AST
