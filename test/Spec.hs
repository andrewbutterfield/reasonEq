module Main where
import Test.Framework as TF (defaultMain, Test)

import LexBase
import AST

main = defaultMain tests

tests :: [TF.Test]
tests
 = test_LexBase ++ test_AST
