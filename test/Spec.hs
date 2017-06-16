module Main where
import Test.Framework as TF (defaultMain, Test)

import AST

main = defaultMain tests

tests :: [TF.Test]
tests
 = test_AST
