module Main where
import Test.Framework as TF (defaultMain, Test)

import LexBase
import Variables
import AST
import Syntax
import Builder
import VarDataTest
import BindingTest
import MatchingTest
import MatchScenarios

main = defaultMain tests

tests :: [TF.Test]
tests
 =  int_tst_LexBase
 ++ int_tst_Variables
 ++ int_tst_AST
 ++ int_tst_Syntax
 ++ int_tst_Builder
 ++ tst_VarData
 ++ tst_Binding
 ++ tst_Matching
 ++ test_match_scenarios
