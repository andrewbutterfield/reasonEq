module Main where
import Test.HUnit
import Test.Framework as TF (defaultMain, Test)
import Test.Framework.Providers.HUnit (testCase)

import LexBase
import Variables
import AST
import SideCond
import FreeVars
import Substitution
import Binding
import Syntax
import Builder
import TermZipper
import FreeVarTest
import VarDataTest
import BindingTest
import MatchingTest
import MatchScenarios

main = defaultMain tests

tests :: [TF.Test]
tests = [testCase "reasonEq Tests\n==============" (2+2 @?= 4)]
-- =  int_tst_LexBase
--  ++ int_tst_Variables
--  ++ int_tst_AST
--  ++ int_tst_SideCond
    ++ int_tst_Subst
--  ++ int_tst_Binding
--  ++ int_tst_Syntax
--  ++ int_tst_Builder
--  ++ int_tst_TermZip
--  ++ int_tst_FreeVar
--  ++ tst_FreeVar
--  ++ tst_VarData
--  ++ tst_Binding
--  ++ tst_Matching
--  ++ test_match_scenarios
