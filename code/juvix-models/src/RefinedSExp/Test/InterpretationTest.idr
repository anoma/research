module RefinedSExp.Test.InterpretationTest

import public Library.Test.TestLibrary
import public RefinedSExp.Interpretation
import public RefinedSExp.Test.ComputationTest

%default total

export
failMExp : MExp
failMExp = Fail $* []

export
failEExp : EExp
failEExp = MExpToEExp failMExp

export
testTerm : EExp
testTerm = EAInterpretation Pair $* [ESNat 1, ESString "a"]

export
failAppliedToTerm : EExp
failAppliedToTerm = ESApply failEExp testTerm

export
extraneousFailArgs : EExp
extraneousFailArgs = EAInterpretation Failure $* [ESNat 0]

export
testElimLeft : EExp
testElimLeft = ESApply (EAMorphism ProductElimLeft $* []) testTerm

export
testElimRight : EExp
testElimRight = ESApply (EAMorphism ProductElimRight $* []) testTerm

export
rightThenLeft : EExp
rightThenLeft = EAMorphism Compose $*
  [EAMorphism ProductElimLeft $* [], EAMorphism ProductElimRight $* []]

export deeperTestTerm : EExp
deeperTestTerm = EAInterpretation Pair $* [ESString "b", testTerm]

export
testRightThenLeft : EExp
testRightThenLeft = ESApply rightThenLeft deeperTestTerm

export
interpretationTests : IO ()
interpretationTests = do
  printLn "Beginning interpretationTests."
  printLn ("failMExp = " ++ show failMExp)
  printLn ("failEExp = " ++ show failEExp)
  printLn ("one step on failEExp = " ++ show (eexpInterpretStep failEExp))
  printLn ("testTerm = " ++ show testTerm)
  printLn ("failAppliedToTerm = " ++ show failAppliedToTerm)
  printLn ("one step on failAppliedToTerm = " ++
    show (eexpInterpretStep failAppliedToTerm))
  printLn ("two steps on failAppliedToTerm = " ++
    show (eexpInterpretSteps 2 failAppliedToTerm))
  printLn ("three steps on failAppliedToTerm = " ++
    show (eexpInterpretSteps 3 failAppliedToTerm))
  printLn ("extraneousFailArgs = " ++ show extraneousFailArgs)
  printLn ("one step on extraneousFailArgs = " ++
    show (eexpInterpretStep extraneousFailArgs))
  printLn ("four steps on extraneousFailArgs = " ++
    show (eexpInterpretSteps 4 extraneousFailArgs))
  printLn ("testElimLeft = " ++ show testElimLeft)
  printLn ("one step on testElimLeft = " ++
    show (eexpInterpretStep testElimLeft))
  printLn ("four steps on testElimLeft = " ++
    show (eexpInterpretSteps 4 testElimLeft))
  printLn ("two steps on testElimRight = " ++
    show (eexpInterpretSteps 2 testElimRight))
  printLn ("testRightThenLeft = " ++ show testRightThenLeft)
  printLn ("one step on testRightThenLeft = " ++
    show (eexpInterpretStep testRightThenLeft))
  printLn ("two steps on testRightThenLeft = " ++
    show (eexpInterpretSteps 2 testRightThenLeft))
  printLn ("three steps on testRightThenLeft = " ++
    show (eexpInterpretSteps 3 testRightThenLeft))
  printLn ("four steps on testRightThenLeft = " ++
    show (eexpInterpretSteps 4 testRightThenLeft))
  printLn "Done with interpretationTests."
  pure ()
