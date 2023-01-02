module RefinedSExp.Test.ComputationTest

import public Library.Test.TestLibrary
import public RefinedSExp.Computation

%default total

public export
computationNotationTest : EExp
computationNotationTest =
  EANat 0 $* (EAMorphism Gödel $* EAString "two" $^^ EANat 3) ::
    (EANat 4 $*** (EANat 5 $* (EANat 6 $*** (EAString "seven" $**^ EANat 8)) $:^
      EAMorphism Turing)) $:^ EAInterpretation Pair

export
computationTests : IO ()
computationTests = do
  printLn "Begin computationTests:"
  printLn $ show computationNotationTest
  printLn "End computationTests."
  pure ()
