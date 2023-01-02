module Executable.Test.Main

import Library.Test.TestLibrary
import Geb.Test.GebTest
import Geb.Test.GebConceptTest
import Geb.Test.GebSExpTest
import Geb.Test.CExpTest
import RefinedSExp.Test.ListTest
import RefinedSExp.PairVariant.Test.SExpTest
import RefinedSExp.Test.ComputableFunctionsTest
import RefinedSExp.Test.SExpApplicativesTest
import RefinedSExp.Test.RefinedSExpTest
import RefinedSExp.Test.RefinementInterpretationTest
import RefinedSExp.Test.AlgebraicSExpTest
import RefinedSExp.Test.AlgebraicSExpInterpretationTest
import RefinedSExp.Test.ComputationTest
import RefinedSExp.Test.SExpTest
import RefinedSExp.Test.NamingTest
import RefinedSExp.Test.InterpretationTest
import Datatypes.Test.AlgebraicTypesTest
import Datatypes.Test.DatatypesTest
import Datatypes.Test.InductiveDatatypesTest
import Datatypes.Test.DependentAlgebraicTypesTest
import Datatypes.Test.DependentInductiveDatatypesTest
import RefinedSExp.Test.SExpFinTest
import Theories.Test.AlgebraicTheoryTest
import Theories.Test.DependentAlgebraicTheoryTest
import Theories.Test.HigherOrderRecursionTest
import Theories.Test.InductiveTypeTheoryTest
import Theories.Test.DependentInductiveTypeTheoryTest
import RefinedSExp.Old.Test.TestLibrary
import RefinedSExp.Old.Test.ListTest
import RefinedSExp.Old.Test.RefinedListTest
import RefinedSExp.Old.Test.SExpTest
import RefinedSExp.Old.Test.RefinedSExpTest
import RefinedSExp.Old.Test.OldSExpTest
import RefinedSExp.Old.Test.ADTTest
import RefinedSExp.ListVariant.Test.TestLibrary
import RefinedSExp.ListVariant.Test.ListTest
import RefinedSExp.ListVariant.Test.RefinedListTest
import RefinedSExp.ListVariant.Test.SExpTest
import RefinedSExp.ListVariant.Test.RefinedSExpTest
import ReflectiveLanguages.Test.SubstitutiveTest
import ReflectiveLanguages.Interpretations.Test.SubstitutiveInterpretationTest
import ReflectiveLanguages.Test.QExpTest
import ReflectiveLanguages.Interpretations.Test.QExpInterpretationTest

%default total

export
main : IO ()
main = do
  Geb.Test.GebConceptTest.gebConceptTests
  RefinedSExp.Test.SExpTest.sexpTests
  RefinedSExp.Test.RefinedSExpTest.refinedSExpTests
  Geb.Test.GebTest.gebTests
  Geb.Test.CExpTest.cexpTests
  {-
  Geb.Test.GebSExpTest.gebSExpTests
  RefinedSExp.Test.ListTest.listTests
  RefinedSExp.PairVariant.Test.SExpTest.sExpTests
  RefinedSExp.Test.ComputableFunctionsTest.computableFunctionsTests
  RefinedSExp.Test.SExpApplicativesTest.sExpApplicativesTests
  RefinedSExp.Test.RefinedSExpTest.refinedSExpTests
  RefinedSExp.Test.RefinementInterpretationTest.refinementInterpretationTests
  RefinedSExp.Test.SExpFinTest.sexpFinTests
  RefinedSExp.Test.AlgebraicSExpTest.algebraicSExpTests
  RefinedSExp.Test.AlgebraicSExpInterpretationTest.algebraicSExpInterpretationTests
  RefinedSExp.Test.ComputationTest.computationTests
  RefinedSExp.Test.NamingTest.namingTests
  RefinedSExp.Test.InterpretationTest.interpretationTests
  Datatypes.Test.AlgebraicTypesTest.algebraicTypesTests
  Datatypes.Test.DatatypesTest.datatypesTests
  Datatypes.Test.InductiveDatatypesTest.inductiveDatatypesTests
  Datatypes.Test.DependentAlgebraicTypesTest.dependentAlgebraicTypesTests
  Datatypes.Test.DependentInductiveDatatypesTest.dependentInductiveDatatypesTests
  Theories.Test.AlgebraicTheoryTest.algebraicTheoryTests
  Theories.Test.DependentAlgebraicTheoryTest.dependentAlgebraicTheoryTests
  Theories.Test.HigherOrderRecursionTest.higherOrderRecursionTests
  Theories.Test.InductiveTypeTheoryTest.inductiveTypeTheoryTests
  Theories.Test.DependentInductiveTypeTheoryTest.dependentInductiveTypeTheoryTests
  RefinedSExp.Old.Test.ListTest.listTests
  RefinedSExp.Old.Test.RefinedListTest.refinedListTests
  RefinedSExp.Old.Test.SExpTest.sExpTests
  RefinedSExp.Old.Test.RefinedSExpTest.refinedSExpTests
  RefinedSExp.ListVariant.Test.ListTest.listTests
  RefinedSExp.ListVariant.Test.RefinedListTest.refinedListTests
  RefinedSExp.ListVariant.Test.SExpTest.sExpTests
  RefinedSExp.ListVariant.Test.RefinedSExpTest.refinedSExpTests
  ReflectiveLanguages.Test.SubstitutiveTest.substitutiveTests
  ReflectiveLanguages.Interpretations.Test.SubstitutiveInterpretationTest.substitutiveInterpretationTests
  ReflectiveLanguages.Test.QExpTest.qexpTests
  ReflectiveLanguages.Interpretations.Test.QExpInterpretationTest.qexpInterpretationTests
  -}
