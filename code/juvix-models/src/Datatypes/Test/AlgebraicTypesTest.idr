module Datatypes.Test.AlgebraicTypesTest

import public Datatypes.AlgebraicTypes
import Library.Test.TestLibrary
import Library.FunctionsAndRelations

%default total

public export
TestPrimEnv : PrimitiveEnv
TestPrimEnv = PrimArgs PrimitiveType

public export
TestPrimTypeInterpretation : PrimitiveTypeInterpretation TestPrimEnv
TestPrimTypeInterpretation = PrimitiveTypeInterpretations interpretPrimitiveType

-- At the moment, this test environment just provides all
-- metalanguage functions on the algebraic closure of the
-- primitive types as generator functions.
public export
TestPrimFuncEnv : PrimitiveFuncEnv TestPrimEnv
TestPrimFuncEnv = CompletePrimitiveFuncEnv TestPrimTypeInterpretation

public export
TestPrimFuncInterpretation :
  PrimitiveFunctionInterpretation TestPrimFuncEnv TestPrimTypeInterpretation
TestPrimFuncInterpretation =
  CompletePrimitiveFunctionInterpretation TestPrimTypeInterpretation

export
algebraicTypesTests : IO ()
algebraicTypesTests = pure ()
