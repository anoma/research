module Datatypes.Test.DatatypesTest

import public Datatypes.Datatypes
import public Datatypes.Test.AlgebraicTypesTest
import Library.Test.TestLibrary
import Library.FunctionsAndRelations
import Library.List

%default total

public export
TestDatatype : Type
TestDatatype = Datatype TestPrimEnv

public export
TestRecord : Type
TestRecord = RecordType TestPrimEnv

public export
TestNatRecord : TestRecord
TestNatRecord = Fields [ Primitive PrimTypeNat ]

public export
TestBoolStringRecord : TestRecord
TestBoolStringRecord =
  Fields [ Primitive PrimTypeBool, Primitive PrimTypeString ]

public export
TestTwoConstructorType : TestDatatype
TestTwoConstructorType =
  DatatypeFromRecords [ TestNatRecord, TestBoolStringRecord ]

public export
interpretTestDatatype : TestDatatype -> Type
interpretTestDatatype = interpretDatatype TestPrimTypeInterpretation

public export
testFirstConstructorExpression : interpretTestDatatype TestTwoConstructorType
testFirstConstructorExpression = Left (0, ())

public export
testSecondConstructorExpression : interpretTestDatatype TestTwoConstructorType
testSecondConstructorExpression = Right (Left (False, "Or is it", ()))

public export
testNestedDeclarationRecord : TestRecord
testNestedDeclarationRecord =
  Fields [TestTwoConstructorType, Primitive PrimTypeBool]

public export
TestNestedDeclarationType : TestDatatype
TestNestedDeclarationType =
  DatatypeFromRecords [testNestedDeclarationRecord, TestNatRecord]

public export
testNestedDeclarationExpressionLeft :
  interpretTestDatatype TestNestedDeclarationType
testNestedDeclarationExpressionLeft =
  Left (testSecondConstructorExpression, True, ())

public export
testNestedDeclarationExpressionRight :
  interpretTestDatatype TestNestedDeclarationType
testNestedDeclarationExpressionRight = Right (Left (1, ()))

public export
datatypesTests : IO ()
datatypesTests = pure ()
