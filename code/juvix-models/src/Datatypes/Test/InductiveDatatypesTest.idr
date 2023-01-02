module Datatypes.Test.InductiveDatatypesTest

import Datatypes.InductiveDatatypes
import Library.Test.TestLibrary
import Library.FunctionsAndRelations
import Datatypes.Test.DatatypesTest

%default total

public export
unitType : TestDatatype
unitType = Algebraic AlgebraicUnit

public export
unitConstructor : TestRecord
unitConstructor = Fields [ unitType ]

public export
identityConstructor : TestDatatype -> TestRecord
identityConstructor type = Fields [ type ]

public export
endoFunction : TestDatatype -> TestDatatype
endoFunction type =
  let underlying = compileDatatype type in
  Algebraic (AlgebraicExponential underlying underlying)

public export
endoFunctionConstructor : TestDatatype -> TestRecord
endoFunctionConstructor type = Fields [ endoFunction type ]

public export
natDatatype : TestDatatype -> TestDatatype
natDatatype carrier =
  DatatypeFromRecords [ unitConstructor, identityConstructor carrier ]

export
inductiveDatatypesTests : IO ()
inductiveDatatypesTests = pure ()
