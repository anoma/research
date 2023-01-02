module Datatypes.InductiveDatatypes

import Library.FunctionsAndRelations
import public Datatypes.AlgebraicTypes
import public Datatypes.Datatypes

%default total

public export
data ParameterizedDatatype : (penv : PrimitiveEnv) -> Type where
  ConstDatatype :
    Datatype penv -> ParameterizedDatatype penv
  VariableDatatype :
    (Datatype penv -> Datatype penv) -> ParameterizedDatatype penv
