module Datatypes.Datatypes

import Library.FunctionsAndRelations
import Library.Decidability
import Category.Category
import Control.WellFounded
import RefinedSExp.List
import public Datatypes.AlgebraicTypes

%default total

mutual
  public export
  data Datatype : (penv : PrimitiveEnv) -> Type where
    Algebraic : AlgebraicType penv -> Datatype penv
    Record : RecordType penv -> Datatype penv
    Constructors : ConstructorType penv -> Datatype penv
    Function : FunctionType penv -> Datatype penv

  public export
  data RecordType : (penv : PrimitiveEnv) -> Type where
    Fields : List (Datatype penv) -> RecordType penv

  public export
  data ConstructorType : (penv : PrimitiveEnv) -> Type where
    Records : List (RecordType penv) -> ConstructorType penv

  public export
  data FunctionType : (penv : PrimitiveEnv) -> Type where
    Signature : Datatype penv -> Datatype penv -> FunctionType penv

  public export
  Primitive : {penv : PrimitiveEnv} -> PrimType penv -> Datatype penv
  Primitive = Algebraic . AlgebraicTypeGenerator

  public export
  FieldsOf : {penv : PrimitiveEnv} -> RecordType penv -> List (Datatype penv)
  FieldsOf (Fields fields) = fields

  public export
  DatatypeFromList : {penv : PrimitiveEnv} ->
    List (Datatype penv) -> Datatype penv
  DatatypeFromList = Record . Fields

  public export
  DatatypeFromRecords : {penv : PrimitiveEnv} ->
    List (RecordType penv) -> Datatype penv
  DatatypeFromRecords = Constructors . Records

  public export
  ConstructorsFromMatrix : {penv : PrimitiveEnv} ->
    List (List (Datatype penv)) -> ConstructorType penv
  ConstructorsFromMatrix = Records . map Fields

  public export
  DatatypeFromMatrix : {penv : PrimitiveEnv} ->
    List (List (Datatype penv)) -> Datatype penv
  DatatypeFromMatrix = Constructors . ConstructorsFromMatrix

  public export
  RecordsOf : {penv : PrimitiveEnv} ->
    ConstructorType penv -> List (RecordType penv)
  RecordsOf (Records records) = records

  public export
  MatrixOf : {penv : PrimitiveEnv} ->
    ConstructorType penv -> List (List (Datatype penv))
  MatrixOf = map FieldsOf . RecordsOf

  public export
  DomainOf : {penv : PrimitiveEnv} -> FunctionType penv -> Datatype penv
  DomainOf (Signature domain _) = domain

  public export
  CodomainOf : {penv : PrimitiveEnv} -> FunctionType penv -> Datatype penv
  CodomainOf (Signature _ codomain) = codomain

  public export
  compileDatatype : {penv : PrimitiveEnv} ->
    Datatype penv -> AlgebraicType penv
  compileDatatype (Algebraic primType) = primType
  compileDatatype (Record rt) = compileRecordType rt
  compileDatatype (Constructors constructors) =
    compileConstructorType constructors
  compileDatatype (Function functionType) =
    compileFunctionType functionType

  public export
  compileDatatypeList : {penv : PrimitiveEnv} ->
    List (Datatype penv) -> List (AlgebraicType penv)
  compileDatatypeList [] = []
  compileDatatypeList (t :: ts) = compileDatatype t :: compileDatatypeList ts

  public export
  compileRecordType : {penv : PrimitiveEnv} ->
    RecordType penv -> AlgebraicType penv
  compileRecordType (Fields types) =
    AlgebraicListProduct (compileDatatypeList types)

  public export
  compileConstructorType : {penv : PrimitiveEnv} ->
    ConstructorType penv -> AlgebraicType penv
  compileConstructorType (Records records) =
    AlgebraicListCoproduct (compileRecordTypeList records)

  public export
  compileFunctionType : {penv : PrimitiveEnv} ->
    FunctionType penv -> AlgebraicType penv
  compileFunctionType (Signature domain codomain) =
    AlgebraicExponential (compileDatatype domain) (compileDatatype codomain)

  public export
  compileRecordTypeList : {penv : PrimitiveEnv} ->
    List (RecordType penv) -> List (AlgebraicType penv)
  compileRecordTypeList [] = []
  compileRecordTypeList (t :: ts) =
    compileRecordType t :: compileRecordTypeList ts

  public export
  data DatatypeFunction : {penv : PrimitiveEnv} ->
    (pfenv : PrimitiveFuncEnv penv) -> (domain, codomain : Datatype penv) ->
    Type where
      DatatypeFromAlgebraic :
        {penv : PrimitiveEnv} -> {pfenv : PrimitiveFuncEnv penv} ->
        {domain, codomain : Datatype penv} ->
        AlgebraicFunction pfenv
          (compileDatatype domain) (compileDatatype codomain) ->
        DatatypeFunction pfenv domain codomain

      PatternMatch :
        {penv : PrimitiveEnv} -> {pfenv : PrimitiveFuncEnv penv} ->
        {records : List (RecordType penv)} ->
        {codomain : Datatype penv} ->
        ListForAll (flip (AlgebraicFunction pfenv) (compileDatatype codomain))
          (compileRecordTypeList records) ->
        DatatypeFunction pfenv (Constructors (Records records)) codomain

  public export
  compileDatatypeFunction : {penv : PrimitiveEnv} ->
    {pfenv : PrimitiveFuncEnv penv} -> {domain, codomain : Datatype penv} ->
    DatatypeFunction pfenv domain codomain ->
    AlgebraicFunction pfenv (compileDatatype domain) (compileDatatype codomain)
  compileDatatypeFunction (DatatypeFromAlgebraic f) = f
  compileDatatypeFunction (PatternMatch patterns) =
    AlgebraicFunctionListCoproduct patterns

  public export
  DatatypeCompose : {penv : PrimitiveEnv} -> {pfenv : PrimitiveFuncEnv penv} ->
    {a, b, c : Datatype penv} ->
    DatatypeFunction pfenv b c ->
    DatatypeFunction pfenv a b ->
    DatatypeFunction pfenv a c
  DatatypeCompose f g =
    DatatypeFromAlgebraic
      (AlgebraicCompose (compileDatatypeFunction f) (compileDatatypeFunction g))

  public export
  DatatypeFunctionGenerator : {penv : PrimitiveEnv} ->
    {pfenv : PrimitiveFuncEnv penv} -> {domain, codomain : Datatype penv} ->
    PrimFuncType pfenv (compileDatatype domain) (compileDatatype codomain) ->
    DatatypeFunction pfenv domain codomain
  DatatypeFunctionGenerator = DatatypeFromAlgebraic . AlgebraicFunctionGenerator

  public export
  interpretDatatype : {penv : PrimitiveEnv} ->
    PrimitiveTypeInterpretation penv -> Datatype penv -> Type
  interpretDatatype interpretation =
    interpretAlgebraicType interpretation . compileDatatype

  public export
  interpretDatatypeFunction : {penv : PrimitiveEnv} ->
    {pfenv : PrimitiveFuncEnv penv} ->
    {typeInterpretation : PrimitiveTypeInterpretation penv} ->
    (functionInterpretation :
      PrimitiveFunctionInterpretation pfenv typeInterpretation) ->
    {domain, codomain : Datatype penv} ->
    DatatypeFunction pfenv domain codomain ->
    interpretAlgebraicFunctionType typeInterpretation
      (compileDatatype domain) (compileDatatype codomain)
  interpretDatatypeFunction functionInterpretation =
    interpretAlgebraicFunction functionInterpretation . compileDatatypeFunction
