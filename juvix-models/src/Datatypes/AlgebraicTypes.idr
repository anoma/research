module Datatypes.AlgebraicTypes

import public Library.FunctionsAndRelations
import public RefinedSExp.List
import public RefinedSExp.SExp

%default total

-- The inductive-datatype system is parameterized on primitive types provided
-- by the type theory in which it is embedded.
public export
record PrimitiveEnv where
  constructor PrimArgs
  PrimType : Type

public export
PrimitiveEnvFunctor : Type
PrimitiveEnvFunctor = PrimitiveEnv -> PrimitiveEnv

-- Standard algebraic data types, with the primitive types added as
-- generators.  We will compile record types and inductive types to
-- these to show that record types and inductive types do not extend
-- the underlying theory (which is that of standard algebraic data types).
public export
data AlgebraicType : (penv : PrimitiveEnv) -> Type where
  AlgebraicTypeGenerator : PrimType penv -> AlgebraicType penv
  AlgebraicVoid : AlgebraicType penv
  AlgebraicUnit : AlgebraicType penv
  AlgebraicProduct :
    (domain, codomain : AlgebraicType penv) -> AlgebraicType penv
  AlgebraicCoproduct :
    (domain, codomain : AlgebraicType penv) -> AlgebraicType penv
  AlgebraicExponential :
    (domain, codomain : AlgebraicType penv) -> AlgebraicType penv

public export
AlgebraicListProduct : List (AlgebraicType penv) -> AlgebraicType penv
AlgebraicListProduct [] = AlgebraicUnit
AlgebraicListProduct (t :: ts) =
  AlgebraicProduct t (AlgebraicListProduct ts)

public export
AlgebraicListCoproduct : List (AlgebraicType penv) -> AlgebraicType penv
AlgebraicListCoproduct [] = AlgebraicVoid
AlgebraicListCoproduct (t :: ts) =
  AlgebraicCoproduct t (AlgebraicListCoproduct ts)

public export
AlgebraicElementType : {penv : PrimitiveEnv} ->
  AlgebraicType penv -> AlgebraicType penv
AlgebraicElementType type = AlgebraicExponential AlgebraicUnit type

-- The theory is also parameterized on primitive _functions_ provided
-- by the system.  We allow the system to provide primitive functions on
-- the algebraic closure of the primitive types, so that the system
-- doesn't need to provide primitive types that would be redundant with
-- algebraic types (such as if it wants to provide a primitive (+) function
-- which takes a pair as an argument).
public export
record PrimitiveFuncEnv (penv : PrimitiveEnv) where
  constructor PrimFuncs
  PrimFuncType : (domain, codomain : AlgebraicType penv) -> Type

public export
PrimitiveFuncEnvFunctor : PrimitiveEnvFunctor -> Type
PrimitiveFuncEnvFunctor f =
  {penv : PrimitiveEnv} -> PrimitiveFuncEnv penv -> PrimitiveFuncEnv (f penv)

public export
data AlgebraicFunction : {penv : PrimitiveEnv} ->
  (pfenv : PrimitiveFuncEnv penv) -> (domain, codomain : AlgebraicType penv) ->
  Type where
    AlgebraicIdentity : (a : AlgebraicType penv) -> AlgebraicFunction pfenv a a

    AlgebraicCompose : {a, b, c : AlgebraicType penv} ->
      AlgebraicFunction pfenv b c ->
      AlgebraicFunction pfenv a b ->
      AlgebraicFunction pfenv a c

    AlgebraicFunctionGenerator :
      PrimFuncType pfenv domain codomain ->
      AlgebraicFunction pfenv domain codomain

    AlgebraicExFalso : AlgebraicFunction pfenv AlgebraicVoid codomain

    AlgebraicConstant : AlgebraicFunction pfenv domain AlgebraicUnit

    -- Consequences of the Yoneda lemma.
    AlgebraicExponentToProduct :
      (x, y, z : AlgebraicType penv) ->
      AlgebraicFunction pfenv
        (AlgebraicExponential z (AlgebraicExponential y x))
        (AlgebraicExponential (AlgebraicProduct z y) x)
    AlgebraicProductToExponent :
      (x, y, z : AlgebraicType penv) ->
      AlgebraicFunction pfenv
        (AlgebraicExponential (AlgebraicProduct z y) x)
        (AlgebraicExponential z (AlgebraicExponential y x))
    AlgebraicUnitElim :
      (codomain : AlgebraicType penv) ->
      AlgebraicFunction pfenv
        (AlgebraicExponential AlgebraicUnit codomain) codomain

    AlgebraicFunctionProduct :
      {pfenv : PrimitiveFuncEnv penv} ->
      {domain : AlgebraicType penv} ->
      {codomainLeft, codomainRight : AlgebraicType penv} ->
      AlgebraicFunction pfenv domain codomainLeft ->
      AlgebraicFunction pfenv domain codomainRight ->
      AlgebraicFunction
        pfenv domain (AlgebraicProduct codomainLeft codomainRight)

    AlgebraicFunctionLeftProjection :
      {pfenv : PrimitiveFuncEnv penv} ->
      {domainLeft, domainRight : AlgebraicType penv} ->
      AlgebraicFunction
        pfenv (AlgebraicProduct domainLeft domainRight) domainLeft

    AlgebraicFunctionRightProjection :
      {pfenv : PrimitiveFuncEnv penv} ->
      {domainLeft, domainRight : AlgebraicType penv} ->
      AlgebraicFunction
        pfenv (AlgebraicProduct domainLeft domainRight) domainRight

    AlgebraicFunctionCoproduct :
      {pfenv : PrimitiveFuncEnv penv} ->
      {domainLeft, domainRight : AlgebraicType penv} ->
      {codomain : AlgebraicType penv} ->
      AlgebraicFunction pfenv domainLeft codomain ->
      AlgebraicFunction pfenv domainRight codomain ->
      AlgebraicFunction
        pfenv (AlgebraicCoproduct domainLeft domainRight) codomain

    AlgebraicFunctionLeftInjection :
      {codomainLeft, codomainRight : AlgebraicType penv} ->
      AlgebraicFunction
        pfenv codomainLeft (AlgebraicCoproduct codomainLeft codomainRight)

    AlgebraicFunctionRightInjection :
      {codomainLeft, codomainRight : AlgebraicType penv} ->
      AlgebraicFunction
        pfenv codomainRight (AlgebraicCoproduct codomainLeft codomainRight)

    AlgebraicFunctionEval : (domain, codomain : AlgebraicType penv) ->
      AlgebraicFunction pfenv
        (AlgebraicProduct (AlgebraicExponential domain codomain) domain)
        codomain

    AlgebraicFunctionCurry :
      {domLeft, domRight, codomain : AlgebraicType penv} ->
      AlgebraicFunction pfenv (AlgebraicProduct domLeft domRight) codomain ->
      AlgebraicFunction pfenv domLeft (AlgebraicExponential domRight codomain)

public export
AlgebraicFunctionListProduct : {penv : PrimitiveEnv} ->
  {pfenv : PrimitiveFuncEnv penv} ->
  {domain : AlgebraicType penv} -> {codomains : List (AlgebraicType penv)} ->
  ListForAll (AlgebraicFunction pfenv domain) codomains ->
  AlgebraicFunction pfenv domain (AlgebraicListProduct codomains)
AlgebraicFunctionListProduct {domain} {codomains} =
  listEliminator
    {lp=(\codomains' =>
      ListForAll (AlgebraicFunction pfenv domain) codomains' ->
      AlgebraicFunction pfenv domain (AlgebraicListProduct codomains'))}
    (ListEliminatorArgs
     (\_ => AlgebraicConstant)
     (\a, l, product, forAll =>
      AlgebraicFunctionProduct (fst forAll) (product (snd forAll)))
    ) codomains

public export
AlgebraicFunctionListCoproduct : {penv : PrimitiveEnv} ->
  {pfenv : PrimitiveFuncEnv penv} ->
  {domains : List (AlgebraicType penv)} -> {codomain : AlgebraicType penv} ->
  ListForAll (flip (AlgebraicFunction pfenv) codomain) domains ->
  AlgebraicFunction pfenv (AlgebraicListCoproduct domains) codomain
AlgebraicFunctionListCoproduct {domains} {codomain} =
  listEliminator
    {lp=(\domains' =>
      ListForAll (flip (AlgebraicFunction pfenv) codomain) domains' ->
      AlgebraicFunction pfenv (AlgebraicListCoproduct domains') codomain)}
    (ListEliminatorArgs
      (\_ => AlgebraicExFalso)
      (\a, l, coproduct, forAll =>
        AlgebraicFunctionCoproduct (fst forAll) (coproduct (snd forAll)))
    ) domains

public export
GeneralizedElement : {penv : PrimitiveEnv} -> (pfenv : PrimitiveFuncEnv penv) ->
  (type, stage : AlgebraicType penv) -> Type
GeneralizedElement pfenv type stage = AlgebraicFunction pfenv stage type

public export
AlgebraicElement : {penv : PrimitiveEnv} -> (pfenv : PrimitiveFuncEnv penv) ->
  AlgebraicType penv -> Type
AlgebraicElement pfenv type = GeneralizedElement pfenv type AlgebraicUnit

public export
AlgebraicFunctionAsElement : {penv : PrimitiveEnv} ->
  {pfenv : PrimitiveFuncEnv penv} ->
  {domain, codomain : AlgebraicType penv} ->
  AlgebraicFunction pfenv domain codomain ->
  AlgebraicElement pfenv (AlgebraicExponential domain codomain)
AlgebraicFunctionAsElement {domain} f =
  AlgebraicFunctionCurry (AlgebraicCompose f AlgebraicFunctionRightProjection)

public export
record ReflectionEnv {penv : PrimitiveEnv} (pfenv : PrimitiveFuncEnv penv) where
  constructor Reflection
  Universe : Type
  CodeType : Universe -> AlgebraicType penv
  MemberType : Universe -> AlgebraicType penv
  EncodeType : (universe : Universe) ->
    AlgebraicFunction pfenv (MemberType universe) (CodeType universe)
  FunctorType : {universe : Universe} ->
    AlgebraicFunction pfenv (CodeType universe) (CodeType universe) -> Type
  ReflectedFunctor :
    {universe : Universe} ->
    {codeMap :
      AlgebraicFunction pfenv (CodeType universe) (CodeType universe)} ->
    FunctorType codeMap ->
    AlgebraicFunction pfenv (MemberType universe) (MemberType universe)

-- The inputs required to interpret algebraic types as metalanguage
-- (Idris) types.
public export
record PrimitiveTypeInterpretation (penv : PrimitiveEnv) where
  constructor PrimitiveTypeInterpretations
  interpretPrimitiveType : PrimType penv -> Type

public export
TypeInterpretationFunctor : PrimitiveEnvFunctor -> Type
TypeInterpretationFunctor f = {penv : PrimitiveEnv} ->
  PrimitiveTypeInterpretation penv -> PrimitiveTypeInterpretation (f penv)

mutual
  -- Interpret an algebraic data type as a metalanguage (Idris) type.
  public export
  interpretAlgebraicType : {penv : PrimitiveEnv} ->
    (interpretation : PrimitiveTypeInterpretation penv) ->
    AlgebraicType penv -> Type
  interpretAlgebraicType interpretation (AlgebraicTypeGenerator primType) =
    interpretPrimitiveType interpretation primType
  interpretAlgebraicType interpretation AlgebraicVoid = Void
  interpretAlgebraicType interpretation AlgebraicUnit = ()
  interpretAlgebraicType interpretation (AlgebraicProduct t t') =
    interpretAlgebraicTypePair interpretation t t'
  interpretAlgebraicType interpretation (AlgebraicCoproduct t t') =
    interpretAlgebraicTypeEither interpretation t t'
  interpretAlgebraicType interpretation (AlgebraicExponential domain codomain) =
    interpretAlgebraicType interpretation domain ->
    interpretAlgebraicType interpretation codomain

  public export
  interpretAlgebraicTypePair : {penv : PrimitiveEnv} ->
    (interpretation : PrimitiveTypeInterpretation penv) ->
    AlgebraicType penv -> AlgebraicType penv -> Type
  interpretAlgebraicTypePair interpretation t t' =
    (interpretAlgebraicType interpretation t,
     interpretAlgebraicType interpretation t')

  public export
  interpretAlgebraicTypeEither : {penv : PrimitiveEnv} ->
    (interpretation : PrimitiveTypeInterpretation penv) ->
    AlgebraicType penv -> AlgebraicType penv -> Type
  interpretAlgebraicTypeEither interpretation t t' =
    Either
      (interpretAlgebraicType interpretation t)
      (interpretAlgebraicType interpretation t')

{-
 - This environment provides all metalanguage types as primitive types.
 -}
public export
CompletePrimitiveTypeEnv : PrimitiveEnv
CompletePrimitiveTypeEnv = PrimArgs Type

public export
CompletePrimitiveTypeInterpretation :
  PrimitiveTypeInterpretation CompletePrimitiveTypeEnv
CompletePrimitiveTypeInterpretation = PrimitiveTypeInterpretations id

public export
interpretAllMetaLanguageAlgebraicTypes :
  AlgebraicType CompletePrimitiveTypeEnv -> Type
interpretAllMetaLanguageAlgebraicTypes =
  interpretAlgebraicType CompletePrimitiveTypeInterpretation

public export
interpretAlgebraicFunctionType : {penv : PrimitiveEnv} ->
  (interpretation : PrimitiveTypeInterpretation penv) ->
  (domain, codomain : AlgebraicType penv) -> Type
interpretAlgebraicFunctionType interpretation domain codomain =
  interpretAlgebraicType interpretation domain ->
  interpretAlgebraicType interpretation codomain

-- The inputs required to interpret algebraic functions as metalanguage
-- (Idris) functions.
public export
record PrimitiveFunctionInterpretation {penv : PrimitiveEnv}
  (pfenv : PrimitiveFuncEnv penv)
  (typeInterpretation : PrimitiveTypeInterpretation penv) where
    constructor PrimitiveFunctionInterpretations
    interpretPrimitiveFunction : {domain, codomain : AlgebraicType penv} ->
      PrimFuncType pfenv domain codomain ->
      interpretAlgebraicType typeInterpretation domain ->
      interpretAlgebraicType typeInterpretation codomain

public export
FunctionInterpretationFunctor : {fenv : PrimitiveEnvFunctor} ->
  {ftype : TypeInterpretationFunctor fenv} ->
  (ffenv : PrimitiveFuncEnvFunctor fenv) ->
  {penv : PrimitiveEnv} ->
  PrimitiveFuncEnv penv ->
  (itype : PrimitiveTypeInterpretation penv) ->
  Type
FunctionInterpretationFunctor {fenv} {ftype} ffenv {penv} pfenv itype =
  PrimitiveFunctionInterpretation {penv} pfenv itype ->
  PrimitiveFunctionInterpretation
    {penv=(fenv penv)} (ffenv {penv} pfenv) (ftype itype)

mutual
  public export
  interpretAlgebraicFunction : {penv : PrimitiveEnv} ->
    {pfenv : PrimitiveFuncEnv penv} ->
    {typeInterpretation : PrimitiveTypeInterpretation penv} ->
    (functionInterpretation :
      PrimitiveFunctionInterpretation pfenv typeInterpretation) ->
    {domain, codomain : AlgebraicType penv} ->
    AlgebraicFunction pfenv domain codomain ->
    interpretAlgebraicFunctionType typeInterpretation domain codomain
  interpretAlgebraicFunction functionInterpretation (AlgebraicIdentity a) = id
  interpretAlgebraicFunction functionInterpretation (AlgebraicCompose g f) =
    interpretAlgebraicFunction functionInterpretation g .
      interpretAlgebraicFunction functionInterpretation f
  interpretAlgebraicFunction functionInterpretation
    (AlgebraicFunctionGenerator f) =
      interpretPrimitiveFunction functionInterpretation f
  interpretAlgebraicFunction _ AlgebraicExFalso =
    \v => void v
  interpretAlgebraicFunction _ AlgebraicConstant =
    \_ => ()
  interpretAlgebraicFunction _ (AlgebraicExponentToProduct x y z) =
    \f, p => f (fst p) (snd p)
  interpretAlgebraicFunction _ (AlgebraicProductToExponent x y z) =
    \f, g, h => f (g, h)
  interpretAlgebraicFunction _ (AlgebraicUnitElim _) =
    \f => f ()
  interpretAlgebraicFunction interpretation (AlgebraicFunctionProduct f f') =
    interpretAlgebraicFunctionProduct interpretation f f'
  interpretAlgebraicFunction interpretation
    AlgebraicFunctionLeftProjection =
      interpretAlgebraicFunctionLeftProjection interpretation
  interpretAlgebraicFunction interpretation
    AlgebraicFunctionRightProjection =
      interpretAlgebraicFunctionRightProjection interpretation
  interpretAlgebraicFunction interpretation (AlgebraicFunctionCoproduct f f') =
    interpretAlgebraicFunctionCoproduct interpretation f f'
  interpretAlgebraicFunction interpretation
    AlgebraicFunctionLeftInjection =
      interpretAlgebraicFunctionLeftInjection interpretation
  interpretAlgebraicFunction interpretation
    AlgebraicFunctionRightInjection =
      interpretAlgebraicFunctionRightInjection interpretation
  interpretAlgebraicFunction interpretation
    (AlgebraicFunctionEval domain codomain) =
      \(eval, x) => eval x
  interpretAlgebraicFunction interpretation
    (AlgebraicFunctionCurry f) =
      (\x, y => interpretAlgebraicFunction interpretation f (x, y))

  public export
  interpretAlgebraicFunctionProduct : {penv : PrimitiveEnv} ->
    {pfenv : PrimitiveFuncEnv penv} ->
    {typeInterpretation : PrimitiveTypeInterpretation penv} ->
    (functionInterpretation :
      PrimitiveFunctionInterpretation pfenv typeInterpretation) ->
    {domain : AlgebraicType penv} ->
    {codomainLeft, codomainRight : AlgebraicType penv} ->
    AlgebraicFunction pfenv domain codomainLeft ->
    AlgebraicFunction pfenv domain codomainRight ->
    interpretAlgebraicFunctionType typeInterpretation
      domain (AlgebraicProduct codomainLeft codomainRight)
  interpretAlgebraicFunctionProduct interpretation f f' =
    \x =>
      (interpretAlgebraicFunction interpretation f x,
       interpretAlgebraicFunction interpretation f' x)

  public export
  interpretAlgebraicFunctionLeftProjection : {penv : PrimitiveEnv} ->
    {pfenv : PrimitiveFuncEnv penv} ->
    {typeInterpretation : PrimitiveTypeInterpretation penv} ->
    (functionInterpretation :
      PrimitiveFunctionInterpretation pfenv typeInterpretation) ->
    {domainLeft, domainRight : AlgebraicType penv} ->
    interpretAlgebraicFunctionType typeInterpretation
      (AlgebraicProduct domainLeft domainRight) domainLeft
  interpretAlgebraicFunctionLeftProjection interpretation = fst

  public export
  interpretAlgebraicFunctionRightProjection : {penv : PrimitiveEnv} ->
    {pfenv : PrimitiveFuncEnv penv} ->
    {typeInterpretation : PrimitiveTypeInterpretation penv} ->
    (functionInterpretation :
      PrimitiveFunctionInterpretation pfenv typeInterpretation) ->
    {domainLeft, domainRight : AlgebraicType penv} ->
    interpretAlgebraicFunctionType typeInterpretation
      (AlgebraicProduct domainLeft domainRight) domainRight
  interpretAlgebraicFunctionRightProjection interpretation = snd

  public export
  interpretAlgebraicFunctionCoproduct : {penv : PrimitiveEnv} ->
    {pfenv : PrimitiveFuncEnv penv} ->
    {typeInterpretation : PrimitiveTypeInterpretation penv} ->
    (functionInterpretation :
      PrimitiveFunctionInterpretation pfenv typeInterpretation) ->
    {domainLeft, domainRight : AlgebraicType penv} ->
    {codomain : AlgebraicType penv} ->
    AlgebraicFunction pfenv domainLeft codomain ->
    AlgebraicFunction pfenv domainRight codomain ->
    interpretAlgebraicFunctionType typeInterpretation
      (AlgebraicCoproduct domainLeft domainRight) codomain
  interpretAlgebraicFunctionCoproduct {penv} interpretation f f' =
    \x => case x of
      Left x' => interpretAlgebraicFunction interpretation f x'
      Right x' => interpretAlgebraicFunction interpretation f' x'

  public export
  interpretAlgebraicFunctionLeftInjection : {penv : PrimitiveEnv} ->
    {pfenv : PrimitiveFuncEnv penv} ->
    {typeInterpretation : PrimitiveTypeInterpretation penv} ->
    (functionInterpretation :
      PrimitiveFunctionInterpretation pfenv typeInterpretation) ->
    {codomainLeft : AlgebraicType penv} ->
    {codomainRight : AlgebraicType penv} ->
    interpretAlgebraicFunctionType typeInterpretation
      codomainLeft (AlgebraicCoproduct codomainLeft codomainRight)
  interpretAlgebraicFunctionLeftInjection interpretation = Left

  public export
  interpretAlgebraicFunctionRightInjection : {penv : PrimitiveEnv} ->
    {pfenv : PrimitiveFuncEnv penv} ->
    {typeInterpretation : PrimitiveTypeInterpretation penv} ->
    (functionInterpretation :
      PrimitiveFunctionInterpretation pfenv typeInterpretation) ->
    {codomainLeft : AlgebraicType penv} ->
    {codomainRight : AlgebraicType penv} ->
    interpretAlgebraicFunctionType typeInterpretation
      codomainRight (AlgebraicCoproduct codomainLeft codomainRight)
  interpretAlgebraicFunctionRightInjection interpretation = Right

-- This environment provides all metalanguage functions on the algebraic
-- closure of the primitive types.
public export
CompletePrimitiveFuncEnv : {penv : PrimitiveEnv} ->
  (typeInterpretation : PrimitiveTypeInterpretation penv) ->
  PrimitiveFuncEnv penv
CompletePrimitiveFuncEnv typeInterpretation =
  PrimFuncs (interpretAlgebraicFunctionType typeInterpretation)

public export
CompletePrimitiveFunctionInterpretation : {penv : PrimitiveEnv} ->
  (typeInterpretation : PrimitiveTypeInterpretation penv) ->
  PrimitiveFunctionInterpretation
    (CompletePrimitiveFuncEnv typeInterpretation) typeInterpretation
CompletePrimitiveFunctionInterpretation typeInterpretation =
  PrimitiveFunctionInterpretations id

public export
interpretAllMetaLanguageAlgebraicFunctions : {penv : PrimitiveEnv} ->
  (typeInterpretation : PrimitiveTypeInterpretation penv) ->
  {domain, codomain : AlgebraicType penv} ->
  AlgebraicFunction (CompletePrimitiveFuncEnv typeInterpretation)
    domain codomain ->
  interpretAlgebraicFunctionType typeInterpretation domain codomain
interpretAllMetaLanguageAlgebraicFunctions typeInterpretation f =
  interpretAlgebraicFunction
    (CompletePrimitiveFunctionInterpretation typeInterpretation) f
