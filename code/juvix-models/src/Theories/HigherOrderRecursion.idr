module Theories.HigherOrderRecursion

import Library.FunctionsAndRelations
import public Theories.InductiveTypeTheory
import public Theories.DependentInductiveTypeTheory

%default total

public export
data HigherOrderType : (penv : PrimitiveEnv) -> Type where
  HigherOrderPrimitiveType : AlgebraicType penv -> HigherOrderType penv
  HigherOrderNat : HigherOrderType penv

public export
HigherOrderPrimEnv : PrimitiveEnv -> PrimitiveEnv
HigherOrderPrimEnv = PrimArgs . HigherOrderType

public export
HigherOrderAlgebraicType : PrimitiveEnv -> Type
HigherOrderAlgebraicType = AlgebraicType . HigherOrderPrimEnv

public export
HigherOrderPrimitiveAlgebraicType : {penv : PrimitiveEnv} ->
  AlgebraicType penv -> HigherOrderAlgebraicType penv
HigherOrderPrimitiveAlgebraicType =
  AlgebraicTypeGenerator . HigherOrderPrimitiveType

public export
AlgebraicNat : {penv : PrimitiveEnv} -> HigherOrderAlgebraicType penv
AlgebraicNat {penv} = AlgebraicTypeGenerator (HigherOrderNat {penv})

public export
HigherOrderRecursorFunction : {penv : PrimitiveEnv} ->
  HigherOrderAlgebraicType penv -> HigherOrderAlgebraicType penv
HigherOrderRecursorFunction type =
  AlgebraicExponential (AlgebraicProduct AlgebraicNat type) type

public export
HigherOrderRecursorDomain : {penv : PrimitiveEnv} ->
  HigherOrderAlgebraicType penv -> HigherOrderAlgebraicType penv
HigherOrderRecursorDomain type =
  (AlgebraicListProduct [type, HigherOrderRecursorFunction type, AlgebraicNat])

public export
data HigherOrderFunction :
  {penv : PrimitiveEnv} ->
  (pfenv : PrimitiveFuncEnv penv) ->
  HigherOrderAlgebraicType penv ->
  HigherOrderAlgebraicType penv ->
  Type where
    HigherOrderPrimitiveFunction : {penv : PrimitiveEnv} ->
      (pfenv : PrimitiveFuncEnv penv) ->
      {domain, codomain : AlgebraicType penv} ->
      PrimFuncType pfenv domain codomain ->
      HigherOrderFunction pfenv
        (HigherOrderPrimitiveAlgebraicType domain)
        (HigherOrderPrimitiveAlgebraicType codomain)
    HigherOrderRecursor : (type : HigherOrderAlgebraicType penv) ->
      HigherOrderFunction pfenv (HigherOrderRecursorDomain type) type

public export
HigherOrderPrimFuncEnv : (penv : PrimitiveEnv) -> Type
HigherOrderPrimFuncEnv = PrimitiveFuncEnv . HigherOrderPrimEnv

public export
HigherOrderFuncEnv : {penv : PrimitiveEnv} ->
  PrimitiveFuncEnv penv -> HigherOrderPrimFuncEnv penv
HigherOrderFuncEnv = PrimFuncs . HigherOrderFunction

public export
HigherOrderPrimitiveTypeInterpretation : PrimitiveEnv -> Type
HigherOrderPrimitiveTypeInterpretation =
  PrimitiveTypeInterpretation . HigherOrderPrimEnv

public export
interpretHigherOrderPrimitiveType :
  {penv : PrimitiveEnv} ->
  (primInterpretation : PrimitiveTypeInterpretation penv) ->
  HigherOrderType penv ->
  Type
interpretHigherOrderPrimitiveType interpretation
  (HigherOrderPrimitiveType type) = interpretAlgebraicType interpretation type
interpretHigherOrderPrimitiveType _
  HigherOrderNat = Nat

public export
HigherOrderTypeInterpretation : {penv : PrimitiveEnv} ->
  PrimitiveTypeInterpretation penv ->
  HigherOrderPrimitiveTypeInterpretation penv
HigherOrderTypeInterpretation interpretation =
  PrimitiveTypeInterpretations
    (interpretHigherOrderPrimitiveType interpretation)

public export
higherOrderRecursion :
  {penv : PrimitiveEnv} -> {pfenv : PrimitiveFuncEnv penv} ->
  {typeInterpretation :
    PrimitiveTypeInterpretation penv} ->
  (functionInterpretation :
    PrimitiveFunctionInterpretation pfenv typeInterpretation) ->
  {type : HigherOrderAlgebraicType penv} ->
  interpretAlgebraicType
    (HigherOrderTypeInterpretation typeInterpretation) type ->
  interpretAlgebraicType
    (HigherOrderTypeInterpretation typeInterpretation)
    (HigherOrderRecursorFunction type) ->
  Nat ->
  interpretAlgebraicType (HigherOrderTypeInterpretation typeInterpretation) type
higherOrderRecursion functionInterpretation initial step Z =
  initial
higherOrderRecursion functionInterpretation initial step (S n) =
  higherOrderRecursion functionInterpretation (step (n, initial)) step n

public export
interpretHigherOrderRecursor :
  {penv : PrimitiveEnv} -> {pfenv : PrimitiveFuncEnv penv} ->
  {typeInterpretation :
    PrimitiveTypeInterpretation penv} ->
  (functionInterpretation :
    PrimitiveFunctionInterpretation pfenv typeInterpretation) ->
  {type : HigherOrderAlgebraicType penv} ->
  (recursorArgs : interpretAlgebraicType
    (HigherOrderTypeInterpretation typeInterpretation)
    (HigherOrderRecursorDomain type)) ->
  interpretAlgebraicType (HigherOrderTypeInterpretation typeInterpretation) type
interpretHigherOrderRecursor functionInterpretation (initial, step, n, ()) =
  higherOrderRecursion functionInterpretation initial step n

public export
interpretHigherOrderFunction :
  {penv : PrimitiveEnv} -> {pfenv : PrimitiveFuncEnv penv} ->
  {typeInterpretation : PrimitiveTypeInterpretation penv} ->
  (functionInterpretation :
    PrimitiveFunctionInterpretation pfenv typeInterpretation) ->
  {domain, codomain : HigherOrderAlgebraicType penv} ->
  HigherOrderFunction pfenv domain codomain ->
  interpretAlgebraicFunctionType
    (HigherOrderTypeInterpretation typeInterpretation) domain codomain
interpretHigherOrderFunction functionInterpretation
  (HigherOrderPrimitiveFunction pfenv f) =
    interpretPrimitiveFunction functionInterpretation f
interpretHigherOrderFunction functionInterpretation
  (HigherOrderRecursor type) =
    interpretHigherOrderRecursor functionInterpretation {type}

public export
HigherOrderFuncInterpretation :
  {penv : PrimitiveEnv} ->
  {pfenv : PrimitiveFuncEnv penv} ->
  {typeInterpretation :
    PrimitiveTypeInterpretation penv} ->
  (functionInterpretation :
    PrimitiveFunctionInterpretation pfenv typeInterpretation) ->
  PrimitiveFunctionInterpretation
    {penv=(HigherOrderPrimEnv penv)}
    (HigherOrderFuncEnv pfenv)
    (HigherOrderTypeInterpretation typeInterpretation)
HigherOrderFuncInterpretation =
  PrimitiveFunctionInterpretations . interpretHigherOrderFunction
