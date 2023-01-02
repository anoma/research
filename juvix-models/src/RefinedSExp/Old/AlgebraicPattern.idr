module RefinedSExp.Old.AlgebraicPattern

import public Data.Nat
import public RefinedSExp.Old.OldRefinedSExp
import public Library.List

%default total

mutual
  prefix 11 |->
  public export
  data ConstructorParam : (primitive : Type) -> Type where
    (|->) : DataType primitive -> ConstructorParam primitive

  prefix 11 |-
  public export
  data TypeConstructor : (primitive : Type) -> Type where
    (|-) : {primitive : Type} -> List (ConstructorParam primitive) ->
      TypeConstructor primitive

  prefix 11 |-#
  public export
  (|-#) : {primitive : Type} -> TypeConstructor primitive -> Nat
  (|-#) = length . typeParams

  prefix 11 |*
  public export
  data ADT : (primitive : Type) -> Type where
    (|*) : {primitive : Type} -> List (TypeConstructor primitive) ->
      ADT primitive

  prefix 11 |*#
  public export
  (|*#) : {primitive : Type} -> ADT primitive -> Nat
  (|*#) = length . constructors

  prefix 11 |.
  prefix 11 |:
  public export
  data DataType : (primitive : Type) -> Type where
    (|.) : primitive -> DataType primitive
    (|:) : ADT primitive -> DataType primitive

  prefix 11 |:*
  public export
  (|:*) : {primitive : Type} -> List (TypeConstructor primitive) ->
    DataType primitive
  (|:*) = (|:) . (|*)

  public export
  typeParams : {primitive : Type} -> TypeConstructor primitive ->
    List (ConstructorParam primitive)
  typeParams (|- l) = l

  infixr 7 |-<
  public export
  (|-<) : {primitive : Type} -> (tc : TypeConstructor primitive) -> (n : Nat) ->
    {auto ok : InBounds n (typeParams tc)} -> ConstructorParam primitive
  tc |-< n = index n (typeParams tc)

  public export
  constructors : {primitive : Type} -> (adt : ADT primitive) ->
    List (TypeConstructor primitive)
  constructors (|* l) = l

  infixr 7 |*<
  public export
  (|*<) : {primitive : Type} -> (adt : ADT primitive) -> (n : Nat) ->
    {auto ok : InBounds n (constructors adt)} -> TypeConstructor primitive
  adt |*< n = index n (constructors adt)

mutual
  public export
  decEqParam : {primitive : Type} -> (decEqPrim : DecEqPred primitive) ->
    DecEqPred (ConstructorParam primitive)
  decEqParam decEqPrim (|-> d) (|-> d') = case decEqDataType decEqPrim d d' of
    Yes Refl => Yes Refl
    No neq => No (\eq => case eq of Refl => neq Refl)

  public export
  decEqConstructor : {primitive : Type} -> (decEqPrim : DecEqPred primitive) ->
    DecEqPred (TypeConstructor primitive)
  decEqConstructor decEqPrim (|- l) (|- l') =
    case listDecEq (decEqParam decEqPrim) l l' of
      Yes Refl => Yes Refl
      No neq => No (\eq => case eq of Refl => neq Refl)

  public export
  decEqADT : {primitive : Type} -> (decEqPrim : DecEqPred primitive) ->
    DecEqPred (ADT primitive)
  decEqADT decEqPrim (|* l) (|* l') =
    case listDecEq (decEqConstructor decEqPrim) l l' of
      Yes Refl => Yes Refl
      No neq => No (\eq => case eq of Refl => neq Refl)

  public export
  decEqDataType : {primitive : Type} -> (decEqPrim : DecEqPred primitive) ->
    DecEqPred (DataType primitive)
  decEqDataType decEqPrim (|. p) (|. p') = case decEqPrim p p' of
    Yes Refl => Yes Refl
    No neq => No (\eq => case eq of Refl => neq Refl)
  decEqDataType decEqPrim (|. p) (|: adt) =
    No (\eq => case eq of Refl impossible)
  decEqDataType decEqPrim (|: adt) (|. p) =
    No (\eq => case eq of Refl impossible)
  decEqDataType decEqPrim (|: adt) (|: adt') =
    case decEqADT decEqPrim adt adt' of
      Yes Refl => Yes Refl
      No neq => No (\eq => case eq of Refl => neq Refl)

prefix 11 |**
public export
data TypeFamily : (primitive : Type) -> Type where
  (|**) : {primitive : Type} -> List (ADT primitive) -> TypeFamily primitive

public export
familyTypes : {primitive : Type} -> (family : TypeFamily primitive) ->
  List (ADT primitive)
familyTypes (|** l) = l

prefix 11 |**#
public export
(|**#) : {primitive : Type} -> TypeFamily primitive -> Nat
(|**#) = length . familyTypes

infixr 7 |**<
public export
(|**<) : {primitive : Type} -> (family : TypeFamily primitive) -> (n : Nat) ->
  {auto ok : InBounds n (familyTypes family)} -> ADT primitive
family |**< n = index n (familyTypes family)

public export
decEqFamily : {primitive : Type} -> (decEqPrim : DecEqPred primitive) ->
  DecEqPred (TypeFamily primitive)
decEqFamily decEqPrim (|** l) (|** l') =
  case listDecEq (decEqADT decEqPrim) l l' of
    Yes Refl => Yes Refl
    No neq => No (\eq => case eq of Refl => neq Refl)

mutual
  -- Atoms of matchable S-expressions.
  public export
  data MAtom : {primType : Type} -> (primExp : primType -> Type) -> Type where
    MPrim : {primType : Type} -> {primExp : primType -> Type} ->
      {type : primType} -> primExp type -> MAtom primExp
    MAbst : {primType : Type} -> {primExp : primType -> Type} ->
      (adt : ADT primType) -> (constructorIndex : Nat) -> MAtom primExp

  public export
  MAtomType : {primType : Type} -> {primExp : primType -> Type} ->
    MAtom primExp -> DataType primType
  MAtomType (MPrim {type} _) = |. type
  MAtomType (MAbst adt _) = |: adt

  public export
  data MatchesType : {primType : Type} -> {primExp : primType -> Type} ->
      DataType primType -> SExp (MAtom primExp) -> Type where
    MatchesPrimType : {primType : Type} -> {primExp : primType -> Type} ->
      {type : primType} -> (p : primExp type) ->
      MatchesType (|. type) ($^ (MPrim {type} {primExp} p))
    MatchesAbstractType : {primType : Type} -> {primExp : primType -> Type} ->
      (adt : ADT primType) -> (constructorIndex : Nat) ->
      (constructorParams : SList (MAtom primExp)) ->
      {auto ok : InBounds constructorIndex (constructors adt)} ->
      MatchesParams
        adt (typeParams (adt |*< constructorIndex)) constructorParams ->
      MatchesType (|: adt) (MAbst adt constructorIndex $: constructorParams)

  public export
  data MatchesParams : {primType : Type} -> {primExp : primType -> Type} ->
      ADT primType -> List (ConstructorParam primType) ->
      SList (MAtom primExp) -> Type where
    MatchesParamsEmpty : {primType : Type} -> {primExp : primType -> Type} ->
      {adt : ADT primType} ->
      MatchesParams {primType} {primExp} adt [] ($|)
    MatchesParamsCons : {primType : Type} -> {primExp : primType -> Type} ->
      {adt : ADT primType} ->
      {param : ConstructorParam primType} ->
      {params : List (ConstructorParam primType)} ->
      {x : SExp (MAtom primExp)} -> {l : SList (MAtom primExp)} ->
      MatchesParam adt param x ->
      MatchesParams adt params l ->
      MatchesParams {primType} {primExp} adt (param :: params) (x $+ l)

  public export
  data MatchesParam : {primType : Type} -> {primExp : primType -> Type} ->
      ADT primType -> ConstructorParam primType ->
      SExp (MAtom primExp) -> Type where
    MatchesDataType : {primType : Type} -> {primExp : primType -> Type} ->
      {adt : ADT primType} ->
      {type : DataType primType} -> {x : SExp (MAtom primExp)} ->
      MatchesType type x -> MatchesParam adt (|-> type) x

  public export
  MatchesSignature : {primType : Type} -> {primExp : primType -> Type} ->
    SExp (MAtom primExp) -> Type
  MatchesSignature (a $: l) = MatchesType (MAtomType a) (a $: l)

  public export
  data MatchFailure : {primType : Type} -> {primExp : primType -> Type} ->
      SExp (MAtom primExp) -> Type where
    PrimitiveWithArgument : {primType : Type} ->
      {primExp : primType -> Type} ->
      {x : SExp (MAtom primExp)} ->
      (firstArg : SExp (MAtom primExp)) ->
      (anyOtherArgs : SList (MAtom primExp)) ->
      MatchFailure {primExp} x
    InvalidConstructorIndex : {primType : Type} ->
      {primExp : primType -> Type} -> {x : SExp (MAtom primExp)} ->
      (adt : ADT primType) -> Nat -> MatchFailure {primExp} x
    ExtraConstructorParameters : {primType : Type} ->
      {primExp : primType -> Type} -> {x : SExp (MAtom primExp)} ->
      (adt : ADT primType) -> (constructorIndex : Nat) ->
      (extraParameters : SList (MAtom primExp)) ->
      MatchFailure {primExp} x
    MissingConstructorParameters : {primType : Type} ->
      {primExp : primType -> Type} -> {x : SExp (MAtom primExp)} ->
      (adt : ADT primType) -> (constructorIndex : Nat) ->
      (missingParameters : List (ConstructorParam primType)) ->
      MatchFailure {primExp} x
    TypeMismatch : {primType : Type} ->
      {primExp : primType -> Type} -> {x : SExp (MAtom primExp)} ->
      (type, type' : DataType primType) ->
      MatchFailure {primExp} x

  public export
  MatchesTypePred : {primType : Type} -> (primExp : primType -> Type) ->
    DecidablePredicate (MAtom primExp)
  MatchesTypePred {primType} primExp =
    ResultPredicates (MatchesSignature {primExp}) (MatchFailure {primExp})

mutual
  public export
  CheckOneMatch : {primType : Type} ->
    {decEqPrim : DecEqPred primType} ->
    {primExp : primType -> Type} ->
    (a : MAtom primExp) -> (l : SList (MAtom primExp)) ->
    SLForAll (MatchesSignature {primExp}) l ->
    DecisionResult (MatchesTypePred primExp) (a $: l)
  CheckOneMatch (MPrim p) ($|) _ =
    DecisionSuccess (MatchesPrimType p)
  CheckOneMatch (MPrim p) (x $+ l) _ =
    DecisionFailure (PrimitiveWithArgument x l)
  CheckOneMatch (MAbst adt constructorIndex) l forAll =
    case inBounds constructorIndex (constructors adt) of
      Yes ok =>
        case CheckOneParameterList {decEqPrim} adt constructorIndex
          (MAbst adt constructorIndex $: l)
          (typeParams (adt |*< constructorIndex)) l forAll of
            Left matchesParams =>
              DecisionSuccess
                (MatchesAbstractType adt constructorIndex l matchesParams)
            Right failure => DecisionFailure failure
      No outOfBounds =>
        DecisionFailure (InvalidConstructorIndex adt constructorIndex)

  public export
  CheckOneParameterList : {primType : Type} ->
    {decEqPrim : DecEqPred primType} ->
    {primExp : primType -> Type} ->
    (adt : ADT primType) ->
    (constructorIndex : Nat) ->
    (originalSExp : SExp (MAtom primExp)) ->
    (params : List (ConstructorParam primType)) ->
    (l : SList (MAtom primExp)) ->
    SLForAll (MatchesSignature {primExp}) l ->
    Either
      (MatchesParams adt params l)
      (MatchFailure originalSExp)
  CheckOneParameterList adt constructorIndex originalSExp [] ($|) forAll =
    Left MatchesParamsEmpty
  CheckOneParameterList adt constructorIndex originalSExp [] (x $+ l) forAll =
    Right (ExtraConstructorParameters adt constructorIndex (x $+ l))
  CheckOneParameterList adt constructorIndex originalSExp
    (p :: ps) ($|) forAll =
      Right (MissingConstructorParameters adt constructorIndex (p :: ps))
  CheckOneParameterList adt constructorIndex originalSExp (p :: ps) (x $+ l)
    SLForAllEmpty impossible
  CheckOneParameterList {decEqPrim} adt constructorIndex originalSExp
    (p :: ps) (x $+ l) (SLForAllCons head forAllTail) =
      case CheckOneParameterList {decEqPrim} adt constructorIndex originalSExp
        ps l forAllTail of
          Left tailChecks => case p of
            (|->) type => case x of
              (a $: l) => case decEqDataType decEqPrim type (MAtomType a) of
                Yes Refl =>
                  Left (MatchesParamsCons (MatchesDataType head) tailChecks)
                No _ => Right (TypeMismatch {x=originalSExp} type (MAtomType a))
          Right tailFails => Right tailFails

  public export
  MatchesTypeInduction : {primType : Type} ->
    (decEqPrim : DecEqPred primType) ->
    (primExp : primType -> Type) ->
    InductiveTypecheck (MatchesTypePred primExp)
  MatchesTypeInduction decEqPrim primExp =
    MkInductiveTypecheck
      (CheckOneMatch {decEqPrim} {primExp})
      (List (DPair (SExp (MAtom primExp)) MatchFailure))
      (\x, fail => [ (x ** fail) ])
      (++)

public export
match : {primType : Type} -> (decEqPrim : DecEqPred primType) ->
  (primExp : primType -> Type) ->
  ((x : SExp (MAtom primExp)) ->
    CheckResult (MatchesTypeInduction decEqPrim primExp) x,
   (l : SList (MAtom primExp)) ->
    ListCheckResult (MatchesTypeInduction decEqPrim primExp) l)
match decEqPrim primExp = typecheck (MatchesTypeInduction decEqPrim primExp)

public export
matchSExp : {primType : Type} -> (decEqPrim : DecEqPred primType) ->
  (primExp : primType -> Type) ->
  (x : SExp (MAtom primExp)) ->
  CheckResult (MatchesTypeInduction decEqPrim primExp) x
matchSExp decEqPrim primExp = fst (match decEqPrim primExp)

public export
matchSList : {primType : Type} -> (decEqPrim : DecEqPred primType) ->
  (primExp : primType -> Type) ->
  (l : SList (MAtom primExp)) ->
  ListCheckResult (MatchesTypeInduction decEqPrim primExp) l
matchSList decEqPrim primExp = snd (match decEqPrim primExp)
