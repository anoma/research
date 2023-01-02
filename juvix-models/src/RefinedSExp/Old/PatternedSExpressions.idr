module RefinedSExp.Old.PatternedSExpressions

import Decidable.Equality
import public Library.List
import public RefinedSExp.Old.AlgebraicPattern

%default total

mutual
  public export
  data Pattern : (primType : Type) -> Type where
    CarrierPat : Nat -> Pattern primType
    PrimPat : primType -> Pattern primType
    ProductPat : PatternList primType -> Pattern primType
    SumPat : PatternList primType -> Pattern primType

  public export
  PatternList : (primType : Type) -> Type
  PatternList = List . Pattern

public export
(#*) : {primType : Type} -> PatternList primType -> Pattern primType
(#*) {primType} = ProductPat

public export
(#|) : {primType : Type} -> PatternList primType -> Pattern primType
(#|) = SumPat

mutual
  patternEq : {primType : Type} -> DecEqPred primType ->
    (pattern, pattern' : Pattern primType) -> Dec (pattern = pattern')
  patternEq primEq (CarrierPat n) (CarrierPat n') =
    case decEq n n' of
      Yes Refl => Yes Refl
      No neq => No (\eq => case eq of Refl => neq Refl)
  patternEq primEq (CarrierPat _) (PrimPat _) =
    No (\eq => case eq of Refl impossible)
  patternEq primEq (CarrierPat _) (ProductPat _) =
    No (\eq => case eq of Refl impossible)
  patternEq primEq (CarrierPat _) (SumPat _) =
    No (\eq => case eq of Refl impossible)
  patternEq primEq (PrimPat _) (CarrierPat _) =
    No (\eq => case eq of Refl impossible)
  patternEq primEq (PrimPat type) (PrimPat type') =
    case primEq type type' of
      Yes Refl => Yes Refl
      No neq => No (\eq => case eq of Refl => neq Refl)
  patternEq primEq (PrimPat _) (ProductPat _) =
    No (\eq => case eq of Refl impossible)
  patternEq primEq (PrimPat _) (SumPat _) =
    No (\eq => case eq of Refl impossible)
  patternEq primEq (ProductPat _) (CarrierPat _) =
    No (\eq => case eq of Refl impossible)
  patternEq primEq (ProductPat _) (PrimPat _) =
    No (\eq => case eq of Refl impossible)
  patternEq primEq (ProductPat patternList) (ProductPat patternList') =
    case patternListEq primEq patternList patternList' of
      Yes Refl => Yes Refl
      No neq => No (\eq => case eq of Refl => neq Refl)
  patternEq primEq (ProductPat _) (SumPat _) =
    No (\eq => case eq of Refl impossible)
  patternEq primEq (SumPat _) (CarrierPat _) =
    No (\eq => case eq of Refl impossible)
  patternEq primEq (SumPat _) (PrimPat _) =
    No (\eq => case eq of Refl impossible)
  patternEq primEq (SumPat _) (ProductPat _) =
    No (\eq => case eq of Refl impossible)
  patternEq primEq (SumPat patternList) (SumPat patternList') =
    case patternListEq primEq patternList patternList' of
      Yes Refl => Yes Refl
      No neq => No (\eq => case eq of Refl => neq Refl)

  patternListEq : {primType : Type} -> DecEqPred primType ->
    (patternList, patternList' : PatternList primType) ->
    Dec (patternList = patternList')
  patternListEq primEq = listDecEq (patternEq primEq)

public export
Signature : (primType : Type) -> Type
Signature primType = (Pattern primType, Pattern primType)

mutual
  public export
  data Transform : (primType : Type) -> Type where
    IdTransform : Transform primType
    ConstructorTransform : TransformList primType -> Transform primType
    MatchTransform : TransformList primType -> Transform primType
    ComposeTransforms : TransformList primType -> Transform primType

  public export
  TransformList : (primType : Type) -> Type
  TransformList = List . Transform

  public export
  sigDomain : {primType : Type} ->
    (signature : Signature primType) -> Pattern primType
  sigDomain = fst

  public export
  sigCodomain : {primType : Type} ->
    (signature : Signature primType) -> Pattern primType
  sigCodomain = snd

  public export
  SignatureList : (primType : Type) -> Type
  SignatureList = List . Signature

  public export
  sigDomains : {primType : Type} ->
    SignatureList primType -> PatternList primType
  sigDomains l = map sigDomain l

  public export
  sigCodomains : {primType : Type} ->
    SignatureList primType -> PatternList primType
  sigCodomains l = map sigCodomain l

mutual
  public export
  data Transforms : {primType : Type} ->
      (domain, codomain : Pattern primType) -> Transform primType -> Type where
    IdTransforms : {pattern : Pattern primType} ->
      Transforms pattern pattern IdTransform
    ConstructorTransforms : {domain, codomain : Pattern primType} ->
      {transforms : TransformList primType} ->
      ListPairForAll (Transforms domain) codomains transforms ->
      Transforms domain (ProductPat codomains) (ConstructorTransform transforms)
    MatchTransforms : {domain : Pattern primType} ->
      {domains : PatternList primType} ->
      {transforms : TransformList primType} ->
      ListPairForAll (flip Transforms codomain) domains transforms ->
      Transforms (SumPat domains) codomain (MatchTransform transforms)
    ComposeTransformsEmptyId : {type : Pattern primType} ->
      Transforms type type (ComposeTransforms [])
    ComposeTransformsSingleton : {domain, codomain : Pattern primType} ->
      {transform : Transform primType} ->
      Transforms domain codomain transform ->
      Transforms domain codomain (ComposeTransforms [transform])
    ComposeTransformsMultiple :
      {domain, intermediate, codomain : Pattern primType} ->
      {transform : Transform primType} ->
      {transforms : TransformList primType} ->
      Transforms intermediate codomain transform ->
      Transforms domain intermediate (ComposeTransforms transforms) ->
      Transforms domain codomain (ComposeTransforms (transform :: transforms))

  public export
  HasSignature : {primType : Type} -> (signature : Signature primType) ->
    (transform : Transform primType) -> Type
  HasSignature (domain, codomain) = Transforms domain codomain

{-
mutual
  public export
  data MatchesExp : Pattern -> SExp -> Type where
    MatchesDefault : (sexp : SExp) -> MatchesExp CarrierPat sexp
    MatchesPrim : (primExp : PrimitiveExp) ->
      MatchesExp (PrimPat (fst primExp)) (SAtom primExp)
    MatchesProduct : {patternList : PatternList} -> {sexpList : SExpList} ->
      MatchesList patternList sexpList ->
      MatchesExp (ProductPat patternList) (SList sexpList)
    MatchesSum : {patternList : PatternList} -> {sexp : SExp} ->
      MatchesSome patternList sexp ->
      MatchesExp (SumPat patternList) sexp

  public export
  MatchesList : PatternList -> SExpList -> Type
  MatchesList = ListPairForAll MatchesExp

  public export
  MatchesSome : PatternList -> SExp -> Type
  MatchesSome = flip (ListExists . (flip MatchesExp))

public export
MatchedSExp : Pattern -> Type
MatchedSExp pattern = DPair SExp (MatchesExp pattern)

public export
MatchedSExpPred : Type -> Pattern -> Type
MatchedSExpPred codomain pattern =
  MatchedSExp pattern -> codomain

public export
MatchedList : PatternList -> Type
MatchedList patternList = DPair SExpList (MatchesList patternList)

public export
MatchedListPred : Type -> PatternList -> Type
MatchedListPred codomain patternList = (MatchedList patternList) -> codomain

public export
MatchedSExpPredList : Type -> PatternList -> Type
MatchedSExpPredList codomain patternList =
  ListForAll (MatchedSExpPred codomain) patternList

mutual
  matchesExp : (pattern : Pattern) -> (sexp : SExp) ->
    Dec (MatchesExp pattern sexp)
  matchesExp pattern sexp = ?matchesExp_hole

  matchesList : (patternList : PatternList) -> (sexpList : SExpList) ->
    Dec (MatchesList patternList sexpList)
  matchesList patternList sexpList = ?matchesList_hole

  matchesSome : (patternList : PatternList) -> (sexp : SExp) ->
    Dec (MatchesSome patternList sexp)
  matchesSome patternList sexp = ?matchesSome_hole

mutual
  data IsSubPattern : (sub, super : Pattern) -> Type where
    SubDefault : (sub : Pattern) -> IsSubPattern sub CarrierPat
    SubPrimitive : (primType : PrimitiveType) ->
      IsSubPattern (PrimPat primType) (PrimPat primType)
    SubProduct : (sub, super : PatternList) ->
      IsSubPatternList sub super ->
      IsSubPattern (ProductPat sub) (ProductPat super)
    SubSum : (sub, super : PatternList) ->
      IsSubPatternList sub super ->
      IsSubPattern (SumPat sub) (SumPat super)

  data IsSubPatternList : (sub, super : PatternList) -> Type where
    SubNil : IsSubPatternList [] []
    SubCons :
      {headSub : Pattern} -> {headSuper : Pattern} ->
      {tailSub : PatternList} -> {tailSuper : PatternList} ->
      IsSubPattern headSub headSuper ->
      IsSubPatternList tailSub tailSuper ->
      IsSubPatternList (headSub :: tailSub) (headSuper :: tailSuper)

mutual
  isSubPattern :
    (sub, super : Pattern) -> Dec (IsSubPattern sub super)
  isSubPattern sub super = ?isSubPattern_hole

  isSubPatternList :
    (sub, super : PatternList) -> Dec (IsSubPatternList sub super)
  isSubPatternList sub super = ?isSubPatternList_hole

mutual
  subPatternReflexive :
    (pattern : Pattern) -> IsSubPattern pattern pattern
  subPatternReflexive = ?subPatternReflexive_hole

  subPatternListReflexive :
    (patternList : PatternList) -> IsSubPatternList patternList patternList
  subPatternListReflexive = ?subPatternListReflexive_hole

mutual
  subPatternTransitive :
    {patternA, patternB, patternC : Pattern} ->
    IsSubPattern patternA patternB ->
    IsSubPattern patternB patternC ->
    IsSubPattern patternA patternC
  subPatternTransitive subAB subBC = ?subPatternTransitive_hole

  subPatternListTransitive :
    {patternListA, patternListB, patternListC : PatternList} ->
    IsSubPatternList patternListA patternListB ->
    IsSubPatternList patternB patternC ->
    IsSubPatternList patternListA patternListC
  subPatternListTransitive subAB subBC = ?subPatternListTransitive_hole

mutual
  patternMatchTransitive :
    {sub, super : Pattern} ->
    IsSubPattern sub super ->
    {sexp : SExp} ->
    MatchesExp sub sexp ->
    MatchesExp super sexp
  patternMatchTransitive isSub matches = ?patternMatchTransitive_hole

  patternMatchProductTransitive :
    {sub, super : PatternList} ->
    IsSubPatternList sub super ->
    {sexp : SExp} ->
    MatchesExp (ProductPat sub) sexp ->
    MatchesExp (ProductPat super) sexp
  patternMatchProductTransitive isSub matches =
    ?patternMatchProductTransitive_hole

  patternMatchSumTransitive :
    {sub, super : PatternList} ->
    IsSubPatternList sub super ->
    {sexp : SExp} ->
    MatchesExp (SumPat sub) sexp ->
    MatchesExp (SumPat super) sexp
  patternMatchSumTransitive isSub matches =
    ?patternMatchSumTransitive_hole

public export
CaseStatement : (domain : Pattern) -> (codomain : Type) -> Type
CaseStatement CarrierPat codomain =
  SExp -> codomain
CaseStatement (PrimPat primitiveType) codomain =
  interpretPrimitiveType primitiveType -> codomain
CaseStatement (ProductPat patternList) codomain =
  MatchedListPred codomain patternList
CaseStatement (SumPat patternList) codomain =
  MatchedSExpPredList codomain patternList

export
match : {domain : Pattern} -> {codomain : Type} ->
  CaseStatement domain codomain ->
  MatchedSExp domain -> codomain
match caseStatement (_ ** matchesDomain) = case matchesDomain of
  MatchesDefault sexp =>
    caseStatement sexp
  MatchesPrim (_ ** primExp) =>
    caseStatement primExp
  MatchesProduct {sexpList} matchesList =>
    caseStatement (sexpList ** matchesList)
  MatchesSum {sexp} {patternList} matchesList =>
    let matchedPattern = snd (listExistsGet matchesList caseStatement) in
    snd matchedPattern (sexp ** fst matchedPattern)

public export
Transformer : (domain, codomain : Pattern) -> Type
Transformer domain codomain = CaseStatement domain (MatchedSExp codomain)

export
transform : {domain, codomain : Pattern} ->
  Transformer domain codomain ->
  MatchedSExp domain -> MatchedSExp codomain
transform = match {domain} {codomain=(MatchedSExp codomain)}
-}

-- Provide a "default" primitive type.

public export
data PrimitiveType : Type where
  PrimTypeBool : PrimitiveType
  PrimTypeNat : PrimitiveType
  PrimTypeString : PrimitiveType

-- Haskell can just derive this.
export
primTypeEq : (primType, primType' : PrimitiveType) -> Dec (primType = primType')
primTypeEq PrimTypeBool PrimTypeBool = Yes Refl
primTypeEq PrimTypeBool PrimTypeNat = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeBool PrimTypeString = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeNat PrimTypeBool = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeNat PrimTypeNat = Yes Refl
primTypeEq PrimTypeNat PrimTypeString = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeString PrimTypeBool = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeString PrimTypeNat = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeString PrimTypeString = Yes Refl

interpretPrimitiveType : PrimitiveType -> Type
interpretPrimitiveType PrimTypeBool = Bool
interpretPrimitiveType PrimTypeNat = Nat
interpretPrimitiveType PrimTypeString = String

public export
primitiveEq : (primType : PrimitiveType) ->
  (x, x' : interpretPrimitiveType primType) -> Dec (x = x')
primitiveEq PrimTypeBool = decEq
primitiveEq PrimTypeNat = decEq
primitiveEq PrimTypeString = decEq

public export
PrimitiveExp : Type
PrimitiveExp = DPair PrimitiveType interpretPrimitiveType

primExpEq : (primExp, primExp' : PrimitiveExp) -> Dec (primExp = primExp')
primExpEq (primType ** primExp) (primType' ** primExp') with
  (primTypeEq primType primType')
    primExpEq (primType ** primExp) (primType ** primExp') | Yes Refl =
      case primitiveEq primType primExp primExp' of
        Yes Refl => Yes Refl
        No neq => No (\eq => case eq of Refl => neq Refl)
    primExpEq (primType ** primExp) (primType' ** primExp') | No neq =
      No (\eq => case eq of Refl => neq Refl)

public export
BoolPat : Pattern PrimitiveType
BoolPat = PrimPat PrimTypeBool

public export
NatPat : Pattern PrimitiveType
NatPat = PrimPat PrimTypeNat

public export
StringPat : Pattern PrimitiveType
StringPat = PrimPat PrimTypeString
