module OldSExp.SExpressionsWithFiniteAtomTypes

import public OldSExp.SExpressions
import public Library.FiniteTypes
import Library.Decidability

%default total

public export
SExprFin : Nat -> Type
SExprFin n = SExpr (Fin n)

export
SExprFinDecEq : {n: Nat} -> DecEqPred (SExprFin n)
SExprFinDecEq (SAtom fin) e' =
  case e' of
    (SAtom fin') => case decEq fin fin' of
      Yes Refl => Yes Refl
      No neq => No (\satomEq => case satomEq of Refl => neq Refl)
    (SPair eSecond eSecond') => No (\eq => case eq of Refl impossible)
SExprFinDecEq (SPair eFirst eSecond) e' =
  case e' of
    (SAtom fin') => No (\eq => case eq of Refl impossible)
    (SPair e'First e'Second) => case SExprFinDecEq eFirst e'First of
      Yes Refl => case SExprFinDecEq eSecond e'Second of
        Yes Refl => Yes Refl
        No neq => No (\eq => case eq of Refl => neq Refl)
      No neq => No (\eq => case eq of Refl => neq Refl)

SExprFinMap : Nat -> Type
SExprFinMap n = SExprFin n -> SExprFin n

finMapToSExprMap : {n: Nat} -> FinMap n -> SExprFinMap n
finMapToSExprMap = sexprMapAtom

sexprMapSym : {n: Nat} -> VectFin n -> SExprFinMap n
sexprMapSym vf s = finMapToSExprMap (vectFinMap vf) s

export
SExprFinPred : Nat -> Type
SExprFinPred n = SExprFin n -> Type

SatisfiesPredWitness : {n: Nat} -> SExprFinPred n -> SExprFin n -> Type
SatisfiesPredWitness pred sexpr = pred sexpr

PredImplies : {n: Nat} -> SExprFinPred n -> SExprFinPred n -> Type
PredImplies antecedent consequent = (s: SExprFin n) ->
  SatisfiesPredWitness antecedent s -> SatisfiesPredWitness consequent s

PredsEquiv : {n: Nat} -> SExprFinPred n -> SExprFinPred n -> Type
PredsEquiv pred pred' = (PredImplies pred pred', PredImplies pred' pred)

SExprWhoseImageSatisfiesPred :
  {n: Nat} -> FinMap n -> SExprFinPred n -> SExprFinPred n
SExprWhoseImageSatisfiesPred finmap pred sexpr =
  SatisfiesPredWitness pred (sexprMapAtom finmap sexpr)

ImageOfSExprWhichSatisfiesPred :
  {n: Nat} -> FinMap n -> SExprFinPred n -> SExprFinPred n
ImageOfSExprWhichSatisfiesPred finmap pred sexpr =
  (preimage : SExprFin n **
            (sexprMapAtom finmap preimage = sexpr,
             SatisfiesPredWitness pred preimage))

PredIsInsensitiveToMap : {n: Nat} -> FinMap n -> SExprFinPred n -> Type
PredIsInsensitiveToMap finmap pred =
  PredsEquiv
    (SExprWhoseImageSatisfiesPred finmap pred)
    (ImageOfSExprWhichSatisfiesPred finmap pred)

export
PredIsInsensitiveToAnyPermutation : {n: Nat} -> SExprFinPred n -> Type
PredIsInsensitiveToAnyPermutation pred =
  (vf: VectFin n) -> IsPermutation vf ->
    PredIsInsensitiveToMap (vectFinMap vf) pred

export
SExprFinTest : Nat -> Type
SExprFinTest n = SExprFin n -> Bool

SExprFinTestCaseDec : {n: Nat} ->
  (test: SExprFinTest n) -> (expression: SExprFin n) ->
    BoolCaseDec (test expression)
SExprFinTestCaseDec test expression = caseDecFromBool (test expression)

SatisfiesTest : {n: Nat} -> SExprFinTest n -> SExprFinPred n
SatisfiesTest test sexpr = test sexpr = True

export
SExprFinTestToPred : {n: Nat} -> SExprFinTest n -> SExprFinPred n
SExprFinTestToPred test s = So (test s)

TestsEquiv : {n: Nat} -> SExprFinTest n -> SExprFinTest n -> Type
TestsEquiv test test' =
  PredsEquiv (SExprFinTestToPred test) (SExprFinTestToPred test')

public export
TestIsInsensitiveToAnyPermutation : {n: Nat} -> SExprFinTest n -> Type
TestIsInsensitiveToAnyPermutation test =
  PredIsInsensitiveToAnyPermutation (SExprFinTestToPred test)
