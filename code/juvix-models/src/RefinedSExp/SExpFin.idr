module RefinedSExp.SExpFin

import public Datatypes.DependentAlgebraicTypes
import public Library.FiniteTypes
import Library.Decidability

%default total

public export
SExpFin : Nat -> Type
SExpFin n = SExp (Fin n)

public export
SListFin : Nat -> Type
SListFin n = SList (Fin n)

export
SExpFinDecEqs : {n: Nat} -> (DecEqPred (SExpFin n), DecEqPred (SListFin n))
SExpFinDecEqs =
  sexpPairEliminators
    (SExpPairEliminatorArgs
      (\a, a' => case decEq a a' of
        Yes Refl => Yes Refl
        No neq => No (\eq => case eq of Refl => neq Refl))
      (\_, _ => No (\eq => case eq of Refl impossible))
      (\_, _ => No (\eq => case eq of Refl impossible))
      (\_, _, leq => case leq of
        Yes Refl => Yes Refl
        No neq => No (\eq => case eq of Refl => neq Refl))
      (Yes Refl)
      (\_, _ => No (\eq => case eq of Refl impossible))
      (\_, _ => No (\eq => case eq of Refl impossible))
      (\_, _, _, _, xeq, leq => case (xeq, leq) of
        (Yes Refl, Yes Refl) => Yes Refl
        (_, No neq) => No (\eq => case eq of Refl => neq Refl)
        (No neq, _) => No (\eq => case eq of Refl => neq Refl))
    )

public export
SExpFinDecEq : {n: Nat} -> DecEqPred (SExpFin n)
SExpFinDecEq = fst SExpFinDecEqs

public export
SListFinDecEq : {n: Nat} -> DecEqPred (SListFin n)
SListFinDecEq = snd SExpFinDecEqs

public export
SExpFinMap : Nat -> Type
SExpFinMap n = SExpFin n -> SExpFin n

public export
finMapToSExpMap : {n: Nat} -> FinMap n -> SExpFinMap n
finMapToSExpMap = sexpMap

public export
sexpMapVect : {n: Nat} -> VectFin n -> SExpFinMap n
sexpMapVect = finMapToSExpMap . vectFinMap

public export
SExpFinPred : Nat -> Type
SExpFinPred n = SExpFin n -> Type

public export
PredImplies : {n: Nat} -> SExpFinPred n -> SExpFinPred n -> Type
PredImplies antecedent consequent =
  (s: SExpFin n) -> antecedent s -> consequent s

public export
PredsEquiv : {n: Nat} -> SExpFinPred n -> SExpFinPred n -> Type
PredsEquiv pred pred' = (PredImplies pred pred', PredImplies pred' pred)

public export
SExpWhoseImageSatisfiesPred :
  {n: Nat} -> FinMap n -> SExpFinPred n -> SExpFinPred n
SExpWhoseImageSatisfiesPred finmap pred sexp = pred (sexpMap finmap sexp)

public export
ImageOfSExpWhichSatisfiesPred :
  {n: Nat} -> FinMap n -> SExpFinPred n -> SExpFinPred n
ImageOfSExpWhichSatisfiesPred finmap pred sexp =
  (preimage : SExpFin n ** (sexpMap finmap preimage = sexp, pred preimage))

public export
PredIsInsensitiveToMap : {n: Nat} -> FinMap n -> SExpFinPred n -> Type
PredIsInsensitiveToMap finmap pred =
  PredsEquiv
    (SExpWhoseImageSatisfiesPred finmap pred)
    (ImageOfSExpWhichSatisfiesPred finmap pred)

public export
PredIsInsensitiveToAnyPermutation : {n: Nat} -> SExpFinPred n -> Type
PredIsInsensitiveToAnyPermutation pred =
  (vf: VectFin n) -> IsPermutation vf ->
    PredIsInsensitiveToMap (vectFinMap vf) pred

public export
SExpFinTest : Nat -> Type
SExpFinTest n = SExpFin n -> Bool

public export
SExpFinTestCaseDec : {n: Nat} ->
  (test: SExpFinTest n) -> (expession: SExpFin n) ->
    BoolCaseDec (test expession)
SExpFinTestCaseDec test expession = caseDecFromBool (test expession)

public export
SatisfiesTest : {n: Nat} -> SExpFinTest n -> SExpFinPred n
SatisfiesTest test sexp = test sexp = True

public export
SExpFinTestToPred : {n: Nat} -> SExpFinTest n -> SExpFinPred n
SExpFinTestToPred test s = So (test s)

public export
TestsEquiv : {n: Nat} -> SExpFinTest n -> SExpFinTest n -> Type
TestsEquiv test test' =
  PredsEquiv (SExpFinTestToPred test) (SExpFinTestToPred test')

public export
TestIsInsensitiveToAnyPermutation : {n: Nat} -> SExpFinTest n -> Type
TestIsInsensitiveToAnyPermutation test =
  PredIsInsensitiveToAnyPermutation (SExpFinTestToPred test)
