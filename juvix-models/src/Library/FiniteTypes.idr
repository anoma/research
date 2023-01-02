module Library.FiniteTypes

import public Data.Fin
import public Data.So
import public Data.Vect
import Library.FunctionsAndRelations
import Library.Decidability

%default total

FinZAbsurd : Fin 0 -> Void
FinZAbsurd FZ impossible
FinZAbsurd (FS _) impossible

FinZAny : {A: Type} -> Fin 0 -> A
FinZAny fin = void (FinZAbsurd fin)

public export
FinMap : (n: Nat) -> Type
FinMap n = Fin n -> Fin n

foundElem : {n: Nat} -> {A: Type} -> (pred: A -> Type) -> (v: Vect n A) -> Type
foundElem {n} pred v = (fin : Fin n ** pred (index fin v))

findElemDec : {n: Nat} -> {A: Type} -> {pred: A -> Type} ->
              (test: (a: A) -> Dec (pred a)) ->
              (v: Vect n A) -> Dec (foundElem pred v)
findElemDec test [] = No (\found => case found of
  (fin ** pf) => FinZAbsurd fin)
findElemDec pred (a :: v') = case pred a of
  Yes headTrue => Yes (FZ ** headTrue)
  No headFalse => case findElemDec pred v' of
    Yes (fin ** inTail) => Yes (FS fin ** inTail)
    No notInTail => No (\inVecCertified => case inVecCertified of
                         (fin ** inVec) => case fin of
                           FZ => headFalse inVec
                           FS fin' => notInTail (fin' ** inVec))

public export
VectFin : Nat -> Type
VectFin n = Vect n (Fin n)

export
vectFinMap : {n: Nat} -> VectFin n -> FinMap n
vectFinMap vf fin = index fin vf

export
allFins : (n: Nat) -> VectFin n
allFins Z = []
allFins (S n') = FZ :: map FS (allFins n')

mapIndex : {n: Nat} -> {A, B: Type} -> (f: A -> B) -> (v: Vect n A) ->
           (fin: Fin n) -> index fin (map f v) = f (index fin v)
mapIndex f [] _ impossible
mapIndex f (a' :: v') FZ = Refl
mapIndex f (a' :: v') (FS fin') = mapIndex f v' fin'

indexAllFinsId : {n: Nat} -> (fin: Fin n) -> index fin (allFins n) = fin
indexAllFinsId FZ = Refl
indexAllFinsId (FS fin') =
  rewrite mapIndex FS (allFins _) fin' in
  rewrite indexAllFinsId fin' in
  Refl

makeVectByIndex : {n : Nat} -> {A: Type} -> (Fin n -> A) -> Vect n A
makeVectByIndex {n} f = map f (allFins n)

decElem : {n: Nat} -> {A: Type} -> (a: A) -> (v: Vect n A) -> Type
decElem {n} a v = (fin : Fin n ** (index fin v = a))

findEqDec : {n: Nat} -> {A: Type} -> DecEq A =>
          (a: A) -> (v: Vect n A) -> Dec (decElem a v)
findEqDec a v = findElemDec (\a' => decEq a' a) v

mapElem : {A, B: Type} -> Eq A => Eq B => DecEq A => DecEq B =>
          {f: A -> B} -> {n: Nat} -> {v: Vect n A} -> {a: A} ->
          decElem a v -> decElem (f a) (map f v)
mapElem (fin ** Refl) = (fin ** mapIndex f _ fin)

elemAllFins : {n: Nat} -> (fin: Fin n) -> decElem fin (allFins n)
elemAllFins FZ = (FZ ** Refl)
elemAllFins {n=(S n')} (FS fin') =
  case (elemAllFins fin') of
       (elem' ** isIndex) =>
         (FS elem' ** rewrite (sym isIndex) in mapIndex FS (allFins n') elem')

export
decAllFins : {n: Nat} -> {pred : Fin n -> Type} ->
             ((fin: Fin n) -> Dec (pred fin)) ->
             Dec ((fin: Fin n) -> pred fin)
decAllFins {n=Z} {pred} p = Yes (\fin => FinZAny fin)
decAllFins {n=(S n')} {pred} p = case p FZ of
  Yes pZHolds => let recCall = decAllFins {n=n'} (\fin' => p (FS fin')) in
    case recCall of
      Yes tailHolds =>
        Yes (\fin' => case fin' of
          FZ => pZHolds
          FS fin'' => tailHolds fin'')
      No tailFails =>
        No (\decAllHolds => tailFails (\fin' => decAllHolds (FS fin')))
  No pZFails =>
    No (\decAllHolds => pZFails (decAllHolds FZ))

SubVectDec : {A: Type} -> DecEq A => {m, n: Nat} ->
  (vsub : Vect m A) -> (vsuper : Vect n A) -> Type
SubVectDec vsub vsuper = ((fin : Fin m) -> decElem (index fin vsub) vsuper)

subVectDec : {A: Type} -> DecEq A => {n: Nat} ->
  (vsub : Vect n A) -> (vsuper : Vect n A) ->
  Dec (SubVectDec vsub vsuper)
subVectDec vsub vsuper = decAllFins (\fin => findEqDec (index fin vsub) vsuper)

allSubAllElems : {n: Nat} -> (v: VectFin n) -> SubVectDec v (allFins n)
allSubAllElems v fin = (index fin v ** indexAllFinsId (index fin v))

VectFinWithoutOneElement : {n: Nat} -> Fin (S n) -> Type
VectFinWithoutOneElement {n} fin = (fin' : Fin (S n) ** Not (fin' = fin))

vectFinWithoutOneToPredecessorVectFin : {n: Nat} ->
  (fin : Fin (S n)) -> (VectFinWithoutOneElement fin -> Fin n)
vectFinWithoutOneToPredecessorVectFin {n=Z} FZ (FZ ** neq) =
  void (neq Refl)
vectFinWithoutOneToPredecessorVectFin {n=Z} (FS fin) (FZ ** neq) =
  FinZAny fin
vectFinWithoutOneToPredecessorVectFin {n=(S n')} fin (FZ ** neq) =
  FZ
vectFinWithoutOneToPredecessorVectFin {n} FZ (FS fin' ** neq) =
  fin'
vectFinWithoutOneToPredecessorVectFin {n=Z} (FS fin) (FS fin' ** neq) =
  FinZAny fin
vectFinWithoutOneToPredecessorVectFin {n=(S n')} (FS fin) (FS fin' ** neq) =
  FS (vectFinWithoutOneToPredecessorVectFin {n=n'} fin
      (fin' ** (\eq => case eq of Refl => neq Refl)))

vectFinWithoutOneToPredecessorVectFinInverse : {n: Nat} ->
  (fin : Fin (S n)) -> (Fin n -> VectFinWithoutOneElement fin)
vectFinWithoutOneToPredecessorVectFinInverse FZ fin' =
  (FS fin' ** (\eq => case eq of Refl impossible))
vectFinWithoutOneToPredecessorVectFinInverse (FS fin) FZ =
  (FZ ** (\eq => case eq of Refl impossible))
vectFinWithoutOneToPredecessorVectFinInverse {n=Z} (FS fin) (FS fin')
  impossible
vectFinWithoutOneToPredecessorVectFinInverse {n=(S n')} (FS fin) (FS fin') =
  case vectFinWithoutOneToPredecessorVectFinInverse fin fin' of
    (fin'' ** neq) => (FS fin'' ** (\eq => case eq of Refl => neq Refl))

export
AreInverses : {n: Nat} -> (vf, vf': VectFin n) -> Type
AreInverses {n} vf vf' = (fin: Fin n) ->
  (index (index fin vf) vf' = fin, index (index fin vf') vf = fin)

export
areInversesDec : {n: Nat} -> (vf, vf': VectFin n) ->
                 Dec (AreInverses vf vf')
areInversesDec vf vf' = decAllFins (\fin =>
  case (decEq (index (index fin vf) vf') fin,
        decEq (index (index fin vf') vf) fin) of
          (Yes eql, Yes eqr) => Yes (eql, eqr)
          (No neq, _) => No (\eq => neq (fst eq))
          (_, No neq) => No (\eq => neq (snd eq)))

export
IsPermutation : {n: Nat} -> VectFin n -> Type
IsPermutation {n} vf = (vf' : VectFin n ** AreInverses vf vf')

inversePermutation : {n : Nat} -> {vf : VectFin n} ->
                     IsPermutation vf -> VectFin n
inversePermutation isP = fst isP

FinPermutation : Nat -> Type
FinPermutation n = (vf : VectFin n ** IsPermutation vf)
