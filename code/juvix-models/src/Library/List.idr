module Library.List

import public Data.List
import public Data.List.Elem
import public Data.List.Equalities
import public Data.Nat
import public Library.Decidability
import public Library.FunctionsAndRelations

%default total

public export
record ListIndSignature {a : Type} (predicate : List a -> Type) where
  constructor ListIndHypotheses
  baseCase : predicate []
  indStep : (x : a) -> (l : List a) -> predicate l -> predicate (x :: l)

public export
listInd : {a : Type} -> {predicate : List a -> Type} ->
  (signature : ListIndSignature predicate) ->
  (l : List a) -> predicate l
listInd signature [] = baseCase signature
listInd signature (x :: l') = indStep signature x l' (listInd signature l')

public export
record ListIndOutputIndSignature {a : Type} {predicate : List a -> Type}
  (signature : ListIndSignature predicate)
  (outputPredicate : (l : List a) -> predicate l -> Type) where
    constructor ListIndOutputIndHypotheses
    outputBaseCase : outputPredicate [] (baseCase signature)
    outputIndStep : (x : a) -> (l : List a) ->
      outputPredicate l (listInd signature l) ->
      outputPredicate (x :: l) (indStep signature x l (listInd signature l))

public export
listIndOutputInd : {a : Type} -> {predicate : List a -> Type} ->
  {signature : ListIndSignature predicate} ->
  {outputPredicate : (l : List a) -> predicate l -> Type} ->
  (outputSignature : ListIndOutputIndSignature signature outputPredicate) ->
  (l : List a) -> outputPredicate l (listInd signature l)
listIndOutputInd outputSignature [] = outputBaseCase outputSignature
listIndOutputInd outputSignature (x :: l') =
  outputIndStep outputSignature x l' (listIndOutputInd outputSignature l')

public export
mapCons : {a, b : Type} -> (f : a -> b) -> (x : a) -> (l : List a) ->
  map f (x :: l) = f x :: map f l
mapCons f x l = Refl

public export
mapPreservesLength : {a, b : Type} -> (f : a -> b) -> (l : List a) ->
  length (map f l) = length l
mapPreservesLength f [] = Refl
mapPreservesLength f (_ :: l) = cong S (mapPreservesLength f l)

public export
data ListForAll : {a : Type} -> (a -> Type) -> List a -> Type where
  ListForAllEmpty : {predicate : a -> Type} -> ListForAll predicate []
  ListForAllCons : {predicate : a -> Type} -> {x : a} -> {l : List a} ->
    predicate x -> ListForAll predicate l -> ListForAll predicate (x :: l)

public export
listForAllHeadTrue : {a : Type} -> {predicate : a -> Type} ->
  {x : a} -> {l : List a} ->
  ListForAll predicate (x :: l) -> predicate x
listForAllHeadTrue ListForAllEmpty impossible
listForAllHeadTrue (ListForAllCons predX _) = predX

public export
listForAllTailTrue : {a : Type} -> {predicate : a -> Type} ->
  {x : a} -> {l : List a} ->
  ListForAll predicate (x :: l) -> ListForAll predicate l
listForAllTailTrue ListForAllEmpty impossible
listForAllTailTrue (ListForAllCons _ predTail) = predTail

public export
listForAll : {a : Type} -> {predicate : a -> Type} -> {l : List a} ->
  (forAll : (x : a) -> Elem x l -> predicate x) ->
  ListForAll predicate l
listForAll {predicate} {l=[]} forAll = ListForAllEmpty
listForAll {predicate} {l=(x :: l')} forAll =
  ListForAllCons
    (forAll x Here)
    (listForAll {l=l'} (\x', elem' => forAll x' (There elem')))

public export
ListForAllDec : {a : Type} -> (predicate : a -> Type) -> List a -> Type
ListForAllDec predicate = Dec . (ListForAll predicate)

public export
ListForAllDecSig : {a : Type} -> {predicate : a -> Type} ->
  (decide : DecPred predicate) -> ListIndSignature (ListForAllDec predicate)
ListForAllDecSig {predicate} decide = ListIndHypotheses
  (Yes ListForAllEmpty)
  (\x, l, tailForAll => case (decide x, tailForAll) of
    (Yes xTrue, Yes tailTrue) => Yes (ListForAllCons xTrue tailTrue)
    (Yes xTrue, No tailFalse) =>
      No (\forAll => tailFalse (listForAllTailTrue forAll))
    (No xFalse, Yes tailTrue) =>
      No (\forAll => xFalse (listForAllHeadTrue forAll))
    (No xFalse, No tailFalse) =>
      No (\forAll => tailFalse (listForAllTailTrue forAll)))

public export
listForAllDec : {a : Type} -> {predicate : a -> Type} ->
  (decide : DecPred predicate) -> (l : List a) -> ListForAllDec predicate l
listForAllDec decide = listInd (ListForAllDecSig decide)

public export
listForAllMaybe : {a : Type} -> {predicate : a -> Type} ->
  (decide : (x : a) -> Maybe (predicate x)) -> (l : List a) ->
  Maybe (ListForAll predicate l)
listForAllMaybe decide [] = Just ListForAllEmpty
listForAllMaybe decide (x :: l) = case (decide x, listForAllMaybe decide l) of
  (Just px, Just pl) => Just (ListForAllCons px pl)
  _ => Nothing

public export
listForAllGet : {a : Type} -> {predicate : a -> Type} -> {l : List a} ->
  (forAll : ListForAll predicate l) -> {n : Nat} -> (inBounds : InBounds n l) ->
  DPair a predicate
listForAllGet ListForAllEmpty _ impossible
listForAllGet (ListForAllCons predX _) InFirst = (_ ** predX)
listForAllGet (ListForAllCons _ forAllTail) (InLater inTail) =
  listForAllGet forAllTail inTail

public export
data ListExists : {a : Type} -> (a -> Type) -> List a -> Type where
  ListExistsHead : {predicate : a -> Type} -> {x : a} -> {l : List a} ->
    predicate x -> ListExists predicate (x :: l)
  ListExistsTail : {predicate : a -> Type} -> {x : a} -> {l : List a} ->
    ListExists predicate l -> ListExists predicate (x :: l)

public export
listExistsHeadOrTailTrue : {a : Type} -> (predicate : a -> Type) ->
  {x : a} -> {l : List a} ->
  ListExists predicate (x :: l) ->
  Either (predicate x) (ListExists predicate l)
listExistsHeadOrTailTrue predicate (ListExistsHead predX) = Left predX
listExistsHeadOrTailTrue predicate (ListExistsTail predTail) = Right predTail

public export
listExistsEmptyVoid : {a : Type} -> (predicate : a -> Type) ->
  ListExists predicate [] -> Void
listExistsEmptyVoid predicate (ListExistsHead _) impossible
listExistsEmptyVoid predicate (ListExistsTail _) impossible

public export
listExistsGet : {a : Type} -> {b, c : a -> Type} -> {l : List a} ->
  ListExists b l -> ListForAll c l -> (x : a ** (b x, c x))
listExistsGet (ListExistsHead _) ListForAllEmpty impossible
listExistsGet (ListExistsHead y) (ListForAllCons z _) =
  (_ ** (y, z))
listExistsGet (ListExistsTail _) ListForAllEmpty impossible
listExistsGet (ListExistsTail existsTail) (ListForAllCons _ forAllTail) =
  listExistsGet existsTail forAllTail

public export
listExists : {a : Type} -> {predicate : a -> Type} -> {l : List a} ->
  (exists : (x : a ** (Elem x l, predicate x))) ->
  ListExists predicate l
listExists {l=[]} (x ** (elem, xTrue)) impossible
listExists {l=(x :: l')} (x ** (Here, xTrue)) =
  ListExistsHead xTrue
listExists {l=(x' :: l')} (x ** (There elem, xTrue)) =
  ListExistsTail (listExists {l=l'} (x ** (elem, xTrue)))

public export
ListExistsDec : {a : Type} -> (predicate : a -> Type) -> List a -> Type
ListExistsDec predicate = Dec . (ListExists predicate)

public export
ListExistsDecSig : {a : Type} -> {predicate : a -> Type} ->
  (decide : DecPred predicate) -> ListIndSignature (ListExistsDec predicate)
ListExistsDecSig {predicate} decide = ListIndHypotheses
  (No (\neq => listExistsEmptyVoid predicate neq))
  (\x, l, tailExists => case (decide x, tailExists) of
    (Yes xTrue, Yes tailTrue) => Yes (ListExistsHead xTrue)
    (Yes xTrue, No tailFalse) => Yes (ListExistsHead xTrue)
    (No xFalse, Yes tailTrue) => Yes (ListExistsTail tailTrue)
    (No xFalse, No tailFalse) => No (\existsTrue =>
      case listExistsHeadOrTailTrue predicate existsTrue of
        Left xTrue => xFalse xTrue
        Right tailTrue => tailFalse tailTrue))

public export
listExistsDec : {a : Type} -> {predicate : a -> Type} ->
  (decide : DecPred predicate) -> (l : List a) -> ListExistsDec predicate l
listExistsDec decide = listInd (ListExistsDecSig decide)

public export
record ListForAllIndSig {a : Type} {predicate : a -> Type}
  (outputPredicate : (l' : List a) -> ListForAll predicate l' -> Type) where
    constructor ListForAllIndHypotheses
    forAllEmpty : outputPredicate [] ListForAllEmpty
    forAllCons : (x : a) -> (l : List a) ->
      (xTrue : predicate x) -> (lTrue : ListForAll predicate l) ->
      outputPredicate l lTrue ->
      outputPredicate (x :: l) (ListForAllCons xTrue lTrue)

public export
ListForAllIndSigToIndSig : {a: Type} -> {predicate : a -> Type} ->
  {outputPredicate : (l' : List a) -> ListForAll predicate l' -> Type} ->
  (signature : ListForAllIndSig {predicate} outputPredicate) ->
  ListIndSignature (\l' =>
    (forAll : ListForAll predicate l') -> outputPredicate l' forAll)
ListForAllIndSigToIndSig signature =
  ListIndHypotheses
    (\forAll => case forAll of
      ListForAllEmpty => forAllEmpty signature
      ListForAllCons _ _ impossible)
    (\x, l, forAllImpliesOutput => \forAll => case forAll of
      ListForAllEmpty impossible
      ListForAllCons xTrue lTrue =>
        forAllCons signature x l xTrue lTrue (forAllImpliesOutput lTrue))

public export
listForAllInd : {a: Type} -> {predicate : a -> Type} ->
  {outputPredicate : (l' : List a) -> ListForAll predicate l' -> Type} ->
  (signature : ListForAllIndSig outputPredicate) ->
  (l : List a) -> (forAll : ListForAll predicate l) ->
  outputPredicate l forAll
listForAllInd signature = listInd (ListForAllIndSigToIndSig signature)

public export
record ListExistsIndSig {a : Type} {predicate : a -> Type}
  (outputPredicate : (l' : List a) -> ListExists predicate l' -> Type) where
    constructor ListExistsIndHypotheses
    firstTrue : (x : a) -> (l : List a) ->
      (xTrue : predicate x) ->
      outputPredicate (x :: l) (ListExistsHead xTrue)
    alreadyTrue : (x : a) -> (l : List a) ->
      (tailExists : ListExists predicate l) ->
      outputPredicate l tailExists ->
      outputPredicate (x :: l) (ListExistsTail tailExists)

public export
ListExistsIndSigToIndSig : {a: Type} -> {predicate : a -> Type} ->
  {outputPredicate : (l' : List a) -> ListExists predicate l' -> Type} ->
  (signature : ListExistsIndSig {predicate} outputPredicate) ->
  ListIndSignature (\l' =>
    (exists : ListExists predicate l') -> outputPredicate l' exists)
ListExistsIndSigToIndSig signature = ListIndHypotheses
  (\exists => case exists of
    ListExistsHead _ impossible
    ListExistsTail _ impossible)
  (\x, l, existsTailImpliesOutput => \exists => case exists of
    ListExistsHead xTrue =>
      firstTrue signature x l xTrue
    ListExistsTail lTrue =>
      alreadyTrue signature x l lTrue (existsTailImpliesOutput lTrue))

public export
listExistsInd : {a: Type} -> {predicate : a -> Type} ->
  {outputPredicate : (l' : List a) -> ListExists predicate l' -> Type} ->
  (signature : ListExistsIndSig {predicate} outputPredicate) ->
  (l : List a) -> (exists : ListExists predicate l) ->
  outputPredicate l exists
listExistsInd signature = listInd (ListExistsIndSigToIndSig signature)

record ListExistsDecIndSig {a : Type} {predicate : a -> Type}
  (outputPredicate : (l' : List a) ->
    ListExists predicate l' -> Type) where
      constructor ListExistsDecIndHypotheses
      firstTrueDec : (x : a) -> (l : List a) ->
        (xTrue : predicate x) ->
        (tailNotExists : Not (ListExists predicate l)) ->
        outputPredicate (x :: l) (ListExistsHead xTrue)
      alreadyTrueDec : (x : a) -> (l : List a) ->
        (tailExists : ListExists predicate l) ->
        outputPredicate l tailExists ->
        outputPredicate (x :: l) (ListExistsTail tailExists)

public export
listExistsDecInd : {a: Type} -> {predicate : a -> Type} ->
  (decide : DecPred predicate) ->
  {outputPredicate : (l' : List a) ->
    ListExists predicate l' -> Type} ->
  (signature : ListExistsDecIndSig outputPredicate) ->
  (l : List a) -> (exists : ListExists predicate l) ->
  (exists' : ListExists predicate l ** outputPredicate l exists')
listExistsDecInd decide signature [] _ impossible
listExistsDecInd decide signature (x :: l) exists =
  case (decide x, listExistsDec decide l) of
    (_, Yes tailTrue) =>
      case (listExistsDecInd decide signature l tailTrue) of
        (exists' ** output) =>
          (ListExistsTail exists' **
            alreadyTrueDec signature x l exists' output)
    (Yes xTrue, No tailFalse) =>
      (ListExistsHead xTrue ** firstTrueDec signature x l xTrue tailFalse)
    (No xFalse, No tailFalse) => case exists of
      ListExistsHead xTrue => void (xFalse xTrue)
      ListExistsTail tailTrue => void (tailFalse tailTrue)

public export
listDecEq : {a : Type} -> DecEqPred a -> DecEqPred (List a)
listDecEq deq [] [] = Yes Refl
listDecEq deq [] (_ :: _) = No (\eq => case eq of Refl impossible)
listDecEq deq (_ :: _) [] = No (\eq => case eq of Refl impossible)
listDecEq deq (x :: l) (x' :: l') =
  case (deq x x', listDecEq deq l l') of
    (Yes Refl, Yes Refl) => Yes Refl
    (Yes xeq, No lneq) => No (\eq => case eq of Refl => lneq Refl)
    (No xneq, _ ) => No (\eq => case eq of Refl => xneq Refl)

public export
MapPreservesPredicate : {a, b : Type} ->
  (predA : a -> Type) -> (predB : b -> Type) ->
  (f : a -> b) -> Type
MapPreservesPredicate predA predB f = (x : a) -> predA x -> predB (f x)

public export
ListFoldAppSig : {a : Type} ->
  ListIndSignature {a=(List a)} (\ll => List a -> List a)
ListFoldAppSig = ListIndHypotheses id (\l, _, accum => \l' => l' ++ accum l)

public export
listFoldApp : {a : Type} -> List a -> List (List a) -> List a
listFoldApp initial ll = listInd ListFoldAppSig ll initial

public export
listJoin : {a : Type} -> List (List a) -> List a
listJoin = listFoldApp []

public export
appNilRightNeutral : {a : Type} -> (l : List a) -> l = l ++ []
appNilRightNeutral = listInd
  (ListIndHypotheses
    Refl
    (\_, _, eq => rewrite (sym eq) in Refl)
  )

public export
foldAppCons : {a : Type} -> (x : a) -> (l : List a) -> (ll : List (List a)) ->
  listFoldApp (x :: l) ll = x :: listFoldApp l ll
foldAppCons x l ll = listInd
  {predicate=(\ll' => (x' : a) -> (l' : List a) ->
    listFoldApp (x' :: l') ll' = x' :: listFoldApp l' ll')}
      (ListIndHypotheses
        (\_, _ => Refl)
        (\_, _, _ => \_, _ => Refl)
      ) ll x l

public export
foldAppDistributeAccum : {a : Type} -> (l, l' : List a) ->
  (ll : List (List a)) ->
  listFoldApp (l ++ l') ll = l ++ listFoldApp l' ll
foldAppDistributeAccum l l' ll = listInd
  {predicate=(\ll' => (l2, l3 : List a) ->
    listFoldApp (l2 ++ l3) ll' = l2 ++ listFoldApp l3 ll')}
      (ListIndHypotheses
        (\_, _ => Refl)
        (\_, _, eq => \_, _ => sym (appendAssociative _ _ _))
      ) ll l l'

public export
foldAppInit : {a : Type} -> (l : List a) -> (ll : List (List a)) ->
  listFoldApp l ll = l ++ listFoldApp [] ll
foldAppInit l ll =
    replace
      {p=(\l' => listFoldApp l' ll = l ++ listFoldApp [] ll)}
      (sym (appNilRightNeutral l))
      (foldAppDistributeAccum l [] ll)

public export
consInAppendOut : {a : Type} -> (List (List a) -> List a) -> Type
consInAppendOut f = (l : List a) -> (ll : List (List a)) ->
    f (l :: ll) = l ++ f ll

public export
joinConsInAppendOut : {a : Type} -> consInAppendOut (listJoin {a})
joinConsInAppendOut l Nil = appNilRightNeutral l
joinConsInAppendOut l (l' :: ll') = Refl

public export
joinDistributesOverAppend : {a : Type} -> (ll, ll' : List (List a)) ->
    listJoin (ll ++ ll') = listJoin ll ++ listJoin ll'
joinDistributesOverAppend Nil ll = Refl
joinDistributesOverAppend (l :: ll) ll' =
  rewrite (joinConsInAppendOut l ll) in
  rewrite (foldAppInit l (ll ++ ll')) in
  rewrite (joinDistributesOverAppend ll ll') in
  (appendAssociative _ _ _)

public export
listForAllAppend : {a : Type} -> {predicate : a -> Type} -> {l, l' : List a} ->
  ListForAll predicate l -> ListForAll predicate l' ->
  ListForAll predicate (l ++ l')
listForAllAppend {l} {l'} forAll forAll' =
  listForAllInd
    {outputPredicate=(\lFirst, forAllFirst =>
      (lSecond : List a) -> ListForAll predicate lSecond ->
      ListForAll predicate (lFirst ++ lSecond))}
    (ListForAllIndHypotheses
      (\_ => id)
      (\x, _, predX, _, indHyp, lNew, predLNew =>
        ListForAllCons predX (indHyp lNew predLNew))
    ) l forAll l' forAll'

public export
substitute : {a, b : Type} -> (a -> List b) -> List a -> List b
substitute = ((.) listJoin) . map

public export
substituteMapCommute : {a, b : Type} -> (f : a -> b) -> (ll : List (List a)) ->
  substitute (map f) ll = map f (listJoin ll)
substituteMapCommute f = listInd (ListIndHypotheses
  {predicate=(\ll' => substitute (map f) ll' = map f (listJoin ll'))}
  Refl
  (\l, ll, eq =>
    rewrite (foldAppInit (map f l) (map (map f) ll)) in
    rewrite eq in
    rewrite (foldAppInit l ll) in
    sym (mapDistributesOverAppend _ _ _)))

public export
joinCommutative : {a : Type} -> (l : List (List (List a))) ->
  listJoin (listJoin l) = substitute (listJoin {a}) l
joinCommutative = listInd (ListIndHypotheses
    {predicate=(\l' => listJoin (listJoin l') = substitute listJoin l')}
    Refl
    (\ll, lll, eq =>
      rewrite (joinConsInAppendOut ll lll) in
      rewrite (joinDistributesOverAppend ll (listJoin lll)) in
      rewrite eq in
      sym (foldAppInit (listJoin ll) (map listJoin lll)))
  )

public export
listReturn : {a : Type} -> a -> List a
listReturn x = [x]

public export
mapDistributesOverCompose : {a, b, c : Type} ->
  (f : b -> c) -> (g : a -> b) -> (l : List a) ->
  map (f . g) l = (map f . map g) l
mapDistributesOverCompose f g [] = Refl
mapDistributesOverCompose f g (x :: l') =
  rewrite (mapDistributesOverCompose f g l') in Refl

public export
ListContains : {a : Type} -> (l : List a) -> a -> Type
ListContains l x = ListExists (\x' => Equal x x') l

listContainsToElem : {a, b : Type} -> {l : List a} -> {x : a} ->
  ListContains l x -> Elem x l
listContainsToElem {l} {x} contains = listExistsInd
  {outputPredicate=(\l', contains' => Elem x l')}
  (ListExistsIndHypotheses
    (\_, _, xeq => rewrite xeq in Here)
    (\_, _, _, elem' => There elem')
  ) l contains

public export
listContains : {a : Type} -> DecEqPred a -> (l : List a) -> (x : a) ->
  Dec (ListContains l x)
listContains deq l x = listExistsDec (deq x) l

public export
ListSuperset : {a : Type} -> (l, l' : List a) -> Type
ListSuperset l l' = ListForAll (ListContains l) l'

public export
listSuperset : {a : Type} -> DecEqPred a -> (l, l' : List a) ->
  Dec (ListSuperset l l')
listSuperset deq l l' = listForAllDec (listContains deq l) l'

public export
ListSubset : {a : Type} -> (l, l' : List a) -> Type
ListSubset l l' = ListForAll (ListContains l') l

public export
listSubset : {a : Type} -> DecEqPred a -> (l, l' : List a) ->
  Dec (ListSubset l l')
listSubset deq l l' = listForAllDec (listContains deq l') l

public export
ListsDisjoint : {a : Type} -> (l, l' : List a) -> Type
ListsDisjoint l l' = ListForAll (Not . ListContains l) l'

public export
SameElements : {a : Type} -> (l, l' : List a) -> Type
SameElements l l' = (ListSubset l l', ListSuperset l l')

public export
members : {a : Type} -> List a -> Type
members l = DPair a (ListContains l)

public export
MemberMap : {a : Type} -> List a -> Type -> Type
MemberMap l b = members l -> b

public export
data ElementsUnique : {a : Type} -> (l : List a) -> Type where
    UniqueNil : ElementsUnique []
    UniqueCons : (x : a) -> ElementsUnique l ->
      Not (ListContains l x) -> ElementsUnique (x :: l)

public export
SetIsomorphic : {a : Type} -> (l, l' : List a) -> Type
SetIsomorphic l l' = (ElementsUnique l, ElementsUnique l', SameElements l l')

public export
removeAndUniquify : {a : Type} -> DecEqPred a ->
  (toRemove, target : List a) -> List a
removeAndUniquify deq toRemove [] = []
removeAndUniquify deq toRemove (x :: l) =
  case (listContains deq toRemove x) of
    Yes _ => removeAndUniquify deq toRemove l
    No _ => x :: removeAndUniquify deq (x :: toRemove) l

public export
uniqueElements : {a : Type} -> DecEqPred a -> List a -> List a
uniqueElements deq l = removeAndUniquify deq [] l

FirstElementsUnique : {a, b : Type} -> List (a, b) -> Type
FirstElementsUnique l = ElementsUnique (map fst l)

public export
listMapContains : {a, b: Type} -> (l : List (a, b)) -> (x : a) ->
  ListContains (map Builtin.fst l) x -> (y : b ** ListContains l (x, y))
listMapContains [] _ (ListExistsHead _) impossible
listMapContains [] _ (ListExistsTail _) impossible
listMapContains ((x, y') :: l') x (ListExistsHead Refl) =
  (y' ** ListExistsHead Refl)
listMapContains (_ :: l') x (ListExistsTail lContains) =
  case listMapContains l' x lContains of
    (y' ** exists') => (y' ** ListExistsTail exists')

public export
listMap : {a, b : Type} -> (l : List (a, b)) -> MemberMap (map Builtin.fst l) b
listMap l (x ** contains) = fst (listMapContains l x contains)

public export
mapContains : {a, b : Type} -> (f : a -> b) -> {l : List a} -> {x : a} ->
  ListContains l x -> ListContains (map f l) (f x)
mapContains f (ListExistsHead Refl) =
  ListExistsHead Refl
mapContains f (ListExistsTail existsTail) =
  ListExistsTail (mapContains f existsTail)

public export
memberMap : {a, b : Type} -> (f : a -> b) -> {l : List a} ->
  members l -> members (map f l)
memberMap f (x ** isMember) = (f x ** mapContains f isMember)

public export
memberMapValue : {a, b : Type} -> (f : a -> b) -> {l : List a} ->
  (m : members l) -> fst (memberMap f {l} m) = f (fst m)
memberMapValue _ (_ ** _) = Refl

public export
data SamePosition : {a, b : Type} -> {la : List a} -> {lb : List b} ->
  {x : a} -> {y : b} -> ListContains la x -> ListContains lb y -> Type where
    BothHead : {a, b : Type} -> {headA : a} -> {tailA : List a} ->
               {headB : b} -> {tailB : List b} ->
               {eqA : Equal headA headA} -> {eqB : Equal headB headB} ->
               SamePosition
                 (ListExistsHead {x=headA} {l=tailA} eqA)
                 (ListExistsHead {x=headB} {l=tailB} eqB)
    BothTail : {a, b : Type} -> {headA : a} -> {tailA : List a} ->
               {headB : b} -> {tailB : List b} -> {x : a} -> {y : b} ->
               {containsA : ListContains tailA x} ->
               {containsB : ListContains tailB y} ->
               SamePosition containsA containsB ->
               SamePosition
                 (ListExistsTail {x=headA} {l=tailA} containsA)
                 (ListExistsTail {x=headB} {l=tailB} containsB)

public export
sameTailSame : {a, b : Type} -> {la : List a} -> {lb : List b} ->
  {x, x' : a} -> {y, y' : b} ->
  (containsA : ListContains la x) -> (containsB : ListContains lb y) ->
  Not (SamePosition containsA containsB) ->
  Not (SamePosition
    (ListExistsTail {x=x'} containsA) (ListExistsTail {x=y'} containsB))
sameTailSame containsA containsB notSame BothHead impossible
sameTailSame containsA containsB notSame (BothTail tailSame) =
  void (notSame tailSame)

samePosition : {a, b : Type} -> {la : List a} -> {lb : List b} ->
  {x : a} -> {y : b} ->
  (containsA : ListContains la x) -> (containsB : ListContains lb y) ->
  Dec (SamePosition containsA containsB)
samePosition (ListExistsHead {x=headA} Refl) (ListExistsHead {x=headB} Refl) =
  Yes BothHead
samePosition (ListExistsHead _) (ListExistsTail _) =
  No (\same =>
    case same of
      BothHead impossible
      BothTail _ impossible)
samePosition (ListExistsTail _) (ListExistsHead _) =
  No (\same =>
    case same of
      BothHead impossible
      BothTail _ impossible)
samePosition
  (ListExistsTail {l=la} containsA) (ListExistsTail {l=lb} containsB) =
    case samePosition containsA containsB of
      Yes same => Yes (BothTail same)
      No notSame => No (\same => sameTailSame containsA containsB notSame same)

public export
substLeftFish : {a, b, c : Type} -> (b -> List c) -> (a -> List b) ->
  (a -> List c)
substLeftFish sbc sab = (substitute sbc) . sab

public export
substRightFish : {a, b, c : Type} -> (a -> List b) -> (b -> List c) ->
  (a -> List c)
substRightFish sbc sab = substLeftFish sab sbc

substCompose : {a, b, c : Type} -> (b -> List c) -> (a -> List b) ->
  List a -> List c
substCompose sbc sab = substitute (substLeftFish sbc sab)

public export
substituteComposes : {a, b, c : Type} ->
  (sbc : b -> List c) -> (sab : a -> List b) -> (la : List a) ->
  substCompose sbc sab la = ((substitute sbc) . (substitute sab)) la
substituteComposes sbc sab la =
  rewrite (sym (substituteMapCommute sbc (map sab la))) in
  rewrite (joinCommutative {a=c} (map (map sbc) (map sab la))) in
  rewrite (mapDistributesOverCompose (listJoin {a=c}) ((map sbc) . sab) la) in
  rewrite (mapDistributesOverCompose (map sbc) sab la) in
  Refl

public export
substLeftFishAssociative : {a, b, c , d: Type} ->
  (scd : c -> List d) -> (sbc : b -> List c) -> (sab : a -> List b) ->
  (l : a) ->
  substLeftFish scd (substLeftFish sbc sab) l =
    substLeftFish (substLeftFish scd sbc) sab l
substLeftFishAssociative scd sbc sab l =
  rewrite (substituteComposes scd sbc (sab l)) in Refl

public export
substAssociative : {a, b, c , d: Type} ->
  (scd : c -> List d) -> (sbc : b -> List c) -> (sab : a -> List b) ->
  (l : List a) ->
  ((substitute scd) . ((substitute sbc) . (substitute sab))) l =
    ((substitute (substLeftFish scd sbc)) . (substitute sab)) l
substAssociative scd sbc sab l =
  rewrite (substituteComposes scd sbc (substitute sab l)) in Refl

ListTransformPreservesForAll : {a, b : Type} ->
  (predA : a -> Type) -> (predB : b -> Type) ->
  (f : a -> List b) -> Type
ListTransformPreservesForAll predA predB f =
  (x : a) -> predA x -> ListForAll predB (f x)

ListTransformPreservesExists : {a, b : Type} ->
  (predA : a -> Type) -> (predB : b -> Type) ->
  (f : a -> List b) -> Type
ListTransformPreservesExists predA predB f =
  (x : a) -> predA x -> ListExists predB (f x)

{-
public export
ListCategory : Category
ListCategory = MkCategory
  Type
  (\a, b => (List a -> List b))
  (\a => \x => x)
  (\f, g => f . g)
  (\f => Refl)
  (\f => Refl)
  (\f, g, h => Refl)
  -}

public export
map_id_ext : {a : Type} -> (l : List a) -> map (id {a}) l = l
map_id_ext [] = Refl
map_id_ext (x :: l) = rewrite map_id_ext l in Refl

Matches : {a, b : Type} -> List a -> List b -> Type
Matches la lb = (f : b -> List a ** substitute f lb = la)

Matching : {a : Type} -> List a -> Type
Matching la = (b : Type ** lb : List b ** Matches lb la)

MatchedBy : {a : Type} -> List a -> Type
MatchedBy la = (b : Type ** lb : List b ** Matches la lb)

MatchingBoth : {a, b : Type} -> List a -> List b -> Type
MatchingBoth la lb =
  (c : Type ** lc : List c ** (Matches lb la, Matches lc la))

MatchedByBoth : {a, b : Type} -> List a -> List b -> Type
MatchedByBoth la lb =
  (c : Type ** lc : List c ** (Matches la lb, Matches la lc))

public export
InBoundsSingleton : {a : Type} -> {k, k' : Nat} -> {xs : List a} ->
  (i : InBounds k xs) -> (i' : InBounds k' xs) -> k = k' -> i = i'
InBoundsSingleton InFirst InFirst Refl = Refl
InBoundsSingleton InFirst (InLater _) Refl impossible
InBoundsSingleton (InLater _) InFirst Refl impossible
InBoundsSingleton (InLater _) (InLater _) Refl =
  cong InLater (InBoundsSingleton _ _ Refl)

public export
IndexInto : {a : Type} -> List a -> Type
IndexInto l = (n ** InBounds n l)

public export
indexNumber : {a : Type} -> {l : List a} -> IndexInto l -> Nat
indexNumber (n ** _) = n

public export
indexInto : {a : Type} -> {l : List a} ->
  (index : IndexInto l) -> (InBounds (indexNumber index) l)
indexInto (_ ** inBounds) = inBounds

public export
IndexIntoInjective : {a : Type} -> {l : List a} ->
  {index, index' : IndexInto l} ->
  indexNumber index = indexNumber index' ->
  index = index'
IndexIntoInjective {index=(n ** inBounds)} {index'=(n' ** inBounds')} eq =
  DPairHeterogeneousInjective eq (InBoundsSingleton inBounds inBounds' eq)

public export
getByIndex : {a : Type} -> {l : List a} -> (index : IndexInto l) -> a
getByIndex {l} (n ** inBounds) = Data.List.index n l {ok=inBounds}

public export
natPrefix : Nat -> List Nat
natPrefix Z = []
natPrefix (S n) = Z :: map S (natPrefix n)

public export
mapInBounds : {n : Nat} -> {a, b : Type} -> {l : List a} ->
  InBounds n l -> {f : a -> b} -> InBounds n (map f l)
mapInBounds InFirst = InFirst
mapInBounds (InLater nInBounds') = InLater (mapInBounds nInBounds')

public export
mapInBoundsInverse : {n : Nat} -> {a, b : Type} -> {l : List a} ->
  {f : a -> b} -> InBounds n (map f l) -> InBounds n l
mapInBoundsInverse {f} {l=[]} nInBounds = case nInBounds of
  InFirst impossible
  InLater _ impossible
mapInBoundsInverse {f} {l=(x :: l')} InFirst = InFirst
mapInBoundsInverse {f} {l=(x :: l')} (InLater nInBounds') =
  InLater (mapInBoundsInverse nInBounds')

public export
forAllGetMap : {a, b : Type} -> {f : a -> b} -> {predicate : b -> Type} ->
  {l : List a} -> {n : Nat} -> (nInBounds : InBounds n l) ->
  ListForAll predicate (map f l) -> predicate (f (index n l {ok=nInBounds}))
forAllGetMap InFirst ListForAllEmpty impossible
forAllGetMap InFirst (ListForAllCons px _) = px
forAllGetMap (InLater nInBounds') ListForAllEmpty impossible
forAllGetMap (InLater nInBounds') (ListForAllCons _ ptail) =
  forAllGetMap nInBounds' ptail

inBoundsInd : {a : Type} ->
  (predicate : (n : Nat) -> (l : List a) -> InBounds n l -> Type) ->
  (base : (x : a) -> (l' : List a) -> InBounds Z (x :: l') ->
    predicate Z (x :: l') InFirst) ->
  (step : (x : a) -> (l' : List a) -> (n : Nat) ->
    (nInBounds : InBounds n l') -> predicate n l' nInBounds ->
    predicate (S n) (x :: l') (InLater nInBounds)) ->
  {n : Nat} -> {l : List a} ->
  (nInBounds : InBounds n l) ->
  predicate n l nInBounds
inBoundsInd predicate base step InFirst = base _ _ InFirst
inBoundsInd predicate base step (InLater nInBounds') =
  step _ _ _ nInBounds' (inBoundsInd predicate base step nInBounds')

public export
indexMap : {a, b : Type} -> {f : a -> b} -> {l : List a} -> {n : Nat} ->
  (nInBounds : InBounds n l) ->
  Data.List.index n (map f l) {ok=(mapInBounds {f} nInBounds)} =
    f (Data.List.index n l {ok=nInBounds})
indexMap {f} =
  inBoundsInd
  (\n, l, nInBounds =>
    Data.List.index n (map f l) {ok=(mapInBounds {f} nInBounds)} =
      f (Data.List.index n l {ok=nInBounds}))
  (\_, _, _ => Refl)
  (\_, _, _, _ => id)

public export
inBoundsNil : {n : Nat} -> InBounds n [] -> Void
inBoundsNil InFirst impossible
inBoundsNil (InLater _) impossible

public export
natPrefixIndex: {n, n': Nat} ->
  (nInBounds : InBounds n (natPrefix n')) ->
  index n (natPrefix n') {ok=nInBounds} = n
natPrefixIndex {n=Z} {n'=Z} nInBounds = void (inBoundsNil nInBounds)
natPrefixIndex {n=Z} {n'=(S n'')} nInBounds = case nInBounds of
  InFirst => Refl
  (InLater _) impossible
natPrefixIndex {n=(S n'')} {n'=Z} nInBounds = void (inBoundsNil nInBounds)
natPrefixIndex {n=(S n'')} {n'=(S n''')} InFirst impossible
natPrefixIndex {n=(S n'')} {n'=(S n''')} (InLater nInBounds') =
  let nInBounds'' = mapInBoundsInverse {f=S} {a=Nat} nInBounds' in
  rewrite InBoundsSingleton nInBounds' (mapInBounds nInBounds'') Refl in
  (trans (indexMap nInBounds'') (cong S (natPrefixIndex nInBounds'')))

public export
natPrefixLengthEquals : (n : Nat) -> length (natPrefix n) = n
natPrefixLengthEquals Z = Refl
natPrefixLengthEquals (S n) =
  cong S (rewrite mapPreservesLength S (natPrefix n) in natPrefixLengthEquals n)

public export
listToNatPrefix : {a : Type} -> (l : List a) -> List Nat
listToNatPrefix l = natPrefix (length l)

public export
natPrefixInBounds : {n : Nat} -> {a : Type} -> {l : List a} ->
  InBounds n l -> InBounds n (natPrefix (length l))
natPrefixInBounds InFirst = InFirst
natPrefixInBounds (InLater nInBounds') =
  InLater (mapInBounds (natPrefixInBounds nInBounds'))

public export
getPrefixIndexed : {a : Type} -> {predicate : Nat -> Type} -> {l : List a} ->
  {n : Nat} -> (forAll : ListForAll predicate (listToNatPrefix l)) ->
  (nInBounds : InBounds n l) -> predicate n
getPrefixIndexed {l=[]} {n=Z} forAll InFirst impossible
getPrefixIndexed {l=[]} {n=(S n')} forAll InFirst impossible
getPrefixIndexed {l=(x :: l')} {n=Z} forAll InFirst = listForAllHeadTrue forAll
getPrefixIndexed {l=(x :: l')} {n=(S n')} forAll InFirst impossible
getPrefixIndexed {l=[]} {n=Z} forAll (InLater nInBounds') impossible
getPrefixIndexed {l=[]} {n=(S n')} forAll (InLater nInBounds') impossible
getPrefixIndexed {l=(x :: l')} {n=Z} forAll (InLater nInBounds') impossible
getPrefixIndexed {l=(x :: l')} {n=(S n')} ListForAllEmpty (InLater nInBounds')
  impossible
getPrefixIndexed {a} {l=(x :: l')} {n=(S n')}
  (ListForAllCons headPred tailPred) InFirst impossible
getPrefixIndexed {a} {l=(x :: l')} {n=(S n')}
  (ListForAllCons headPred tailPred) (InLater nInBounds') =
    rewrite (sym (natPrefixIndex (natPrefixInBounds nInBounds'))) in
    (forAllGetMap {a=Nat} {f=S} {n=n'} _ tailPred)

public export
indexIntoCons : {a : Type} -> {x : a} -> {l : List a} -> IndexInto l ->
  IndexInto (x :: l)
indexIntoCons (n ** nInBounds) = (S n ** InLater nInBounds)

public export
indexIntoConsTail : {a : Type} -> {x : a} -> {l : List a} ->
  (nInBounds : IndexInto l) ->
  Data.List.index (fst nInBounds) l {ok=(snd nInBounds)} =
  Data.List.index (fst (indexIntoCons {x} nInBounds)) (x :: l)
    {ok=(snd (indexIntoCons nInBounds))}
indexIntoConsTail (_ ** _) = Refl

public export
listIndexes : {a : Type} -> (l : List a) -> List (IndexInto l)
listIndexes [] = []
listIndexes (_ :: l) = (Z ** InFirst) :: map indexIntoCons (listIndexes l)

public export
listIndexesEqualLength : {a : Type} -> (l : List a) ->
  length l = length (listIndexes l)
listIndexesEqualLength [] = Refl
listIndexesEqualLength (_ :: l) =
  cong S
    (trans
      (listIndexesEqualLength l)
      (sym (mapPreservesLength indexIntoCons (listIndexes l))))

public export
indexEqualLength : {a, b : Type} -> (la : List a) -> (lb : List b) ->
  length la = length lb -> {n : Nat} -> InBounds n la -> InBounds n lb
indexEqualLength [] [] eq InFirst impossible
indexEqualLength [] [] eq (InLater _) impossible
indexEqualLength [] (_ :: _) Refl nInBounds impossible
indexEqualLength (_ :: _) [] Refl nInBounds impossible
indexEqualLength (x :: la) (y :: lb) eq nInBounds =
  case nInBounds of
    InFirst => InFirst
    InLater nInBounds' =>
      InLater (indexEqualLength la lb (injective eq) nInBounds')

public export
indexesIndex : {a : Type} -> {l : List a} -> {n : Nat} ->
  InBounds n l -> InBounds n (listIndexes l)
indexesIndex nInBounds =
  indexEqualLength l (listIndexes l) (listIndexesEqualLength l) nInBounds

public export
IndexedListForAllPredicate : {a : Type} ->
  (predicate : a -> Type) -> (n : Nat) -> Type
IndexedListForAllPredicate predicate n =
  (l : List a) -> (nInBounds : InBounds n l) ->
    predicate (Data.List.index n l {ok=nInBounds})

public export
IndexedListForAll : {a : Type} -> (predicate : a -> Type) -> (l : List a) ->
  Type
IndexedListForAll predicate l =
  ListForAll (IndexedListForAllPredicate predicate) (natPrefix (length l))

public export
data ListPairForAll : {a, b : Type} ->
  (predicate : a -> b -> Type) -> List a -> List b -> Type where
    ListPairForAllEmpty : ListPairForAll predicate [] []
    ListPairForAllCons : {x : a} -> {y : b} -> {la : List a} -> {lb : List b} ->
      predicate x y -> ListPairForAll predicate la lb ->
      ListPairForAll predicate (x :: la) (y :: lb)

public export
data ForAllListPairForAll : {a, b : Type} -> {c : a -> b -> Type} ->
  (predicate : (x : a) -> (y : b) -> c x y -> Type) ->
  {la : List a} -> {lb : List b} ->
  (forAll : ListPairForAll c la lb) -> Type where
    ForAllListPairForAllEmpty :
      {a, b : Type} -> {c : a -> b -> Type} ->
      {predicate : (x : a) -> (y : b) -> c x y -> Type} ->
      ForAllListPairForAll predicate ListPairForAllEmpty
    ForAllListPairForAllCons :
      {a, b : Type} -> {c : a -> b -> Type} ->
      {predicate : (x : a) -> (y : b) -> c x y -> Type} ->
      {x : a} -> {y : b} -> {la : List a} -> {lb : List b} ->
      {cxy : c x y} -> predicate x y cxy ->
      {forAll : ListPairForAll {a} {b} c la lb} ->
      ForAllListPairForAll {a} {b} {c} predicate forAll ->
      ForAllListPairForAll predicate (ListPairForAllCons cxy forAll)

public export
lpForAllInd : {a, b : Type} -> {c : a -> b -> Type} ->
  {predicate :
    (la : List a) -> (lb : List b) -> ListPairForAll c la lb -> Type} ->
  (base : predicate [] [] ListPairForAllEmpty) ->
  (step : (x : a) -> (y : b) -> (la : List a) -> (lb : List b) ->
          (cxy : c x y) -> (forAll : ListPairForAll c la lb) ->
          predicate la lb forAll ->
          predicate (x :: la) (y :: lb) (ListPairForAllCons cxy forAll)) ->
  (la : List a) -> (lb : List b) -> (forAll : ListPairForAll c la lb) ->
  predicate la lb forAll
lpForAllInd base step [] [] ListPairForAllEmpty = base
lpForAllInd base step (x :: la) (y :: lb) (ListPairForAllCons cxy forAll) =
  step x y la lb cxy forAll (lpForAllInd base step la lb forAll)

public export
lpForAllNilConsImpossible : {a, b : Type} -> {c : a -> b -> Type} ->
  {y : b} -> {lb : List b} -> ListPairForAll c [] (y :: lb) -> Void
lpForAllNilConsImpossible ListPairForAllEmpty impossible
lpForAllNilConsImpossible (ListPairForAllCons _ _) impossible

public export
lpForAllConsNilImpossible : {a, b : Type} -> {c : a -> b -> Type} ->
  {x : a} -> {la : List a} -> ListPairForAll c (x :: la) [] -> Void
lpForAllConsNilImpossible ListPairForAllEmpty impossible
lpForAllConsNilImpossible (ListPairForAllCons _ _) impossible

public export
lpForAllDec : {a, b : Type} -> {c : a -> b -> Type} ->
  (dec : (x : a) -> (y : b) -> Dec (c x y)) -> (la : List a) -> (lb : List b) ->
  Dec (ListPairForAll c la lb)
lpForAllDec dec [] [] = Yes ListPairForAllEmpty
lpForAllDec dec [] (y :: lb) = No lpForAllNilConsImpossible
lpForAllDec dec (x :: la) [] = No lpForAllConsNilImpossible
lpForAllDec dec (x :: la) (y :: lb) = case (dec x y, lpForAllDec dec la lb) of
  (Yes cxy, Yes yesTail) => Yes (ListPairForAllCons cxy yesTail)
  (No noHead, _) =>
    No (\yesCons => case yesCons of
      ListPairForAllEmpty impossible
      ListPairForAllCons yesHead _ => noHead yesHead)
  (_, No noTail) =>
    No (\yesCons => case yesCons of
      ListPairForAllEmpty impossible
      ListPairForAllCons _ yesTail => noTail yesTail)

public export
lpForAllPairInd : {a, b : Type} -> {c : a -> b -> Type} ->
  {predicate : (la : List a) -> (lb : List b) ->
    (forAll, forAll' : ListPairForAll c la lb) -> Type} ->
  (base : predicate [] [] ListPairForAllEmpty ListPairForAllEmpty) ->
  (step : (x : a) -> (y : b) -> (la : List a) -> (lb : List b) ->
          (cxy, cxy' : c x y) ->
          (forAll, forAll' : ListPairForAll c la lb) ->
            predicate la lb forAll forAll' ->
          predicate (x :: la) (y :: lb)
            (ListPairForAllCons cxy forAll)
            (ListPairForAllCons cxy' forAll')) ->
  (la : List a) -> (lb : List b) ->
  (forAll, forAll' : ListPairForAll c la lb) ->
  predicate la lb forAll forAll'
lpForAllPairInd base step [] []
  ListPairForAllEmpty ListPairForAllEmpty = base
lpForAllPairInd base step (_ :: _) _
  (ListPairForAllCons _ _) ListPairForAllEmpty impossible
lpForAllPairInd base step _ (_ :: _)
  ListPairForAllEmpty (ListPairForAllCons _ _) impossible
lpForAllPairInd base step (x :: xs) (y :: ys)
  (ListPairForAllCons cxy forAll) (ListPairForAllCons cxy' forAll') =
    step x y xs ys cxy cxy' forAll forAll'
      (lpForAllPairInd base step xs ys forAll forAll')

public export
mkListPairForAll : {a, b : Type} -> {c : a -> b -> Type} ->
  (mk : (x : a) -> (y : b) -> c x y) -> (la : List a) -> (lb : List b) ->
  length la = length lb -> ListPairForAll c la lb
mkListPairForAll mk [] [] Refl = ListPairForAllEmpty
mkListPairForAll mk [] (_ :: _) Refl impossible
mkListPairForAll mk (_ :: _) [] Refl impossible
mkListPairForAll mk (x :: xs) (y :: ys) eq =
  ListPairForAllCons (mk x y) (mkListPairForAll mk xs ys (injective eq))

public export
(~!) : {a : Type} -> {b : a -> Type} ->
  ListForAll b []
(~!) = ListForAllEmpty

infixl 30 ~::
public export
(~::) : {a : Type} -> {b : a -> Type} -> {x : a} -> {l : List a} ->
  (y : b x) -> ListForAll b l -> ListForAll b (x :: l)
(~::) = ListForAllCons

public export
(~!!) : {a, b : Type} -> {c : a -> b -> Type} ->
  ListPairForAll c [] []
(~!!) = ListPairForAllEmpty

infixl 31 ~:::
public export
(~:::) : {a, b : Type} -> {c : a -> b -> Type} ->
  {x : a} -> {x' : b} -> {l : List a} -> {l' : List b} ->
  (y : c x x') -> ListPairForAll c l l' -> ListPairForAll c (x :: l) (x' :: l')
(~:::) = ListPairForAllCons

public export
(~^) : {a : Type} -> {b : a -> Type} -> {x : a} -> {l : List a} ->
    b x -> ListExists b (x :: l)
(~^) = ListExistsHead

infixl 30 ~::
public export
(~$) : {a : Type} -> {b : a -> Type} -> {x : a} -> {l : List a} ->
    ListExists b l -> ListExists b (x :: l)
(~$) = ListExistsTail

public export
NonEmptyList : Type -> Type
NonEmptyList atom = (atom, List atom)

public export
neListMap : {0 a, b : Type} -> (a -> b) -> NonEmptyList a -> NonEmptyList b
neListMap f (x, l) = (f x, map f l)

public export
Functor NonEmptyList where
  map = neListMap

public export
typeProduct : List Type -> Type
typeProduct = foldr Pair ()

public export
typeCoproduct : List Type -> Type
typeCoproduct = foldr Either Void
