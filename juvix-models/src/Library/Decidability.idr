module Library.Decidability

import External.IntegerSquareRoot
import Library.FunctionsAndRelations
import public Data.Fin
import public Decidable.Equality
import public Data.Maybe
import public Data.Nat
import public Data.List

%default total

public export
IsTrue : Bool -> Type
IsTrue b = (b = True)

public export
IsFalse : Bool -> Type
IsFalse b = (b = False)

public export
isYes : {t: Type} -> Dec t -> Bool
isYes (Yes _) = True
isYes (No _) = False

public export
[decEqToEq] DecEq a => Eq a where
  x == x' = isYes $ decEq x x'

public export
IsYes : {type : Type} -> Dec type -> Type
IsYes dec = isYes dec = True

public export
IsYesExtract : {type : Type} -> {dec : Dec type} -> IsYes dec -> type
IsYesExtract {dec=(Yes x)} Refl = x
IsYesExtract {dec=(No _)} Refl impossible

public export
isYesExtract : {type : Type} -> (dec : Dec type) -> isYes dec = True -> type
isYesExtract (Yes x) Refl = x
isYesExtract (No _) Refl impossible

public export
isNoExtract : {type : Type} -> (dec : Dec type) -> isYes dec = False -> Not type
isNoExtract (Yes _) Refl impossible
isNoExtract (No isNo) _ = isNo

export
yesInjective : Yes x = Yes y -> x = y
yesInjective Refl = Refl

public export
DecPred : {A: Type} -> (pred: A -> Type) -> Type
DecPred pred = ((a : A) -> Dec (pred a))

public export
DecEqPred : (a: Type) -> Type
DecEqPred a = (x, x': a) -> Dec (x = x')

public export
decEqBool : {a: Type} -> DecEqPred a -> (x, x' : a) -> Bool
decEqBool deq x x' = isYes (deq x x')

public export
decEqRefl : {a : Type} -> (deq : DecEqPred a) -> (x : a) -> deq x x = Yes Refl
decEqRefl deq x with (deq x x)
  decEqRefl deq x | Yes Refl = Refl
  decEqRefl deq x | No neq = void (neq Refl)

public export
decEqReflYes : {a : Type} -> {deq : DecEqPred a} -> {x : a} ->
  isYes (deq x x) = True
decEqReflYes {deq} {x} with (decEqRefl deq x)
  decEqReflYes {deq} {x} | eq = rewrite eq in Refl

public export
data AreDecEq : {a : Type} -> (deq : DecEqPred a) -> (x, x' : a) -> Type where
  DecEqReturnsYes : {a : Type} -> {deq : DecEqPred a} -> {x, x' : a} ->
    {eq : x = x'} -> deq x x' = Yes eq -> AreDecEq deq x x'

public export
AreDecEqExtract : {a : Type} -> {deq : DecEqPred a} -> {x, x' : a} ->
  AreDecEq deq x x' -> x = x'
AreDecEqExtract (DecEqReturnsYes {eq} _) = eq

export
encodingDecEq : {a, b : Type} ->
  (encode : a -> b) -> (decode : b -> Maybe a) ->
  (encodingIsCorrect : (x : a) -> decode (encode x) = Just x) ->
  (bDecEq : DecEqPred b) ->
  DecEqPred a
encodingDecEq encode decode encodingIsCorrect bDecEq x x' with
  (bDecEq (encode x) (encode x'))
    encodingDecEq encode decode encodingIsCorrect bDecEq x x' | Yes eq = Yes $
      injective $
        trans
          (sym (encodingIsCorrect x))
          (trans
            (cong decode eq)
            (encodingIsCorrect x'))
    encodingDecEq encode decode encodingIsCorrect bDecEq x x' | No neq =
      No $ \xeq => neq $ cong encode xeq

public export
DecidableType : Type
DecidableType = DPair Type DecEqPred

public export
DecidableElem : DecidableType -> Type
DecidableElem type = fst type

public export
DecidablePred : {type : DecidableType} -> DecEqPred (DecidableElem type)
DecidablePred {type} = snd type

public export
listConsEq : {type : Type} -> {x, x' : type} -> {xs, xs' : List type} ->
             x = x' -> xs = xs' -> x :: xs = x' :: xs'
listConsEq elemEq listEq = rewrite elemEq in rewrite listEq in Refl

public export
DecEqList : {type : DecidableType} -> DecEqPred (List (DecidableElem type))
DecEqList [] [] = Yes Refl
DecEqList [] (x :: xs) = No (\eq => case eq of Refl impossible)
DecEqList (x :: xs) [] = No (\eq => case eq of Refl impossible)
DecEqList (x :: xs) (x' :: xs') =
  case (DecidablePred x x', DecEqList xs xs') of
    (Yes elemEq, Yes listEq) => Yes (listConsEq elemEq listEq)
    (No neq, _) => No (\eq => case eq of Refl => neq Refl)
    (_, No neq) => No (\eq => case eq of Refl => neq Refl)

public export
BoolCaseDec : Bool -> Type
BoolCaseDec b = Either (b = True) (b = False)

public export
caseDecFromBool : (b: Bool) -> BoolCaseDec b
caseDecFromBool True = Left Refl
caseDecFromBool False = Right Refl

public export
boolFromCaseDec : {b: Bool} -> BoolCaseDec b -> Bool
boolFromCaseDec bcd = case bcd of
                           Left Refl => True
                           Right Refl => False

public export
boolCaseDecIf : {A, B: Type} -> (b: Bool) ->
  (b = True -> A) -> (b = False -> B) -> if b then A else B
boolCaseDecIf b trueCase falseCase = case caseDecFromBool b of
  Left Refl => trueCase Refl
  Right Refl => falseCase Refl

public export
ifElimination : {t, t', result : Type} ->
  (b : Bool) ->
  (trueCase : b = True -> t -> result) ->
  (falseCase : b = False -> t' -> result) ->
  (test : if b then t else t') ->
  result
ifElimination True trueCase falseCase test = trueCase Refl test
ifElimination False trueCase falseCase test = falseCase Refl test

public export
boolCaseDecEither : (b: Bool) ->
                    {A: (b = True) -> Type} -> {B: (b = False) -> Type} ->
                    ((isTrue: b = True) -> A isTrue) ->
                    ((isFalse: b = False) -> B isFalse) ->
                    Either
                      (isTrue : b = True ** A isTrue)
                      (isFalse : b = False ** B isFalse)
boolCaseDecEither b trueCase falseCase = case caseDecFromBool b of
  Left Refl => Left (Refl ** trueCase Refl)
  Right Refl => Right (Refl ** falseCase Refl)

public export
orElimination : {b, b': Bool} -> IsTrue (b || b') ->
                Either (IsTrue b) (IsTrue b')
orElimination {b=True} {b'=True} Refl = Left Refl
orElimination {b=True} {b'=False} Refl = Left Refl
orElimination {b=False} {b'=True} Refl = Right Refl
orElimination {b=False} {b'=False} Refl impossible

public export
orIntroductionLeft : (b: Bool) -> {b': Bool} -> IsTrue b' -> IsTrue (b || b')
orIntroductionLeft True Refl = Refl
orIntroductionLeft False Refl = Refl

public export
orIntroductionRight : {b: Bool} -> (b': Bool) -> IsTrue b -> IsTrue (b || b')
orIntroductionRight True Refl = Refl
orIntroductionRight False Refl = Refl

public export
andLeft : {b, b': Bool} -> IsTrue (b && b') -> IsTrue b
andLeft {b=True} Refl = Refl

public export
andRight : {b, b': Bool} -> IsTrue (b && b') -> IsTrue b'
andRight {b=True} Refl = Refl

public export
andElimination : {b, b': Bool} -> IsTrue (b && b') ->
                 ((IsTrue b), (IsTrue b'))
andElimination t = (andLeft t, andRight t)

public export
andIntroduction : {b, b': Bool} -> IsTrue b -> IsTrue b' -> IsTrue (b && b')
andIntroduction bTrue bTrue' = case (bTrue, bTrue') of (Refl, Refl) => Refl

public export
andLeftElim : {b, b': Bool} -> (t : IsTrue b) -> (t' : IsTrue b') ->
  andLeft {b} {b'} (andIntroduction {b} {b'} t t') = t
andLeftElim Refl Refl = Refl

public export
andRightElim : {b, b': Bool} -> (t : IsTrue b) -> (t' : IsTrue b') ->
  andRight {b} {b'} (andIntroduction {b} {b'} t t') = t'
andRightElim Refl Refl = Refl

public export
isLeft : {A, B: Type} -> Either A B -> Bool
isLeft (Left _) = True
isLeft (Right _) = False

public export
maybeCase : {a : Type} -> (m: Maybe a) ->
            Either (x : a ** m = Just x) (m = Nothing)
maybeCase (Just x) = Left (x ** Refl)
maybeCase Nothing = Right Refl

public export
maybeElimination : {a, b, c : Type} -> (m: Maybe a) ->
                   (case m of
                     Just x => b
                     Nothing => c) ->
                   Either (x : a ** (m = Just x, b)) (m = Nothing, c)
maybeElimination (Just x) c = Left (x ** (Refl, c))
maybeElimination Nothing c = Right (Refl, c)

public export
maybeMapElimination : {a: Type} ->
                      {ma: Maybe a} -> {ma': a -> Maybe a} -> {x : a} ->
                      (case ma of
                        Just y => ma' y
                        Nothing => Nothing) = Just x ->
                      (z : a ** ma' z = Just x)
maybeMapElimination {ma=(Just y)} eq = (y ** eq)
maybeMapElimination {ma=Nothing} Refl impossible

public export
maybePairElimination : {a, b : Type} -> (ma: Maybe a) -> (mb: Maybe b) ->
                       Either (p : (a, b) **
                                   (ma = Just (fst p), mb = Just (snd p)))
                              (Either (ma = Nothing) (mb = Nothing))
maybePairElimination (Just x) (Just y) = Left ((x, y) ** (Refl, Refl))
maybePairElimination Nothing _ = Right (Left Refl)
maybePairElimination (Just x) Nothing = Right (Right Refl)

public export
data IsNothing : {a: Type} -> Maybe a -> Type where
  ItIsNothing : {a : Type} -> IsNothing {a} Nothing

public export
IsJustIsTrue : {a : Type} -> (m : Maybe a) -> Type
IsJustIsTrue = IsTrue . isJust

public export
IsJustIsTrueElim : {a : Type} -> {m : Maybe a} -> IsJustIsTrue m -> a
IsJustIsTrueElim {m=(Just x)} Refl = x
IsJustIsTrueElim {m=Nothing} Refl impossible

public export
IsJustIsTrueRefl : {a : Type} -> {x : a} ->
                   (just : IsJustIsTrue (Just x)) ->
                   IsJustIsTrueElim {m=(Just x)} just = x
IsJustIsTrueRefl Refl = Refl

public export
isJustIsTrueDec : {a : Type} -> (m : Maybe a) ->
                  Dec (IsJustIsTrue m)
isJustIsTrueDec (Just _) = Yes Refl
isJustIsTrueDec Nothing = No (\eq => case eq of Refl impossible)

public export
IsJustDec : {a : Type} -> (m : Maybe a) -> Dec (IsJust m)
IsJustDec (Just _) = Yes ItIsJust
IsJustDec Nothing = No (\eq => case eq of ItIsJust impossible)

public export IsJustToTrue : {a : Type} -> {m : Maybe a} -> IsJust m ->
                             IsJustIsTrue m
IsJustToTrue ItIsJust = Refl

public export IsTrueToJust : {a : Type} -> {m : Maybe a} ->
                             IsTrue (isJust m) -> IsJust m
IsTrueToJust {m=(Just _)} Refl = ItIsJust
IsTrueToJust {m=Nothing} Refl impossible

public export EqJustToIsJust : {a : Type} -> {m : Maybe a} -> {x: a} ->
                               m = Just x -> IsJust m
EqJustToIsJust {m=(Just _)} Refl = ItIsJust
EqJustToIsJust {m=(Nothing)} Refl impossible

public export isJustElim : {a : Type} -> {m : Maybe a} ->
                           IsJustIsTrue m -> a
isJustElim {m=(Just x)} Refl = x
isJustElim {m=(Nothing)} Refl impossible

public export isJustElimElim :
  {a : Type} -> {m : Maybe a} -> (just : IsJustIsTrue m) ->
  m = Just (isJustElim {m} just)
isJustElimElim {m=(Just x)} Refl = Refl
isJustElimElim {m=(Nothing)} Refl impossible

public export IsJustElim : {a : Type} -> {m : Maybe a} ->
                           IsJust m -> a
IsJustElim {m=(Just x)} ItIsJust = x
IsJustElim {m=(Nothing)} ItIsJust impossible

public export IsJustElimElim : {a : Type} -> (x : a) ->
                               IsJustElim (ItIsJust {x}) = x
IsJustElimElim _ = Refl

public export
NotPred : {A: Type} -> (p: A -> Type) -> Type
NotPred p = (a: A) -> Not (p a)

public export
NotDec : {A: Type} -> (p: A -> Type) -> Type
NotDec p = Dec (NotPred p)

public export
notDec : {A: Type} -> {pred: A -> Type} -> (p : (a: A) -> Dec (pred a)) ->
         ((a: A) -> Dec (Not (pred a)))
notDec p a = case p a of
  Yes predTrue => No (\notPred => notPred predTrue)
  No predFalse => Yes predFalse

public export
IsGodelNumbering : {type : Type} -> (type -> Nat) -> Type
IsGodelNumbering {type} g = (inv : (Nat -> Maybe type) **
                             ((x : type) -> inv (g x) = Just x))

public export
GodelNumbering : Type -> Type
GodelNumbering type = DPair (type -> Nat) IsGodelNumbering

public export
GodelNumbered : Type
GodelNumbered = DPair Type GodelNumbering

public export
GodelType : GodelNumbered -> Type
GodelType = fst

public export
numberingDecEq : {type : Type} -> GodelNumbering type -> DecEqPred type
numberingDecEq (g ** (inv ** isInverse)) x x' with (decEq (g x) (g x'))
  numberingDecEq (g ** (inv ** isInverse)) x x' | Yes eq =
    let
      invx = isInverse x
      invx' = isInverse x'
      eqx = replace {p=(\y => inv y = Just x)} eq invx
      eqx' = replace {p=(\y => y = Just x')} eqx invx'
    in
    Yes (injective eqx')
  numberingDecEq (g ** (inv ** isInverse)) x x' | No neq =
    No (\eq => case eq of Refl => neq Refl)

public export
godelDecEq : (type : GodelNumbered) -> DecEqPred (fst type)
godelDecEq type = numberingDecEq (snd type)

public export
uip : {a : Type} -> {x, y : a} -> (eq, eq' : x = y) -> eq = eq'
uip Refl Refl = Refl

public export
rewrite_uip : {a : Type} -> {x, y : a} ->
  {p : (eq : x = y) -> Type} ->
  {f : (eq : x = y) -> p eq} ->
  {eq, eq' : x = y} ->
  f eq = f eq'
rewrite_uip {eq} {eq'} = rewrite (uip eq eq') in Refl

export
AreDecEqUnique : {a : Type} -> {deq : DecEqPred a} -> {x, x' : a} ->
  (eq, eq' : AreDecEq deq x x') -> eq = eq'
AreDecEqUnique
  (DecEqReturnsYes {eq=Refl} yes) (DecEqReturnsYes {eq=Refl} yes') =
    cong DecEqReturnsYes (uip yes yes')

public export
IsYesUnique : {type : Type} -> {dec : Dec type} -> (yes, yes' : IsYes dec) ->
  yes = yes'
IsYesUnique yes yes' = uip yes yes'

public export
IsJustUnique : {type : Type} -> {m : Maybe type} -> (just, just' : IsJust m) ->
  just = just'
IsJustUnique ItIsJust ItIsJust = Refl

public export
YesDPairInjective : {a : Type} -> {b : a -> Type} ->
  {dec : (x : a) -> Dec (b x)} ->
  {d, d' : DPair a (\x => IsYes (dec x))} -> fst d = fst d' -> d = d'
YesDPairInjective =
  UniqueHeterogeneousDPairInjective (\_, yes, yes' => IsYesUnique yes yes')

public export
JustDPairInjective : {a : Type} -> {b : a -> Type} ->
  {dec : (x : a) -> Maybe (b x)} ->
  {d, d' : DPair a (\x => IsJust (dec x))} -> fst d = fst d' -> d = d'
JustDPairInjective =
  UniqueHeterogeneousDPairInjective (\_, just, just' => IsJustUnique just just')

public export
square : Nat -> Nat
square x = x * x

public export
elegantPairing : (Nat, Nat) -> Nat
elegantPairing (x, y) =
  if x < y then
    square y + x
  else
    square x + x + y

public export
elegantPairingInverse : Nat -> (Nat, Nat)
elegantPairingInverse z =
  let
    sqrtz = intSqrt z
    w = minus z (square sqrtz)
  in
  if w < sqrtz then (w, sqrtz) else (sqrtz, minus w sqrtz)

public export
DepEither : {a : Type} -> (b, c : a -> Type) -> a -> Type
DepEither {a} b c = \x : a => Either (b x) (c x)

public export
PiEither : {a : Type} -> (b, c : a -> Type) -> Type
PiEither {a} b c = a ~> DepEither b c

public export
DepLeft : {a : Type} -> {b, c : a -> Type} -> {x : a} -> b x -> DepEither b c x
DepLeft bx = Left bx

public export
DepRight : {a : Type} -> {b, c : a -> Type} -> {x : a} -> c x -> DepEither b c x
DepRight cx = Right cx

public export
DPairEither : {a : Type} -> (b, c : a -> Type) -> Type
DPairEither {a} b c = Either (DPair a b) (DPair a c)

infixr 4 **<
(**<) : {a : Type} -> {b, c : a -> Type} -> (x : a) -> b x ->
  DPairEither b c
x **< bx = Left (x ** bx)

infixr 4 **>
(**>) : {a : Type} -> {b, c : a -> Type} -> (x : a) -> c x ->
  DPairEither b c
x **> cx = Right (x ** cx)

public export
data IsLeft : {a, b : Type} -> Either a b -> Type where
  ItIsLeft : {a, b : Type} -> {x : a} -> IsLeft (Left x)

public export
data IsRight : {a, b : Type} -> Either a b -> Type where
  ItIsRight : {a, b : Type} -> {x : a} -> IsRight (Right x)

public export
NotLeftAndRight : {a, b : Type} -> {e : Either a b} ->
  IsLeft e -> IsRight e -> Void
NotLeftAndRight e e' =
  case e of ItIsLeft {x} => case e' of ItIsRight {x} impossible

public export
IsLeftElim : {A, B: Type} -> {x : Either A B} -> IsLeft x -> A
IsLeftElim {x=(Left x')} ItIsLeft = x'
IsLeftElim {x=(Right _)} ItIsLeft impossible

public export
certifiedMaybeToMaybe : {0 a, b : Type} ->
  (inverse : b -> a) ->
  ((x : a) -> Maybe (y : b ** inverse y = x)) ->
  (x : a) -> Maybe b
certifiedMaybeToMaybe _ certified x = map fst $ certified x

public export
certifiedMaybeToCorrectness : {0 a, b : Type} ->
  (inverse : b -> a) ->
  (certified : (x : a) -> Maybe (y : b ** inverse y = x)) ->
  (x : a) -> (y : b) ->
  certifiedMaybeToMaybe inverse certified x = Just y -> inverse y = x
certifiedMaybeToCorrectness _ certified x y isjust with (certified x)
  certifiedMaybeToCorrectness _ certified x y Refl | Just (_ ** correct) =
    correct
  certifiedMaybeToCorrectness _ certified x y ItIsJust | Nothing impossible

public export
maybeToEither : {0 a : Type} -> Maybe a -> Either a ()
maybeToEither (Just x) = Left x
maybeToEither Nothing = Right ()

public export
eitherToMaybe : {0 a : Type} -> Either a () -> Maybe a
eitherToMaybe (Left x) = Just x
eitherToMaybe (Right ()) = Nothing

public export
eitherToDec : {0 a : Type} -> Either a (Not a) -> Dec a
eitherToDec (Left x) = Yes x
eitherToDec (Right n) = No n

public export
decToEither : {0 a : Type} -> Dec a -> Either a (Not a)
decToEither (Yes y) = Left y
decToEither (No n) = Right n

public export
decToMaybe : {0 a : Type} -> Dec a -> Maybe a
decToMaybe (Yes x) = Just x
decToMaybe (No _) = Nothing

public export
decMapToMaybe : {0 a, b : Type} ->
  {inverse : b -> a} ->
  ((x : a) -> Dec (y : b ** inverse y = x)) ->
  (x : a) -> Maybe b
decMapToMaybe dec x = map fst $ decToMaybe (dec x)

public export
decMapToMaybe_correct : {0 a, b : Type} ->
  {inverse : b -> a} ->
  (dec : ((x : a) -> Dec (y : b ** inverse y = x))) ->
  (x : a) -> (y : b) ->
  decMapToMaybe dec x = Just y -> inverse y = x
decMapToMaybe_correct dec x y isjust with (dec x)
  decMapToMaybe_correct dec x y Refl | Yes (_ ** isyes) =
    isyes
  decMapToMaybe_correct dec x y Refl | No _ impossible

public export
decMapToMaybe_injective : {0 a, b : Type} ->
  {inverse : b -> a} ->
  (dec : ((x : a) -> Dec (y : b ** inverse y = x))) ->
  (inverseCorrect : (y : b) -> decMapToMaybe dec (inverse y) = Just y) ->
  (y, y' : b) -> inverse y = inverse y' ->
  y = y'
decMapToMaybe_injective {a} {b} dec inverseCorrect y y' eq =
  injective $
    trans
      (sym $
        replace {p=(\y'' => decMapToMaybe dec y'' = Just y)}
          eq (inverseCorrect y))
      (inverseCorrect y')

public export
depDecComplete_implies_unique : {0 a : Type} -> {0 b : a -> Type} ->
  (dec : (x : a) -> Dec (b x)) ->
  (complete : {x : a} -> (y : b x) -> dec x = Yes y) ->
  {x : a} -> (y, y' : b x) -> y = y'
depDecComplete_implies_unique dec complete {x} y y' with
  (complete {x} y, complete {x} y')
    depDecComplete_implies_unique dec complete {x} y y' | (c, c') =
      yesInjective $ trans (sym c) c'

public export
eitherIntroLeft : {a, b, c : Type} -> (a -> b) -> (a -> Either b c)
eitherIntroLeft f = Left . f

public export
eitherIntroRight : {a, b, c : Type} -> (a -> c) -> (a -> Either b c)
eitherIntroRight f = Right . f

public export
eitherElim : {a, b, c : Type} -> (a -> c, b -> c) -> Either a b -> c
eitherElim signature either = case either of
  Left x => fst signature x
  Right y => snd signature y

public export
eitherMap : {a, b, c, d : Type} ->
  (a -> c) -> (b -> d) -> Either a b -> Either c d
eitherMap fac fbd either = case either of
  Left x => Left $ fac x
  Right y => Right $ fbd y

public export
applyPairMap : {f : Type -> Type} -> Applicative f => {a, b, c, d : Type} ->
  (f a -> f b) -> (f c -> f d) -> f (a, c) -> f (b, d)
applyPairMap {f} fab fcd fp = applyPair (fab $ map fst fp) (fcd $ map snd fp)

public export
applyDecToEither :
  {f : Type -> Type} -> Monad f => {a, b, c : Type} ->
  (f a -> f b) -> (f (Not a) -> f c) -> f (Dec a) -> f (Either b c)
applyDecToEither {f} fab fnac fda = do
  da <- fda
  case da of
    Yes a => map Left $ fab $ pure a
    No nota => map Right $ fnac $ pure nota

public export
mergeDecNot : {a : Type} -> Either (Dec a) (Not a) -> Dec a
mergeDecNot (Left (Yes a)) = Yes a
mergeDecNot (Left (No notA)) = No notA
mergeDecNot (Right notA) = No notA

public export
natToFinCert : {m, n : Nat} -> m `LT` n -> Fin n
natToFinCert {m=Z} LTEZero impossible
natToFinCert {m=Z} (LTESucc lte) = FZ
natToFinCert {m=(S m')} LTEZero impossible
natToFinCert {m=(S m')} (LTESucc lte) = FS (natToFinCert {m=m'} lte)

public export
noDuplicates : Eq a => List a -> Bool
noDuplicates [] = True
noDuplicates (x :: l) = find (== x) l == Nothing && noDuplicates l

public export
NoDuplicates : Eq a => List a -> Type
NoDuplicates = IsTrue . noDuplicates

public export
noDuplicatesTail : Eq a => {x : a} -> {l : List a} ->
  NoDuplicates (x :: l) -> NoDuplicates l
noDuplicatesTail {l=[]} noDups = Refl
noDuplicatesTail {x} {l=(x' :: l')} noDups with (x' == x)
  noDuplicatesTail {x} {l=(x' :: l')} Refl | True impossible
  noDuplicatesTail {x} {l=(x' :: l')} noDups | False =
    snd $ andElimination noDups
