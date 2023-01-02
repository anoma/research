module RefinedSExp.AlgebraicSExp

import public Library.FunctionsAndRelations
import public Library.Decidability
import public Library.List
import public Category.ComputableCategories

%default total

mutual
  infixr 7 $*
  public export
  data SExp : (atom : Type) -> Type where
    ($*) : atom -> SList atom -> SExp atom

  public export
  SList : (atom : Type) -> Type
  SList = List . SExp

prefix 11 $^
public export
($^) : {atom : Type} -> atom -> SExp atom
($^) a = a $* []

infixr 7 $^:
public export
($^:) : {atom : Type} -> atom -> SList atom -> SList atom
a $^: l = $^ a :: l

prefix 11 $*^
public export
($*^) : {atom : Type} -> atom -> SList atom
($*^) a = a $^: []

prefix 11 $**
public export
($**) : {atom : Type} -> SExp atom -> SList atom
($**) x = x :: []

infixr 7 $***
public export
($***) : {atom : Type} -> atom -> SExp atom -> SExp atom
a $*** x = a $* $** x

infixr 7 $:*
public export
($:*) : {atom : Type} -> SExp atom -> SExp atom -> SList atom
x $:* x' = x :: $** x'

infixr 7 $:^
public export
($:^) : {atom : Type} -> SExp atom -> atom -> SList atom
x $:^ a = x $:* $^ a

infixr 7 $^^
public export
($^^) : {atom : Type} -> atom -> atom -> SList atom
a $^^ a' = a $^: $*^ a'

infixr 7 $**^
public export
($**^) : {atom : Type} -> atom -> atom -> SExp atom
a $**^ a' = a $* $*^ a'

public export
SPred : (atom : Type) -> Type
SPred atom = !- (SExp atom)

public export
SLPred : (atom : Type) -> Type
SLPred atom = !- (SList atom)

public export
record SExpEliminatorSig
  {atom : Type} (0 sp : SPred atom) (0 lp : SLPred atom)
  where
    constructor SExpEliminatorArgs
    expElim : (a : atom) -> (l : SList atom) -> lp l -> sp (a $* l)
    nilElim : lp []
    consElim : (x : SExp atom) -> (l : SList atom) ->
      sp x -> lp l -> lp (x :: l)

mutual
  public export
  sexpEliminator :
    {atom : Type} -> {0 sp : SPred atom} -> {0 lp : SLPred atom} ->
    (signature : SExpEliminatorSig sp lp) ->
    SExp atom ~> sp
  sexpEliminator signature (a $* l) =
    expElim signature a l (slistEliminator signature l)

  public export
  slistEliminator :
    {atom : Type} -> {0 sp : SPred atom} -> {0 lp : SLPred atom} ->
    (signature : SExpEliminatorSig sp lp) ->
    SList atom ~> lp
  slistEliminator signature [] =
    nilElim signature
  slistEliminator signature (x :: l) =
    consElim signature x l
      (sexpEliminator signature x) (slistEliminator signature l)

public export
sexpEliminators :
  {atom : Type} -> {0 sp : SPred atom} -> {0 lp : SLPred atom} ->
  (signature : SExpEliminatorSig sp lp) ->
  (SExp atom ~> sp, SList atom ~> lp)
sexpEliminators signature =
  (sexpEliminator signature, slistEliminator signature)

public export
sexpShows : {atom : Type} -> (showAtom : atom -> String) ->
  (SExp atom -> String, SList atom -> String)
sexpShows {atom} showAtom =
  sexpEliminators $ SExpEliminatorArgs
    (\a, l, lString => case l of
      [] => showAtom a
      _ :: _ => "(" ++ showAtom a ++ " $* " ++ lString ++ ")")
    ""
    (\_, l, sx, sl => case l of
      [] => sx
      _ :: _ => sx ++ " : " ++ sl)

mutual
  public export
  sexpDecEq :
    {0 atom : Type} -> (aEq : DecEqPred atom) -> DecEqPred (SExp atom)
  sexpDecEq aEq (a $* l) (a' $* l') =
    case (aEq a a', slistDecEq aEq l l') of
      (Yes Refl, Yes Refl) => Yes Refl
      (No aNeq, _) => No $ \eq => case eq of Refl => aNeq Refl
      (_ , No lNeq) => No $ \eq => case eq of Refl => lNeq Refl

  public export
  slistDecEq :
    {0 atom : Type} -> (aEq : DecEqPred atom) -> DecEqPred (SList atom)
  slistDecEq aEq [] [] = Yes Refl
  slistDecEq aEq [] (x :: l) = No $ \eq => case eq of Refl impossible
  slistDecEq aEq (x :: l) [] = No $ \eq => case eq of Refl impossible
  slistDecEq aEq (x :: l) (x' :: l') =
    case (sexpDecEq aEq x x', slistDecEq aEq l l') of
      (Yes Refl, Yes Refl) => Yes Refl
      (No xNeq, _) => No $ \eq => case eq of Refl => xNeq Refl
      (_ , No lNeq) => No $ \eq => case eq of Refl => lNeq Refl

mutual
  data SExpForAll : {0 atom : Type} -> SPred atom -> SPred atom where
    SExpAndList : {pred : SPred atom} -> pred (a $* l) -> SListForAll pred l ->
      SExpForAll pred (a $* l)

  data SListForAll : {0 atom : Type} -> SPred atom -> SLPred atom where
    SForAllNil : {pred : SPred atom} -> SListForAll pred []
    SForAllCons : {pred : SPred atom} ->
      SExpForAll pred x -> SListForAll pred l ->
      SListForAll pred (x :: l)

mutual
  data SExpExists : {0 atom : Type} -> SPred atom -> SPred atom where
    SExpThis : {pred : SPred atom} -> pred x -> SExpExists pred x
    SExpInList : {pred : SPred atom} -> SListExists pred l ->
      SExpExists pred (x $* l)

  data SListExists : {0 atom : Type} -> SPred atom -> SLPred atom where
    SExpHead : {pred : SPred atom} -> SExpExists pred x ->
      SListExists pred (x :: l)
    SExpTail : {pred : SPred atom} -> SListExists pred l ->
      SListExists pred (x :: l)

-- | Names are ways of accesssing the the context; put another way, a context
-- | is an interpretation of names.  Therefore, there is no interpretation
-- | of names outside of the notion of interpreting an S-expression:  for
-- | example, there is no inherent connection between the name "RNNat 5" and
-- | the natural number 5.  The only structure that names have is a decidable
-- | equality.
public export
data RefinedName : Type where
  RNNat : Nat -> RefinedName
  RNString : String -> RefinedName

Show RefinedName where
  show (RNNat n) = show n
  show (RNString s) = s

export
rnDecEq : DecEqPred RefinedName
rnDecEq (RNNat n) (RNNat n') = case decEq n n' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl
rnDecEq (RNNat _) (RNString _) =
  No $ \eq => case eq of Refl impossible
rnDecEq (RNString _) (RNNat _) =
  No $ \eq => case eq of Refl impossible
rnDecEq (RNString s) (RNString s') = case decEq s s' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl

public export
DecEq RefinedName where
  decEq = rnDecEq

public export
data RefinedKeyword : Type where
  RKFailed : RefinedKeyword
  RKWithName : RefinedKeyword
  RKIdentity : RefinedKeyword
  RKCompose : RefinedKeyword
  RKVoid : RefinedKeyword
  RKFromVoid : RefinedKeyword
  RKUnitType : RefinedKeyword
  RKUnitTerm : RefinedKeyword
  RKToUnit : RefinedKeyword

Show RefinedKeyword where
  show RKFailed = "RKFailed"
  show RKIdentity = "RKIdentity"
  show RKCompose = "RKCompose"
  show RKVoid = "RKVoid"
  show RKFromVoid = "RKFromVoid"
  show RKUnitType = "RKUnitType"
  show RKUnitTerm = "RKUnitTerm"
  show RKToUnit = "RKToUnit"
  show RKWithName = "RKWithName"

public export
rkEncode : RefinedKeyword -> Nat
rkEncode RKFailed = 0
rkEncode RKIdentity = 1
rkEncode RKCompose = 2
rkEncode RKVoid = 3
rkEncode RKFromVoid = 4
rkEncode RKUnitType = 5
rkEncode RKUnitTerm = 6
rkEncode RKToUnit = 7
rkEncode RKWithName = 8

public export
rkDecode : Nat -> RefinedKeyword
rkDecode 1 = RKIdentity
rkDecode 2 = RKCompose
rkDecode 3 = RKVoid
rkDecode 4 = RKFromVoid
rkDecode 5 = RKUnitType
rkDecode 6 = RKUnitTerm
rkDecode 7 = RKToUnit
rkDecode 8 = RKWithName
rkDecode _ = RKFailed

export
rkDecodeIsLeftInverse :
  IsLeftInverseOf AlgebraicSExp.rkEncode AlgebraicSExp.rkDecode
rkDecodeIsLeftInverse RKFailed = Refl
rkDecodeIsLeftInverse RKIdentity = Refl
rkDecodeIsLeftInverse RKCompose = Refl
rkDecodeIsLeftInverse RKVoid = Refl
rkDecodeIsLeftInverse RKFromVoid = Refl
rkDecodeIsLeftInverse RKUnitType = Refl
rkDecodeIsLeftInverse RKUnitTerm = Refl
rkDecodeIsLeftInverse RKToUnit = Refl
rkDecodeIsLeftInverse RKWithName = Refl

export
rkEncodeIsInjective : IsInjective AlgebraicSExp.rkEncode
rkEncodeIsInjective =
  leftInverseImpliesInjective rkEncode {g=rkDecode} rkDecodeIsLeftInverse

public export
RKInjection : Injection RefinedKeyword Nat
RKInjection = (rkEncode ** rkEncodeIsInjective)

public export
RKCountable : Countable
RKCountable = (RefinedKeyword ** RKInjection)

public export
rkDecEq : DecEqPred RefinedKeyword
rkDecEq = countableEq RKCountable

public export
DecEq RefinedKeyword where
  decEq = rkDecEq

public export
data RefinedAtom : Type where
  RAKeyword : RefinedKeyword -> RefinedAtom
  RAName : RefinedName -> RefinedAtom

Show RefinedAtom where
  show (RAKeyword k) = show k
  show (RAName n) = show n

public export
raShow : RefinedAtom -> String
raShow = show

public export
raDecEq : DecEqPred RefinedAtom
raDecEq (RAKeyword n) (RAKeyword n') = case decEq n n' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl
raDecEq (RAKeyword _) (RAName _) =
  No $ \eq => case eq of Refl impossible
raDecEq (RAName _) (RAKeyword _) =
  No $ \eq => case eq of Refl impossible
raDecEq (RAName s) (RAName s') = case decEq s s' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl

public export
DecEq RefinedAtom where
  decEq = raDecEq

public export
Eq RefinedAtom using decEqToEq where
  (==) = (==)

public export
RefinedSExp : Type
RefinedSExp = SExp RefinedAtom

public export
RefinedSList : Type
RefinedSList = SList RefinedAtom

public export
Show RefinedSExp where
  show = fst (sexpShows show)

public export
Show RefinedSList where
  show l = "(" ++ snd (sexpShows show) l ++ ")"

public export
rsDecEq : DecEqPred RefinedSExp
rsDecEq = sexpDecEq raDecEq

public export
rslDecEq : DecEqPred RefinedSList
rslDecEq = slistDecEq raDecEq

public export
DecEq RefinedSExp where
  decEq = rsDecEq

public export
DecEq RefinedSList where
  decEq = rslDecEq

public export
RANat : Nat -> RefinedAtom
RANat = RAName . RNNat

public export
RSNat : Nat -> RefinedSExp
RSNat = ($^) . RANat

public export
RAString : String -> RefinedAtom
RAString = RAName . RNString

public export
RSString : String -> RefinedSExp
RSString = ($^) . RAString

public export
atomIsNat : RefinedAtom -> Bool
atomIsNat (RAName (RNNat _)) = True
atomIsNat _ = False

public export
atomIsString : RefinedAtom -> Bool
atomIsString (RAName (RNString _)) = True
atomIsString _ = False

public export
RAFailed : RefinedAtom
RAFailed = RAKeyword RKVoid

public export
RSFailed : RefinedSExp
RSFailed = $^ RAFailed

public export
RAVoid : RefinedAtom
RAVoid = RAKeyword RKVoid

public export
RSVoid : RefinedSExp
RSVoid = $^ RAVoid

public export
RAIdentity : RefinedAtom
RAIdentity = RAKeyword RKIdentity

public export
RSIdentity : RefinedSExp
RSIdentity = $^ RAIdentity

public export
RAFromVoid : RefinedAtom
RAFromVoid = RAKeyword RKFromVoid

public export
RSFromVoid : (codomainRep : RefinedSExp) -> RefinedSExp
RSFromVoid codomainRep = RAFromVoid $*** codomainRep

public export
RAUnitType : RefinedAtom
RAUnitType = RAKeyword RKUnitType

public export
RAUnitTerm : RefinedAtom
RAUnitTerm = RAKeyword RKUnitTerm

public export
RSUnitType : RefinedSExp
RSUnitType = $^ RAUnitType

public export
RSUnitTerm : RefinedSExp
RSUnitTerm = $^ RAUnitTerm

public export
RAToUnit : RefinedAtom
RAToUnit = RAKeyword RKToUnit

public export
RSToUnit : RefinedSExp
RSToUnit = $^ RAToUnit

public export
RACompose : RefinedAtom
RACompose = RAKeyword RKCompose

public export
RSCompose : (functions : RefinedSList) -> RefinedSExp
RSCompose = ($*) RACompose

public export
RAWithName : RefinedAtom
RAWithName = RAKeyword RKWithName

public export
RSWithName : RefinedSExp
RSWithName = $^ RAWithName
