module RefinedSExp.ComputableFunctions

import Library.FunctionsAndRelations
import Library.Decidability
import RefinedSExp.SExp
import Category.ComputableCategories

%default total

-------------------------
---- Representations ----
-------------------------

public export
data ComputableAtom : Type where
  -- | The initial object of the Substitution category (type system).
  CASVoid : ComputableAtom

  -- | The unique morphism from the initial object to a given object.
  CASFromVoid : ComputableAtom

  -- | The terminal object of the Substitution category.
  CASUnit : ComputableAtom

  -- | The unique morphism to the terminal object from a given object.
  CASToUnit : ComputableAtom

  -- | The unique term of the type interpretation of the terminal object.
  CASUnitTerm : ComputableAtom

  -- | The universal product type in the substitution category.
  CASProduct : ComputableAtom

  -- | Product introduction in the substitution category.
  CASProductIntro : ComputableAtom

  -- | Product elimination in the substitution category.
  CASProductElimLeft : ComputableAtom
  CASProductElimRight : ComputableAtom

  -- | A term of the type interpretation of a product object.
  CASPair : ComputableAtom

  -- | The universal coproduct type in the substitution category.
  CASCoproduct : ComputableAtom

  -- | Coproduct introduction in the substitution category.
  CASCoproductIntroLeft : ComputableAtom
  CASCoproductIntroRight : ComputableAtom

  -- | Coproduct elimination in the substitution category.
  CASCoproductElim : ComputableAtom

  -- | A term of the type interpretation of a coproduct object.
  CASLeft : ComputableAtom
  CASRight : ComputableAtom

  -- | The identity morphism for a given object.
  CASIdentity : ComputableAtom

  -- | Composition of morphisms.
  CASCompose : ComputableAtom

  -- | The type of atoms in the substitution category.
  AtomType : ComputableAtom

  -- | Atom introduction in the substitution category.
  AtomIntro : ComputableAtom

  -- | Atom elimination:  a decidable equality test.
  AtomElim : ComputableAtom

  -- | Terms in the interpretation of the atom type.
  AtomTerm : ComputableAtom

  -- | Terms in the interpretation of the list type.
  SListTermNil : ComputableAtom
  SListTermCons : ComputableAtom

  -- | Terms in the interpretation of the expression type.
  SExpTerm : ComputableAtom

  -- | The type of SList in the substitution category.
  SListType : ComputableAtom

  -- | SList introduction.
  SListIntroNil : ComputableAtom
  SListIntroCons : ComputableAtom

  -- | SList elimination.  Takes two cases, nil and cons.
  SListElim : ComputableAtom

  -- | The type of SExp in the substitution category.
  SExpType : ComputableAtom

  -- | SExp introduction.  Takes a pair of atom and list.
  SExpIntro : ComputableAtom

  -- | SExp elimination.  Takes a function whose parameter is a pair of atom
  -- | and list.
  SExpElim : ComputableAtom

public export
computableAtomToString : ComputableAtom -> String
computableAtomToString CASVoid = "SVoid"
computableAtomToString CASFromVoid = "SFromVoid"
computableAtomToString CASUnit = "SUnit"
computableAtomToString CASToUnit = "SToUnit"
computableAtomToString CASUnitTerm = "SUnitTerm"
computableAtomToString CASProduct = "SProduct"
computableAtomToString CASProductIntro = "SProductIntro"
computableAtomToString CASProductElimLeft = "SProductElimLeft"
computableAtomToString CASProductElimRight = "SProductElimRight"
computableAtomToString CASPair = "SPair"
computableAtomToString CASCoproduct = "SCoproduct"
computableAtomToString CASCoproductIntroLeft = "SCoproductIntroLeft"
computableAtomToString CASCoproductIntroRight = "SCoproductIntroRight"
computableAtomToString CASCoproductElim = "SCoproductElim"
computableAtomToString CASLeft = "SLeft"
computableAtomToString CASRight = "SRight"
computableAtomToString CASIdentity = "SIdentity"
computableAtomToString CASCompose = "SCompose"
computableAtomToString AtomType = "AtomType"
computableAtomToString AtomIntro = "AtomIntro"
computableAtomToString AtomElim = "AtomElim"
computableAtomToString SListType = "SListType"
computableAtomToString SListIntroNil = "SListIntroNil"
computableAtomToString SListIntroCons = "SListIntroCons"
computableAtomToString SListElim = "SListElim"
computableAtomToString SExpType = "SExpType"
computableAtomToString SExpIntro = "SExpIntro"
computableAtomToString SExpElim = "SExpElim"
computableAtomToString AtomTerm = "AtomTerm"
computableAtomToString SListTermNil = "SListTermNil"
computableAtomToString SListTermCons = "SListTermCons"
computableAtomToString SExpTerm = "SExpTerm"

public export
Show ComputableAtom where
  show a = ":" ++ computableAtomToString a

public export
caEncode : ComputableAtom -> Nat
caEncode CASVoid = 0
caEncode CASFromVoid = 1
caEncode CASUnit = 2
caEncode CASToUnit = 3
caEncode CASUnitTerm = 4
caEncode CASProduct = 5
caEncode CASProductIntro = 6
caEncode CASProductElimLeft = 7
caEncode CASProductElimRight = 8
caEncode CASPair = 9
caEncode CASCoproduct = 10
caEncode CASCoproductIntroLeft = 11
caEncode CASCoproductIntroRight = 12
caEncode CASCoproductElim = 13
caEncode CASLeft = 14
caEncode CASRight = 15
caEncode CASIdentity = 16
caEncode CASCompose = 17
caEncode AtomType = 18
caEncode AtomIntro = 19
caEncode AtomElim = 20
caEncode SListType = 21
caEncode SListIntroNil = 22
caEncode SListIntroCons = 23
caEncode SListElim = 24
caEncode SExpType = 25
caEncode SExpIntro = 26
caEncode SExpElim = 27
caEncode AtomTerm = 28
caEncode SListTermNil = 29
caEncode SListTermCons = 30
caEncode SExpTerm = 31

public export
caDecode : Nat -> ComputableAtom
caDecode 0 = CASVoid
caDecode 1 = CASFromVoid
caDecode 2 = CASUnit
caDecode 3 = CASToUnit
caDecode 4 = CASUnitTerm
caDecode 5 = CASProduct
caDecode 6 = CASProductIntro
caDecode 7 = CASProductElimLeft
caDecode 8 = CASProductElimRight
caDecode 9 = CASPair
caDecode 10 = CASCoproduct
caDecode 11 = CASCoproductIntroLeft
caDecode 12 = CASCoproductIntroRight
caDecode 13 = CASCoproductElim
caDecode 14 = CASLeft
caDecode 15 = CASRight
caDecode 16 = CASIdentity
caDecode 17 = CASCompose
caDecode 18 = AtomType
caDecode 19 = AtomIntro
caDecode 20 = AtomElim
caDecode 21 = SListType
caDecode 22 = SListIntroNil
caDecode 23 = SListIntroCons
caDecode 24 = SListElim
caDecode 25 = SExpType
caDecode 26 = SExpIntro
caDecode 27 = SExpElim
caDecode 28 = AtomTerm
caDecode 29 = SListTermNil
caDecode 30 = SListTermCons
caDecode 31 = SExpTerm
caDecode _ = CASVoid

export
caDecodeIsLeftInverse :
  IsLeftInverseOf ComputableFunctions.caEncode ComputableFunctions.caDecode
caDecodeIsLeftInverse CASVoid = Refl
caDecodeIsLeftInverse CASFromVoid = Refl
caDecodeIsLeftInverse CASUnit = Refl
caDecodeIsLeftInverse CASToUnit = Refl
caDecodeIsLeftInverse CASUnitTerm = Refl
caDecodeIsLeftInverse CASProduct = Refl
caDecodeIsLeftInverse CASProductIntro = Refl
caDecodeIsLeftInverse CASProductElimLeft = Refl
caDecodeIsLeftInverse CASProductElimRight = Refl
caDecodeIsLeftInverse CASPair = Refl
caDecodeIsLeftInverse CASCoproduct = Refl
caDecodeIsLeftInverse CASCoproductIntroLeft = Refl
caDecodeIsLeftInverse CASCoproductIntroRight = Refl
caDecodeIsLeftInverse CASCoproductElim = Refl
caDecodeIsLeftInverse CASLeft = Refl
caDecodeIsLeftInverse CASRight = Refl
caDecodeIsLeftInverse CASIdentity = Refl
caDecodeIsLeftInverse CASCompose = Refl
caDecodeIsLeftInverse AtomType = Refl
caDecodeIsLeftInverse AtomIntro = Refl
caDecodeIsLeftInverse AtomElim = Refl
caDecodeIsLeftInverse SListType = Refl
caDecodeIsLeftInverse SListIntroNil = Refl
caDecodeIsLeftInverse SListIntroCons = Refl
caDecodeIsLeftInverse SListElim = Refl
caDecodeIsLeftInverse SExpType = Refl
caDecodeIsLeftInverse SExpIntro = Refl
caDecodeIsLeftInverse SExpElim = Refl
caDecodeIsLeftInverse AtomTerm = Refl
caDecodeIsLeftInverse SListTermNil = Refl
caDecodeIsLeftInverse SListTermCons = Refl
caDecodeIsLeftInverse SExpTerm = Refl

export
caEncodeIsInjective : IsInjective ComputableFunctions.caEncode
caEncodeIsInjective =
  leftInverseImpliesInjective caEncode {g=caDecode} caDecodeIsLeftInverse

public export
CAInjection : Injection ComputableAtom Nat
CAInjection = (caEncode ** caEncodeIsInjective)

public export
CACountable : Countable
CACountable = (ComputableAtom ** CAInjection)

public export
caDecEq : DecEqPred ComputableAtom
caDecEq = countableEq CACountable

public export
DecEq ComputableAtom where
  decEq = caDecEq

public export
Eq ComputableAtom using decEqToEq where
  (==) = (==)

public export
Ord ComputableAtom where
  a < a' = caEncode a < caEncode a'

public export
ComputableExp : Type
ComputableExp = SExp ComputableAtom

public export
ComputableList : Type
ComputableList = SList ComputableAtom

public export
Show ComputableExp where
  show = fst (sexpShows show)

public export
Show ComputableList where
  show l = "(" ++ snd (sexpShows show) l ++ ")"

public export
csDecEq : DecEqPred ComputableExp
csDecEq = sexpDecEq caDecEq

public export
cslDecEq : DecEqPred ComputableList
cslDecEq = slistDecEq caDecEq

public export
DecEq ComputableExp where
  decEq = csDecEq

public export
DecEq ComputableList where
  decEq = cslDecEq

public export
Eq ComputableExp using decEqToEq where
  (==) = (==)

public export
Ord ComputableExp where
  (<) = sexpLessThan (<)

public export
Ord ComputableList where
  (<) = slistLessThan (<)

------------------------------------------------
---- The category of substitutive functions ----
------------------------------------------------
public export
data SubstitutionType : (representation : ComputableExp) -> Type where
    SVoid : SubstitutionType ($^ CASVoid)
    SUnit : SubstitutionType ($^ CASUnit)
    SProduct : {leftRep, rightRep : ComputableExp} ->
      SubstitutionType leftRep -> SubstitutionType rightRep ->
      SubstitutionType (CASProduct $* [leftRep, rightRep])
    SCoproduct : {leftRep, rightRep : ComputableExp} ->
      SubstitutionType leftRep -> SubstitutionType rightRep ->
      SubstitutionType (CASCoproduct $* [leftRep, rightRep])
    SAtomObject : SubstitutionType ($^ AtomType)
    SListObject : SubstitutionType ($^ SListType)
    SExpObject : SubstitutionType ($^ SExpType)

public export
data SubstitutionMorphism : (representation : ComputableExp) ->
  {domainRep, codomainRep : ComputableExp} ->
  (domain : SubstitutionType domainRep) ->
  (codomain : SubstitutionType codomainRep) ->
  Type where
    SIdentity : {objectRep : ComputableExp} ->
      (object : SubstitutionType objectRep) ->
      SubstitutionMorphism (CASIdentity $* [objectRep]) object object
    SCompose : {aRep, bRep, cRep, leftRep, rightRep : ComputableExp} ->
      {a : SubstitutionType aRep} ->
      {b : SubstitutionType bRep} ->
      {c : SubstitutionType cRep} ->
      SubstitutionMorphism leftRep b c ->
      SubstitutionMorphism rightRep a b ->
      SubstitutionMorphism (CASCompose $* [leftRep, rightRep]) a c
    SFromVoid : {codomainRep : ComputableExp} ->
      (codomain : SubstitutionType codomainRep) ->
      SubstitutionMorphism (CASFromVoid $* [codomainRep]) SVoid codomain
    SToUnit : {domainRep : ComputableExp} ->
      (domain : SubstitutionType domainRep) ->
      SubstitutionMorphism (CASToUnit $* [domainRep]) domain SUnit
    SProductIntro :
      {domainRep, codomainLeftRep, codomainRightRep,
        leftMorphismRep, rightMorphismRep : ComputableExp} ->
      {domain : SubstitutionType domainRep} ->
      {codomainLeft : SubstitutionType codomainLeftRep} ->
      {codomainRight : SubstitutionType codomainRightRep} ->
      SubstitutionMorphism leftMorphismRep domain codomainLeft ->
      SubstitutionMorphism rightMorphismRep domain codomainRight ->
      SubstitutionMorphism
        (CASProductIntro $* [leftMorphismRep, rightMorphismRep])
        domain (SProduct codomainLeft codomainRight)
    SProductElimLeft :
      {domainLeftRep, domainRightRep : ComputableExp} ->
      (domainLeft : SubstitutionType domainLeftRep) ->
      (domainRight : SubstitutionType domainRightRep) ->
      SubstitutionMorphism
        (CASProductElimLeft $* [domainLeftRep, domainRightRep])
        (SProduct domainLeft domainRight) domainLeft
    SProductElimRight :
      {domainLeftRep, domainRightRep : ComputableExp} ->
      (domainLeft : SubstitutionType domainLeftRep) ->
      (domainRight : SubstitutionType domainRightRep) ->
      SubstitutionMorphism
        (CASProductElimRight $* [domainLeftRep, domainRightRep])
        (SProduct domainLeft domainRight) domainRight
    SCoproductIntroLeft :
      {codomainLeftRep, codomainRightRep : ComputableExp} ->
      (codomainLeft : SubstitutionType codomainLeftRep) ->
      (codomainRight : SubstitutionType codomainRightRep) ->
      SubstitutionMorphism
        (CASCoproductIntroLeft $* [codomainLeftRep, codomainRightRep])
        codomainLeft (SCoproduct codomainLeft codomainRight)
    SCoproductIntroRight :
      {codomainLeftRep, codomainRightRep : ComputableExp} ->
      (codomainLeft : SubstitutionType codomainLeftRep) ->
      (codomainRight : SubstitutionType codomainRightRep) ->
      SubstitutionMorphism
        (CASCoproductIntroRight $* [codomainLeftRep, codomainRightRep])
        codomainRight (SCoproduct codomainLeft codomainRight)
    SCoproductElim :
      {domainLeftRep, domainRightRep, codomainRep,
        leftMorphismRep, rightMorphismRep : ComputableExp} ->
      {domainLeft : SubstitutionType domainLeftRep} ->
      {domainRight : SubstitutionType domainRightRep} ->
      {codomain : SubstitutionType codomainRep} ->
      SubstitutionMorphism leftMorphismRep domainLeft codomain ->
      SubstitutionMorphism rightMorphismRep domainRight codomain ->
      SubstitutionMorphism
        (CASCoproductElim $* [leftMorphismRep, rightMorphismRep])
        (SCoproduct domainLeft domainRight) codomain
    SAtomIntro : (atom : ComputableAtom) -> {domainRep : ComputableExp} ->
      (domain : SubstitutionType domainRep) ->
      SubstitutionMorphism (AtomIntro $* [$^ atom]) domain SAtomObject
    SAtomElim :
      {atomRep, atomRep', domainRep, codomainRep, eqRep, neqRep :
        ComputableExp} ->
      {domain : SubstitutionType domainRep} ->
      {codomain : SubstitutionType codomainRep} ->
      (atom : SubstitutionMorphism atomRep domain SAtomObject) ->
      (atom' : SubstitutionMorphism atomRep' domain SAtomObject) ->
      (eq : SubstitutionMorphism eqRep domain codomain) ->
      (neq : SubstitutionMorphism neqRep domain codomain) ->
      SubstitutionMorphism
        (AtomElim $* [atomRep, atomRep', domainRep, codomainRep, eqRep, neqRep])
        domain codomain

public export
data SubstitutionTerm : (representation : ComputableExp) ->
  {typeRep : ComputableExp} -> SubstitutionType typeRep -> Type where
    SUnitTerm : SubstitutionTerm ($^ CASUnitTerm) SUnit
    SPair :
      {leftTypeRep, rightTypeRep, leftTermRep, rightTermRep : ComputableExp} ->
      {leftType : SubstitutionType leftTypeRep} ->
      {rightType : SubstitutionType rightTypeRep} ->
      SubstitutionTerm leftTermRep leftType ->
      SubstitutionTerm rightTermRep rightType ->
      SubstitutionTerm (CASPair $* [leftTermRep, rightTermRep])
        (SProduct leftType rightType)
    SLeft :
      {leftTypeRep, rightTypeRep, leftTermRep : ComputableExp} ->
      {leftType : SubstitutionType leftTypeRep} ->
      {rightType : SubstitutionType rightTypeRep} ->
      SubstitutionTerm leftTermRep leftType ->
      SubstitutionTerm (CASLeft $* [leftTermRep])
        (SCoproduct leftType rightType)
    SRight :
      {leftTypeRep, rightTypeRep, rightTermRep : ComputableExp} ->
      {leftType : SubstitutionType leftTypeRep} ->
      {rightType : SubstitutionType rightTypeRep} ->
      SubstitutionTerm rightTermRep rightType ->
      SubstitutionTerm (CASRight $* [rightTermRep])
        (SCoproduct leftType rightType)
    SAtom : (atom : ComputableAtom) ->
      SubstitutionTerm (AtomTerm $* [$^ atom]) SAtomObject

public export
checkSubstitutionType : (representation : ComputableExp) ->
  Maybe (SubstitutionType representation)
checkSubstitutionType (CASVoid $* []) = Just SVoid
checkSubstitutionType (CASUnit $* []) = Just SUnit
checkSubstitutionType (CASProduct $* [leftRep, rightRep]) =
  case (checkSubstitutionType leftRep, checkSubstitutionType rightRep) of
    (Just leftType, Just rightType) => Just (SProduct leftType rightType)
    _ => Nothing
checkSubstitutionType (CASCoproduct $* [leftRep, rightRep]) =
  case (checkSubstitutionType leftRep, checkSubstitutionType rightRep) of
    (Just leftType, Just rightType) => Just (SCoproduct leftType rightType)
    _ => Nothing
checkSubstitutionType _ = Nothing

public export
checkSubstitutionTypeComplete : {representation : ComputableExp} ->
  (type : SubstitutionType representation) ->
  checkSubstitutionType representation = Just type
checkSubstitutionTypeComplete SVoid = Refl
checkSubstitutionTypeComplete SUnit = Refl
checkSubstitutionTypeComplete (SProduct leftType rightType) =
  rewrite (checkSubstitutionTypeComplete leftType) in
  rewrite (checkSubstitutionTypeComplete rightType) in
  Refl
checkSubstitutionTypeComplete (SCoproduct leftType rightType) =
  rewrite (checkSubstitutionTypeComplete leftType) in
  rewrite (checkSubstitutionTypeComplete rightType) in
  Refl
checkSubstitutionTypeComplete _ = ?checkSubstitutionTypeComplete_hole

public export
checkSubstitutionMorphism : (representation : ComputableExp) ->
  {domainRep, codomainRep : ComputableExp} ->
  (domain : SubstitutionType domainRep) ->
  (codomain : SubstitutionType codomainRep) ->
  Maybe (SubstitutionMorphism representation domain codomain)
checkSubstitutionMorphism
  (CASFromVoid $* [codomainRep']) {codomainRep} SVoid codomain =
    case decEq codomainRep' codomainRep of
      Yes Refl => Just (SFromVoid codomain)
      No _ => Nothing
checkSubstitutionMorphism
  (CASToUnit $* [domainRep']) {domainRep} domain SUnit =
    case decEq domainRep' domainRep of
      Yes Refl => Just (SToUnit domain)
      No _ => Nothing
checkSubstitutionMorphism _ _ _ = Nothing

public export
checkSubstitutionMorphismComplete :
  {representation, domainRep, codomainRep : ComputableExp} ->
  {domain : SubstitutionType domainRep} ->
  {codomain : SubstitutionType codomainRep} ->
  (morphism : SubstitutionMorphism representation domain codomain) ->
  checkSubstitutionMorphism representation domain codomain =
    Just morphism
checkSubstitutionMorphismComplete {codomainRep}
  (SFromVoid {codomainRep} codomain) with (decEqRefl decEq codomainRep)
    checkSubstitutionMorphismComplete {codomainRep}
      (SFromVoid {codomainRep} codomain) | eq = rewrite eq in Refl
checkSubstitutionMorphismComplete {domainRep}
  (SToUnit {domainRep} domain) with (decEqRefl decEq domainRep)
    checkSubstitutionMorphismComplete {domainRep}
      (SToUnit {domainRep} domain) | eq = rewrite eq in Refl
checkSubstitutionMorphismComplete (SProductIntro leftMorphism rightMorphism) =
  ?checkSubstitutionMorphismComplete_hole_product_intro
checkSubstitutionMorphismComplete (SProductElimLeft leftType rightType) =
  ?checkSubstitutionMorphismComplete_hole_product_elim_left
checkSubstitutionMorphismComplete (SProductElimRight leftType rightType) =
  ?checkSubstitutionMorphismComplete_hole_product_elim_right
checkSubstitutionMorphismComplete (SCoproductIntroLeft leftType rightType) =
  ?checkSubstitutionMorphismComplete_hole_coproduct_intro_left
checkSubstitutionMorphismComplete (SCoproductIntroRight leftType rightType) =
  ?checkSubstitutionMorphismComplete_hole_coproduct_intro_right
checkSubstitutionMorphismComplete (SCoproductElim leftMorphism rightMorphism) =
  ?checkSubstitutionMorphismComplete_hole_coproduct_elim
checkSubstitutionMorphismComplete _ =
  ?checkSubstitutionMorphismComplete_hole_other

public export
checkSubstitutionTerm : (representation : ComputableExp) ->
  {typeRep : ComputableExp} -> (type : SubstitutionType typeRep) ->
  Maybe (SubstitutionTerm representation type)
checkSubstitutionTerm (CASUnitTerm $* []) SUnit = Just SUnitTerm
checkSubstitutionTerm (CASPair $* [leftTermRep, rightTermRep])
  (SProduct leftType rightType) =
    case (checkSubstitutionTerm leftTermRep leftType,
          checkSubstitutionTerm rightTermRep rightType) of
      (Just leftTerm, Just rightTerm) => Just (SPair leftTerm rightTerm)
      _ => Nothing
checkSubstitutionTerm (CASLeft $* [leftTermRep])
  (SCoproduct leftType rightType) =
    case checkSubstitutionTerm leftTermRep leftType of
      Just leftTerm => Just (SLeft leftTerm)
      _ => Nothing
checkSubstitutionTerm (CASRight $* [rightTermRep])
  (SCoproduct leftType rightType) =
    case checkSubstitutionTerm rightTermRep rightType of
      Just rightTerm => Just (SRight rightTerm)
      _ => Nothing
checkSubstitutionTerm _ _ = Nothing

public export
checkSubstitutionTermComplete : {representation, typeRep : ComputableExp} ->
  (term : SubstitutionTerm representation type) ->
  checkSubstitutionTerm representation type = Just term
checkSubstitutionTermComplete SUnitTerm = Refl
checkSubstitutionTermComplete (SPair leftTerm rightTerm) =
  ?checkSubstitutionTermComplete_hole_pair
checkSubstitutionTermComplete (SLeft leftTerm) =
  ?checkSubstitutionTermComplete_hole_left
checkSubstitutionTermComplete (SRight rightTerm) =
  ?checkSubstitutionTermComplete_hole_right
checkSubstitutionTermComplete _ = ?checkSubstitutionTermComplete_hole

----------------------------------------------------------------------
---- The interpretation into Idris-2 of the substitutive category ----
----------------------------------------------------------------------
public export
interpretSubstitutionType : {representation : ComputableExp} ->
  SubstitutionType representation -> Type
interpretSubstitutionType SVoid = Void
interpretSubstitutionType SUnit = ()
interpretSubstitutionType (SProduct left right) =
  (interpretSubstitutionType left, interpretSubstitutionType right)
interpretSubstitutionType (SCoproduct left right) =
  Either (interpretSubstitutionType left) (interpretSubstitutionType right)
interpretSubstitutionType _ = ?interpretSubstitutionType_hole

public export
interpretSubstitutionMorphism :
  {representation, domainRep, codomainRep : ComputableExp} ->
  {domain : SubstitutionType domainRep} ->
  {codomain : SubstitutionType codomainRep} ->
  SubstitutionMorphism representation domain codomain ->
  interpretSubstitutionType domain -> interpretSubstitutionType codomain
interpretSubstitutionMorphism (SIdentity type) x = x
interpretSubstitutionMorphism (SCompose leftMorphism rightMorphism) x =
  interpretSubstitutionMorphism leftMorphism (
    interpretSubstitutionMorphism rightMorphism x)
interpretSubstitutionMorphism (SFromVoid codomain) v = void v
interpretSubstitutionMorphism (SToUnit domain) _ = ()
interpretSubstitutionMorphism
  (SProductIntro leftMorphism rightMorphism) domainTerm =
    (interpretSubstitutionMorphism leftMorphism domainTerm,
     interpretSubstitutionMorphism rightMorphism domainTerm)
interpretSubstitutionMorphism
  (SProductElimLeft leftType rightType) pairTerm =
    fst pairTerm
interpretSubstitutionMorphism
  (SProductElimRight leftType rightType) pairTerm =
    snd pairTerm
interpretSubstitutionMorphism
  (SCoproductIntroLeft leftType rightType) leftTerm =
    Left leftTerm
interpretSubstitutionMorphism
  (SCoproductIntroRight leftType rightType) rightTerm =
    Right rightTerm
interpretSubstitutionMorphism
  (SCoproductElim leftMorphism rightMorphism) eitherTerm =
    case eitherTerm of
      Left leftTerm => interpretSubstitutionMorphism leftMorphism leftTerm
      Right rightTerm => interpretSubstitutionMorphism rightMorphism rightTerm
interpretSubstitutionMorphism _ _ = ?checkSubstitutionMorphismComplete_hole

public export
interpretSubstitutionTerm :
  {representation, typeRep : ComputableExp} ->
  {type : SubstitutionType typeRep} ->
  SubstitutionTerm representation type ->
  interpretSubstitutionType type
interpretSubstitutionTerm SUnitTerm = ()
interpretSubstitutionTerm (SPair leftTerm rightTerm) =
  (interpretSubstitutionTerm leftTerm, interpretSubstitutionTerm rightTerm)
interpretSubstitutionTerm (SLeft leftTerm) =
  Left $ interpretSubstitutionTerm leftTerm
interpretSubstitutionTerm (SRight rightTerm) =
  Right $ interpretSubstitutionTerm rightTerm
interpretSubstitutionTerm _ = ?interpretSubstitutionTerm_hole

-----------------------------------------------------
---- Term reduction in the substitutive category ----
-----------------------------------------------------
public export
bigStepSubstitution : {representation, typeRep : ComputableExp} ->
  {type : SubstitutionType typeRep} ->
  SubstitutionTerm representation type ->
  SubstitutionTerm representation type
bigStepSubstitution SUnitTerm = SUnitTerm
bigStepSubstitution (SPair leftTerm rightTerm) =
  SPair (bigStepSubstitution leftTerm) (bigStepSubstitution rightTerm)
bigStepSubstitution (SLeft leftTerm) =
  SLeft (bigStepSubstitution leftTerm)
bigStepSubstitution (SRight rightTerm) =
  SRight (bigStepSubstitution rightTerm)
bigStepSubstitution _ = ?bigStepSubstitution_hole

public export
bigStepSubstitutionCorrect : {representation, typeRep : ComputableExp} ->
  {type : SubstitutionType typeRep} ->
  (term : SubstitutionTerm representation type) ->
  interpretSubstitutionTerm (bigStepSubstitution term) =
    interpretSubstitutionTerm term
bigStepSubstitutionCorrect SUnitTerm = Refl
bigStepSubstitutionCorrect (SPair leftTerm rightTerm) =
  rewrite bigStepSubstitutionCorrect leftTerm in
  rewrite bigStepSubstitutionCorrect rightTerm in
  Refl
bigStepSubstitutionCorrect (SLeft leftTerm) =
  ?bigStepSubstitutionCorrect_hole_left
bigStepSubstitutionCorrect (SRight rightTerm) =
  ?bigStepSubstitutionCorrect_hole_right
bigStepSubstitutionCorrect _ = ?bigStepSubstitutionCorrect_hole

public export
bigStepSubstitutionIdempotent : {representation, typeRep : ComputableExp} ->
  {type : SubstitutionType typeRep} ->
  (term : SubstitutionTerm representation type) ->
  bigStepSubstitution (bigStepSubstitution term) = bigStepSubstitution term
bigStepSubstitutionIdempotent SUnitTerm = Refl
bigStepSubstitutionIdempotent (SPair leftTerm rightTerm) =
  rewrite bigStepSubstitutionIdempotent leftTerm in
  rewrite bigStepSubstitutionIdempotent rightTerm in
  Refl
bigStepSubstitutionIdempotent (SLeft leftTerm) =
  ?bigStepSubstitutionIdempotent_hole_left
bigStepSubstitutionIdempotent (SRight rightTerm) =
  ?bigStepSubstitutionIdempotent_hole_right
bigStepSubstitutionIdempotent _ = ?bigStepSubstitutionIdempotent_hole

public export
smallStepSubstitution : {representation, typeRep : ComputableExp} ->
  {type : SubstitutionType typeRep} ->
  SubstitutionTerm representation type ->
  Maybe (SubstitutionTerm representation type)
smallStepSubstitution SUnitTerm = Nothing
smallStepSubstitution (SPair leftTerm rightTerm) =
  case smallStepSubstitution leftTerm of
    Just leftReduced => Just $ SPair leftReduced rightTerm
    Nothing => case smallStepSubstitution rightTerm of
      Just rightReduced => Just $ SPair leftTerm rightReduced
      Nothing => Nothing
smallStepSubstitution (SLeft leftTerm) =
  case smallStepSubstitution leftTerm of
    Just leftReduced => Just $ SLeft leftReduced
    Nothing => Nothing
smallStepSubstitution (SRight rightTerm) =
  case smallStepSubstitution rightTerm of
    Just rightReduced => Just $ SRight rightReduced
    Nothing => Nothing
smallStepSubstitution _ = ?smallStepSubstitution_hole

public export
smallStepSubstitutionCorrect : {representation, typeRep : ComputableExp} ->
  {type : SubstitutionType typeRep} ->
  (original, reduced : SubstitutionTerm representation type) ->
  smallStepSubstitution original = Just reduced ->
  interpretSubstitutionTerm original = interpretSubstitutionTerm reduced
smallStepSubstitutionCorrect SUnitTerm _ Refl impossible
smallStepSubstitutionCorrect (SPair _ _) SUnitTerm Refl impossible
smallStepSubstitutionCorrect
  (SPair leftTerm rightTerm) (SPair leftTerm' rightTerm') just =
    ?smallStepSubstitutionCorrect_hole_pair
smallStepSubstitutionCorrect
  (SLeft leftTerm) _ just =
    ?smallStepSubstitutionCorrect_hole_left
smallStepSubstitutionCorrect
  (SRight rightTerm) _ just =
    ?smallStepSubstitutionCorrect_hole_right
smallStepSubstitutionCorrect _ _ _ = ?smallStepSubstitutionCorrect_hole

public export
bigStepSubstitutionComplete : {representation, typeRep : ComputableExp} ->
  {type : SubstitutionType typeRep} ->
  (term : SubstitutionTerm representation type) ->
  smallStepSubstitution (bigStepSubstitution term) = Nothing
bigStepSubstitutionComplete SUnitTerm = Refl
bigStepSubstitutionComplete (SPair leftTerm rightTerm) =
  ?bigStepSubstitutionComplete_hole_pair
bigStepSubstitutionComplete (SLeft leftTerm) =
  ?bigStepSubstitutionComplete_hole_left
bigStepSubstitutionComplete (SRight rightTerm) =
  ?bigStepSubstitutionComplete_hole_right
bigStepSubstitutionComplete _ = ?bigStepSubstitutionComplete_hole
