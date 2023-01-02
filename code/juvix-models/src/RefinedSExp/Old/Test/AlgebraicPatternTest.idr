module RefinedSExp.Old.Test.AlgebraicPatternTest

import public RefinedSExp.Old.AlgebraicPattern
import public RefinedSExp.Old.Test.TestLibrary
import Library.Decidability

%default total

TCP : Type
TCP = TypeConstructor PrimitiveType

ADTP : Type
ADTP = ADT PrimitiveType

DTP : Type
DTP = DataType PrimitiveType

TFP : Type
TFP = TypeFamily PrimitiveType

TAtom : Type
TAtom = MAtom interpretPrimitiveType

TBool : Bool -> TAtom
TBool = MPrim {type=PrimTypeBool}

TNat : Nat -> TAtom
TNat = MPrim {type=PrimTypeNat}

TString : String -> TAtom
TString = MPrim {type=PrimTypeString}

TExp : Type
TExp = SExp TAtom

TList : Type
TList = SList TAtom

TCheckResult : TExp -> Type
TCheckResult =
  CheckResult (MatchesTypeInduction primTypeEq interpretPrimitiveType)

TListCheckResult : TList -> Type
TListCheckResult =
  ListCheckResult (MatchesTypeInduction primTypeEq interpretPrimitiveType)

public export
testMatch : (x : TExp) -> TCheckResult x
testMatch = matchSExp primTypeEq interpretPrimitiveType

testListMatch : (x : TList) -> TListCheckResult x
testListMatch = matchSList primTypeEq interpretPrimitiveType

-- Empty constructor
Uc : TCP
Uc = |- []

-- Unit type
Ut : ADTP
Ut = |* [ Uc ]

-- Primitive boolean type
Bt : DTP
Bt = |. PrimTypeBool

public export
primChecks : Bool
primChecks =
  isCheckSuccess (testMatch ($^ (TBool True))) &&
  isCheckSuccess (testMatch ($^ (TBool False))) &&
  isCheckSuccess (testMatch ($^ (TNat 0)))

-- Boolean equivalents without using primitive types
Bta : ADTP
Bta = |* [ Uc, Uc ]

Btd : DTP
Btd = |: Bta

public export
boolChecks : Bool
boolChecks =
  isCheckSuccess (testMatch ($^ (MAbst Bta 0))) &&
  isCheckSuccess (testMatch ($^ (MAbst Bta 1))) &&
  isCheckFailure (testMatch ($^ (MAbst Bta 2))) && -- out-of-bounds constructor
  isCheckFailure (testMatch (MAbst Bta 0 $^^ MAbst Bta 0)) -- extra parameter

-- Primitive natural number
Nt : DTP
Nt = |. PrimTypeNat

-- Primitive string
St : DTP
St = |. PrimTypeString

-- Constructor containing two natural numbers
N2c : TCP
N2c = |- [ |-> Nt , |-> Nt ]

-- Constructor containing one string
Sc : TCP
Sc = |- [ |-> St ]

-- ADT comprising either two natural numbers or one string
N2Sta : ADTP
N2Sta = |* [ N2c , Sc ]

N2Std : DTP
N2Std = |: N2Sta

adtChecks : Bool
adtChecks =
  isCheckFailure (testMatch ($^ (MAbst N2Sta 0)))

adtChecksCorrect : Assertion
adtChecksCorrect = Assert adtChecks

boolChecksCorrect : Assertion
boolChecksCorrect = Assert boolChecks

primChecksCorrect : Assertion
primChecksCorrect = Assert primChecks

-- Test some notation

typeNotationTest : |:* [ Uc, Uc ] = |: (|* [ Uc, Uc ])
typeNotationTest = Refl

getConstructorTest_Bta_0 : Bta |*< 0 = Uc
getConstructorTest_Bta_0 = Refl

getConstructorTest_Bta_1 : Bta |*< 1 = Uc
getConstructorTest_Bta_1 = Refl
