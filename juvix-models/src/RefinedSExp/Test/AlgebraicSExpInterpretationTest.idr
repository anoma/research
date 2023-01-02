module RefinedSExp.Test.AlgebraicSExpInterpretationTest

import public RefinedSExp.AlgebraicSExp
import public RefinedSExp.AlgebraicSExpInterpretation
import RefinedSExp.Test.AlgebraicSExpTest
import Library.Test.TestLibrary
import Data.Vect

%default total

identityExp : RefinedSExp
identityExp = RSIdentity

interpretedIdentity : GeneralComputableFunction
interpretedIdentity = interpretClosedRSExp identityExp

helloWorld : RefinedSExp
helloWorld = RSString "helloWorld"

identityIsJust :
  interpretedIdentity AlgebraicSExpInterpretationTest.helloWorld =
  Just AlgebraicSExpInterpretationTest.helloWorld
identityIsJust = Refl

toUnitIsConstant :
  interpretClosedRSExp RSToUnit (RSString "helloWorld") = Just RSUnitTerm
toUnitIsConstant = Refl

sevenIsNatAtom : IsTrue $ isNatAtom $ RSNat 7
sevenIsNatAtom = Refl

sevenIsNotStringAtom : IsFalse $ isStringAtom $ RSNat 7
sevenIsNotStringAtom = Refl

atomZ : RefinedAtom
atomZ = RAString "Z"

expZ : RefinedSExp
expZ = $^ atomZ

atomS : RefinedAtom
atomS = RAString "S"

expS : RefinedSExp
expS = $^ atomS

isStringZ : Refinement
isStringZ = isGivenString "Z"

isStringS : Refinement
isStringS = isGivenString "S"

isStringNatList : ListRefinement
isStringNatList [] = False
isStringNatList [x] = isStringZ x
isStringNatList (x :: x' :: xs) = isStringS x && isStringNatList (x' :: xs)

isStringNat : Refinement
isStringNat (a $* l) = a == RACompose && isStringNatList l

zeroStringNatList : RefinedSList
zeroStringNatList = [expZ]

stringNatList : Nat -> RefinedSList
stringNatList 0 = zeroStringNatList
stringNatList (S n) = expS :: stringNatList n

stringNatExp : Nat -> RefinedSExp
stringNatExp = RSCompose . stringNatList

stringNat8 : RefinedSExp
stringNat8 = stringNatExp 8

corruptedStringNat8 : RefinedSExp
corruptedStringNat8 = RSCompose (RSString "corrupt" :: stringNatList 8)

VectTypeFamily : Type -> TypeFamily
VectTypeFamily a = (Nat ** flip Vect a)

export
algebraicSExpInterpretationTests : IO ()
algebraicSExpInterpretationTests = do
  -- printLn "Begin algebraicSExpInterpretationTests:"
  -- printLn $ "stringNat 8 = " ++ (show $ stringNat8)
  -- printLn $ "stringNat 8 is " ++ (if isStringNat stringNat8 then "a string nat" else "something else")
  -- printLn $ "corruptedStringNat 8 = " ++ (show $ corruptedStringNat8)
  -- printLn $ "corruptedStringNat 8 is " ++ (if isStringNat corruptedStringNat8 then "a string nat" else "something else")
  -- printLn "End algebraicSExpInterpretationTests."
  pure ()
