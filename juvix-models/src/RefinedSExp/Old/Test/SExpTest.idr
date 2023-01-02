module RefinedSExp.Old.Test.SExpTest

import public RefinedSExp.Old.SExp
import public RefinedSExp.Old.Test.TestLibrary

%default total

public export
sexpShows : {atom : Type} -> (showAtom : atom -> String) ->
  (SExp atom -> String, SList atom -> List String)
sexpShows showAtom =
  sexpNonDepListFolds
    (SExpNonDepListFoldArgs
      (\a, l, s => case l of
        [] => "$(" ++ showAtom a ++ ")"
        _ => "$(" ++ showAtom a ++ ":" ++
          (foldl Prelude.Types.String.(++) "" s) ++ ")\n"))

public export
Show atom => Show (SExp atom) where
  show x = show' x where
    show' : SExp atom -> String
    show' x = case x of (a $: _) => fst (sexpShows show) x

NSExp : Type
NSExp = SExp Nat

NSList : Type
NSList = SList Nat

NSCons : Nat -> NSList -> NSExp
NSCons = SCons

NSNil : NSList
NSNil = SNil

NSLCons : NSExp -> NSList -> NSList
NSLCons = SLCons

NSAtom : Nat -> NSExp
NSAtom = SAtom

ns0 : NSExp
ns0 = $^ 0

ns1 : NSExp
ns1 = $^ 1

ns2 : NSExp
ns2 = $^ 2

ns0_1 : NSExp
ns0_1 = 0 $: ns1 $+ NSNil

ns0_1' : NSExp
ns0_1' = 0 $:| ns1

notationTest : 0 $: $^ 1 $+ ($|) = 0 $^^ 1
notationTest = Refl

bigNotationTest : SExp Nat
bigNotationTest =
  0 $:
  (1 $: 2 $:^ 3) $+
  (4 $: 5 $^+ (6 $: 7 $^+ (8 $: 9 $:^ 10) $+^ 11) $+ 12 $:^ 13) $+
  14 $^+
  15 $^+
  (16 $: 17 $:^ 18) $+
  (19 $^^ 20) $+^
  21

bigNotationTestCheck :
  0 $:
  (1 $: 2 $:^ 3) $+
  (4 $: 5 $^+ (6 $: 7 $^+ (8 $: 9 $:^ 10) $+^ 11) $+ 12 $:^ 13) $+
  14 $^+
  15 $^+
  (16 $: 17 $:^ 18) $+
  (19 $^^ 20) $+^
  21 =
  NSCons 0
  (NSLCons
    (NSCons 1
    (NSLCons (NSAtom 2)
    (NSLCons (NSAtom 3)
    NSNil)))
  (NSLCons
    (NSCons 4
    (NSLCons (NSAtom 5)
    (NSLCons
      (NSCons 6
      (NSLCons (NSAtom 7)
      (NSLCons
        (NSCons 8 (NSLCons (NSAtom 9) (NSLCons (NSAtom 10) NSNil)))
      (NSLCons (NSAtom 11)
      NSNil))))
    (NSLCons (NSAtom 12)
    (NSLCons (NSAtom 13)
    NSNil)))))
  (NSLCons
    (NSCons 14 NSNil)
  (NSLCons (NSAtom 15)
  (NSLCons
    (NSCons 16
    (NSLCons (NSAtom 17) (NSLCons (NSAtom 18) (NSNil))))
  (NSLCons (NSCons 19 (NSLCons (NSAtom 20) NSNil))
  (NSLCons (NSAtom 21)
  NSNil)))))))
bigNotationTestCheck = Refl

TestSExp : Type
TestSExp = SExp PrimitiveExp

TestSList : Type
TestSList = SList PrimitiveExp

nilNotationTest : SList Nat
nilNotationTest = ($|)

testShowTestSExp : TestSExp
testShowTestSExp = $^ (PrimTypeBool ** True)

export
sExpTests : IO ()
sExpTests = do
  -- printLn nilNotationTest
  -- printLn bigNotationTest
  -- printLn testShowTestSExp
  pure ()
