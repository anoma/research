module RefinedSExp.Old.Test.PatternedSExpressionsTest

import RefinedSExp.Old.PatternedSExpressions

%default total

NatOrStringPat : Pattern PrimitiveType
NatOrStringPat = (#|) [ NatPat , StringPat ]

PairNatOrStringPat : Pattern PrimitiveType
PairNatOrStringPat = (#*) [ NatOrStringPat , NatOrStringPat ]

LocationAnnotation : Pattern PrimitiveType
LocationAnnotation = NatPat

PairWithLocation : Pattern PrimitiveType
PairWithLocation = (#*) [ PairNatOrStringPat , LocationAnnotation ]

IsNumericAnnotation : Pattern PrimitiveType
IsNumericAnnotation = BoolPat

LocationAndIsNumericAnnotation : Pattern PrimitiveType
LocationAndIsNumericAnnotation =
  (#*) [ LocationAnnotation , IsNumericAnnotation ]

{-
AnnotatePairNatOrStringPatWithLocation :
  Transformer PairNatOrStringPat PairWithLocation
AnnotatePairNatOrStringPatWithLocation matchedList = case matchedList of
  (_ ** ListPairForAllEmpty)
    impossible
  (_ ** (ListPairForAllCons _ ListPairForAllEmpty))
    impossible
  ([ left, right ] **
   (ListPairForAllCons leftMatches
    (ListPairForAllCons rightMatches ListPairForAllEmpty))) =>
      ?AnnotatePairNatOrStringPatWithLocation_hole
  (_ **(ListPairForAllCons _ (ListPairForAllCons _ (ListPairForAllCons _ _))))
    impossible
-}
