module RefinedSExp.Old.DependentADT

import RefinedSExp.Old.RefinedSExp

%default total

record ADTGroupSignature where
  constructor MkADTGroupSignature
  NumADTsInGroup : Nat

prefix 11 $$
data WithKeywords : Type -> Type where
  ($$) : {symbol : Type} -> symbol -> WithKeywords symbol
  WKADT : {symbol : Type} -> WithKeywords symbol
  WKFunc : {symbol : Type} -> WithKeywords symbol
