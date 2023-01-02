module RefinedSExp.RefinedSExp

import public Library.Decidability
import public RefinedSExp.SExp

%default total

public export
PureSExpRefinement : Type -> Type
PureSExpRefinement atom = SExp atom -> Bool

public export
PureSExpIsRefined : {atom : Type} -> PureSExpRefinement atom -> SPred atom
PureSExpIsRefined refinement x = IsTrue $ refinement x

public export
RespectsEndpoints : {atom, atom' : Type} ->
  (domain : PureSExpRefinement atom) ->
  (codomain : PureSExpRefinement atom') ->
  (f : SExp atom -> SExp atom') ->
  Type
RespectsEndpoints {atom} {atom'} domain codomain f = (x : SExp atom) ->
  PureSExpIsRefined domain x -> PureSExpIsRefined codomain (f x)

public export
SExpRefinementInContext : Type -> Type -> Type
SExpRefinementInContext atom context = SExp atom -> context -> Bool

public export
SExpIsRefinedInContext : {atom, context : Type} ->
  SExpRefinementInContext atom context -> SExp atom -> context -> Type
SExpIsRefinedInContext refinement x context = IsTrue $ refinement x context
