module RefinedSExp.Old.Match

import public RefinedSExp.Old.OldRefinedSExp
import public Library.Decidability

%default total

mutual
  public export
  sMap : {atom, atom' : Type} -> (atomMap : atom -> atom') ->
    (x : SExp atom) -> SExp atom'
  sMap atomMap (a $: l) = atomMap a $: sListMap atomMap l

  sListMap : {atom, atom' : Type} -> (atomMap : atom -> atom') ->
    (l : SList atom) -> SList atom'
  sListMap _ ($|) = ($|)
  sListMap atomMap (x $+ l) = sMap atomMap x $+ sListMap atomMap l

mutual
  public export
  sSubst : {atom, atom' : Type} -> (exprMap : atom -> atom') ->
    (x : SExp atom) -> SExp atom'
  sSubst exprMap (a $: l) = exprMap a $: sListSubst exprMap l

  sListSubst : {atom, atom' : Type} -> (exprMap : atom -> atom') ->
    (l : SList atom) -> SList atom'
  sListSubst _ ($|) = ($|)
  sListSubst exprMap (x $+ l) = sSubst exprMap x $+ sListSubst exprMap l
