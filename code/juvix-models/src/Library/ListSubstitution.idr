module Library.ListSubstitution

import Category.Category
import Library.Decidability
import Library.List

%default total

public export
AssociationList : (a, b : Type) -> Type
AssociationList a b = List (a, b)

boundElements : {a, b : Type} -> AssociationList a b -> List a
boundElements = map fst

bindingListCases : {a, b : Type} -> AssociationList a b -> List b
bindingListCases = map snd

MapsElement : {a, b : Type} -> AssociationList a b -> a -> Type
MapsElement bl x = ListContains (boundElements bl) x

mapsElement : {a, b : Type} -> (deq : DecEqPred a) ->
  (bl : AssociationList a b) -> (x : a) ->
  Dec (MapsElement bl x)
mapsElement deq bl x = listContains deq (boundElements bl) x

MapsElementDec : {a, b : Type} -> DecEqPred a ->
  AssociationList a b -> a -> Type
MapsElementDec deq bl x = IsYes (mapsElement deq bl x)

associationMap : {a, b : Type} -> {l : AssociationList a b} -> {x : a} ->
  MapsElement l x -> b
associationMap {l} {x} m = listMap l (x ** m)

associationMapList : {a, b : Type} -> (lab : AssociationList a b) ->
  (la : List a) -> ListSuperset (boundElements lab) la -> List b
associationMapList _ [] _ = []
associationMapList lab (x :: la') ListForAllEmpty impossible
associationMapList lab (x :: la') (ListForAllCons containsX includesL) =
  associationMap containsX :: associationMapList lab la' includesL

composeAssociations : {a, b, c : Type} ->
  (lbc : AssociationList b c) -> (lab : AssociationList a b) ->
  ListSuperset (boundElements lbc) (bindingListCases lab) ->
  AssociationList a c
composeAssociations _ [] isSuperset = []
composeAssociations lbc ((x, y) :: lab') forAllSuperset = case forAllSuperset of
  ListForAllEmpty impossible
  ListForAllCons containsX includesTail =>
    (x, associationMap containsX) :: (composeAssociations lbc lab' includesTail)

BindingList : (a, b : Type) -> Type
BindingList a b = AssociationList a (List b)

BindsAllElements : {a, b : Type} -> BindingList a b -> List a -> Type
BindsAllElements bl la = ListSuperset (boundElements bl) la

bindsAllElements : {a, b : Type} -> (deq : DecEqPred a) ->
  (bl : BindingList a b) -> (la : List a) ->
  Dec (BindsAllElements bl la)
bindsAllElements deq bl la = listSuperset deq (boundElements bl) la

BindsAllElementsDec : {a, b : Type} -> DecEqPred a ->
  BindingList a b -> List a -> Type
BindsAllElementsDec deq bl la = IsYes (bindsAllElements deq bl la)

BindsAllElementsDecUnique : {a, b : Type} -> {deq : DecEqPred a} ->
  {bl : BindingList a b} -> {la : List a} ->
  (bindsAll, bindsAll' : BindsAllElementsDec deq bl la) ->
  bindsAll = bindsAll'
BindsAllElementsDecUnique = IsYesUnique

BindingListSubstitutionDomain : {a, b : Type} -> DecEqPred a ->
  BindingList a b -> Type
BindingListSubstitutionDomain deq bl =
  DPair (List a) (BindsAllElementsDec deq bl)

BindingListDomainInjective : {a, b : Type} -> {deq : DecEqPred a} ->
  {bl : BindingList a b} ->
  {dom, dom' : BindingListSubstitutionDomain deq bl} ->
  fst dom = fst dom' ->
  dom = dom'
BindingListDomainInjective {deq} {bl} {dom} =
  YesDPairInjective {dec=(bindsAllElements deq bl)}

finSubstList : {a, b : Type} -> (bl : BindingList a b) -> (la : List a) ->
  BindsAllElements bl la -> List (List b)
finSubstList bl la bindsAll = listForAllInd
  {outputPredicate=(\la', bindsAll' => List (List b))}
  (ListForAllIndHypotheses
    []
    (\x, l, mapsX, bindsAllL, llb => associationMap mapsX :: llb)
  ) la bindsAll

finSubst : {a, b : Type} -> (bl : BindingList a b) -> (la : List a) ->
  BindsAllElements bl la -> List b
finSubst bl la bindsAll = listJoin (finSubstList bl la bindsAll)

bindingSubstIsFinSubst : {a, b : Type} -> (deq : DecEqPred a) ->
  (bl : BindingList a b) -> (la : List a) -> BindsAllElementsDec deq bl la ->
  ListSubset la (boundElements bl)
bindingSubstIsFinSubst deq bl la bindsAll = IsYesExtract bindsAll

bindingSubst : {a, b : Type} -> (deq : DecEqPred a) -> (bl : BindingList a b) ->
  (la : List a) -> BindsAllElementsDec deq bl la -> List b
bindingSubst deq bl la isSubst =
  finSubst bl la (bindingSubstIsFinSubst deq bl la isSubst)

BindingListsCompose : {a, b, c : Type} ->
  (lbc : BindingList b c) -> (lab : BindingList a b) -> Type
BindingListsCompose lbc lab =
  ListForAll (ListSuperset (boundElements lbc)) (bindingListCases lab)

bindingListCompose : {a, b, c : Type} ->
  (lbc : BindingList b c) -> (lab : BindingList a b) ->
  BindingListsCompose lbc lab -> BindingList a c
bindingListCompose _ [] forAllSuperset = []
bindingListCompose lbc ((x, lb) :: lab') forAllSuperset = case forAllSuperset of
  ListForAllEmpty impossible
  ListForAllCons isSuperset forAllSuperset =>
    (x, finSubst lbc lb isSuperset) ::
      bindingListCompose lbc lab' forAllSuperset

SubstitutionArrow : {a, b : Type} -> (deq : DecEqPred a) ->
  (la : List a) -> (lb : List b) -> Type
SubstitutionArrow deq la lb =
  (bl : BindingList a b ** isSubst : BindsAllElementsDec deq bl la **
   bindingSubst deq bl la isSubst = lb)

{- TODO
public export
SubstitutionCategory : Category
SubstitutionCategory = MkCategory
  (a : DecidableType ** List (DecidableElem a))
  (\a, b => SubstitutionArrow
    {a=(DecidableElem (fst a))}
    {b=(DecidableElem (fst b))}
    (DecidablePred {type=(fst a)}) (snd a) (snd b))
  SubstitutionCategory_id
  SubstitutionCategory_compose
  SubstitutionCategory_left_id
  SubstitutionCategory_right_id
  SubstitutionCategory_associative
  -}

public export
HasTypeArrow : {a, b : Type} -> (deq : DecEqPred b) ->
  (la : List a) -> (lb : List b) -> Type
HasTypeArrow {a} {b} deq la lb = SubstitutionArrow {a=b} {b=a} deq lb la

public export
SubstitutionType : Type -> Type
SubstitutionType a = List (List a)

public export
HasSubstitutionType : {a : Type} -> (deq : DecEqPred a) -> SubstitutionType a ->
  List a -> Type
HasSubstitutionType {a} deq stype la = ListExists (HasTypeArrow deq la) stype

{- TODO
public export
SubstitutionMorphism : {a : DecidableType} ->
  (domain, codomain : SubstitutionType (DecidableElem a)) -> Type
SubstitutionMorphism domain codomain =
  SubstitutionMorphism_hole
  -}

CaseStatementWithDefault : (a, b : Type) -> Type
CaseStatementWithDefault a b = (BindingList a b, List b)

finMapDefault : {a, b : Type} -> DecEqPred a ->
  BindingList a b -> List b -> (a -> List b)
finMapDefault deq [] d _ = d
finMapDefault deq ((x, bl) :: bs) d x' = case deq x x' of
  Yes Refl => bl
  No neq => finMapDefault deq bs d x'

caseMap : {a, b : Type} -> DecEqPred a -> CaseStatementWithDefault a b ->
  a -> List b
caseMap deq (bl, d) = finMapDefault deq bl d

{- TODO
caseSubst : {a, b : Type} -> DecEqPred a -> CaseStatementWithDefault a b ->
  List a -> List b
caseSubst deq (bl, d) la = caseSubst_hole

caseSubstCompose : {a, b, c : Type} -> DecEqPred a -> DecEqPred b ->
  CaseStatementWithDefault b c -> CaseStatementWithDefault a b ->
  List a -> List c
caseSubstCompose aDeq bDeq cbc cab =
  (caseSubst bDeq cbc) . (caseSubst aDeq cab)
-}
