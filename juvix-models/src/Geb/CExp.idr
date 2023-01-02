module Geb.CExp

import Library.FunctionsAndRelations
import Library.Decidability
import public Data.SortedSet
import public Data.SortedMap
import public Data.DPair

%default total

public export
data Inductivity : Type where
  Finite : Inductivity
  Infinite : Inductivity
  EitherInductivity : Inductivity

public export
data IsNotNecessarilyInfinite : Inductivity -> Type where
  FiniteIsNotNecessarilyInfinite : IsNotNecessarilyInfinite Finite
  EitherIsNotNecessarilyInfinite : IsNotNecessarilyInfinite EitherInductivity

public export
data ValidConsExpInductivity :
  (headExpInductivity, tailExpInductivity, consExpInductivity : Inductivity) ->
  Type where
    AllFinite : ValidConsExpInductivity Finite Finite Finite
    AllInfinite : ValidConsExpInductivity Infinite Infinite Infinite
    EitherExpInductivity :
      {headExpInductivity, tailExpInductivity : Inductivity} ->
      ValidConsExpInductivity
        headExpInductivity tailExpInductivity EitherInductivity

public export
data ValidConsListInductivity :
  (tailListInductivity, consListInductivity : Inductivity) ->
  Type where
    TailFinite : ValidConsListInductivity Finite Finite
    TailInfinite : ValidConsListInductivity Infinite Infinite
    EitherConsInductivity : {tailListInductivity : Inductivity} ->
      ValidConsListInductivity tailListInductivity EitherInductivity

mutual
  public export
  data CExp : Type -> Inductivity -> Inductivity -> Type where
    CNode : {atom : Type} -> {expInductivity, listInductivity : Inductivity} ->
      atom -> CList atom expInductivity listInductivity ->
      CExp atom expInductivity listInductivity

  public export
  data CList : Type -> Inductivity -> Inductivity -> Type where
    CNil : {atom : Type} -> {expInductivity, listInductivity : Inductivity} ->
      {auto expNotInfinite : IsNotNecessarilyInfinite expInductivity} ->
      {auto listNotInfinite : IsNotNecessarilyInfinite tailInductivity} ->
      CList atom expInductivity tailInductivity
    CCons : {headExpInductivity, headListInductivity,
             tailExpInductivity, tailListInductivity,
             consExpInductivity, consListInductivity: Inductivity} ->
      CExp atom headExpInductivity headListInductivity ->
      CList atom tailExpInductivity tailListInductivity ->
      {auto validExpInductivity : ValidConsExpInductivity
        headExpInductivity tailExpInductivity consExpInductivity} ->
      {auto validListInductivity : ValidConsListInductivity
        tailListInductivity consListInductivity} ->
      CList atom consExpInductivity consListInductivity
