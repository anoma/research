module Datatypes.DependentAlgebraicTypes

import Library.FunctionsAndRelations
import Library.TypesAndFunctions
import public RefinedSExp.List

%default total

mutual
  prefix 11 $^
  prefix 11 $|
  public export
  data SExp : (atom : Type) -> Type where
    ($^) : atom -> SExp atom
    ($|) : SList atom -> SExp atom

  public export
  SList : (atom : Type) -> Type
  SList atom = List (SExp atom)

public export
($-) : {0 atom : Type} -> SExp atom
($-) = $| []

prefix 11 $|-
public export
($|-) : {0 atom : Type} -> SExp atom -> SExp atom
($|-) x = $| [ x ]

prefix 11 $^-
public export
($^-) : {0 atom : Type} -> atom -> SExp atom
($^-) a = $|- $^ a

infix 7 $|:
public export
($|:) : {0 atom : Type} -> SExp atom -> SList atom -> SExp atom
x $|: l = $| (x :: l)

infix 7 $.
public export
($.) : {0 atom : Type} -> SExp atom -> SExp atom -> SExp atom
x $. x' = $| [x, x']

infix 7 $^.
public export
($^.) : {0 atom : Type} -> atom -> SExp atom -> SExp atom
a $^. x' = $^ a $. x'

prefix 11 $^|
public export
($^|) : {0 atom : Type} -> atom -> SList atom
($^|) a = [ $^ a ]

infix 7 $^:
public export
($^:) : {0 atom : Type} -> atom -> SList atom -> SList atom
a $^: l' = $^ a :: l'

infix 7 $^^
public export
($^^) : {0 atom : Type} -> atom -> atom -> SList atom
a $^^ a' = a $^: $^| a'

infix 7 $:^
public export
($:^) : {0 atom : Type} -> atom -> atom -> SExp atom
a $:^ a' = $| (a $^^ a')

public export
SPred : (atom : Type) -> Type
SPred atom = !- (SExp atom)

public export
SLPred : (atom : Type) -> Type
SLPred atom = !- (SList atom)

public export
record SExpEliminatorSig
  {0 atom : Type} (0 sp : SPred atom) (0 lp : SLPred atom)
  where
    constructor SExpEliminatorArgs
    atomElim : (a : atom) -> sp ($^ a)
    listElim : (l : SList atom) -> lp l -> sp ($| l)
    nilElim : lp []
    consElim : (x : SExp atom) -> (l : SList atom) ->
      sp x -> lp l -> lp (x :: l)

mutual
  public export
  sexpEliminator :
    {0 atom : Type} -> {0 sp : SPred atom} -> {0 lp : SLPred atom} ->
    (signature : SExpEliminatorSig sp lp) ->
    SExp atom ~> sp
  sexpEliminator signature ($^ a) =
    atomElim signature a
  sexpEliminator signature ($| l) =
    listElim signature l (slistEliminator signature l)

  public export
  slistEliminator :
    {0 atom : Type} -> {0 sp : SPred atom} -> {0 lp : SLPred atom} ->
    (signature : SExpEliminatorSig sp lp) ->
    SList atom ~> lp
  slistEliminator signature [] =
    nilElim signature
  slistEliminator signature (x :: l) =
    consElim signature x l
      (sexpEliminator signature x) (slistEliminator signature l)

public export
sexpEliminators :
  {0 atom : Type} -> {0 sp : SPred atom} -> {0 lp : SLPred atom} ->
  (signature : SExpEliminatorSig sp lp) ->
  (SExp atom ~> sp, SList atom ~> lp)
sexpEliminators signature =
  (sexpEliminator signature, slistEliminator signature)

public export
record SExpSinglePredEliminatorSig
  {0 atom : Type} (0 sp : SPred atom)
  where
    constructor SExpSinglePredEliminatorArgs
    atomElim : (a : atom) -> sp ($^ a)
    nilElim : sp ($-)
    consElim : (x : SExp atom) -> (l : SList atom) ->
      sp x -> sp ($| l) -> sp (x $|: l)

public export
SPredList : {0 atom : Type} -> (sp : SPred atom) -> !- (SList atom)
SPredList sp = sp . ($|)

public export
SExpSinglePredEliminatorSigToEliminatorSig :
  {0 atom : Type} -> {0 sp : SPred atom} ->
  SExpSinglePredEliminatorSig sp ->
  SExpEliminatorSig sp (SPredList sp)
SExpSinglePredEliminatorSigToEliminatorSig signature =
  SExpEliminatorArgs
    (atomElim signature) (\_ => id) (nilElim signature) (consElim signature)

public export
sexpSinglePredEliminators : {0 atom : Type} -> {0 sp : SPred atom} ->
  SExpSinglePredEliminatorSig sp ->
  (SExp atom ~> sp, SList atom ~> SPredList sp)
sexpSinglePredEliminators signature =
  sexpEliminators (SExpSinglePredEliminatorSigToEliminatorSig signature)

public export
sexpMaps : {0 a : Type} -> (a -> b) -> (SExp a -> SExp b, SList a -> SList b)
sexpMaps f =
  sexpEliminators
    (SExpEliminatorArgs (($^) . f) (\_ => ($|)) [] (\_, _ => (::)))

public export
sexpMap : {0 a : Type} -> (a -> b) -> SExp a -> SExp b
sexpMap = fst . sexpMaps

public export
slistMap : {0 a : Type} -> (a -> b) -> SList a -> SList b
slistMap = snd . sexpMaps

public export
Functor SExp where
  map = sexpMap

public export
Functor SList where
  map = slistMap

public export
SPairPred : (atom : Type) -> Type
SPairPred atom = SExp atom -> SExp atom -> Type

public export
SLPairPred : (atom : Type) -> Type
SLPairPred atom = SList atom -> SList atom -> Type

public export
SPredPair : {atom : Type} -> (spp : SPairPred atom) -> SPred atom
SPredPair {atom} spp = \x => (x' : SExp atom) -> spp x x'

public export
SLPredPair : {atom : Type} -> (lpp : SLPairPred atom) -> SLPred atom
SLPredPair {atom} lpp = \l => (l' : SList atom) ->  lpp l l'

public export
record SExpPairEliminatorSig
  {0 atom : Type} (0 spp : SPairPred atom) (0 lpp : SLPairPred atom)
  where
    constructor SExpPairEliminatorArgs
    atomAtomElim : (a, a' : atom) -> spp ($^ a) ($^ a')
    atomListElim : (a : atom) -> (l : SList atom) -> spp ($^ a) ($| l)
    listAtomElim : (l : SList atom) -> (a : atom) -> spp ($| l) ($^ a)
    listListElim : (l, l' : SList atom) -> lpp l l' -> spp ($| l) ($| l')
    nilNilElim : lpp [] []
    nilConsElim : (x : SExp atom) -> (l : SList atom) -> lpp [] (x :: l)
    consNilElim : (x : SExp atom) -> (l : SList atom) -> lpp (x :: l) []
    consConsElim :
      (x, x' : SExp atom) -> (l, l' : SList atom) ->
      spp x x' -> lpp l l' -> lpp (x :: l) (x' :: l')

public export
SExpPairEliminatorSigToEliminatorSig :
  {0 atom : Type} -> {0 spp : SPairPred atom} -> {0 lpp : SLPairPred atom} ->
  SExpPairEliminatorSig spp lpp ->
  SExpEliminatorSig (SPredPair spp) (SLPredPair lpp)
SExpPairEliminatorSigToEliminatorSig signature =
  SExpEliminatorArgs
    (\a, x => case x of
      $^ a' => atomAtomElim signature a a'
      $| l' => atomListElim signature a l')
    (\l, lppl, x' => case x' of
      $^ a' => listAtomElim signature l a'
      $| l' => listListElim signature l l' (lppl l'))
    (\l => case l of
      [] => nilNilElim signature
      (x' :: l') => nilConsElim signature x' l')
    (\x, l, sppx, lppl, l' => case l' of
      [] => consNilElim signature x l
      (x' :: l') => consConsElim signature x x' l l' (sppx x') (lppl l'))

public export
sexpPairEliminators :
  {0 atom : Type} -> {0 spp : SPairPred atom} -> {0 lpp : SLPairPred atom} ->
  SExpPairEliminatorSig spp lpp ->
  ((x, x' : SExp atom) -> spp x x', (l, l' : SList atom) -> lpp l l')
sexpPairEliminators signature =
  sexpEliminators (SExpPairEliminatorSigToEliminatorSig signature)
