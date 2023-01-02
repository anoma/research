module RefinedSExp.Old.List

import Library.FunctionsAndRelations
import public Data.List

%default total

public export
record ListEliminatorSig
  {atom : Type} (lp : List atom -> Type)
  where
    constructor ListEliminatorArgs
    nilElim : lp []
    consElim : (a : atom) -> (l : List atom) -> lp l -> lp (a :: l)

public export
listEliminator :
  {atom : Type} -> {lp : !- (List atom)} ->
  (signature : ListEliminatorSig lp) ->
  List atom ~> lp
listEliminator signature [] =
  nilElim signature
listEliminator signature (a :: l) =
  consElim signature a l (listEliminator signature l)

public export
listParameterizedEliminator :
  {atom : Type} -> {lp : (List (!- (List atom))) -> (!- (List atom))} ->
  (signature : ((List (!- (List atom))) ~> (ListEliminatorSig . lp))) ->
  (params: List (!- (List atom))) ->
  (List atom ~> lp params)
listParameterizedEliminator {lp} signature params =
  listEliminator
    (ListEliminatorArgs
      (nilElim (signature params))
      (consElim (signature params)))

public export
ListDepFoldSig : (f : Type -> Type) -> {atom : Type} -> {contextType : Type} ->
  (lp : contextType -> List atom -> Type) -> Type
ListDepFoldSig f lp =
  ListEliminatorSig (\l =>
    (context : contextType) -> f (contextType, lp context l))

public export
listDepFoldFlip : {f : Type -> Type} -> {atom : Type} -> {contextType : Type} ->
  {lp : (context : contextType) -> List atom -> Type} ->
  (signature : ListDepFoldSig f lp) ->
  (l : List atom) -> (context : contextType) ->
  f (contextType, lp context l)
listDepFoldFlip {f} {lp} = listEliminator

public export
listDepFold : {f : Type -> Type} -> {atom : Type} -> {contextType : Type} ->
  {lp : (context : contextType) -> List atom -> Type} ->
  (signature : ListDepFoldSig f lp) ->
  (context : contextType) -> (l : List atom) ->
  f (contextType, lp context l)
listDepFold {f} {lp} signature context l =
  listDepFoldFlip {f} {lp} signature l context

infixr 7 :::
public export
data ListForAll :
  {atom : Type} -> (ap : atom -> Type) -> List atom -> Type where
    (|:|) : {atom : Type} -> {ap : atom -> Type} ->
            ListForAll ap []
    (:::) : {atom : Type} -> {ap : atom -> Type} ->
            {a : atom} -> {l : List atom} ->
            ap a -> ListForAll ap l ->
            ListForAll ap (a :: l)

public export
ListForAllHead :
  {atom : Type} -> {ap : atom -> Type} -> {a : atom} -> {l : List atom} ->
  ListForAll ap (a :: l) -> ap a
ListForAllHead (|:|) impossible
ListForAllHead (apa ::: _) = apa

public export
ListForAllTail :
  {atom : Type} -> {ap : atom -> Type} -> {a : atom} -> {l : List atom} ->
  ListForAll ap (a :: l) -> ListForAll ap l
ListForAllTail (|:|) impossible
ListForAllTail (_ ::: apl) = apl

public export
ListForAllApplications : {f : Type -> Type} -> Applicative f =>
  {atom : Type} -> {depType : atom -> Type} ->
  (l : List atom) -> ListForAll (f . depType) l -> f (ListForAll depType l)
ListForAllApplications {f} {depType} =
  listEliminator
    (ListEliminatorArgs
      (\_ => pure (|:|))
      (\a, l, mapForAll, forAll =>
        map (:::) (ListForAllHead forAll) <*>
          mapForAll (ListForAllTail forAll)))

public export
ListForAllConstruct : {atom : Type} ->
  {ap : atom -> Type} ->
  (construct : (a : atom) -> ap a) -> (l : List atom) ->
  ListForAll ap l
ListForAllConstruct {ap} construct =
  listEliminator {lp=(ListForAll ap)}
    (ListEliminatorArgs
      (|:|)
      (\a, _, lpl => construct a ::: lpl))

infixr 7 :::
public export
ListForAllConsDec : {atom : Type} -> {ap : atom -> Type} ->
  {a : atom} -> {l : List atom} ->
  Dec (ap a) -> Dec (ListForAll ap l) ->
  Dec (ListForAll ap (a :: l))
ListForAllConsDec decHead decTail =
  case (decHead, decTail) of
    (Yes yesHead, Yes yesTail) => Yes (yesHead ::: yesTail)
    (No noHead, _) =>
      No (\yesTail =>
        case yesTail of
          (|:|) impossible
          (yesHead ::: _) => noHead yesHead)
    (_, No noTail) =>
      No (\yesHead =>
        case yesHead of
          (|:|) impossible
          (_ ::: yesTail) => noTail yesTail)

public export
DecListForAll : {atom : Type} ->
  {ap : atom -> Type} ->
  (dec : (a : atom) -> Dec (ap a)) -> (l : List atom) ->
  Dec (ListForAll ap l)
DecListForAll {ap} dec =
  listEliminator
    {lp=(\l => Dec (ListForAll ap l))}
    (ListEliminatorArgs
      (Yes (|:|))
      (\a, _, decList => ListForAllConsDec {ap} (dec a) decList))

prefix 11 <::
prefix 11 >::
public export
data ListExists :
  {atom : Type} -> (ap : atom -> Type) -> List atom -> Type where
    (<::) : {atom : Type} -> {ap : atom -> Type} ->
            {a : atom} -> {l : List atom} ->
            ap a ->
            ListExists ap (a :: l)
    (>::) : {atom : Type} -> {ap : atom -> Type} ->
            {a : atom} -> {l : List atom} ->
            ListExists ap l ->
            ListExists ap (a :: l)

public export
NoExistsNil : {atom : Type} -> {ap : atom -> Type} -> Not (ListExists ap [])
NoExistsNil ((<::) _) impossible
NoExistsNil ((>::) _) impossible

public export
NoExistsNeither : {atom : Type} -> {ap : atom -> Type} ->
  {a : atom} -> {l : List atom} ->
  Not (ap a) -> Not (ListExists ap l) ->
  Not (ListExists ap (a :: l))
NoExistsNeither noA _ ((<::) existsA) = noA existsA
NoExistsNeither _ noList ((>::) existsList) = noList existsList

public export
ListExistsEitherDec : {atom : Type} -> {ap : atom -> Type} ->
  {a : atom} -> {l : List atom} ->
  Dec (ap a) -> Dec (ListExists ap l) ->
  Dec (ListExists ap (a :: l))
ListExistsEitherDec decHead decTail =
  case (decHead, decTail) of
    (Yes yesA, _) => Yes (<:: yesA)
    (_, Yes existsList) => Yes (>:: existsList)
    (No noA, No noList) => No (NoExistsNeither noA noList)

public export
DecListExists : {atom : Type} ->
  {ap : atom -> Type} ->
  (dec : (a : atom) -> Dec (ap a)) -> (l : List atom) ->
  Dec (ListExists ap l)
DecListExists {ap} dec =
  listEliminator
    (ListEliminatorArgs
      (No NoExistsNil)
      (\a, _, decList => ListExistsEitherDec (dec a) decList))

public export
record
ListForAllFoldSig {atom : Type}
  (ap : atom -> Type) where
    constructor ListForAllFoldArgs
    consElim :
      (a : atom) -> (l : List atom) ->
      (recursiveResult : ListForAll ap l) ->
      ap a

public export
ListForAllFoldSigToEliminatorSig :
  {atom : Type} -> {ap : atom -> Type} ->
  ListForAllFoldSig {atom} ap ->
  ListEliminatorSig (ListForAll ap)
ListForAllFoldSigToEliminatorSig {atom} {ap} signature =
  ListEliminatorArgs {lp=(ListForAll ap)}
    (|:|)
    (\a, l, forAll => consElim signature a l forAll ::: forAll)

public export
listForAllFold : {atom : Type} ->
  {ap : atom -> Type} ->
  (signature : ListForAllFoldSig ap) ->
  List atom ~> ListForAll ap
listForAllFold {atom} signature =
  listEliminator (ListForAllFoldSigToEliminatorSig signature)

public export
record ListMetaEliminatorSig
  {atom : Type}
  {lp : !- (List atom)}
  (signature : ListEliminatorSig lp)
  (lpp : (l : List atom) -> lp l -> Type)
  where
    constructor ListMetaEliminatorArgs
    metaNilElim : lpp [] (nilElim signature)
    metaConsElim :
      (a : atom) -> (l : List atom) ->
      (lppl : lpp l (listEliminator signature l)) ->
      lpp (a :: l) (consElim signature a l (listEliminator signature l))

public export
listMetaEliminator :
  {atom : Type} ->
  {lp : !- (List atom)} ->
  {signature : ListEliminatorSig lp} ->
  {lpp : (l : List atom) -> lp l -> Type} ->
  (metaSig : ListMetaEliminatorSig signature lpp) ->
  (l : List atom) -> lpp l (listEliminator signature l)
listMetaEliminator metaSig =
  listEliminator
    (ListEliminatorArgs
      (metaNilElim metaSig) (metaConsElim metaSig))
