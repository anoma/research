module RefinedSExp.Old.InductiveSExp

import public RefinedSExp.Old.OldSExp

%default total

-- An inductive predicate on S-expressions is a type family whose type at a
-- given S-expression can be expressed as a function of its types at the
-- given S-expression's sub-expressions.
record InductiveDefinition {atom : Type}
    (sp : SPredicate atom) (lp : SLPredicate atom) where
  constructor InductiveConstructors
  SExpConstructor : (a : atom) -> {l : SList atom} -> lp l -> Type
  SExpConstruct : {a : atom} -> {l : SList atom} -> (lpl : lp l) ->
    SExpConstructor a lpl -> sp (a $: l)
  SNilConstructor : Type
  SNilConstruct : SNilConstructor -> lp ($|)
  SConsConstructor : {x : SExp atom} -> {l : SList atom} -> sp x -> lp l -> Type
  SConsConstruct : {x : SExp atom} -> {l : SList atom} ->
    (spx : sp x) -> (lpl : lp l) ->
    SConsConstructor spx lpl -> lp (x $+ l)

InductiveConstructorType : {atom : Type} -> (sp : SPredicate atom) -> Type
InductiveConstructorType {atom} sp =
  (a : atom) -> {l : SList atom} -> SLForAll sp l -> Type

InductiveConstructor : {atom : Type} -> {sp : SPredicate atom} ->
  InductiveConstructorType sp -> Type
InductiveConstructor {atom} {sp} constructorType =
  {a : atom} -> {l : SList atom} -> (spl : SLForAll sp l) ->
  constructorType a spl -> sp (a $: l)

inductiveDefinition : {atom : Type} -> {sp : SPredicate atom} ->
  {constructorType : InductiveConstructorType sp} ->
  InductiveConstructor constructorType ->
  InductiveDefinition sp (SLForAll sp)
inductiveDefinition {constructorType} construct =
  InductiveConstructors
    constructorType
    construct
    ()
    (\_ => SLForAllEmpty)
    (\_, _ => ())
    (\spx, spl, _ => SLForAllCons spx spl)

mutual
  infixr 7 *:
  data InductiveTerm : {atom : Type} ->
      {sp : SPredicate atom} -> {lp : SLPredicate atom} ->
      InductiveDefinition sp lp -> SExp atom -> Type where
    IExp : {atom : Type} -> {sp : SPredicate atom} -> {lp : SLPredicate atom} ->
      {iType : InductiveDefinition sp lp} -> {a : atom} -> {l : SList atom} ->
      {il : InductiveList iType l} ->
      SExpConstructor iType a (listToPred il) ->
      InductiveTerm iType (a $: l)

  data InductiveList : {atom : Type} ->
      {sp : SPredicate atom} -> {lp : SLPredicate atom} ->
      InductiveDefinition sp lp -> SList atom -> Type where
    INil : {atom : Type} -> {sp : SPredicate atom} -> {lp : SLPredicate atom} ->
      {iType : InductiveDefinition sp lp} ->
      SNilConstructor iType -> InductiveList iType ($|)
    ICons : {atom : Type} ->
      {sp : SPredicate atom} -> {lp : SLPredicate atom} ->
      {iType : InductiveDefinition sp lp} ->
      {x : SExp atom} -> {l : SList atom} ->
      {it : InductiveTerm iType x} -> {il : InductiveList iType l} ->
      SConsConstructor iType (termToPred it) (listToPred il) ->
      InductiveList iType (x $+ l)

  termToPred : {atom : Type} ->
    {sp : SPredicate atom} -> {lp : SLPredicate atom} ->
    {iType : InductiveDefinition sp lp} -> {x : SExp atom} ->
    InductiveTerm iType x -> sp x
  termToPred {iType} (IExp {il} construct) =
    SExpConstruct iType (listToPred il) construct

  listToPred : {atom : Type} ->
    {sp : SPredicate atom} -> {lp : SLPredicate atom} ->
    {iType : InductiveDefinition sp lp} -> {l : SList atom} ->
    InductiveList iType l -> lp l
  listToPred {iType} (INil construct) =
    SNilConstruct iType construct
  listToPred {iType} (ICons {it} {il} construct) =
    SConsConstruct iType (termToPred it) (listToPred il) construct

mutual
  iTermInd :
    {atom : Type} -> {sp : SPredicate atom} -> {lp : SLPredicate atom} ->
    {iType : InductiveDefinition sp lp} ->
    {itp : (x : SExp atom) -> InductiveTerm iType x -> Type} ->
    {ilp : (l : SList atom) -> InductiveList iType l -> Type} ->
    (expElim : (a : atom) -> (l : SList atom) -> (il : InductiveList iType l) ->
      (sec : SExpConstructor iType a (listToPred il)) ->
      ilp l il -> itp (a $: l) (IExp {il} sec)) ->
    (nilElim : (snc : SNilConstructor iType) -> ilp ($|) (INil snc)) ->
    (consElim : (x : SExp atom) -> (l : SList atom) ->
      (it : InductiveTerm iType x) -> (il : InductiveList iType l) ->
      (sec : SConsConstructor iType (termToPred it) (listToPred il)) ->
      itp x it -> ilp l il -> ilp (x $+ l) (ICons {it} {il} sec)) ->
    {x : SExp atom} -> (it : InductiveTerm iType x) -> itp x it
  iTermInd {itp} {ilp} expElim nilElim consElim
    (IExp {a} {l} {il} construct) =
      expElim
        a l il construct
          (iListInd {itp} {ilp} expElim nilElim consElim il)

  iListInd :
    {atom : Type} -> {sp : SPredicate atom} -> {lp : SLPredicate atom} ->
    {iType : InductiveDefinition sp lp} ->
    {itp : (x : SExp atom) -> InductiveTerm iType x -> Type} ->
    {ilp : (l : SList atom) -> InductiveList iType l -> Type} ->
    (expElim : (a : atom) -> (l : SList atom) -> (il : InductiveList iType l) ->
      (sec : SExpConstructor iType a (listToPred il)) ->
      ilp l il -> itp (a $: l) (IExp {il} sec)) ->
    (nilElim : (snc : SNilConstructor iType) -> ilp ($|) (INil snc)) ->
    (consElim : (x : SExp atom) -> (l : SList atom) ->
      (it : InductiveTerm iType x) -> (il : InductiveList iType l) ->
      (sec : SConsConstructor iType (termToPred it) (listToPred il)) ->
      itp x it -> ilp l il -> ilp (x $+ l) (ICons {it} {il} sec)) ->
    {l : SList atom} -> (il : InductiveList iType l) -> ilp l il
  iListInd {itp} {ilp} expElim nilElim consElim
    (INil construct) =
      nilElim construct
  iListInd {itp} {ilp} expElim nilElim consElim
    (ICons {x} {l} {it} {il} construct) =
      consElim x l it il construct
        (iTermInd {itp} {ilp} expElim nilElim consElim it)
        (iListInd {itp} {ilp} expElim nilElim consElim il)

inductiveElim :
  {atom : Type} -> {sp : SPredicate atom} -> {lp : SLPredicate atom} ->
  {iType : InductiveDefinition sp lp} ->
  {itp : (x : SExp atom) -> InductiveTerm iType x -> Type} ->
  {ilp : (l : SList atom) -> InductiveList iType l -> Type} ->
  (expElim : (a : atom) -> (l : SList atom) -> (il : InductiveList iType l) ->
    (sec : SExpConstructor iType a (listToPred il)) ->
    ilp l il -> itp (a $: l) (IExp {il} sec)) ->
  (nilElim : (snc : SNilConstructor iType) -> ilp ($|) (INil snc)) ->
  (consElim : (x : SExp atom) -> (l : SList atom) ->
    (it : InductiveTerm iType x) -> (il : InductiveList iType l) ->
    (sec : SConsConstructor iType (termToPred it) (listToPred il)) ->
    itp x it -> ilp l il -> ilp (x $+ l) (ICons {it} {il} sec)) ->
  ({x : SExp atom} -> (it : InductiveTerm iType x) -> itp x it,
   {l : SList atom} -> (il : InductiveList iType l) -> ilp l il)
inductiveElim expElim nilElim consElim =
  (iTermInd expElim nilElim consElim, iListInd expElim nilElim consElim)
