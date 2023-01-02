module RefinedSExp.Old.OldSExp

import Category.ComputableCategories
import Decidable.Equality

%default total

mutual
  infixr 7 $:
  public export
  data SExp : Type -> Type where
    ($:) : {atom : Type} -> atom -> SList atom -> SExp atom

  infixr 7 $+
  public export
  data SList : Type -> Type where
    ($|) : {atom : Type} -> SList atom
    ($+) : {atom : Type} -> SExp atom -> SList atom -> SList atom

public export
SCons : {atom : Type} -> atom -> SList atom -> SExp atom
SCons = ($:)

public export
SNil : {atom : Type} -> SList atom
SNil = ($|)

public export
SLCons : {atom : Type} -> SExp atom -> SList atom -> SList atom
SLCons = ($+)

prefix 11 $^
public export
($^) : {atom : Type} -> atom -> SExp atom
($^) a = a $: ($|)

public export
SAtom : {atom : Type} -> atom -> SExp atom
SAtom = ($^)

prefix 11 $<*
public export
($<*) : {atom : Type} -> List (SExp atom) -> SList atom
($<*) [] = ($|)
($<*) (x :: l) = x $+ $<* l

prefix 11 $>*
public export
($>*) : {atom : Type} -> SList atom -> List (SExp atom)
($>*) ($|) = []
($>*) (x $+ l) = x :: $>* l

public export
ListToSListToListEq : {atom : Type} -> (l : List (SExp atom)) ->
  ($>*) ($<* l) = l
ListToSListToListEq [] = Refl
ListToSListToListEq (x :: l) = cong ((::) x) (ListToSListToListEq l)

public export
SListToListToSListEq : {atom : Type} -> (l : SList atom) ->
  ($<*) ($>* l) = l
SListToListToSListEq ($|) = Refl
SListToListToSListEq (x $+ l) = cong (($+) x) (SListToListToSListEq l)

prefix 11 <$
public export
(<$) : {atom : Type} -> SExp atom -> atom
(<$) (a $: _) = a

prefix 11 >$
public export
(>$) : {atom : Type} -> SExp atom -> SList atom
(>$) (_ $: l) = l

prefix 11 $+|
public export
($+|) : {atom : Type} -> SExp atom -> SList atom
($+|) x = x $+ ($|)

infixr 7 $++
public export
($++) : {atom : Type} -> SExp atom -> SExp atom -> SList atom
x $++ x' = x $+ $+| x'

infixr 7 $+^
public export
($+^) : {atom : Type} -> SExp atom -> atom -> SList atom
x $+^ a = x $++ $^ a

prefix 11 $^|
public export
($^|) : {atom : Type} -> atom -> SList atom
($^|) a = $+| ($^ a)

infixr 7 $:|
public export
($:|) : {atom : Type} -> atom -> SExp atom -> SExp atom
a $:| x = a $: $+| x

infixr 7 $^^
public export
($^^) : {atom : Type} -> atom -> atom -> SExp atom
a $^^ a' = a $:| $^ a'

infixr 7 $^+
public export
($^+) : {atom : Type} -> atom -> SList atom -> SList atom
a $^+ l = $^ a $+ l

infixr 7 $:+
public export
($:+) : {atom : Type} -> atom -> SExp atom -> SList atom
a $:+ x = a $^+ $+| x

infixr 7 $:^
public export
($:^) : {atom : Type} -> atom -> atom -> SList atom
a $:^ a' = a $:+ $^ a'

public export
SPredicate : (atom : Type) -> Type
SPredicate atom = SExp atom -> Type

public export
SLPredicate : (atom : Type) -> Type
SLPredicate atom = SList atom -> Type

public export
record
SIndSig {atom : Type} (sp : SPredicate atom) (lp : SLPredicate atom) where
  constructor SIndArgs
  expElim : (a : atom) -> (l : SList atom) -> lp l -> sp (a $: l)
  nilElim : lp ($|)
  consElim : (x : SExp atom) -> (l : SList atom) -> sp x -> lp l -> lp (x $+ l)

mutual
  public export
  sExpInd :
    {atom : Type} -> {sp : SPredicate atom} -> {lp : SLPredicate atom} ->
    SIndSig sp lp ->
    (x : SExp atom) -> sp x
  sExpInd signature (a $: l) = expElim signature a l (sListInd signature l)

  public export
  sListInd :
    {atom : Type} -> {sp : SPredicate atom} -> {lp : SLPredicate atom} ->
    SIndSig sp lp ->
    (l : SList atom) -> lp l
  sListInd signature ($|) = nilElim signature
  sListInd signature (x $+ l) =
    consElim signature x l (sExpInd signature x) (sListInd signature l)

public export
sInd :
  {atom : Type} -> {sp : SPredicate atom} -> {lp : SLPredicate atom} ->
  SIndSig sp lp ->
  ((x : SExp atom) -> sp x, (l : SList atom) -> lp l)
sInd signature = (sExpInd signature, sListInd signature)

public export
data SLForAll : {atom : Type} -> SPredicate atom -> SLPredicate atom where
  SLForAllEmpty : {atom : Type} -> {predicate : SPredicate atom} ->
    SLForAll predicate ($|)
  SLForAllCons : {atom : Type} -> {predicate : SPredicate atom} ->
    {x : SExp atom} -> {l : SList atom} ->
    predicate x -> SLForAll predicate l -> SLForAll predicate (x $+ l)

public export
mapSLForAll : {atom : Type} ->
  {sp, sp' : SPredicate atom} -> {l : SList atom} ->
  (f : (x : SExp atom) -> sp x -> sp' x) ->
  SLForAll sp l -> SLForAll sp' l
mapSLForAll f SLForAllEmpty = SLForAllEmpty
mapSLForAll f (SLForAllCons head forAllTail) =
  SLForAllCons (f _ head) (mapSLForAll f forAllTail)

public export
SLForAllUnique : {atom : Type} -> {sp : SPredicate atom} -> {l : SList atom} ->
  (forAll, forAll' : SLForAll sp l) ->
  ((x : SExp atom) -> (spx, spx' : sp x) -> spx = spx') ->
  forAll = forAll'
SLForAllUnique SLForAllEmpty SLForAllEmpty spUnique = Refl
SLForAllUnique SLForAllEmpty (SLForAllCons _ _) _ impossible
SLForAllUnique (SLForAllCons _ _) SLForAllEmpty _ impossible
SLForAllUnique (SLForAllCons head tail) (SLForAllCons head' tail') spUnique =
  case spUnique _ head head' of
    Refl => cong (SLForAllCons head) (SLForAllUnique tail tail' spUnique)

public export
data SForAllSub : {atom : Type} -> SPredicate atom -> SPredicate atom where
  SExpAll : {atom : Type} -> {predicate : SPredicate atom} ->
    {a : atom} -> {l : SList atom} ->
    predicate (a $: l) -> SLForAll (SForAllSub predicate) l ->
    SForAllSub predicate (a $: l)

public export
SLForAllSub : {atom : Type} -> SPredicate atom -> SLPredicate atom
SLForAllSub predicate = SLForAll (SForAllSub predicate)

public export
record SIndForAllSig {atom : Type} (sp : SPredicate atom) where
  constructor SIndForAllArgs
  forAllElim : (a : atom) -> (l : SList atom) -> SLForAll sp l -> sp (a $: l)

public export
sIndForAll :
  {atom : Type} -> {sp : SPredicate atom} ->
  SIndForAllSig sp ->
  ((x : SExp atom) -> sp x, (l : SList atom) -> SLForAll sp l)
sIndForAll signature =
  sInd {sp} {lp=(SLForAll sp)}
    (SIndArgs (forAllElim signature) SLForAllEmpty (\_, _ => SLForAllCons))

public export
sExpIndForAll :
  {atom : Type} -> {sp : SPredicate atom} ->
  SIndForAllSig sp ->
  (x : SExp atom) -> sp x
sExpIndForAll signature = fst (sIndForAll signature)

public export
sListIndForAll :
  {atom : Type} -> {sp : SPredicate atom} ->
  SIndForAllSig sp ->
  (l : SList atom) -> SLForAll sp l
sListIndForAll signature = snd (sIndForAll signature)

public export
record SIndGenSig {atom : Type} (sp : SPredicate atom) where
  constructor SIndGenArgs
  expElim : (a : atom) -> (l : SList atom) -> SLForAllSub sp l -> sp (a $: l)

public export
sIndGen :
  {atom : Type} -> {sp : SPredicate atom} ->
  SIndGenSig sp ->
  ((x : SExp atom) -> SForAllSub sp x, (l : SList atom) -> SLForAllSub sp l)
sIndGen signature =
  sInd {atom} {sp=(SForAllSub sp)} {lp=(SLForAllSub sp)}
    (SIndArgs
      (\a, l, spl => SExpAll (expElim signature a l spl) spl)
      SLForAllEmpty
      (\_, _ => SLForAllCons))

public export
record STransformSig (atom, atom' : Type) where
  expTransform :
    atom -> (l : SList atom) -> SLForAll (\_ => SExp atom') l -> SExp atom'

public export
sTransform :
  {atom, atom' : Type} ->
  STransformSig atom atom' ->
  (SExp atom -> SExp atom', (l : SList atom) -> SLForAll (\_ => SExp atom') l)
sTransform {atom} {atom'} signature =
  sIndForAll {atom} {sp=(\_ => SExp atom')}
    (SIndForAllArgs (expTransform signature))

public export
sExpTransform :
  {atom, atom' : Type} ->
  STransformSig atom atom' ->
  SExp atom -> SExp atom'
sExpTransform = fst . sTransform

public export
sListTransform :
  {atom, atom' : Type} ->
  STransformSig atom atom' ->
  (l : SList atom) -> SLForAll (\_ => SExp atom') l
sListTransform = snd . sTransform

public export
SContextPred : (contextType : Type) -> (atom : Type) -> Type
SContextPred contextType atom = contextType -> SPredicate atom

public export
SLContextPred : (contextType : Type) -> (atom : Type) -> Type
SLContextPred contextType atom = contextType -> SLPredicate atom

public export
record
SIndContextSig {contextType : Type} {atom : Type}
  (sp : SContextPred contextType atom)
  (lp : SLContextPred contextType atom) where
    constructor SIndContextArgs
    expElim :
      (contextUponEntry : contextType) ->
      (a : atom) -> (l : SList atom) ->
      (listInduction :
        (context : contextType) -> (contextType, lp context l)) ->
      (contextType, sp contextUponEntry (a $: l))
    nilElim : (context : contextType) -> (contextType, lp context ($|))
    consElim :
      (contextUponEntry : contextType) ->
      (x : SExp atom) -> (l : SList atom) ->
      (expInduction : (context : contextType) ->
        (contextType, sp context x)) ->
      (listInduction : (context : contextType) ->
        (contextType, lp context l)) ->
      (contextType, lp contextUponEntry (x $+ l))

public export
sIndContextFlip :
  {contextType : Type} ->
  {atom : Type} ->
  {sp : contextType -> SPredicate atom} ->
  {lp : contextType -> SLPredicate atom} ->
  SIndContextSig sp lp ->
  ((x : SExp atom) -> (context : contextType) -> (contextType, sp context x),
   (l : SList atom) -> (context : contextType) -> (contextType, lp context l))
sIndContextFlip {sp} {lp} signature =
  sInd {atom}
    {sp=(\x => (context : contextType) -> (contextType, sp context x))}
    {lp=(\l => (context : contextType) -> (contextType, lp context l))}
    (SIndArgs
      (\a, l, listInd, contextUponEntry =>
        expElim signature contextUponEntry a l listInd)
      (nilElim signature)
      (\x, l, expInd, listInd, contextUponEntry =>
        consElim signature contextUponEntry x l expInd listInd))

public export
sIndContext :
  {contextType : Type} ->
  {atom : Type} ->
  {sp : contextType -> SPredicate atom} ->
  {lp : contextType -> SLPredicate atom} ->
  SIndContextSig sp lp ->
  ((context : contextType) -> (x : SExp atom) -> (contextType, sp context x),
   (context : contextType) -> (l : SList atom) -> (contextType, lp context l))
sIndContext {sp} {lp} signature =
  let flipped = sIndContextFlip signature in
  (\context, x => fst flipped x context, \context, l => snd flipped l context)

public export
sExpIndContextFlip :
  {contextType : Type} ->
  {atom : Type} ->
  {sp : contextType -> SPredicate atom} ->
  {lp : contextType -> SLPredicate atom} ->
  SIndContextSig sp lp ->
  (x : SExp atom) -> (context : contextType) -> (contextType, sp context x)
sExpIndContextFlip {sp} {lp} signature =
  fst (sIndContextFlip {sp} {lp} signature)

public export
sExpIndContext :
  {contextType : Type} ->
  {atom : Type} ->
  {sp : contextType -> SPredicate atom} ->
  {lp : contextType -> SLPredicate atom} ->
  SIndContextSig sp lp ->
  (context : contextType) -> (x : SExp atom) -> (contextType, sp context x)
sExpIndContext {sp} {lp} signature =
  fst (sIndContext {sp} {lp} signature)

public export
sListIndContextFlip :
  {contextType : Type} ->
  {atom : Type} ->
  {sp : contextType -> SPredicate atom} ->
  {lp : contextType -> SLPredicate atom} ->
  SIndContextSig sp lp ->
  (l : SList atom) -> (context : contextType) -> (contextType, lp context l)
sListIndContextFlip {sp} {lp} signature =
  snd (sIndContextFlip {sp} {lp} signature)

public export
sListIndContext :
  {contextType : Type} ->
  {atom : Type} ->
  {sp : contextType -> SPredicate atom} ->
  {lp : contextType -> SLPredicate atom} ->
  SIndContextSig sp lp ->
  (context : contextType) -> (l : SList atom) -> (contextType, lp context l)
sListIndContext {sp} {lp} signature =
  snd (sIndContext {sp} {lp} signature)

public export
record
SIndContextForAllSig {contextType : Type} {atom : Type}
  (sp : contextType -> SPredicate atom) where
    constructor SIndContextForAllArgs
    expElim :
      (contextUponEntry : contextType) ->
      (a : atom) -> (l : SList atom) ->
      (listInduction :
        (context : contextType) -> (contextType, SLForAll (sp context) l)) ->
      (contextType, sp contextUponEntry (a $: l))

public export
sIndContextForAllSigToIndContextSig :
  {contextType : Type} ->
  {atom : Type} ->
  {sp : contextType -> SPredicate atom} ->
  SIndContextForAllSig sp ->
  SIndContextSig sp (SLForAll . sp)
sIndContextForAllSigToIndContextSig signature =
  (SIndContextArgs
    (expElim signature)
    (\context => (context, SLForAllEmpty))
    (\contextUponEntry, x, l, expInd, listInd =>
      (contextUponEntry,
       SLForAllCons
        (snd (expInd contextUponEntry))
        (snd (listInd contextUponEntry)))))

public export
sIndContextForAll :
  {contextType : Type} ->
  {atom : Type} ->
  {sp : contextType -> SPredicate atom} ->
  SIndContextForAllSig sp ->
  ((context : contextType) -> (x : SExp atom) -> (contextType, sp context x),
   (context : contextType) -> (l : SList atom) ->
    (contextType, SLForAll (sp context) l))
sIndContextForAll {sp} signature =
  sIndContext {sp} {lp=(SLForAll . sp)}
    (sIndContextForAllSigToIndContextSig signature)

public export
sExpIndContextForAll :
  {contextType : Type} ->
  {atom : Type} ->
  {sp : contextType -> SPredicate atom} ->
  SIndContextForAllSig sp ->
  (context : contextType) -> (x : SExp atom) -> (contextType, sp context x)
sExpIndContextForAll signature = fst (sIndContextForAll signature)

public export
sListIndContextForAll :
  {contextType : Type} ->
  {atom : Type} ->
  {sp : contextType -> SPredicate atom} ->
  SIndContextForAllSig sp ->
  (context : contextType) -> (l : SList atom) ->
  (contextType, SLForAll (sp context) l)
sListIndContextForAll signature = snd (sIndContextForAll signature)

public export
sListIndContextForAllFlip :
  {contextType : Type} ->
  {atom : Type} ->
  {sp : contextType -> SPredicate atom} ->
  SIndContextForAllSig sp ->
  (l : SList atom) -> (context : contextType) ->
  (contextType, SLForAll (sp context) l)
sListIndContextForAllFlip signature l context =
  sListIndContextForAll signature context l

public export
SDepPred : {atom : Type} -> SPredicate atom -> Type
SDepPred {atom} pred = (x : SExp atom) -> pred x -> Type

public export
SDepPredPair : {atom : Type} -> {sp : SPredicate atom} ->
  SDepPred sp -> SPredicate atom
SDepPredPair {sp} sdp = \x => (spx : sp x ** sdp x spx)

public export
SLDepPred : {atom : Type} -> SLPredicate atom -> Type
SLDepPred {atom} pred = (l : SList atom) -> pred l -> Type

public export
SLDepPredPair : {atom : Type} -> {lp : SLPredicate atom} ->
  SLDepPred lp -> SLPredicate atom
SLDepPredPair {lp} ldp = \l => (lpl : lp l ** ldp l lpl)

public export
record SDepIndSig {atom : Type} {sp : SPredicate atom} {lp : SLPredicate atom}
  (sdp : SDepPred sp) (ldp : SLDepPred lp)
  (sIndSig : SIndSig sp lp) where
    constructor SDepIndArgs
    depExpElim : (a : atom) -> (l : SList atom) ->
      ldp l (sListInd sIndSig l) ->
      sdp (a $:l) (expElim sIndSig a l (sListInd sIndSig l))
    depNilElim : ldp ($|) (nilElim sIndSig)
    depConsElim : (x : SExp atom) -> (l: SList atom) ->
      sdp x (sExpInd sIndSig x) ->
      ldp l (sListInd sIndSig l) ->
      ldp (x $+ l)
        (consElim sIndSig x l
          (sExpInd sIndSig x)
          (sListInd sIndSig l))

public export
sDepInd :
  {atom : Type} -> {sp : SPredicate atom} -> {lp : SLPredicate atom} ->
  {sdp : SDepPred sp} -> {ldp : SLDepPred lp} ->
  {sIndSig : SIndSig sp lp} ->
  SDepIndSig sdp ldp sIndSig ->
  ((x : SExp atom) -> sdp x (sExpInd sIndSig x),
   (l : SList atom) -> ldp l (sListInd sIndSig l))
sDepInd {sIndSig} signature =
  sInd
    (SIndArgs
      (depExpElim signature)
      (depNilElim signature)
      (depConsElim signature))

public export
SDepContextPred : {contextType : Type} -> {atom : Type} ->
  (sp : SContextPred contextType atom) -> Type
SDepContextPred {contextType} {atom} sp =
  (context : contextType) -> (x : SExp atom) -> sp context x -> Type

public export
SLDepContextPred : {contextType : Type} -> {atom : Type} ->
  (lp : SLContextPred contextType atom) -> Type
SLDepContextPred {contextType} {atom} lp =
  (context : contextType) -> (l : SList atom) -> lp context l -> Type

public export
record SDepIndContextSig {contextType : Type} {atom : Type}
  {sp : SContextPred contextType atom}
  {lp : SLContextPred contextType atom}
  (sdp : SDepContextPred sp)
  (ldp : SLDepContextPred lp)
  (sIndContextSig : SIndContextSig sp lp) where
    constructor SDepIndContextArgs
    depExpElim :
      (contextUponEntry : contextType) ->
      (a : atom) -> (l : SList atom) ->
      (listDepInduction : (context : contextType) ->
        (contextType,
          ldp context l
            (snd (sListIndContextFlip {sp} {lp} sIndContextSig l context)))) ->
      (contextType,
        sdp contextUponEntry (a $:l)
          (snd
            (expElim sIndContextSig contextUponEntry a l
              (sListIndContextFlip {sp} {lp} sIndContextSig l))))
    depNilElim :
      (context : contextType) ->
        (contextType, ldp context ($|) (snd (nilElim sIndContextSig context)))
    depConsElim :
      (contextUponEntry : contextType) ->
      (x : SExp atom) -> (l: SList atom) ->
      (expDepInduction : (context : contextType) ->
        (contextType,
          sdp context x
          (snd
            (sExpIndContextFlip {sp} {lp} sIndContextSig x context)))) ->
      (listDepInduction : (context : contextType) ->
        (contextType,
          ldp context l
            (snd (sListIndContextFlip {sp} {lp} sIndContextSig l context)))) ->
      (contextType,
        ldp contextUponEntry (x $+ l)
          (snd
            (consElim sIndContextSig contextUponEntry x l
              (sExpIndContextFlip {sp} {lp} sIndContextSig x)
              (sListIndContextFlip {sp} {lp} sIndContextSig l))))

public export
sDepIndContextFlip :
  {contextType : Type} ->
  {atom : Type} ->
  {sp : contextType -> SPredicate atom} ->
  {lp : contextType -> SLPredicate atom} ->
  {sdp : (context : contextType) -> (x : SExp atom) -> sp context x -> Type} ->
  {ldp : (context : contextType) -> (l : SList atom) -> lp context l -> Type} ->
  {sIndContextSig : SIndContextSig sp lp} ->
  SDepIndContextSig {sp} {lp} sdp ldp sIndContextSig ->
  ((x : SExp atom) -> (context : contextType) ->
    (contextType,
     sdp context x
       (snd (sExpIndContextFlip {sp} {lp} sIndContextSig x context))),
   (l : SList atom) -> (context : contextType) ->
    (contextType,
     ldp context l
       (snd (sListIndContextFlip {sp} {lp} sIndContextSig l context))))
sDepIndContextFlip
  {sp} {lp} {sdp} {ldp} {sIndContextSig} signature =
    sDepInd {atom}
      {sp=(\x => (context : contextType) -> (contextType, sp context x))}
      {lp=(\l => (context : contextType) -> (contextType, lp context l))}
      {sdp=(\x, spInd => (context : contextType) ->
        (contextType, sdp context x (snd (spInd context))))}
      {ldp=(\l, lpInd => (context : contextType) ->
        (contextType, ldp context l (snd (lpInd context))))}
      (SDepIndArgs
        (\a, l, listDepInd, contextUponEntry =>
          depExpElim signature contextUponEntry a l listDepInd)
        (depNilElim signature)
        (\x, l, expDepInd, listDepInd, contextUponEntry =>
          depConsElim signature contextUponEntry x l expDepInd listDepInd))

public export
sDepIndContext :
  {contextType : Type} ->
  {atom : Type} ->
  {sp : contextType -> SPredicate atom} ->
  {lp : contextType -> SLPredicate atom} ->
  {sdp : (context : contextType) -> (x : SExp atom) -> sp context x -> Type} ->
  {ldp : (context : contextType) -> (l : SList atom) -> lp context l -> Type} ->
  {sIndContextSig : SIndContextSig sp lp} ->
  SDepIndContextSig {sp} {lp} sdp ldp sIndContextSig ->
  ((context : contextType) -> (x : SExp atom) ->
    (contextType,
     sdp context x
       (snd (sExpIndContext {sp} {lp} sIndContextSig context x))),
   (context : contextType) -> (l : SList atom) ->
    (contextType,
     ldp context l
       (snd (sListIndContext {sp} {lp} sIndContextSig context l))))
sDepIndContext signature =
  let flipped = sDepIndContextFlip signature in
  (\context, x => fst flipped x context, \context, l => snd flipped l context)

public export
data SLForAllDep : {atom : Type} -> {sp : SPredicate atom} ->
    SDepPred sp -> SLDepPred (SLForAll sp) where
  SLForAllDepEmpty : {atom : Type} -> {sp : SPredicate atom} ->
    {sdp : SDepPred sp} -> SLForAllDep sdp ($|) SLForAllEmpty
  SLForAllDepCons : {atom : Type} -> {sp : SPredicate atom} ->
    {sdp : SDepPred sp} ->
    {x : SExp atom} -> {l : SList atom} ->
    {spx : sp x} -> {splForAll : SLForAll sp l} ->
    sdp x spx -> SLForAllDep sdp l splForAll ->
    SLForAllDep sdp (x $+ l) (SLForAllCons spx splForAll)

public export
SLPairsFst : {atom : Type} -> {sp : SPredicate atom} ->
  {sdp : SDepPred sp} -> {l : SList atom} ->
  (forAll : SLForAll (SDepPredPair sdp) l) ->
  SLForAll sp l
SLPairsFst SLForAllEmpty = SLForAllEmpty
SLPairsFst (SLForAllCons sdpx sdpl) = SLForAllCons (fst sdpx) (SLPairsFst sdpl)

public export
SLPairsSnd : {atom : Type} -> {sp : SPredicate atom} ->
  {sdp : SDepPred sp} -> {l : SList atom} ->
  (forAll : SLForAll (SDepPredPair sdp) l) ->
  SLForAllDep sdp l (SLPairsFst forAll)
SLPairsSnd SLForAllEmpty = SLForAllDepEmpty
SLPairsSnd {sdp} (SLForAllCons sdpx sdpl) =
  SLForAllDepCons {sdp} (snd sdpx) (SLPairsSnd {sdp} sdpl)

public export
SLPairsToForAllDep : {atom : Type} -> {sp : SPredicate atom} ->
  {sdp : SDepPred sp} -> {l : SList atom} ->
  (forAll : SLForAll (SDepPredPair sdp) l) ->
  SLForAllDep sdp l (SLPairsFst forAll)
SLPairsToForAllDep SLForAllEmpty = SLForAllDepEmpty
SLPairsToForAllDep {sdp} (SLForAllCons (_ ** head) forAllTail) =
  SLForAllDepCons head (SLPairsToForAllDep {sdp} forAllTail)

public export
SLForAllDepToPairs : {atom : Type} -> {sp : SPredicate atom} ->
  {sdp : SDepPred sp} -> {l : SList atom} ->
  {forAll : SLForAll sp l} -> SLForAllDep sdp l forAll ->
  SLForAll (SDepPredPair sdp) l
SLForAllDepToPairs SLForAllDepEmpty = SLForAllEmpty
SLForAllDepToPairs (SLForAllDepCons head forAllTail) =
  SLForAllCons (_ ** head) (SLForAllDepToPairs forAllTail)

public export
record SDepIndForAllSig
  {atom : Type} {sp : SPredicate atom} (sdp : SDepPred sp)
  (sIndForAllSig : SIndForAllSig sp) where
    constructor SDepIndForAllArgs
    depForAllElim : (a : atom) -> (l : SList atom) ->
      SLForAllDep sdp l (sListIndForAll sIndForAllSig l) ->
      sdp (a $: l)
        (forAllElim sIndForAllSig a l (sListIndForAll sIndForAllSig l))

public export
sDepIndForAll :
  {atom : Type} -> {sp : SPredicate atom} -> {sdp : SDepPred sp} ->
  {sIndSig : SIndSig sp (SLForAll sp)} ->
  {sIndForAllSig : SIndForAllSig sp} ->
  SDepIndForAllSig sdp sIndForAllSig ->
  ((x : SExp atom) -> sdp x (sExpIndForAll sIndForAllSig x),
   (l : SList atom) -> SLForAllDep sdp l (sListIndForAll sIndForAllSig l))
sDepIndForAll {sIndForAllSig} signature =
  sDepInd {sp} {lp=(SLForAll sp)}
    {sdp} {ldp=(SLForAllDep sdp)}
    (SDepIndArgs
      (depForAllElim signature)
      SLForAllDepEmpty
      (\_, _ => SLForAllDepCons))

public export
SDPair : {atom : Type} -> SPredicate atom -> Type
SDPair {atom} pred = DPair (SExp atom) pred

prefix 11 <:$
public export
(<:$) : {atom : Type} -> {pred : SPredicate atom} -> SDPair pred -> SExp atom
(<:$) (x ** _) = x

prefix 11 >:$
public export
(>:$) : {atom : Type} -> {pred : SPredicate atom} -> (dx : SDPair pred) ->
  pred (<:$ dx)
(>:$) (_ ** spx) = spx

public export
SLDPair : {atom : Type} -> SLPredicate atom -> Type
SLDPair {atom} pred = DPair (SList atom) pred

prefix 11 <+$
public export
(<+$) : {atom : Type} -> {pred : SLPredicate atom} -> SLDPair pred -> SList atom
(<+$) (l ** _) = l

prefix 11 >+$
public export
(>+$) : {atom : Type} -> {pred : SLPredicate atom} -> (dl : SLDPair pred) ->
  pred (<+$ dl)
(>+$) (_ ** lpl) = lpl

public export
SDPairPred : {atom : Type} -> SPredicate atom -> Type
SDPairPred pred = SDPair pred -> Type

public export
SLDPairPred : {atom : Type} -> SLPredicate atom -> Type
SLDPairPred pred = SLDPair pred -> Type

public export
record SDPairIndSig
  {atom : Type} {sp : SPredicate atom} {lp : SLPredicate atom}
  (sdp : SDPairPred sp) (ldp : SLDPairPred lp)
  (sIndSig : SIndSig sp lp) where
    constructor SDPairIndArgs
    depExpElim : (a : atom) -> (l : SList atom) ->
      ldp (l ** (sListInd sIndSig l)) ->
      sdp (a $: l ** expElim sIndSig a l (sListInd sIndSig l))
    depNilElim : ldp (($|) ** (nilElim sIndSig))
    depConsElim : (x : SExp atom) -> (l: SList atom) ->
      sdp (x ** (sExpInd sIndSig x)) ->
      ldp (l ** (sListInd sIndSig l)) ->
      ldp
        (x $+ l **
          consElim sIndSig x l
            (sExpInd sIndSig x)
            (sListInd sIndSig l))

-- Construct a dependent function on dependent pairs.
public export
sdpairInd :
  {atom : Type} -> {sp : SPredicate atom} -> {lp : SLPredicate atom} ->
  {sdp : SDPairPred sp} -> {ldp : SLDPairPred lp} ->
  {sIndSig : SIndSig sp lp} ->
  SDPairIndSig sdp ldp sIndSig ->
  ((x : SExp atom) -> sdp (x ** sExpInd sIndSig x),
   (l : SList atom) -> ldp (l ** sListInd sIndSig l))
sdpairInd {sdp} {ldp} signature =
  sDepInd {sdp=(\x, spx => sdp (x ** spx))} {ldp=(\l, lpl => ldp (l ** lpl))}
    (SDepIndArgs
      (depExpElim signature)
      (depNilElim signature)
      (depConsElim signature))

public export
DSExp : {atom : Type} -> SPredicate atom -> Type
DSExp {atom} pred = DPair (SExp atom) pred

public export
DSList : {atom : Type} -> SLPredicate atom -> Type
DSList {atom} pred = DPair (SList atom) pred

public export
SDPairContextPred : {contextType : Type} -> {atom : Type} ->
  (sp : SContextPred contextType atom) -> Type
SDPairContextPred {contextType} {atom} sp =
  (context : contextType) -> DSExp (sp context) -> Type

public export
SLDPairContextPred : {contextType : Type} -> {atom : Type} ->
  (lp : SLContextPred contextType atom) -> Type
SLDPairContextPred {contextType} {atom} lp =
  (context : contextType) -> DSList (lp context) -> Type
