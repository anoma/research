module RefinedSExp.ListVariant.SExp

import public RefinedSExp.ListVariant.List
import Library.FunctionsAndRelations
import Library.Decidability
import Library.List
import public Category.Category

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
  SList = List . SExp

public export
SExpPred : Type -> Type
SExpPred atom = !- (SExp atom)

public export
SListPred : Type -> Type
SListPred atom = !- (SList atom)

public export
SExpPreds : Type -> Type
SExpPreds atom = (SExpPred atom, SListPred atom)

public export
SPredsExp : {0 atom : Type} -> SExpPreds atom -> SExpPred atom
SPredsExp = fst

public export
SPredsList : {0 atom : Type} -> SExpPreds atom -> SListPred atom
SPredsList = snd

public export
sexpPredsCompose : {atom : Type} ->
  (Type -> Type) -> SExpPreds atom -> SExpPreds atom
sexpPredsCompose f sps = (f . SPredsExp sps, f . SPredsList sps)

public export
SExpPi : {atom : Type} -> SExpPred atom -> Type
SExpPi sp = SExp atom ~> sp

public export
SListPi : {atom : Type} -> SListPred atom -> Type
SListPi sp = SList atom ~> sp

public export
SPisExp : {atom : Type} -> (sps : SExpPreds atom) -> Type
SPisExp = SExpPi . SPredsExp

public export
SPisList : {atom : Type} -> (sps : SExpPreds atom) -> Type
SPisList = SListPi . SPredsList

public export
SPredPis : {atom : Type} -> SExpPreds atom -> Type
SPredPis sps = (SPisExp sps, SPisList sps)

public export
record SExpEliminatorSig
  {atom : Type} (sps : SExpPreds atom)
  where
    constructor SExpEliminatorArgs
    atomElim : (a : atom) ->
      SPredsExp sps ($^ a)
    listElim : (l : SList atom) ->
      SPredsList sps l -> SPredsExp sps ($| l)
    nilElim :
      SPredsList sps []
    consElim :
      (x : SExp atom) -> (l : SList atom) ->
      SPredsExp sps x -> SPredsList sps l -> SPredsList sps (x :: l)

mutual
  public export
  sexpEliminator :
    {0 atom : Type} -> {0 sps : SExpPreds atom} ->
    (signature : SExpEliminatorSig sps) ->
    SPisExp sps
  sexpEliminator signature ($^ a) =
    atomElim signature a
  sexpEliminator signature ($| l) =
    listElim signature l (slistEliminator signature l)

  public export
  slistEliminator :
    {0 atom : Type} -> {0 sps : SExpPreds atom} ->
    (signature : SExpEliminatorSig sps) ->
    SPisList sps
  slistEliminator signature [] =
    nilElim signature
  slistEliminator signature (x :: l) =
    consElim signature x l
      (sexpEliminator signature x) (slistEliminator signature l)

public export
SExpSignatureComposeSig :
  {f : Type -> Type} ->
  {app : Applicative f} ->
  {atom : Type} ->
  {sps : SExpPreds atom} ->
  (signature : f (SExpEliminatorSig sps)) ->
  SExpEliminatorSig (sexpPredsCompose f sps)
SExpSignatureComposeSig {app} signature =
  SExpEliminatorArgs {sps=(sexpPredsCompose f sps)}
    (\a => dpure app (map {f} atomElim signature) a)
    (\l, flpl => (dpure app (map {f} listElim signature) l) <*> flpl)
    (map {f} nilElim signature)
    (\x, l, fspx, flpl =>
      ((dpure app (dpure app (map {f} consElim signature) x) l) <*> fspx)
        <*> flpl)

public export
sexpEliminators :
  {0 atom : Type} -> {0 sps : SExpPreds atom} ->
  (signature : SExpEliminatorSig sps) ->
  SPredPis sps
sexpEliminators signature =
  (sexpEliminator signature, slistEliminator signature)

public export
sexpEliminatorsComposeSig :
  {f : Type -> Type} -> {app : Applicative f} ->
  {atom : Type} ->
  {sps : SExpPreds atom} ->
  (signature : f (SExpEliminatorSig sps)) ->
  SPredPis (sexpPredsCompose f sps)
sexpEliminatorsComposeSig = sexpEliminators . SExpSignatureComposeSig {app}

public export
SExpPredsToListPred :
  {atom : Type} -> (sps : SExpPreds atom) -> ListPred (SExp atom)
SExpPredsToListPred sps [] = SPredsList sps []
SExpPredsToListPred sps (x :: l) = SPredsExp sps x -> SPredsList sps (x :: l)

public export
SListPiToListPi :
  {atom : Type} ->
  {sps : SExpPreds atom} ->
  (signature : SExpEliminatorSig sps) ->
  (l : SList atom) ->
  SExpPredsToListPred sps l ->
  SPredsList sps l
SListPiToListPi signature [] pred = pred
SListPiToListPi signature (x :: l) pred = pred (sexpEliminator signature x)

public export
SExpSigToListSig :
  {atom : Type} -> {sps : SExpPreds atom} ->
  SExpEliminatorSig sps ->
  ListEliminatorSig (SExpPredsToListPred sps)
SExpSigToListSig signature =
  ListEliminatorArgs
    (nilElim signature)
    (\x, l, pred, spx =>
      consElim signature x l spx (SListPiToListPi signature l pred))

export
slistEliminatorMatchesListFold :
  {atom : Type} ->
  {sps : SExpPreds atom} ->
  (signature : SExpEliminatorSig sps) ->
  (l : SList atom) ->
  slistEliminator signature l =
    SListPiToListPi {sps} signature l
      (listEliminator (SExpSigToListSig signature) l)
slistEliminatorMatchesListFold signature [] =
  Refl
slistEliminatorMatchesListFold signature (x :: l) =
  applyEq {f=(consElim signature x l (sexpEliminator signature x))} Refl
    (slistEliminatorMatchesListFold signature l)

public export
SExpMetaPred : {atom : Type} -> SExpPred atom -> Type
SExpMetaPred {atom} sp = (x : SExp atom) -> sp x -> Type

public export
SListMetaPred : {atom : Type} -> SListPred atom -> Type
SListMetaPred {atom} lp = (l : SList atom) -> lp l -> Type

public export
SExpPredsMetaExp : {atom : Type} -> SExpPreds atom -> Type
SExpPredsMetaExp = SExpMetaPred . SPredsExp

public export
SExpPredsMetaList : {atom : Type} -> SExpPreds atom -> Type
SExpPredsMetaList = SListMetaPred . SPredsList

public export
SExpMetaPreds : {atom : Type} -> SExpPreds atom -> Type
SExpMetaPreds sps = (SExpPredsMetaExp sps, SExpPredsMetaList sps)

public export
SExpMetaPredsExp : {atom : Type} -> {sps : SExpPreds atom} ->
  SExpMetaPreds sps -> SExpPredsMetaExp sps
SExpMetaPredsExp = fst

public export
SExpMetaPredsList : {atom : Type} -> {sps : SExpPreds atom} ->
  SExpMetaPreds sps -> SExpPredsMetaList sps
SExpMetaPredsList = snd

public export
sexpMetaPredCompose : {atom : Type} ->
  (Type -> Type) -> {sps : SExpPreds atom} ->
  SExpPredsMetaExp sps -> SExpPredsMetaExp sps
sexpMetaPredCompose f smp = \x, spx => f (smp x spx)

public export
slistMetaPredCompose : {atom : Type} ->
  (Type -> Type) -> {sps : SExpPreds atom} ->
  SExpPredsMetaList sps -> SExpPredsMetaList sps
slistMetaPredCompose f lmp = \l, lpl => f (lmp l lpl)

public export
sexpMetaPredsCompose : {atom : Type} ->
  (Type -> Type) -> {sps : SExpPreds atom} ->
  SExpMetaPreds sps -> SExpMetaPreds sps
sexpMetaPredsCompose f smps =
  (sexpMetaPredCompose f (SExpMetaPredsExp smps),
   slistMetaPredCompose f (SExpMetaPredsList smps))

public export
SExpMetaComposedPreds : {atom : Type} ->
  (Type -> Type) -> SExpPreds atom -> Type
SExpMetaComposedPreds f sps = SExpMetaPreds (sexpPredsCompose f sps)

public export
SExpMetaPredToPred : {atom : Type} -> {sp : SExpPred atom} ->
  SExpMetaPred sp -> SExpPred atom
SExpMetaPredToPred {sp} smp = \l => sp l ~> smp l

public export
SListMetaPredToPred : {atom : Type} -> {lp : SListPred atom} ->
  SListMetaPred lp -> SListPred atom
SListMetaPredToPred {lp} lmp = \l => lp l ~> lmp l

public export
SExpMetaPi : {atom : Type} -> {sp : SExpPred atom} ->
  SExpMetaPred sp -> Type
SExpMetaPi {atom} {sp} smp = (x : SExp atom) -> (spx : sp x) -> smp x spx

public export
SListMetaPi : {atom : Type} -> {lp : SListPred atom} ->
  SListMetaPred lp -> Type
SListMetaPi {atom} {lp} lmp = (l : SList atom) -> (lpl : lp l) -> lmp l lpl

public export
SExpSigToMetaPred : {atom : Type} -> {sps : SExpPreds atom} ->
  SExpEliminatorSig sps -> SExpPredsMetaExp sps -> SExpPred atom
SExpSigToMetaPred signature smp = \x => smp x (sexpEliminator signature x)

public export
SListSigToMetaPred : {atom : Type} -> {sps : SExpPreds atom} ->
  SExpEliminatorSig sps -> SExpPredsMetaList sps -> SListPred atom
SListSigToMetaPred signature lmp = \l => lmp l (slistEliminator signature l)

public export
SExpSigToMetaPredExp : {atom : Type} -> {sps : SExpPreds atom} ->
  SExpMetaPreds sps -> SExpEliminatorSig sps -> SExpPred atom
SExpSigToMetaPredExp smps signature =
  SExpSigToMetaPred signature (SExpMetaPredsExp smps)

public export
SExpSigToMetaPredList : {atom : Type} -> {sps : SExpPreds atom} ->
  (smps : SExpMetaPreds sps) -> SExpEliminatorSig sps -> SListPred atom
SExpSigToMetaPredList smps signature =
  SListSigToMetaPred signature (SExpMetaPredsList smps)

public export
SExpSigToMetaPreds : {atom : Type} -> {sps : SExpPreds atom} ->
  (smps : SExpMetaPreds sps) -> SExpEliminatorSig sps -> SExpPreds atom
SExpSigToMetaPreds smps signature =
  (SExpSigToMetaPredExp smps signature, SExpSigToMetaPredList smps signature)

public export
SExpSigToComposedMetaPreds : {atom : Type} -> {sps : SExpPreds atom} ->
  (Type -> Type) -> SExpMetaPreds sps -> SExpEliminatorSig sps -> SExpPreds atom
SExpSigToComposedMetaPreds f smps signature =
  sexpPredsCompose f (SExpSigToMetaPreds smps signature)

public export
SExpSigPi : {atom : Type} -> {sps : SExpPreds atom} ->
  SExpEliminatorSig sps -> SExpMetaPred (SPredsExp sps) -> Type
SExpSigPi signature smp = SExpPi (SExpSigToMetaPred signature smp)

public export
SListSigPi : {atom : Type} -> {sps : SExpPreds atom} ->
  SExpEliminatorSig sps -> SListMetaPred (SPredsList sps) -> Type
SListSigPi signature lmp = SListPi (SListSigToMetaPred signature lmp)

public export
SSigPisExp : {atom : Type} -> {sps : SExpPreds atom} ->
  SExpMetaPreds sps -> SExpEliminatorSig sps -> Type
SSigPisExp smps signature = SExpSigPi signature (SExpMetaPredsExp smps)

public export
SSigPisList : {atom : Type} -> {sps : SExpPreds atom} ->
  SExpMetaPreds sps -> SExpEliminatorSig sps -> Type
SSigPisList smps signature = SListSigPi signature (SExpMetaPredsList smps)

public export
SExpSigPis : {atom : Type} -> {sps : SExpPreds atom} ->
  SExpMetaPreds sps -> SExpEliminatorSig sps -> Type
SExpSigPis smps signature =
  (SSigPisExp smps signature, SSigPisList smps signature)

public export
SExpMetaEliminatorSig : {atom : Type} -> {sps : SExpPreds atom} ->
  SExpMetaPreds sps -> SExpEliminatorSig sps -> Type
SExpMetaEliminatorSig smps signature =
  SExpEliminatorSig (SExpSigToMetaPreds smps signature)

public export
sexpMetaEliminators :
  {atom : Type} -> {0 sps : SExpPreds atom} ->
  {0 smps : SExpMetaPreds sps} ->
  {signature : SExpEliminatorSig sps} ->
  SExpMetaEliminatorSig smps signature ->
  SExpSigPis smps signature
sexpMetaEliminators = sexpEliminators

public export
sexpMetaEliminator :
  {atom : Type} -> {0 sps : SExpPreds atom} ->
  {0 smps : SExpMetaPreds sps} ->
  {signature : SExpEliminatorSig sps} ->
  SExpMetaEliminatorSig smps signature ->
  SSigPisExp smps signature
sexpMetaEliminator = fst . sexpEliminators

public export
slistMetaEliminator :
  {atom : Type} -> {0 sps : SExpPreds atom} ->
  {0 smps : SExpMetaPreds sps} ->
  {signature : SExpEliminatorSig sps} ->
  SExpMetaEliminatorSig smps signature ->
  SSigPisList smps signature
slistMetaEliminator = snd . sexpEliminators

public export
sexpMetaComposedSigEliminators :
  {f : Type -> Type} -> {app : Applicative f} ->
  {atom : Type} -> {sps : SExpPreds atom} ->
  {0 smps : SExpMetaComposedPreds f sps} ->
  {signature : f (SExpEliminatorSig sps)} ->
  SExpMetaEliminatorSig
    {sps=(sexpPredsCompose f sps)} smps
    (SExpSignatureComposeSig {sps} {app} signature) ->
  SExpSigPis
    {sps=(sexpPredsCompose f sps)} smps
    (SExpSignatureComposeSig {sps} {app} signature)
sexpMetaComposedSigEliminators = sexpMetaEliminators

public export
SExpMetaSignatureComposeSig :
  {f : Type -> Type} -> {app : Applicative f} ->
  {atom : Type} -> {sps : SExpPreds atom} ->
  {smps : SExpMetaPreds sps} ->
  {signature : SExpEliminatorSig sps} ->
  f (SExpMetaEliminatorSig {sps} smps signature) ->
  SExpMetaEliminatorSig {sps} (sexpMetaPredsCompose {sps} f smps) signature
SExpMetaSignatureComposeSig {f} {app} {smps} {signature} metaSig =
  SExpSignatureComposeSig
    {f} {app} {sps=(SExpSigToMetaPreds smps signature)} metaSig

public export
sexpMetaSignatureComposeSig :
  {f : Type -> Type} -> {app : Applicative f} ->
  {atom : Type} -> {sps : SExpPreds atom} ->
  {smps : SExpMetaPreds sps} ->
  {signature : SExpEliminatorSig sps} ->
  f (SExpMetaEliminatorSig smps signature) ->
  SExpSigPis {sps} (sexpMetaPredsCompose {sps} f smps) signature
sexpMetaSignatureComposeSig {f} {app} {sps} {smps} {signature} metaSig =
  sexpMetaEliminators {signature} {smps=(sexpMetaPredsCompose f smps)}
    (SExpMetaSignatureComposeSig {f} {app} {smps} metaSig)

public export
sexpMetaEliminatorsComposeSig :
  {atom : Type} -> {0 sps : SExpPreds atom} ->
  {0 smps : SExpMetaPreds sps} ->
  {signature : SExpEliminatorSig sps} ->
  SExpMetaEliminatorSig smps signature ->
  SExpSigPis smps signature
sexpMetaEliminatorsComposeSig = sexpEliminators

{- XXX express this in terms of signature composition -}
public export
sexpParameterizedEliminators :
  {0 atom : Type} ->
  {0 sps : List (SExpPreds atom) -> SExpPreds atom} ->
  (parameterizedSignature : List (SExpPreds atom) ~> SExpEliminatorSig . sps) ->
  List (SExpPreds atom) ~> SPredPis . sps
sexpParameterizedEliminators parameterizedSignature params =
  sexpEliminators (parameterizedSignature params)

{- XXX express this in terms of signature composition so that we can
 - act on the parameterized version rather than paramaterizing acting
 - on a non-parameterized version -}
public export
sexpMetaParameterizedSigEliminators :
  {atom : Type} -> {sps : List (SExpPreds atom) -> SExpPreds atom} ->
  {0 smps : List (SExpPreds atom) ~> SExpMetaPreds . sps} ->
  {signature : List (SExpPreds atom) ~> SExpEliminatorSig . sps} ->
  ((params : List (SExpPreds atom)) ->
    SExpMetaEliminatorSig (smps params) (signature params)) ->
  (params : List (SExpPreds atom)) ->
  SExpSigPis {sps=(sps params)} (smps params) (signature params)
sexpMetaParameterizedSigEliminators parameterizedMetaSig params =
  sexpMetaEliminators (parameterizedMetaSig params)

public export
SExpConstPred : {atom : Type} -> Type -> SExpPred atom
SExpConstPred type _ = type

public export
SListConstPred : {atom : Type} -> Type -> SListPred atom
SListConstPred type _ = type

public export
SExpConstPreds : {atom : Type} -> Type -> Type -> SExpPreds atom
SExpConstPreds sp lp = (SExpConstPred sp, SListConstPred lp)

public export
sexpConstEliminators :
  {0 atom : Type} -> {0 sp : Type} -> {0 lp : Type} ->
  (signature : SExpEliminatorSig {atom} (SExpConstPreds sp lp)) ->
  (SExp atom -> sp, SList atom -> lp)
sexpConstEliminators = sexpEliminators

public export
NonEmptySList : Type -> Type
NonEmptySList atom = NonEmptyList (SExp atom)

public export
SExpForAllTypes :
  {0 atom : Type} -> SExpPred atom -> SExpPreds atom
SExpForAllTypes sp =
  sexpConstEliminators {sp=Type} {lp=Type}
    (SExpEliminatorArgs
      (sp . ($^))
      (Pair . sp . ($|))
      ()
      (const (const Pair)))

public export
SExpForAll: {0 atom : Type} -> SExpPred atom -> SExpPred atom
SExpForAll = SPredsExp . SExpForAllTypes

public export
SListForAll: {0 atom : Type} -> SExpPred atom -> SListPred atom
SListForAll = SPredsList . SExpForAllTypes

public export
record SExpForAllEliminatorSig {atom : Type} (sp : SExpPred atom) where
  constructor SExpForAllEliminatorArgs
  atomElim : (a : atom) -> sp ($^ a)
  listElim : (l : SList atom) -> SListForAll sp l -> sp ($| l)

public export
SExpForAllEliminatorSigToEliminatorSig :
  {atom : Type} -> {sp : SExpPred atom} ->
  SExpForAllEliminatorSig sp ->
  SExpEliminatorSig (SExpForAll sp, SListForAll sp)
SExpForAllEliminatorSigToEliminatorSig signature =
  (SExpEliminatorArgs
    (atomElim signature)
    (\l, lForAll => (listElim signature l lForAll, lForAll))
    ()
    (\_, _ => MkPair))

public export
SForAllPis : {atom : Type} -> SExpPred atom -> Type
SForAllPis sp = (SExp atom ~> SExpForAll sp, SList atom ~> SListForAll sp)

public export
sexpForAllEliminators : {atom : Type} -> {sp : SExpPred atom} ->
  SExpForAllEliminatorSig sp ->
  SForAllPis sp
sexpForAllEliminators = sexpEliminators . SExpForAllEliminatorSigToEliminatorSig

public export
sexpForAllEliminator : {atom : Type} -> {sp : SExpPred atom} ->
  SExpForAllEliminatorSig sp ->
  SExp atom ~> SExpForAll sp
sexpForAllEliminator = fst . sexpForAllEliminators

public export
slistForAllEliminator : {atom : Type} -> {sp : SExpPred atom} ->
  SExpForAllEliminatorSig sp ->
  SList atom ~> SListForAll sp
slistForAllEliminator = snd . sexpForAllEliminators

public export
sexpForAllApplications :
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {atom : Type} -> {sp : SExp atom -> Type} ->
  ((x : SExp atom) -> SExpForAll (f . sp) x -> f (SExpForAll sp x),
   (l : SList atom) -> SListForAll (f . sp) l -> f (SListForAll sp l))
sexpForAllApplications {f} {sp} =
  sexpEliminators
    {sps=(\x => SExpForAll (f . sp) x -> f (SExpForAll sp x),
          \l => SListForAll (f . sp) l -> f (SListForAll sp l))}
    (SExpEliminatorArgs
      (\_ => id)
      (\l, mapLForAll, slForAll =>
        map MkPair (fst slForAll) <*> mapLForAll (snd slForAll))
      (\_ => pure ())
      (\x, l, mapSForAll, mapLForAll, slForAll =>
        (map MkPair
          (mapSForAll (fst slForAll))) <*> (mapLForAll (snd slForAll)))
    )

public export
sexpForAllApply :
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {atom : Type} -> {sp : SExp atom -> Type} ->
  (x : SExp atom) -> SExpForAll (f . sp) x -> f (SExpForAll sp x)
sexpForAllApply {f} {isApplicative} {sp} =
  fst (sexpForAllApplications {f} {isApplicative} {sp})

public export
slistForAllApply :
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {atom : Type} -> {sp : SExp atom -> Type} ->
  (l : SList atom) -> SListForAll (f . sp) l -> f (SListForAll sp l)
slistForAllApply {f} {isApplicative} {sp} =
  snd (sexpForAllApplications {f} {isApplicative} {sp})

public export
SExpForAllEliminatorComposeSig :
  {f : Type -> Type} -> {app : Applicative f} ->
  {atom : Type} -> {sp : SExpPred atom} ->
  f (SExpForAllEliminatorSig sp) ->
  SExpForAllEliminatorSig (f . sp)
SExpForAllEliminatorComposeSig {f} {app} {sp} signature =
  SExpForAllEliminatorArgs
    (\a => dpure app (map {f} atomElim signature) a)
    (\l, flpl =>
      (dpure app (map {f} (listElim {sp}) signature) l) <*>
        (slistForAllApply {f} {isApplicative=app} {sp} l flpl))

public export
sexpForAllEliminatorsComposeSig :
  {f : Type -> Type} -> {app : Applicative f} ->
  {atom : Type} -> {sp : SExpPred atom} ->
  f (SExpForAllEliminatorSig sp) ->
  SForAllPis (f . sp)
sexpForAllEliminatorsComposeSig {f} {sp} {app} =
  sexpForAllEliminators . SExpForAllEliminatorComposeSig {f} {sp} {app}

export
sexpForAllEliminatorsComposeSigConsistent :
  {f : Type -> Type} -> {app : Applicative f} ->
  {atom : Type} -> {sp : SExpPred atom} ->
  (signature : f (SExpForAllEliminatorSig sp)) ->
  ((x : SExp atom) ->
    sexpForAllApply {f} {isApplicative=app} {sp}
      x (sexpForAllEliminator {sp=(f . sp)}
          (SExpForAllEliminatorComposeSig {app} {sp} signature) x) =
    sexpEliminator {sps=(f . SExpForAll sp, f . SListForAll sp)}
      (SExpSignatureComposeSig {sps=(SExpForAll sp, SListForAll sp)} {app}
        (map {f} SExpForAllEliminatorSigToEliminatorSig signature))
      x,
   (l : SList atom) ->
    slistForAllApply {f} {isApplicative=app} {sp}
      l (slistForAllEliminator {sp=(f . sp)}
          (SExpForAllEliminatorComposeSig {app} {sp} signature) l) =
    slistEliminator {sps=(f . SExpForAll sp, f . SListForAll sp)}
      (SExpSignatureComposeSig {sps=(SExpForAll sp, SListForAll sp)} {app}
        (map {f} SExpForAllEliminatorSigToEliminatorSig signature))
      l)
sexpForAllEliminatorsComposeSigConsistent {app} {sp} signature =
  sexpEliminators
    {sps=
      (\x =>
        sexpForAllApply {f} {isApplicative=app} {sp}
          x (sexpForAllEliminator {sp=(f . sp)}
              (SExpForAllEliminatorComposeSig {app} {sp} signature) x) =
        sexpEliminator {sps=(f . SExpForAll sp, f . SListForAll sp)}
          (SExpSignatureComposeSig {sps=(SExpForAll sp, SListForAll sp)} {app}
            (map {f} SExpForAllEliminatorSigToEliminatorSig signature))
          x,
       \l =>
        slistForAllApply {f} {isApplicative=app} {sp}
          l (slistForAllEliminator {sp=(f . sp)}
              (SExpForAllEliminatorComposeSig {app} {sp} signature) l) =
        slistEliminator {sps=(f . SExpForAll sp, f . SListForAll sp)}
          (SExpSignatureComposeSig {sps=(SExpForAll sp, SListForAll sp)} {app}
            (map {f} SExpForAllEliminatorSigToEliminatorSig signature))
          l)}
    (SExpEliminatorArgs
      (?sexpForAllEliminatorsComposeSigConsistent_hole_atomElim)
      (?sexpForAllEliminatorsComposeSigConsistent_hole_listElim)
      (?sexpForAllEliminatorsComposeSigConsistent_hole_nilElim)
      (?sexpForAllEliminatorsComposeSigConsistent_hole_consElim)
    )

public export
SExpForAllMetaPred : {atom : Type} -> SExpPred atom -> Type
SExpForAllMetaPred sp = (x : SExp atom) -> SExpForAll sp x -> Type

public export
SListForAllMetaPred : {atom : Type} -> SExpPred atom -> Type
SListForAllMetaPred sp = (l : SList atom) -> SListForAll sp l -> Type

public export
SExpForAllMetaPreds : {atom : Type} -> SExpPred atom -> Type
SExpForAllMetaPreds sp = (SExpForAllMetaPred sp, SListForAllMetaPred sp)

public export
SExpForAllMetaPi : {atom : Type} -> {sp : SExpPred atom} ->
  SExpForAllMetaPreds sp -> SExpForAllEliminatorSig sp -> Type
SExpForAllMetaPi {atom} smps signature =
  (x : SExp atom) -> fst smps x (sexpForAllEliminator signature x)

public export
SListForAllMetaPi : {atom : Type} -> {sp : SExpPred atom} ->
  SExpForAllMetaPreds sp -> SExpForAllEliminatorSig sp -> Type
SListForAllMetaPi {atom} smps signature =
  (l : SList atom) -> snd smps l (slistForAllEliminator signature l)

public export
SExpForAllMetaPis : {atom : Type} -> {sp : SExpPred atom} ->
  SExpForAllMetaPreds sp -> SExpForAllEliminatorSig sp -> Type
SExpForAllMetaPis smps signature =
  (SExpForAllMetaPi smps signature, SListForAllMetaPi smps signature)

public export
sexpForAllMetaEliminators : {atom : Type} -> {sp : SExpPred atom} ->
  {smps : SExpForAllMetaPreds sp} ->
  {signature : SExpForAllEliminatorSig sp} ->
  SExpMetaEliminatorSig smps
    (SExpForAllEliminatorSigToEliminatorSig signature) ->
  SExpForAllMetaPis smps signature
sexpForAllMetaEliminators = sexpMetaEliminators

public export
SExpExistsTypes :
  {0 atom : Type} -> SExpPred atom -> SExpPreds atom
SExpExistsTypes sp =
  sexpConstEliminators {sp=Type} {lp=Type}
    (SExpEliminatorArgs
      (sp . ($^))
      (Either . sp . ($|))
      Void
      (const (const Either)))

public export
SExpExists : {0 atom : Type} -> SExpPred atom -> SExpPred atom
SExpExists = SPredsExp . SExpExistsTypes

public export
SListExists : {0 atom : Type} -> SExpPred atom -> SListPred atom
SListExists = SPredsList . SExpExistsTypes

public export
SExpExistsSome : {0 atom : Type} -> SExpPred atom -> SExpPred atom
SExpExistsSome sp = NonEmptyList . SExpExists sp

public export
SListExistsSome : {0 atom : Type} -> SExpPred atom -> SListPred atom
SListExistsSome sp = NonEmptyList . SListExists sp

public export
SExpAllLeftOrExistsRight : {0 atom : Type} -> (sr, sl : SExpPred atom) ->
  SExpPred atom
SExpAllLeftOrExistsRight sr sl x =
  Either (SExpForAll sr x) (SExpExistsSome sl x)

public export
SListAllLeftOrExistsRight : {0 atom : Type} -> (sr, sl : SExpPred atom) ->
  SListPred atom
SListAllLeftOrExistsRight sr sl l =
  Either (SListForAll sr l) (SListExistsSome sl l)

public export
slistExistsSomeShift : {0 atom : Type} ->
  {sl, sr : SExpPred atom} ->
  {x : SExp atom} -> {l : SList atom} ->
  SListExistsSome sr l ->
  SListExistsSome sr (x :: l)
slistExistsSomeShift = neListMap Right

{- XXX write signature composer for this -}
public export
record SExpConstListEliminatorSig {0 atom : Type} (sp : Type) where
  constructor SExpConstListEliminatorArgs
  atomElim : atom -> sp
  listElim : (l : SList atom) -> List sp -> sp

public export
SExpConstListEliminatorSigToEliminatorSig :
  {0 atom : Type} -> {0 sp : Type} ->
  SExpConstListEliminatorSig {atom} sp ->
  SExpEliminatorSig {atom} (const sp, const (List sp))
SExpConstListEliminatorSigToEliminatorSig {atom} signature =
  (SExpEliminatorArgs {atom}
    (atomElim signature)
    (listElim signature)
    []
    (const (const (::))))

public export
sexpConstListEliminators :
  {0 atom : Type} -> {0 sp : Type} ->
  (signature : SExpConstListEliminatorSig {atom} sp) ->
  (SExp atom -> sp, SList atom -> List sp)
sexpConstListEliminators {atom} {sp} =
  sexpEliminators . SExpConstListEliminatorSigToEliminatorSig {atom} {sp}

public export
sexpMaps : {0 a, b : Type} -> (a -> b) -> (SExp a -> SExp b, SList a -> SList b)
sexpMaps f =
  sexpConstListEliminators (SExpConstListEliminatorArgs (($^) . f) (const ($|)))

public export
sexpMap : {0 a, b : Type} -> (a -> b) -> SExp a -> SExp b
sexpMap = fst . sexpMaps

public export
slistMap : {0 a, b : Type} -> (a -> b) -> SList a -> SList b
slistMap = snd . sexpMaps

Functor SExp where
  map = sexpMap

Functor SList where
  map = slistMap

public export
sexpApplicationsToAtom : {0 a, b : Type} ->
  SExp (a -> b) ->
  a -> SExp b
sexpApplicationsToAtom xab x =
  fst
    (sexpConstListEliminators
      (SExpConstListEliminatorArgs
        (\x' => $^ (x' x))
        (const ($|))))
  xab

public export
sexpApplications : {0 a, b : Type} ->
  SExp (a -> b) ->
  (SExp a -> SExp b, SList a -> SList b)
sexpApplications xab =
  sexpConstListEliminators
    (SExpConstListEliminatorArgs
      (sexpApplicationsToAtom xab)
      (const ($|)))

public export
sexpApply : {0 a, b : Type} -> SExp (a -> b) -> SExp a -> SExp b
sexpApply xab = fst (sexpApplications xab)

public export
sexpApplyList : {0 a, b : Type} -> SExp (a -> b) -> SList a -> SList b
sexpApplyList xab = snd (sexpApplications xab)

public export
slistApply : {0 a, b : Type} -> SList (a -> b) -> SList a -> SList b
slistApply =
  listEliminator {atom=(SExp (a -> b))} {lp=const (SList a -> SList b)}
    (ListEliminatorArgs
      (const [])
      (\xab, lab, lalb, la => sexpApplyList xab la ++ lalb la))

Applicative SExp where
  pure = ($^)
  (<*>) = sexpApply

Applicative SList where
  pure x = [ ($^ x) ]
  (<*>) = slistApply
