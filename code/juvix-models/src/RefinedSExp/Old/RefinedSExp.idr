module RefinedSExp.Old.RefinedSExp

import public RefinedSExp.Old.RefinedList
import public RefinedSExp.Old.SExp
import public Library.Decidability

%default total

public export
record SExpEitherFoldSig {atom : Type} (f : Type -> Type)
  (sl, sr : SExp atom -> Type) where
    constructor SExpEitherFoldArgs
    expElim : (a : atom) -> (l : SList atom) ->
      f (SListForAll sl l -> DepEither sl sr (a $: l))

public export
SExpEitherExpElimToExpElim :
  {atom : Type} ->
  {f : Type -> Type} -> Applicative f =>
  {sl, sr : SExp atom -> Type} ->
  ((a : atom) -> (l : SList atom) ->
    f (SListForAll sl l -> DepEither sl sr (a $: l))) ->
  ((a : atom) -> (l : SList atom) ->
    f (SListEitherForAll sl sr l) -> f (SExpEitherForAll sl sr (a $: l)))
SExpEitherExpElimToExpElim expElimIn a l =
  map SExpEitherForAllExpPairMergeResult .
    applyEitherElim
      (pure (SExpEitherForAllExpResultExecuted {sl}) <.>
        map fMkPair (expElimIn a l))
      (pure SExpEitherForAllExpResultNotExecuted)

public export
SExpEitherFoldSigToEliminatorSig :
  {atom : Type} ->
  {f : Type -> Type} -> Applicative f =>
  {sl, sr : SExp atom -> Type} ->
  SExpEitherFoldSig f sl sr ->
  SExpEliminatorSig (f . SExpEitherForAll sl sr) (f . SListEitherForAll sl sr)
SExpEitherFoldSigToEliminatorSig {f} {sl} signature =
  (SExpEliminatorArgs
    (SExpEitherExpElimToExpElim {sl} (expElim signature))
    (pure (Left ()))
    (\_, _ => SExpEitherForAllCons {f} {sl}))

public export
sexpEitherFolds :
  {atom : Type} ->
  {f : Type -> Type} -> Applicative f =>
  {sl, sr : SExp atom -> Type} ->
  (signature : SExpEitherFoldSig f sl sr) ->
  ((x : SExp atom) -> f (SExpEitherForAll sl sr x),
   (l : SList atom) -> f (SListEitherForAll sl sr l))
sexpEitherFolds {atom} {f} {sl} {sr} signature =
  sexpEliminators (SExpEitherFoldSigToEliminatorSig signature)

public export
sexpEitherFold :
  {atom : Type} ->
  {f : Type -> Type} -> Applicative f =>
  {sl, sr : SExp atom -> Type} ->
  (signature : SExpEitherFoldSig f sl sr) ->
  (x : SExp atom) -> f (SExpEitherForAll sl sr x)
sexpEitherFold {atom} {f} {sl} {sr} signature =
  fst (sexpEitherFolds signature)

public export
slistEitherFold :
  {atom : Type} ->
  {f : Type -> Type} -> Applicative f =>
  {sl, sr : SExp atom -> Type} ->
  (signature : SExpEitherFoldSig f sl sr) ->
  (l : SList atom) -> f (SListEitherForAll sl sr l)
slistEitherFold {atom} {f} {sl} {sr} signature =
  snd (sexpEitherFolds signature)

public export
record SExpEitherMetaFoldSig
  {atom : Type}
  {f : Type -> Type} {isApplicative : Applicative f}
  {sl, sr : SExp atom -> Type}
  (signature : SExpEitherFoldSig f sl sr)
  (spp : (x : SExp atom) -> f (SExpEitherForAll sl sr x) -> Type)
  (lpp : (l : SList atom) -> f (SListEitherForAll sl sr l) -> Type)
  where
    constructor SExpEitherMetaFoldArgs
    metaExpElim : (a : atom) -> (l : SList atom) ->
      lpp l (slistEitherFold signature l) ->
      spp (a $: l)
        (SExpEitherExpElimToExpElim {f} {sl} {sr} (expElim signature)
          a l (slistEitherFold signature l))
    metaNilElim : lpp [] (pure (Left ()))
    metaConsElim : (x : SExp atom) -> (l : SList atom) ->
      spp x (sexpEitherFold signature x) ->
      lpp l (slistEitherFold signature l) ->
      lpp (x $+ l) (SExpEitherForAllCons {f} {sl} {sr}
        (sexpEitherFold signature x) (slistEitherFold signature l))

public export
SExpEitherMetaFoldSigToEliminatorSig :
  {atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {sl, sr : SExp atom -> Type} ->
  {signature : SExpEitherFoldSig f sl sr} ->
  {spp : (x : SExp atom) -> f (SExpEitherForAll sl sr x) -> Type} ->
  {lpp : (l : SList atom) -> f (SListEitherForAll sl sr l) -> Type} ->
  (metaSig : SExpEitherMetaFoldSig {isApplicative} signature spp lpp) ->
  SExpEliminatorSig
    (\x => spp x (sexpEitherFold signature x))
    (\l => lpp l (slistEitherFold signature l))
SExpEitherMetaFoldSigToEliminatorSig metaSig =
  SExpEliminatorArgs
    (metaExpElim metaSig)
    (metaNilElim metaSig)
    (metaConsElim metaSig)

public export
sexpEitherMetaFolds :
  {atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {sl, sr : SExp atom -> Type} ->
  {signature : SExpEitherFoldSig f sl sr} ->
  {spp : (x : SExp atom) -> f (SExpEitherForAll sl sr x) -> Type} ->
  {lpp : (l : SList atom) -> f (SListEitherForAll sl sr l) -> Type} ->
  (metaSig : SExpEitherMetaFoldSig {isApplicative} signature spp lpp) ->
  ((x : SExp atom) -> spp x (sexpEitherFold signature x),
   (l : SList atom) -> lpp l (slistEitherFold signature l))
sexpEitherMetaFolds metaSig =
  sexpEliminators (SExpEitherMetaFoldSigToEliminatorSig metaSig)

public export
sexpEitherMetaFold :
  {atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {sl, sr : SExp atom -> Type} ->
  {signature : SExpEitherFoldSig f sl sr} ->
  {spp : (x : SExp atom) -> f (SExpEitherForAll sl sr x) -> Type} ->
  {lpp : (l : SList atom) -> f (SListEitherForAll sl sr l) -> Type} ->
  (metaSig : SExpEitherMetaFoldSig {isApplicative} signature spp lpp) ->
  (x : SExp atom) -> spp x (sexpEitherFold signature x)
sexpEitherMetaFold = fst . sexpEitherMetaFolds

public export
slistEitherMetaFold :
  {atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {sl, sr : SExp atom -> Type} ->
  {signature : SExpEitherFoldSig f sl sr} ->
  {spp : (x : SExp atom) -> f (SExpEitherForAll sl sr x) -> Type} ->
  {lpp : (l : SList atom) -> f (SListEitherForAll sl sr l) -> Type} ->
  (metaSig : SExpEitherMetaFoldSig {isApplicative} signature spp lpp) ->
  (l : SList atom) -> lpp l (slistEitherFold signature l)
slistEitherMetaFold = snd . sexpEitherMetaFolds

public export
SExpRefinements :
  {atom : Type} ->
  {f : Type -> Type} -> Applicative f =>
  {sl, sr : SExp atom -> Type} ->
  (selector : SExpEitherFoldSig f sl sr) ->
  (SExp atom -> f Type, SList atom -> f Type)
SExpRefinements selector =
  let folds = sexpEitherFolds selector in
  (\x => map IsLeft (fst folds x), \l => map IsLeft (snd folds l))

public export
SExpRefinement :
  {atom : Type} ->
  {f : Type -> Type} -> Applicative f =>
  {sl, sr : SExp atom -> Type} ->
  (selector : SExpEitherFoldSig f sl sr) ->
  SExp atom -> f Type
SExpRefinement = fst . SExpRefinements

public export
SListRefinement :
  {atom : Type} ->
  {f : Type -> Type} -> Applicative f =>
  {sl, sr : SExp atom -> Type} ->
  (selector : SExpEitherFoldSig f sl sr) ->
  SList atom -> f Type
SListRefinement = snd . SExpRefinements

public export
SExpLiftedRefinements :
  {atom : Type} ->
  {f : Type -> Type} -> Applicative f =>
  {sl, sr : SExp atom -> Type} ->
  (selector : SExpEitherFoldSig f sl sr) ->
  (f (SExp atom -> Type), f (SList atom -> Type))
SExpLiftedRefinements selector =
  let refinements = SExpRefinements selector in
  ?SExpLiftedRefinements_hole

public export
RefinedSExpTypes :
  {atom : Type} ->
  {f : Type -> Type} -> Applicative f =>
  {sl, sr : SExp atom -> Type} ->
  (selector : SExpEitherFoldSig f sl sr) ->
  (f Type, f Type)
RefinedSExpTypes selector =
  let refinements = SExpLiftedRefinements selector in
  (map (DPair (SExp atom)) (fst refinements),
   map (DPair (SList atom)) (snd refinements))

public export
RefinedSExp :
  {atom : Type} ->
  {f : Type -> Type} -> Applicative f =>
  {sl, sr : SExp atom -> Type} ->
  (selector : SExpEitherFoldSig f sl sr) ->
  f Type
RefinedSExp selector =
  fst (RefinedSExpTypes selector)

public export
RefinedSList :
  {atom : Type} ->
  {f : Type -> Type} -> Applicative f =>
  {sl, sr : SExp atom -> Type} ->
  (selector : SExpEitherFoldSig f sl sr) ->
  f Type
RefinedSList selector =
  snd (RefinedSExpTypes selector)

public export
record SExpRefinementEliminatorSig
  {atom : Type}
  {f : Type -> Type}
  {isApplicative : Applicative f}
  {mAlg : Algebra f Type}
  {sl, sr : SExp atom -> Type}
  (signature : SExpEitherFoldSig f sl sr)
  (srp : (x : SExp atom) -> mAlg (SExpRefinement signature x) -> Type)
  (lrp : (l : SList atom) -> mAlg (SListRefinement signature l) -> Type)
  where
    constructor SExpRefinementEliminatorArgs

public export
sexpRefinementEliminators :
  {atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {mAlg : Algebra f Type} ->
  {sl, sr : SExp atom -> Type} ->
  {signature : SExpEitherFoldSig f sl sr} ->
  {srp : (x : SExp atom) -> mAlg (SExpRefinement signature x) -> Type} ->
  {lrp : (l : SList atom) -> mAlg (SListRefinement signature l) -> Type} ->
  (metaSig : SExpRefinementEliminatorSig {isApplicative} {mAlg} signature srp lrp) ->
  ((x : SExp atom) -> (rx : mAlg (SExpRefinement signature x)) -> srp x rx,
   (l : SList atom) -> (rl : mAlg (SListRefinement signature l)) -> lrp l rl)
sexpRefinementEliminators = ?sexpRefinementEliminators_hole

public export
record RefinedSExpEliminatorSig
  {atom : Type}
  {f : Type -> Type}
  {isApplicative : Applicative f} {mAlg : Algebra f Type}
  {sl, sr : SExp atom -> Type}
  (signature : SExpEitherFoldSig f sl sr)
  (srp : mAlg (RefinedSExp signature) -> Type)
  (lrp : mAlg (RefinedSList signature) -> Type)
  where
    constructor RefinedSExpEliminatorArgs

public export
refinedSExpEliminators :
  {atom : Type} ->
  {f : Type -> Type} ->
  {isApplicative : Applicative f} ->
  {mAlg : Algebra f Type} ->
  {sl, sr : SExp atom -> Type} ->
  {signature : SExpEitherFoldSig f sl sr} ->
  {srp : mAlg (RefinedSExp signature) -> Type} ->
  {lrp : mAlg (RefinedSList signature) -> Type} ->
  (metaSig : RefinedSExpEliminatorSig
    {isApplicative} {mAlg} signature srp lrp) ->
  ((rx : mAlg (RefinedSExp signature)) -> srp rx,
   (rl : mAlg (RefinedSList signature)) -> lrp rl)
refinedSExpEliminators = ?refinedSExpEliminators_hole

public export
record RefinedSExpTransformerSig
  {f : Type -> Type}
  {isApplicative : Applicative f}
  {mAlg : Algebra f Type}
  {atom, atom' : Type}
  {sl, sr, sl', sr' : SExp atom -> Type}
  (signature : SExpEitherFoldSig f sl sr)
  (signature' : SExpEitherFoldSig f sl' sr')
  where
    constructor RefinedSExpTransformerArgs

public export
refinedSExpTransformers :
  {f : Type -> Type} ->
  {isApplicative : Applicative f} ->
  {mAlg : Algebra f Type} ->
  {atom, atom' : Type} ->
  {sl, sr, sl', sr' : SExp atom -> Type} ->
  {signature : SExpEitherFoldSig f sl sr} ->
  {signature' : SExpEitherFoldSig f sl' sr'} ->
  (transformSig : RefinedSExpTransformerSig
    {isApplicative} {mAlg} signature signature') ->
  (mAlg (RefinedSExp signature) ->
    mAlg (RefinedSExp signature'),
   mAlg (RefinedSList signature) ->
    mAlg (RefinedSList signature'))
refinedSExpTransformers = ?refinedSExpTransformers_hole

public export
record DecidablePredicate (atom : Type) where
  constructor ResultPredicates
  SuccessPredicate : SExp atom -> Type
  FailurePredicate : SExp atom -> Type

public export
data DecisionResult : {atom : Type} ->
    (predicate : DecidablePredicate atom) -> SExp atom -> Type where
  DecisionSuccess : {predicate : DecidablePredicate atom} -> {x : SExp atom} ->
    SuccessPredicate predicate x -> DecisionResult predicate x
  DecisionFailure : {predicate : DecidablePredicate atom} -> {x : SExp atom} ->
    FailurePredicate predicate x -> DecisionResult predicate x

public export
DecisionSuccessInjective : {atom : Type} ->
  {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> {result, result' : SuccessPredicate predicate x} ->
  DecisionSuccess {x} {predicate} result =
    DecisionSuccess {x} {predicate} result' ->
  result = result'
DecisionSuccessInjective Refl = Refl

public export
DecisionFailureInjective : {atom : Type} ->
  {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> {result, result' : FailurePredicate predicate x} ->
  DecisionFailure {x} {predicate} result =
    DecisionFailure {x} {predicate} result' ->
  result = result'
DecisionFailureInjective Refl = Refl

public export
data IsSuccess : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    {x : SExp atom} -> DecisionResult predicate x -> Type where
  Successful : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    {x : SExp atom} -> (result : SuccessPredicate predicate x) ->
    IsSuccess {x} {predicate} (DecisionSuccess result)

public export
IsSuccessExtract : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> {result : DecisionResult predicate x} ->
  IsSuccess result -> SuccessPredicate predicate x
IsSuccessExtract (Successful success) = success

public export
IsSuccessExtractElim : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> {result : DecisionResult predicate x} ->
  (succeeded : IsSuccess result) ->
  result = DecisionSuccess (IsSuccessExtract succeeded)
IsSuccessExtractElim (Successful _) = Refl

public export
SuccessIsSuccessful : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> {success : SuccessPredicate predicate x} ->
  {result : DecisionResult predicate x} ->
  result = DecisionSuccess {x} {predicate} success ->
  IsSuccess {x} {predicate} result
SuccessIsSuccessful {x} {success} Refl = Successful success

public export
isSuccess : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> (result : DecisionResult predicate x) ->
  Dec (IsSuccess result)
isSuccess (DecisionSuccess success) = Yes (Successful success)
isSuccess (DecisionFailure _) =
  No (\success => case success of Successful _ impossible)

public export
NotSuccessExtract : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> {result : DecisionResult predicate x} ->
  Not (IsSuccess result) -> FailurePredicate predicate x
NotSuccessExtract {result=(DecisionSuccess success)} notSuccess =
  void (notSuccess (Successful success))
NotSuccessExtract {result=(DecisionFailure failure)} _ = failure

public export
data IsFailure : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    {x : SExp atom} -> DecisionResult predicate x -> Type where
  Failed : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    {x : SExp atom} -> (result : FailurePredicate predicate x) ->
    IsFailure {x} {predicate} (DecisionFailure result)

public export
IsFailureExtract : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> {result : DecisionResult predicate x} ->
  IsFailure result -> FailurePredicate predicate x
IsFailureExtract (Failed failure) = failure

public export
IsFailureExtractElim : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> {result : DecisionResult predicate x} ->
  (succeeded : IsFailure result) ->
  result = DecisionFailure (IsFailureExtract succeeded)
IsFailureExtractElim (Failed _) = Refl

public export
isFailure : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> (result : DecisionResult predicate x) ->
  Dec (IsFailure result)
isFailure (DecisionSuccess _) =
  No (\failed => case failed of Failed _ impossible)
isFailure (DecisionFailure failed) = Yes (Failed failed)

public export
NotFailureExtract : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> {result : DecisionResult predicate x} ->
  Not (IsFailure result) -> SuccessPredicate predicate x
NotFailureExtract {result=(DecisionSuccess success)} _ = success
NotFailureExtract {result=(DecisionFailure failure)} notFailure =
  void (notFailure (Failed failure))

public export
record InductiveDecisionSig
  {atom : Type}
  (predicate : DecidablePredicate atom)
  (contextType : Type) where
    constructor InductiveDecisionArgs
    initialContext : contextType
    decideOne :
      (a : atom) -> (l : SList atom) ->
      SListForAll (SuccessPredicate predicate) l ->
      (contextType -> (contextType, DecisionResult predicate (a $: l)))
    failOne :
      DPair (SExp atom) (FailurePredicate predicate) ->
      contextType -> contextType

public export
inductiveDecide : {atom : Type} ->
  {predicate : DecidablePredicate atom} -> {contextType : Type} ->
  InductiveDecisionSig predicate contextType ->
  (x : SExp atom) -> Maybe (SExpForAll (SuccessPredicate predicate) x)
inductiveDecide decisionSig x' =
  Builtin.snd (fst
    (sexpDepFoldsContextIndependent
      {fs=(Prelude.Basics.id)} {fl=(Prelude.Basics.id)}
      {sp=(\x => Maybe (SExpForAll (SuccessPredicate predicate) x))}
      {lp=(\x => Maybe (SListForAll (SuccessPredicate predicate) x))}
      (SExpEliminatorArgs
        (\a, l, tail, context =>
          let
            (tailContext, tailDecision) = tail context
          in
          case tailDecision of
            Just tailSuccess =>
              case decideOne decisionSig a l tailSuccess tailContext of
                (returnContext, DecisionSuccess headSuccess) =>
                  (returnContext, Just (headSuccess, tailSuccess))
                (failureContext, DecisionFailure headFailure) =>
                  (failOne decisionSig ((a $: l) ** headFailure) failureContext,
                   Nothing)
            Nothing => (tailContext, Nothing))
        (\context => (context, Just ()))
        (\x, l, head, tail, context =>
          let
            (tailContext, tailResult) = tail context
          in
          case tailResult of
            Just tailSuccess =>
              let (headContext, headResult) = head tailContext in
              case headResult of
                Just headSuccess =>
                  (headContext, Just (headSuccess, tailSuccess))
                Nothing => (headContext, Nothing)
            Nothing => (fst (head tailContext), Nothing)))
      (initialContext decisionSig)
    )
  x')

public export
Checks : {atom : Type} ->
  {predicate : DecidablePredicate atom} -> {contextType : Type} ->
  InductiveDecisionSig predicate contextType ->
  SExp atom -> Type
Checks signature x = IsJust (inductiveDecide signature x)

public export
Checked : {atom : Type} ->
  {predicate : DecidablePredicate atom} -> {contextType : Type} ->
  InductiveDecisionSig predicate contextType ->
  Type
Checked signature = DPair (SExp atom) (Checks signature)

public export
decChecked : {atom : Type} ->
  {predicate : DecidablePredicate atom} -> {contextType : Type} ->
  (signature : InductiveDecisionSig predicate contextType) ->
  (x : SExp atom) -> Dec (Checks signature x)
decChecked signature x = IsJustDec (inductiveDecide signature x)

public export
checksInjective : {atom : Type} ->
  {predicate : DecidablePredicate atom} -> {contextType : Type} ->
  {signature : InductiveDecisionSig predicate contextType} ->
  {x : SExp atom} -> (checks, checks' : Checks signature x) ->
  checks = checks'
checksInjective = IsJustUnique

public export
checkedInjective : {atom : Type} ->
  {predicate : DecidablePredicate atom} -> {contextType : Type} ->
  {signature : InductiveDecisionSig predicate contextType} ->
  {checked, checked' : Checked signature} ->
  (fst checked = fst checked') ->
  checked = checked'
checkedInjective {signature} =
  JustDPairInjective {dec=(inductiveDecide signature)}
