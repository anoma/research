module RefinedSExp.Old.OldRefinedSExp

import public RefinedSExp.Old.OldSExp
import public Library.Decidability

%default total

mutual
  public export
  sExpEq : {atom : Type} -> DecEqPred atom -> DecEqPred (SExp atom)
  sExpEq deq (a $: l) (a' $: l') = case (deq a a', sListEq deq l l') of
    (Yes Refl, Yes Refl) => Yes Refl
    (No neq, _) => No (\eq => case eq of Refl => neq Refl)
    (_ , No neq) => No (\eq => case eq of Refl => neq Refl)

  public export
  sListEq : {atom : Type} -> DecEqPred atom -> DecEqPred (SList atom)
  sListEq deq ($|) ($|) = Yes Refl
  sListEq deq (x $+ l) ($|) = No (\eq => case eq of Refl impossible)
  sListEq deq ($|) (x $+ l) = No (\eq => case eq of Refl impossible)
  sListEq deq (x $+ l) (x' $+ l') = case (sExpEq deq x x', sListEq deq l l') of
    (Yes Refl, Yes Refl) => Yes Refl
    (No neq, _) => No (\eq => case eq of Refl => neq Refl)
    (_ , No neq) => No (\eq => case eq of Refl => neq Refl)

public export
record DecidablePredicate (atom : Type) where
  constructor ResultPredicates
  SuccessPredicate : SPredicate atom
  FailurePredicate : SPredicate atom

public export
data DecisionResult : {atom : Type} ->
    (predicate : DecidablePredicate atom) -> SPredicate atom where
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
DecidableContextPred : (contextType, atom : Type) -> Type
DecidableContextPred contextType atom = contextType -> DecidablePredicate atom

public export
record InductiveDecisionSig {contextType : Type} {atom : Type}
  (predicate : DecidableContextPred contextType atom) where
    constructor InductiveDecisionArgs
    pushExp : contextType -> SExp atom -> contextType
    pushFailure : Void
    expElim :
      (contextUponEntry : contextType) ->
      (a : atom) -> (l : SList atom) ->
      SLForAll
        (SuccessPredicate (predicate (pushExp contextUponEntry (a $: l)))) l ->
      (contextType, DecisionResult (predicate contextUponEntry) (a $: l))

public export
ListDecisionResult : {contextType : Type} -> {atom : Type} ->
  (predicate : DecidableContextPred contextType atom) ->
  contextType -> SLPredicate atom
ListDecisionResult predicate context l =
  Maybe (SLForAll (SuccessPredicate (predicate context)) l)

public export
inductiveDecide : {contextType : Type} -> {atom : Type} ->
  {predicate : DecidableContextPred contextType atom} ->
  InductiveDecisionSig predicate ->
  (context : contextType) ->
  (x : SExp atom) ->
  (contextType, DecisionResult (predicate context) x)
inductiveDecide signature =
  sExpIndContext
    {sp=(DecisionResult . predicate)}
    {lp=(ListDecisionResult predicate)}
    (SIndContextArgs
      (\contextUponEntry, a, l, listInd =>
        let indOut = listInd (pushExp signature contextUponEntry (a $: l)) in
        case (snd indOut) of
          Just allSucceed => ?inductiveDecide_hole_expElim_success
          Nothing => ?inductiveDecide_hole_expElim_failure)
      (?inductiveDecide_hole_nilElim)
      (?inductiveDecide_hole_consElim))

mutual
  public export
  sDecideInd :
    {atom : Type} -> {sp : SPredicate atom} -> {lp : SLPredicate atom} ->
    SIndSig sp lp ->
    (x : SExp atom) -> sp x
  sDecideInd signature (a $: l) = expElim signature a l (sListInd signature l)

  public export
  sListDecideInd :
    {atom : Type} -> {sp : SPredicate atom} -> {lp : SLPredicate atom} ->
    SIndSig sp lp ->
    (l : SList atom) -> lp l
  sListDecideInd signature ($|) = nilElim signature
  sListDecideInd signature (x $+ l) =
    consElim signature x l (sExpInd signature x) (sListInd signature l)

public export
InductiveType : {contextType : Type} -> {atom : Type} ->
  {predicate : DecidableContextPred contextType atom} ->
  InductiveDecisionSig predicate ->
  (context : contextType) ->
  Type
InductiveType signature context =
  (x : SExp atom ** IsSuccess (snd (inductiveDecide signature context x)))

public export
record InductiveLambdaSig {contextType : Type} {domAtom : Type} {codAtom : Type}
  {domPred : DecidableContextPred contextType domAtom}
  {codPred : DecidableContextPred contextType codAtom}
  (domain : InductiveDecisionSig domPred)
  (codomain : InductiveDecisionSig codPred)
  where
    constructor InductiveLambda

public export
inductiveFunction : {contextType : Type} -> {domAtom, codAtom : Type} ->
  {domPred : DecidableContextPred contextType domAtom} ->
  {codPred : DecidableContextPred contextType codAtom} ->
  {domain : InductiveDecisionSig domPred} ->
  {codomain : InductiveDecisionSig codPred} ->
  InductiveLambdaSig domain codomain ->
  (context : contextType) ->
  (InductiveType domain context -> InductiveType codomain context)
inductiveFunction signature context = ?InductiveFunction_hole

public export
record InductivePiSig {contextType : Type} {domAtom : Type} {codAtom : Type}
  {domPred : DecidableContextPred contextType domAtom}
  {codPred : DecidableContextPred contextType codAtom}
  (domain : InductiveDecisionSig domPred)
  (codomain : InductiveDecisionSig codPred)
  where
    constructor InductivePi

public export
inductiveDependentFunction : {contextType : Type} -> {domAtom, codAtom : Type} ->
  {domPred : DecidableContextPred contextType domAtom} ->
  {codPred : DecidableContextPred contextType codAtom} ->
  {domain : InductiveDecisionSig domPred} ->
  {codomain : InductiveDecisionSig codPred} ->
  InductivePiSig domain codomain ->
  (context : contextType) ->
  (InductiveType domain context -> InductiveType codomain context)
inductiveDependentFunction signature context = ?InductiveDependent_Function_hole

public export
record InductiveTypecheck {atom : Type}
    (predicate : DecidablePredicate atom) where
  constructor MkInductiveTypecheck
  typecheckOne : (a : atom) -> (l : SList atom) ->
    SLForAll (SuccessPredicate predicate) l -> DecisionResult predicate (a $: l)
  MergedFailures : Type
  firstFailure : (x : SExp atom) -> FailurePredicate predicate x ->
    MergedFailures
  mergeFailures : MergedFailures -> MergedFailures -> MergedFailures

public export
data TypechecksAs : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    InductiveTypecheck predicate ->
    (x : SExp atom) -> SuccessPredicate predicate x -> Type where
  AllSubtermsTypecheckAs : {atom : Type} ->
    {predicate : DecidablePredicate atom} ->
    {check : InductiveTypecheck predicate} ->
    {a : atom} -> {l : SList atom} ->
    (subtermsCheck : SLForAll (SDepPredPair (TypechecksAs check)) l) ->
    (checkedType : SuccessPredicate predicate (a $: l)) ->
    (termChecks :
      typecheckOne check a l (SLPairsFst subtermsCheck) =
        DecisionSuccess {predicate} checkedType) ->
    TypechecksAs check (a $: l) checkedType

public export
TypechecksAsSubterms : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    {check : InductiveTypecheck predicate} ->
    {a : atom} -> {l : SList atom} ->
    {checkedType : SuccessPredicate predicate (a $: l)} ->
    TypechecksAs check (a $: l) checkedType ->
    SLForAll (SDepPredPair (TypechecksAs check)) l
TypechecksAsSubterms (AllSubtermsTypecheckAs subtermsCheck _ _) = subtermsCheck

public export
Typechecks : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  InductiveTypecheck predicate -> (x : SExp atom) -> Type
Typechecks check x = DPair (SuccessPredicate predicate x) (TypechecksAs check x)

public export
TypecheckedTerm : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  InductiveTypecheck predicate -> Type
TypecheckedTerm check = DPair (SExp atom) (Typechecks check)

mutual
  public export
  CheckedTypesUnique : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    {check : InductiveTypecheck predicate} ->
    {x : SExp atom} -> {type, type' : SuccessPredicate predicate x} ->
    (typechecksAs : TypechecksAs check x type) ->
    (typechecksAs' : TypechecksAs check x type') ->
    type = type'
  CheckedTypesUnique {check}
    (AllSubtermsTypecheckAs subtermsCheck checkedType termChecks)
    (AllSubtermsTypecheckAs subtermsCheck' checkedType' termChecks') =
      case ListTypechecksUnique {check} subtermsCheck subtermsCheck' of
        Refl => DecisionSuccessInjective (trans (sym termChecks) termChecks')

  public export
  TypechecksAsUnique :
    {atom : Type} -> {predicate : DecidablePredicate atom} ->
    {check : InductiveTypecheck predicate} ->
    {a : atom} -> {l : SList atom} ->
    {type, type' : SuccessPredicate predicate (a $: l)} ->
    (typechecksAs : TypechecksAs check (a $: l) type) ->
    (typechecksAs' : TypechecksAs check (a $: l) type) ->
    typechecksAs = typechecksAs'
  TypechecksAsUnique {check}
    (AllSubtermsTypecheckAs subtermsCheck checkedType termChecks)
    (AllSubtermsTypecheckAs subtermsCheck' checkedType termChecks') =
      case SLForAllUnique subtermsCheck subtermsCheck'
        (\x, typechecks, typechecks' => case x of
          (a $: l) => TypechecksUnique typechecks typechecks') of
        Refl => case uip termChecks termChecks' of Refl => Refl

  public export
  HeterogeneousTypechecksAsUnique :
    {atom : Type} -> {predicate : DecidablePredicate atom} ->
    {check : InductiveTypecheck predicate} ->
    {a : atom} -> {l : SList atom} ->
    {type, type' : SuccessPredicate predicate (a $: l)} ->
    (typechecksAs : TypechecksAs check (a $: l) type) ->
    (typechecksAs' : TypechecksAs check (a $: l) type') ->
    typechecksAs = typechecksAs'
  HeterogeneousTypechecksAsUnique {type} {type'} typechecksAs typechecksAs' =
    case CheckedTypesUnique typechecksAs typechecksAs' of
      Refl => TypechecksAsUnique {type} {type'=type} typechecksAs typechecksAs'

  public export
  TypechecksUnique : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    {check : InductiveTypecheck predicate} ->
    {a : atom} -> {l : SList atom} ->
    (typechecks, typechecks' : Typechecks check (a $: l)) ->
    typechecks = typechecks'
  TypechecksUnique (type ** typechecksAs) (type' ** typechecksAs') =
    case CheckedTypesUnique typechecksAs typechecksAs' of
      Refl =>
        cong
          (MkDPair type)
          (TypechecksAsUnique {type} {type'=type} typechecksAs typechecksAs')

  public export
  ListTypechecksUnique : {atom : Type} ->
    {predicate : DecidablePredicate atom} ->
    {check : InductiveTypecheck predicate} -> {l : SList atom} ->
    (typecheckList, typecheckList' : SLForAll (Typechecks check) l) ->
    typecheckList = typecheckList'
  ListTypechecksUnique SLForAllEmpty SLForAllEmpty = Refl
  ListTypechecksUnique SLForAllEmpty (SLForAllCons _ _) impossible
  ListTypechecksUnique (SLForAllCons _ _) SLForAllEmpty impossible
  ListTypechecksUnique
    (SLForAllCons {x=(a $: l)} head tail)
    (SLForAllCons head' tail') =
      case TypechecksUnique {check} head head' of
        Refl =>
          replace
            {p=(\tail'' => SLForAllCons head tail = SLForAllCons head tail'')}
            (ListTypechecksUnique tail tail')
            Refl

public export
data CheckResult : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    (check : InductiveTypecheck predicate) -> (x : SExp atom) -> Type where
  CheckSuccess : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    {check : InductiveTypecheck predicate} -> {x : SExp atom} ->
    Typechecks check x -> CheckResult check x
  CheckFailure : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    {check : InductiveTypecheck predicate} -> {x : SExp atom} ->
    Not (Typechecks check x) -> MergedFailures check -> CheckResult check x

public export
isCheckSuccess : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {check : InductiveTypecheck predicate} -> {x : SExp atom} ->
  CheckResult check x -> Bool
isCheckSuccess (CheckSuccess _) = True
isCheckSuccess (CheckFailure _ _) = False

public export
isCheckFailure : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {check : InductiveTypecheck predicate} -> {x : SExp atom} ->
  CheckResult check x -> Bool
isCheckFailure = not . isCheckSuccess

public export
data ListCheckResult : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    (check : InductiveTypecheck predicate) -> (l : SList atom) -> Type where
  ListCheckSuccess : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    {check : InductiveTypecheck predicate} -> {l : SList atom} ->
    SLForAll (Typechecks check) l ->
    ListCheckResult check l
  ListCheckFailure : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    {check : InductiveTypecheck predicate} -> {l : SList atom} ->
    Not (SLForAll (Typechecks check) l) -> MergedFailures check ->
    ListCheckResult check l

public export
isListCheckSuccess : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {check : InductiveTypecheck predicate} -> {l : SList atom} ->
  ListCheckResult check l -> Bool
isListCheckSuccess (ListCheckSuccess _) = True
isListCheckSuccess (ListCheckFailure _ _) = False

public export
isListCheckFailure : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {check : InductiveTypecheck predicate} -> {l : SList atom} ->
  ListCheckResult check l -> Bool
isListCheckFailure = not . isListCheckSuccess

public export
CheckResultCons : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {check : InductiveTypecheck predicate} ->
  {x : SExp atom} -> {l : SList atom} ->
  CheckResult check x -> ListCheckResult check l ->
  ListCheckResult check (x $+ l)
CheckResultCons (CheckSuccess head) (ListCheckSuccess tail) =
  ListCheckSuccess (SLForAllCons head tail)
CheckResultCons (CheckFailure head headFailure) (ListCheckSuccess tail) =
  ListCheckFailure
    (\success => case success of
      SLForAllEmpty impossible
      SLForAllCons headSuccess tailSuccess => head headSuccess)
    headFailure
CheckResultCons (CheckSuccess head) (ListCheckFailure tail tailFailure) =
  ListCheckFailure
    (\success => case success of
      SLForAllEmpty impossible
      SLForAllCons headSuccess tailSuccess => tail tailSuccess)
    tailFailure
CheckResultCons
  (CheckFailure head headFailure) (ListCheckFailure tail tailFailure) =
    ListCheckFailure
      (\success => case success of
        SLForAllEmpty impossible
        SLForAllCons headSuccess tailSuccess => head headSuccess)
      (mergeFailures check headFailure tailFailure)

public export
SLForAllConsDec : {atom : Type} -> {sp : SPredicate atom} ->
  {x : SExp atom} -> {l : SList atom} ->
  Dec (sp x) -> Dec (SLForAll sp l) -> Dec (SLForAll sp (x $+ l))
SLForAllConsDec (Yes spx) (Yes forAll) = Yes (SLForAllCons spx forAll)
SLForAllConsDec (No spxFails) _ =
  No (\forAllCons => case forAllCons of
    SLForAllEmpty impossible
    SLForAllCons spx _ => spxFails spx)
SLForAllConsDec _ (No forAllFails) =
  No (\forAllCons => case forAllCons of
    SLForAllEmpty impossible
    SLForAllCons _ forAll => forAllFails forAll)

public export
typecheck : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  (check : InductiveTypecheck predicate) ->
  ((x : SExp atom) -> CheckResult check x,
   (l : SList atom) -> ListCheckResult check l)
typecheck check =
  sInd {lp=(ListCheckResult check)} (SIndArgs
    (\a, l, lCheck => case lCheck of
      ListCheckSuccess lChecks =>
        case isSuccess
          (typecheckOne check a l (SLPairsFst lChecks)) of
            Yes termChecks =>
              CheckSuccess (IsSuccessExtract termChecks **
                   AllSubtermsTypecheckAs
                     lChecks
                     (IsSuccessExtract termChecks)
                     (IsSuccessExtractElim termChecks))
            No termFails =>
              CheckFailure (\termChecks => case termChecks of
                (_ ** typechecks) => case typechecks of
                  AllSubtermsTypecheckAs subtermsCheck checkedType termChecks =>
                    termFails
                      (replace
                        {p=(\subtermsCheck' =>
                          IsSuccess (typecheckOne check a l
                            (SLPairsFst
                              {sdp=(TypechecksAs check)} subtermsCheck')))}
                        (ListTypechecksUnique subtermsCheck lChecks)
                         (SuccessIsSuccessful termChecks)))
               (firstFailure check (a $: l) (NotSuccessExtract termFails))
      ListCheckFailure lFails mergedFailure =>
        CheckFailure (\typedTerm => case typedTerm of
          (_ ** typechecks) => case typechecks of
            AllSubtermsTypecheckAs subtermsCheck _ _ =>
              lFails subtermsCheck)
          mergedFailure)
    (ListCheckSuccess SLForAllEmpty)
    (\_, _ => CheckResultCons))

public export
data FAtom : (domainAtom, codomainAtom : Type) -> Type where
  FDA : domainAtom -> FAtom domainAtom codomainAtom
  CDA : codomainAtom -> FAtom domainAtom codomainAtom

public export
FExp : (domainAtom, codomainAtom : Type) -> Type
FExp domainAtom codomainAtom = SExp (FAtom domainAtom codomainAtom)

public export
FList : (domainAtom, codomainAtom : Type) -> Type
FList domainAtom codomainAtom = SList (FAtom domainAtom codomainAtom)

public export
record TypecheckFunctionPredicate {atom, atom' : Type}
    (domain : DecidablePredicate atom)
    (codomain : DecidablePredicate atom') where
  constructor MkTypecheckFunctionPredicate
  DomainCheck : InductiveTypecheck domain
  CodomainCheck : InductiveTypecheck codomain

{- XXX
public export
FunctionSuccessPredicate : {atom, atom' : Type} ->
  {domain : DecidablePredicate atom} ->
  {codomain : DecidablePredicate atom'} ->
  TypecheckFunctionPredicate domain codomain ->
  SPredicate (FAtom atom atom')
FunctionSuccessPredicate predicate x = FunctionSuccessPredicate_hole

public export
FunctionFailurePredicate : {atom, atom' : Type} ->
  {domain : DecidablePredicate atom} ->
  {codomain : DecidablePredicate atom'} ->
  TypecheckFunctionPredicate domain codomain ->
  SPredicate (FAtom atom atom')
FunctionFailurePredicate predicate x = FunctionFailurePredicate_hole

public export
FunctionDecidablePredicate : {atom, atom' : Type} ->
  {domain : DecidablePredicate atom} ->
  {codomain : DecidablePredicate atom'} ->
  TypecheckFunctionPredicate domain codomain ->
  DecidablePredicate (FAtom atom atom')
FunctionDecidablePredicate predicate =
  ResultPredicates
    (FunctionSuccessPredicate predicate)
    (FunctionFailurePredicate predicate)

public export
FunctionTypecheckOne : {atom, atom' : Type} ->
  {domain : DecidablePredicate atom} ->
  {codomain : DecidablePredicate atom'} ->
  (predicate : TypecheckFunctionPredicate domain codomain) ->
  (a : FAtom atom atom') ->
  (l : FList atom atom') ->
  SLForAll (FunctionSuccessPredicate predicate) l ->
  DecisionResult (FunctionDecidablePredicate predicate) (a $: l)
FunctionTypecheckOne predicate a l subtermsCheck = FunctionTypecheckOne_hole

public export
data FunctionMergedFailures : {atom, atom' : Type} ->
    {domain : DecidablePredicate atom} ->
    {codomain : DecidablePredicate atom'} ->
    (predicate : TypecheckFunctionPredicate domain codomain) -> Type where
  DomainFailure :
    {domain : DecidablePredicate atom} ->
    {codomain : DecidablePredicate atom'} ->
    (predicate : TypecheckFunctionPredicate domain codomain) ->
    MergedFailures (DomainCheck predicate) ->
    FunctionMergedFailures {domain} {codomain} predicate
  CodomainFailure :
    {domain : DecidablePredicate atom} ->
    {codomain : DecidablePredicate atom'} ->
    (predicate : TypecheckFunctionPredicate domain codomain) ->
    MergedFailures (CodomainCheck predicate) ->
    FunctionMergedFailures {domain} {codomain} predicate

public export
FunctionFirstFailure : {atom, atom' : Type} ->
    {domain : DecidablePredicate atom} ->
    {codomain : DecidablePredicate atom'} ->
    {predicate : TypecheckFunctionPredicate domain codomain} ->
    (x : FExp atom atom') -> FunctionFailurePredicate predicate x ->
    FunctionMergedFailures predicate
FunctionFirstFailure x failure = FunctionFirstFailure_hole

public export
FunctionMergeFailures : {atom, atom' : Type} ->
    {domain : DecidablePredicate atom} ->
    {codomain : DecidablePredicate atom'} ->
    {predicate : TypecheckFunctionPredicate domain codomain} ->
    FunctionMergedFailures predicate ->
    FunctionMergedFailures predicate ->
    FunctionMergedFailures predicate
FunctionMergeFailures x failure = FunctionMergeFailures_hole

public export
FunctionTypecheckInductive : {atom, atom' : Type} ->
  {domain : DecidablePredicate atom} ->
  {codomain : DecidablePredicate atom'} ->
  (predicate : TypecheckFunctionPredicate domain codomain) ->
  InductiveTypecheck (FunctionDecidablePredicate predicate)
FunctionTypecheckInductive predicate =
  MkInductiveTypecheck
    (FunctionTypecheckOne predicate)
    (FunctionMergedFailures predicate)
    (FunctionFirstFailure {predicate})
    (FunctionMergeFailures {predicate})

public export
CheckFunctionResult : {atom, atom' : Type} ->
  {domain : DecidablePredicate atom} ->
  {codomain : DecidablePredicate atom'} ->
  (predicate : TypecheckFunctionPredicate domain codomain) ->
  FExp atom atom' -> Type
CheckFunctionResult predicate =
  CheckResult (FunctionTypecheckInductive predicate)

public export
ListCheckFunctionResult : {atom, atom' : Type} ->
  {domain : DecidablePredicate atom} ->
  {codomain : DecidablePredicate atom'} ->
  (predicate : TypecheckFunctionPredicate domain codomain) ->
  FList atom atom' -> Type
ListCheckFunctionResult predicate =
  ListCheckResult (FunctionTypecheckInductive predicate)

public export
typecheckFunction :
  {atom, atom' : Type} ->
  {domain : DecidablePredicate atom} ->
  {codomain : DecidablePredicate atom'} ->
  (predicate : TypecheckFunctionPredicate domain codomain) ->
  ((x : FExp atom atom') -> CheckFunctionResult predicate x,
   (l : FList atom atom') -> ListCheckFunctionResult predicate l)
typecheckFunction predicate = typecheck (FunctionTypecheckInductive predicate)

public export
FTypechecks :
  {atom, atom' : Type} ->
  {domain : DecidablePredicate atom} ->
  {codomain : DecidablePredicate atom'} ->
  (predicate : TypecheckFunctionPredicate domain codomain) ->
  (x : FExp atom atom') -> Type
FTypechecks check = Typechecks (FunctionTypecheckInductive check)

public export
generatedFunction :
  {atom, atom' : Type} ->
  {domain : DecidablePredicate atom} ->
  {codomain : DecidablePredicate atom'} ->
  {predicate : TypecheckFunctionPredicate domain codomain} ->
  TypecheckedTerm (FunctionTypecheckInductive predicate) ->
  TypecheckedTerm (DomainCheck predicate) ->
  TypecheckedTerm (CodomainCheck predicate)
generatedFunction (fx ** (ftype ** fchecks)) (dx ** (dtype ** dchecks)) =
  (generatedFunction_hole_cx **
  (generatedFunction_hole_ctype **
   generatedFunction_hole_cchecks))
   -}
