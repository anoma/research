module RefinedSExp.PairVariant.SExp

import Library.FunctionsAndRelations
import Library.Decidability
import Library.List
import public Category.Category
import public Control.WellFounded
import public RefinedSExp.List

%default total

prefix 1 $:
infixr 7 $.
public export
data SExp : (atom : Type) -> Type where
  ($:) : atom -> SExp atom
  ($.) : SExp atom -> SExp atom -> SExp atom

prefix 1 $..
public export
($..) : PairOf (SExp atom) -> SExp atom
($..) p = fst p $. snd p

public export
sexpAtomInjective : {atom : Type} -> {a, a' : atom} -> $: a = $: a' -> a = a'
sexpAtomInjective Refl = Refl

public export
sexpPairInjective : {atom : Type} -> {x, x', y, y' : SExp atom} ->
  x $. x' = y $. y' -> (x = y, x' = y')
sexpPairInjective Refl = (Refl, Refl)

public export
SExpPred : (atom : Type) -> Type
SExpPred atom = !- (SExp atom)

public export
SExpPi : {atom : Type} -> SExpPred atom -> Type
SExpPi {atom} sp = SExp atom ~> sp

public export
SExpTypeConstructor : (atom : Type) -> Type
SExpTypeConstructor atom = DependentTypeConstructor (SExp atom)

public export
SExpComposeConstructor : {0 atom : Type} ->
  (Type -> Type) -> SExpTypeConstructor atom -> SExpTypeConstructor atom
SExpComposeConstructor g f sp x = g (f sp x)

public export
SExpStrengthenedPred : {0 atom : Type} ->
  SExpTypeConstructor atom -> SExpTypeConstructor atom
SExpStrengthenedPred {atom} typeConstructor sp =
  \x : SExp atom => (sp x, typeConstructor sp x)

public export
SExpPredList : (atom : Type) -> Type
SExpPredList atom = List (SExpPred atom)

public export
SExpDependentApplicative :
  {atom : Type} -> SExpTypeConstructor atom -> Type
SExpDependentApplicative {atom} = DependentApplicativeOn {a=(SExp atom)}

public export
SExpApplicativeConstructor :
  {f : Type -> Type} -> (app : Applicative f) -> {0 atom : Type} ->
  SExpDependentApplicative (ConstructorToDependent {a=(SExp atom)} f)
SExpApplicativeConstructor app = ApplicativeToDependent app

public export
SExpApplicativePred : (f : Type -> Type) -> Type -> Type
SExpApplicativePred f atom = !- (f (SExp atom))

public export
record SExpEliminatorSig {0 atom : Type} (0 sp : SExpPred atom) where
  constructor SExpEliminatorArgs
  atomElim : (a : atom) -> sp ($: a)
  pairElim : (x, x' : SExp atom) -> sp x -> sp x' -> sp (x $. x')

public export
sexpEliminator :
  {0 atom : Type} -> {0 sp : SExpPred atom} ->
  SExpEliminatorSig sp -> SExpPi sp
sexpEliminator signature ($: a) =
  atomElim signature a
sexpEliminator signature (x $. x') =
  pairElim signature x x'
    (sexpEliminator signature x) (sexpEliminator signature x')

public export
SExpSignatureComposeSig :
  {atom : Type} ->
  {f : Type -> Type} ->
  (app : Applicative f) ->
  {sp : SExpPred atom} ->
  f (SExpEliminatorSig sp) ->
  SExpEliminatorSig (f . sp)
SExpSignatureComposeSig app fsignature =
  SExpEliminatorArgs
    (dpure app (map {f} atomElim fsignature))
    (\x, x', fsx, fsx' =>
      ((dpure app (dpure app (map {f} pairElim fsignature) x) x') <*> fsx)
        <*> fsx')

public export
sexpEliminatorComposeSig :
  {atom : Type} ->
  {f : Type -> Type} ->
  (app : Applicative f) ->
  {sp : SExpPred atom} ->
  f (SExpEliminatorSig sp) ->
  SExpPi (f . sp)
sexpEliminatorComposeSig app = sexpEliminator . SExpSignatureComposeSig app

public export
record SExpInductionStrengthenerSig
  {0 atom : Type} (0 f : SExpTypeConstructor atom) where
    constructor SExpInductionStrengthenerArgs
    atomStrengthener : (0 sp : SExpPred atom) ->
      (a : atom) -> sp ($: a) -> f sp ($: a)
    pairStrengthener : (0 sp : SExpPred atom) ->
      (x, x' : SExp atom) -> f sp x -> f sp x' -> sp (x $. x') -> f sp (x $. x')

public export
record SExpStrengthenedInductionSig
  {0 atom : Type} (0 f : SExpTypeConstructor atom) (sp : SExpPred atom) where
    constructor SExpStrengthenedInductionArgs
    atomElim : (a : atom) -> sp ($: a)
    pairElim : (x, x' : SExp atom) -> f sp x -> f sp x' -> sp (x $. x')

public export
SExpStrengthenedInductionSigToEliminatorSig :
  {0 atom : Type} ->
  {0 f : SExpTypeConstructor atom} ->
  SExpInductionStrengthenerSig f ->
  {0 sp : SExpPred atom} ->
  SExpStrengthenedInductionSig f sp ->
  SExpEliminatorSig (SExpStrengthenedPred f sp)
SExpStrengthenedInductionSigToEliminatorSig {sp} strengthenerSig inductionSig =
  SExpEliminatorArgs
    (\a =>
      let spa = atomElim inductionSig a in
      (spa, atomStrengthener strengthenerSig sp a spa))
    (\x, x', sfsx, sfsx' => case (sfsx, sfsx') of
      ((spx, fspx), (spx', fspx')) =>
        let spxx' = pairElim inductionSig x x' fspx fspx' in
        (spxx', pairStrengthener strengthenerSig sp x x' fspx fspx' spxx'))

public export
SExpStrengthenedPi : {atom : Type} ->
  (f : SExpTypeConstructor atom) -> (sp : SExpPred atom) -> Type
SExpStrengthenedPi {atom} f sp = SExpPi {atom} (SExpStrengthenedPred f sp)

public export
sexpStrengthenedInduction :
  {0 atom : Type} ->
  {0 f : SExpTypeConstructor atom} ->
  (strengthenerSig : SExpInductionStrengthenerSig f) ->
  {0 sp : SExpPred atom} ->
  (inductionSig : SExpStrengthenedInductionSig f sp) ->
  SExpStrengthenedPi f sp
sexpStrengthenedInduction strengthenerSig inductionSig =
  sexpEliminator
    (SExpStrengthenedInductionSigToEliminatorSig strengthenerSig inductionSig)

public export
record SExpEncodingSig (0 type : Type) (0 atom : Type) where
  constructor SExpEncodingArgs
  encode : type -> SExp atom
  injective : (y, y' : type) -> encode y = encode y' -> y = y'

public export
SExpAtomEncodingSig : (atom : Type) -> SExpEncodingSig atom atom
SExpAtomEncodingSig atom = SExpEncodingArgs ($:) (\_, _ => sexpAtomInjective)

public export
SExpIdentityEncodingSig : (atom : Type) -> SExpEncodingSig (SExp atom) atom
SExpIdentityEncodingSig atom = SExpEncodingArgs id (\_, _ => id)

public export
SExpPairEncodingSig : (atom : Type) -> SExpEncodingSig (PairOf (SExp atom)) atom
SExpPairEncodingSig atom =
  SExpEncodingArgs
    ($..)
    (\p, p', eq =>
      let (fsteq, sndeq) = sexpPairInjective eq in pairInjective fsteq sndeq)

public export
record SExpApplicativeEncodingSig
  {f : Type -> Type} (0 app : Applicative f) (0 atom : Type) where
    constructor SExpApplicativeEncodingArgs
    encodings : (type : Type) ->
      SExpEncodingSig type atom -> SExpEncodingSig (f type) atom

public export
SExpParameterize : (parameter : Type) -> Type -> Type
SExpParameterize parameter type = parameter -> type

public export
SExpParameterizedPred : (atom : Type) -> (parameter : Type) -> Type
SExpParameterizedPred atom parameter =
  SExp atom -> SExpParameterize parameter Type

public export
SExpParameterizedPredToPred : {0 atom : Type} -> {parameter : Type} ->
  (sp : SExpParameterizedPred atom parameter) -> SExpPred atom
SExpParameterizedPredToPred {parameter} sp = \x => parameter ~> sp x

public export
SExpParameterizedEliminatorSig : {0 atom : Type} -> {0 parameter : Type} ->
  (0 sp : SExpParameterizedPred atom parameter) -> Type
SExpParameterizedEliminatorSig sp =
  SExpEliminatorSig (SExpParameterizedPredToPred sp)

public export
SExpParameterizedPi : {atom : Type} -> {parameter : Type} ->
  (sp : SExpParameterizedPred atom parameter) -> Type
SExpParameterizedPi = SExpPi . SExpParameterizedPredToPred

sexpParameterizedEliminator :
  {0 atom : Type} -> {0 parameter : Type} ->
  {sp : SExpParameterizedPred atom parameter} ->
  SExpParameterizedEliminatorSig sp ->
  SExpParameterizedPi sp
sexpParameterizedEliminator = sexpEliminator

public export
SExpMetaPred : {atom : Type} -> (sp : SExpPred atom) -> Type
SExpMetaPred {atom} sp = (x : SExp atom) -> sp x -> Type

public export
SExpMetaPi : {atom : Type} -> {sp : SExpPred atom} ->
  (smp : SExpMetaPred sp) -> Type
SExpMetaPi {atom} {sp} smp = (x : SExp atom) -> (spx : sp x) -> smp x spx

public export
SExpMetaPredToPred : {0 atom : Type} -> {sp : SExpPred atom} ->
  SExpMetaPred sp -> SExpPred atom
SExpMetaPredToPred {sp} smp = \x => sp x ~> smp x

public export
sexpMetaPredCompose : {0 atom : Type} ->
  (f : Type -> Type) -> {0 sp : SExpPred atom} ->
  (smp : SExpMetaPred sp) -> SExpMetaPred sp
sexpMetaPredCompose f smp = \x, spx => f (smp x spx)

public export
SExpEliminatorPred : {0 atom : Type} -> {0 sp : SExpPred atom} ->
  SExpEliminatorSig sp -> SExpMetaPred sp -> SExpPred atom
SExpEliminatorPred signature smp = \x => smp x (sexpEliminator signature x)

public export
SExpEliminatorPi : {atom : Type} -> {0 sp : SExpPred atom} ->
  SExpEliminatorSig sp -> SExpMetaPred sp -> Type
SExpEliminatorPi signature smp = SExpPi (SExpEliminatorPred signature smp)

public export
SExpMetaEliminatorSig : {0 atom : Type} -> {0 sp : SExpPred atom} ->
  (0 signature : SExpEliminatorSig sp) -> (0 smp : SExpMetaPred sp) -> Type
SExpMetaEliminatorSig signature smp =
  SExpEliminatorSig (SExpEliminatorPred signature smp)

public export
sexpMetaEliminator :
  {0 atom : Type} -> {0 sp : SExpPred atom} ->
  {0 signature : SExpEliminatorSig sp} ->
  {0 smp : SExpMetaPred sp} ->
  (metaSig : SExpMetaEliminatorSig signature smp) ->
  SExpEliminatorPi signature smp
sexpMetaEliminator = sexpEliminator

public export
SExpMetaStrengthenedPred : {atom : Type} ->
  (f : SExpTypeConstructor atom) -> (sp : SExpPred atom) -> Type
SExpMetaStrengthenedPred {atom} f sp =
  SExpMetaPred (SExpStrengthenedPred {atom} f sp)

public export
SExpMetaStrengthenedPi :
  {atom : Type} -> {f : SExpTypeConstructor atom} ->
  SExpInductionStrengthenerSig f ->
  {sp : SExpPred atom} ->
  SExpMetaStrengthenedPred f sp ->
  SExpStrengthenedInductionSig f sp ->
  Type
SExpMetaStrengthenedPi {atom} strengthenerSig smp strengthenedSig =
  SExpEliminatorPi
    (SExpStrengthenedInductionSigToEliminatorSig
      strengthenerSig strengthenedSig)
    smp

public export
SExpMetaStrengthenedInductionSig :
  {0 atom : Type} ->
  {f : SExpTypeConstructor atom} ->
  (strengthenerSig : SExpInductionStrengthenerSig f) ->
  {0 sp : SExpPred atom} ->
  (0 smp : SExpMetaStrengthenedPred f sp) ->
  (inductionSig : SExpStrengthenedInductionSig f sp) ->
  Type
SExpMetaStrengthenedInductionSig strengthenerSig smp inductionSig =
  SExpMetaEliminatorSig
    (SExpStrengthenedInductionSigToEliminatorSig strengthenerSig inductionSig)
    smp

public export
sexpMetaStrengthenedInduction :
  {0 atom : Type} ->
  {0 f : SExpTypeConstructor atom} ->
  {strengthenerSig : SExpInductionStrengthenerSig f} ->
  {0 sp : SExpPred atom} ->
  {smp : SExpMetaStrengthenedPred f sp} ->
  {inductionSig : SExpStrengthenedInductionSig f sp} ->
  SExpMetaStrengthenedInductionSig {f} strengthenerSig smp inductionSig ->
  SExpMetaStrengthenedPi {f} strengthenerSig smp inductionSig
sexpMetaStrengthenedInduction {f} {sp} {smp} =
  sexpMetaEliminator
    {sp=(SExpStrengthenedPred f sp)}
    {signature=
      (SExpStrengthenedInductionSigToEliminatorSig
        strengthenerSig inductionSig)}
    {smp}

public export
sexpMetaComposedSigEliminator :
  {0 atom : Type} ->
  {0 f : Type -> Type} -> {0 app : Applicative f} ->
  {0 sp : SExpPred atom} ->
  {0 smp : SExpMetaPred (f . sp)} ->
  {0 fsignature : f (SExpEliminatorSig sp)} ->
  SExpMetaEliminatorSig (SExpSignatureComposeSig app fsignature) smp ->
  SExpEliminatorPi (SExpSignatureComposeSig app fsignature) smp
sexpMetaComposedSigEliminator {smp} = sexpMetaEliminator {smp}

public export
sexpMetaEliminatorComposeSig :
  {atom : Type} ->
  {f : Type -> Type} -> (app : Applicative f) ->
  {0 sp : SExpPred atom} ->
  {smp : SExpMetaPred sp} ->
  {signature : SExpEliminatorSig sp} ->
  f (SExpMetaEliminatorSig signature smp) ->
  SExpEliminatorPi signature (sexpMetaPredCompose f smp)
sexpMetaEliminatorComposeSig app = sexpEliminatorComposeSig app

public export
SExpConstPred : {0 atom : Type} -> Type -> SExpPred atom
SExpConstPred type _ = type

public export
sexpConstEliminator :
  {0 atom : Type} -> {0 sp : Type} ->
  (signature : SExpEliminatorSig {atom} (SExpConstPred sp)) ->
  SExp atom -> sp
sexpConstEliminator = sexpEliminator

public export
SExpPair : (atom : Type) -> Type
SExpPair atom = (SExp atom, SExp atom)

public export
SExpPairPred : (atom : Type) -> Type
SExpPairPred atom = SExpPair atom -> Type

public export
record SExpWithPairPredEliminatorSig {0 atom : Type}
  (0 sp : SExpPred atom) (0 pp : SExpPairPred atom) where
    constructor SExpWithPairPredEliminatorArgs
    atomElim : (a : atom) -> sp ($: a)
    pairElim :
      (x, x' : SExp atom) -> sp x -> sp x' -> pp (x, x') -> sp (x $. x')
    atomPairIntro :
      (a, a' : atom) -> sp ($: a) -> sp ($: a') -> pp ($: a, $: a')
    expPairIntroLeft :
      (x, x', x'' : SExp atom) -> sp x -> sp x' -> sp x'' ->
        pp (x, x') -> pp ((x $. x'), x'')
    expPairIntroRight :
      (x, x', x'' : SExp atom) -> sp x -> sp x' -> sp x'' ->
        pp (x', x'') -> pp (x, (x' $. x''))

public export
SExpPairPi : {atom : Type} -> SExpPairPred atom -> Type
SExpPairPi pp = SExpPair atom ~> pp

public export
SExpWithPairPi : {atom : Type} ->
  (expPred : SExpPred atom) -> (pairPred : SExpPairPred atom) -> Type
SExpWithPairPi expPred pairPred = (SExpPi expPred, SExpPairPi pairPred)

public export
SExpPredWithPairPred : {0 atom : Type} ->
  SExpPred atom -> SExpPairPred atom -> SExpPred atom
SExpPredWithPairPred expPred pairPred x =
  case x of
    ($:) a => expPred ($: a)
    x $. x' => (expPred x, expPred x', expPred (x $. x'), pairPred (x, x'))

public export
SExpPredWithPairPredToPred : {0 atom : Type} ->
  {0 sp : SExpPred atom} -> {0 spp : SExpPairPred atom} ->
  {x : SExp atom} -> SExpPredWithPairPred sp spp x ->
  sp x
SExpPredWithPairPredToPred {x=($: a)} sppx = sppx
SExpPredWithPairPredToPred {x=(x' $. x'')} sppx = proj43 sppx

sexpWithPairPredPairElim : {0 atom : Type} ->
  {0 expPred : SExpPred atom} -> {0 pairPred : SExpPairPred atom} ->
  SExpWithPairPredEliminatorSig expPred pairPred ->
  (x, x' : SExp atom) ->
  SExpPredWithPairPred expPred pairPred x ->
  SExpPredWithPairPred expPred pairPred x' ->
  SExpPredWithPairPred expPred pairPred (x $. x')
sexpWithPairPredPairElim signature ($: a) ($: a') spa spa' =
  let
    spaa' = atomPairIntro signature a a' spa spa'
    spp = pairElim signature ($: a) ($: a') spa spa' spaa'
  in
  (spa, spa', spp, spaa')
sexpWithPairPredPairElim signature ($: a) (x $. x') spa spxx' =
  let
    (spx, spx', spp, pp) = spxx'
    ppxx' = expPairIntroRight signature ($: a) x x' spa spx spx' pp
    spaxx' = pairElim signature ($: a) (x $. x') spa spp ppxx'
  in
  (spa, spp, spaxx', ppxx')
sexpWithPairPredPairElim signature (x $. x') y spxx' sppy =
  let
    (spx, spx', spp, pp) = spxx'
    spy = SExpPredWithPairPredToPred sppy
    ppxy = expPairIntroLeft signature x x' y spx spx' spy pp
    spxy = pairElim signature (x $. x') y spp spy ppxy
  in
  (spp, spy, spxy, ppxy)

SExpWithPairPredSigToEliminatorSig : {0 atom : Type} ->
  {0 expPred : SExpPred atom} -> {0 pairPred : SExpPairPred atom} ->
  SExpWithPairPredEliminatorSig expPred pairPred ->
  SExpEliminatorSig (SExpPredWithPairPred expPred pairPred)
SExpWithPairPredSigToEliminatorSig signature =
  SExpEliminatorArgs
    (atomElim signature)
    (sexpWithPairPredPairElim signature)

public export
SExpPiToWithPairPi : {0 atom : Type} ->
  {0 expPred : SExpPred atom} -> {0 pairPred : SExpPairPred atom} ->
  SExpPi (SExpPredWithPairPred expPred pairPred) ->
  SExpWithPairPi expPred pairPred
SExpPiToWithPairPi forAllExp =
  (\x => SExpPredWithPairPredToPred (forAllExp x),
   \p => case p of (x', x'') => proj44 (forAllExp (x' $. x'')))

sexpWithPairPredEliminators : {0 atom : Type} ->
  {0 expPred : SExpPred atom} -> {0 pairPred : SExpPairPred atom} ->
  SExpWithPairPredEliminatorSig expPred pairPred ->
  SExpWithPairPi expPred pairPred
sexpWithPairPredEliminators signature =
  SExpPiToWithPairPi
    (sexpEliminator (SExpWithPairPredSigToEliminatorSig signature))

sexpWithPairPredEliminator : {0 atom : Type} ->
  {0 expPred : SExpPred atom} -> {0 pairPred : SExpPairPred atom} ->
  SExpWithPairPredEliminatorSig expPred pairPred ->
  SExpPi expPred
sexpWithPairPredEliminator = fst . sexpWithPairPredEliminators

spairWithPairPredEliminator : {0 atom : Type} ->
  {0 expPred : SExpPred atom} -> {0 pairPred : SExpPairPred atom} ->
  SExpWithPairPredEliminatorSig expPred pairPred ->
  SExpPairPi pairPred
spairWithPairPredEliminator = snd . sexpWithPairPredEliminators

public export
SExpForAll :
  {0 atom : Type} -> (sp : SExpPred atom) -> SExpPred atom
SExpForAll sp =
  sexpConstEliminator {sp=Type}
    (SExpEliminatorArgs
      (sp . ($:))
      (\x, x', forAll, forAll' => (sp (x $. x'), forAll, forAll')))

public export sexpForAllSelf : {0 atom : Type} -> {0 sp : SExpPred atom} ->
  {x : SExp atom} -> SExpForAll sp x -> sp x
sexpForAllSelf {x} = sexpEliminator {sp=(\x => SExpForAll sp x -> sp x)}
  (SExpEliminatorArgs (\_ => id) (\_, _, _, _ => fst)) x

public export
SExpGeneralInductionStrengthenerSig : SExpInductionStrengthenerSig SExpForAll
SExpGeneralInductionStrengthenerSig =
  SExpInductionStrengthenerArgs
    (\_, _ => id)
    (\_, _, _, forAll, forAll', spxx' => (spxx', forAll, forAll'))

public export
sexpForAllStrengthenedInduction : {0 atom : Type} -> {0 sp : SExpPred atom} ->
  SExpStrengthenedInductionSig SExpForAll sp ->
  SExpStrengthenedPi SExpForAll sp
sexpForAllStrengthenedInduction =
  sexpStrengthenedInduction SExpGeneralInductionStrengthenerSig

public export
SExpGeneralInductionSig : {0 atom : Type} -> (sp : SExpPred atom) -> Type
SExpGeneralInductionSig = SExpStrengthenedInductionSig SExpForAll

public export
SExpForAllPi : {atom : Type} -> (sp : SExpPred atom) -> Type
SExpForAllPi = SExpPi . SExpForAll

public export
sexpGeneralInduction : {0 atom : Type} -> {0 sp : SExpPred atom} ->
  SExpGeneralInductionSig sp ->
  SExpForAllPi sp
sexpGeneralInduction signature x =
  snd (sexpForAllStrengthenedInduction signature x)

public export
sexpGeneralInductionSelf : {0 atom : Type} -> {0 sp : SExpPred atom} ->
  SExpGeneralInductionSig sp ->
  SExpPi sp
sexpGeneralInductionSelf {sp} signature x =
  sexpForAllSelf {sp} (sexpGeneralInduction signature x)

public export
SExpForAllBoth : {0 atom : Type} -> (sp : SExpPred atom) -> SExpPairPred atom
SExpForAllBoth sp (x, x') = (SExpForAll sp x, SExpForAll sp x')

public export
SExpForAllWithPairPred : {0 atom : Type} -> (sp : SExpPred atom) ->
  SExpPred atom
SExpForAllWithPairPred sp = SExpPredWithPairPred sp (SExpForAllBoth sp)

public export
sexpForAllApplicationsPairElim :
  {0 atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {sp : SExp atom -> Type} ->
  (x, x' : SExp atom) ->
  (SExpForAll (f . sp) x -> f (SExpForAll sp x)) ->
  (SExpForAll (f . sp) x' -> f (SExpForAll sp x')) ->
  (SExpForAllBoth (f . sp) (x, x') -> f (SExpForAllBoth sp (x, x'))) ->
  SExpForAll (f . sp) (x $. x') ->
  f (SExpForAll sp (x $. x'))
sexpForAllApplicationsPairElim {f} {isApplicative} {sp}
  x x' mapForAll mapForAll' mapForAllBoth (fsp, forAll, forAll') =
    applyTriple
      fsp
      (mapForAll forAll)
      (mapForAll' forAll')

public export
sexpForAllApplicationsPairIntroLeft :
  {0 atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {sp : SExp atom -> Type} ->
  (x, x', x'' : SExp atom) ->
  (SExpForAll (f . sp) x -> f (SExpForAll sp x)) ->
  (SExpForAll (f . sp) x' -> f (SExpForAll sp x')) ->
  (SExpForAll (f . sp) x'' -> f (SExpForAll sp x'')) ->
  (SExpForAllBoth (f . sp) (x, x') -> f (SExpForAllBoth sp (x, x'))) ->
  SExpForAllBoth (f . sp) ((x $. x'), x'') ->
  f (SExpForAllBoth sp ((x $. x'), x''))
sexpForAllApplicationsPairIntroLeft {f} {isApplicative} {sp}
  x x' x'' mapForAll mapForAll' mapForAll'' mapForAllBoth forAllBoth =
    let ((fsp, fpp), forAll'') = forAllBoth in
    applyPair (applyPair
      fsp
      (mapForAllBoth fpp))
      (mapForAll'' forAll'')

public export
sexpForAllApplicationsPairIntroRight :
  {0 atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {sp : SExp atom -> Type} ->
  (x, x', x'' : SExp atom) ->
  (SExpForAll (f . sp) x -> f (SExpForAll sp x)) ->
  (SExpForAll (f . sp) x' -> f (SExpForAll sp x')) ->
  (SExpForAll (f . sp) x'' -> f (SExpForAll sp x'')) ->
  (SExpForAllBoth (f . sp) (x', x'') -> f (SExpForAllBoth sp (x', x''))) ->
  SExpForAllBoth (f . sp) (x, (x' $. x'')) ->
  f (SExpForAllBoth sp (x, (x' $. x'')))
sexpForAllApplicationsPairIntroRight {f} {isApplicative} {sp}
  x x' x'' mapForAll mapForAll' mapForAll'' mapForAllBoth forAllBoth =
    let (forAll, fsp, fpp) = forAllBoth in
    applyTriple
      (mapForAll forAll)
      fsp
      (mapForAllBoth fpp)

public export
sexpForAllApplications :
  {0 atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {sp : SExp atom -> Type} ->
  SExpWithPairPi
    (\x => SExpForAll (f . sp) x -> f (SExpForAll sp x))
    (\p => SExpForAllBoth (f . sp) p -> f (SExpForAllBoth sp p))
sexpForAllApplications {f} {isApplicative} {sp} =
  sexpWithPairPredEliminators
    (SExpWithPairPredEliminatorArgs
      (\_ => id)
      (sexpForAllApplicationsPairElim {f} {isApplicative} {sp})
      (\a, a', _, _, fp => applyPair (fst fp) (snd fp))
      (sexpForAllApplicationsPairIntroLeft {f} {isApplicative} {sp})
      (sexpForAllApplicationsPairIntroRight {f} {isApplicative} {sp})
    )

public export
sexpForAllApply :
  {0 atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {sp : SExp atom -> Type} ->
  (x : SExp atom) -> SExpForAll (f . sp) x -> f (SExpForAll sp x)
sexpForAllApply {isApplicative} {sp} =
  fst (sexpForAllApplications {isApplicative} {sp})

public export
spairForAllApply :
  {0 atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {sp : SExp atom -> Type} ->
  (p : SExpPair atom) -> SExpForAllBoth (f . sp) p -> f (SExpForAllBoth sp p)
spairForAllApply {isApplicative} {sp} =
  snd (sexpForAllApplications {isApplicative} {sp})

public export
SExpForAllMetaPred : {atom : Type} -> SExpPred atom -> Type
SExpForAllMetaPred sp = SExpMetaStrengthenedPred SExpForAll sp

public export
SExpForAllMetaPi : {atom : Type} -> {sp : SExpPred atom} ->
  SExpForAllMetaPred sp -> SExpGeneralInductionSig sp -> Type
SExpForAllMetaPi = SExpMetaStrengthenedPi SExpGeneralInductionStrengthenerSig

public export
sexpForAllMetaEliminator : {atom : Type} -> {sp : SExpPred atom} ->
  {smp : SExpForAllMetaPred sp} ->
  {inductionSig : SExpGeneralInductionSig sp} ->
  SExpMetaStrengthenedInductionSig
    SExpGeneralInductionStrengthenerSig smp inductionSig ->
  SExpForAllMetaPi smp inductionSig
sexpForAllMetaEliminator {smp} =
  sexpMetaStrengthenedInduction
    {strengthenerSig=SExpGeneralInductionStrengthenerSig}
    {smp}

public export
SExpExists :
  {0 atom : Type} -> (sp : SExpPred atom) -> SExpPred atom
SExpExists sp =
  sexpConstEliminator {sp=Type}
    (SExpEliminatorArgs
      (sp . ($:))
      (\x, x', exists, exists' =>
        EitherList [sp (x $. x'), exists, exists']))

public export
SExpExistsEither : {0 atom : Type} -> (sp : SExpPred atom) -> SExpPairPred atom
SExpExistsEither sp (x, x') = Either (SExpExists sp x) (SExpExists sp x')

public export
NonEmptySList : Type -> Type
NonEmptySList atom = NonEmptyList (SExp atom)

public export
SExpExistsSome : {0 atom : Type} -> SExpPred atom -> SExpPred atom
SExpExistsSome sp = NonEmptyList . SExpExists sp

public export
SExpDecForAll : {0 atom : Type} -> (sp : SExpPred atom) -> SExpPred atom
SExpDecForAll sp x = Either (SExpForAll sp x) (SExpExistsSome (Not . sp) x)

public export
sexpMap : {0 a, b : Type} -> (a -> b) -> (SExp a -> SExp b)
sexpMap f = sexpEliminator (SExpEliminatorArgs (($:) . f) (const (const ($.))))

public export
Functor SExp where
  map = sexpMap

public export
sexpApplyToAtom : {0 a, b : Type} -> SExp (a -> b) -> a -> SExp b
sexpApplyToAtom xf v = map (\f => f v) xf

public export
sexpApply : {0 a, b : Type} -> SExp (a -> b) -> SExp a -> SExp b
sexpApply xab =
  sexpEliminator (SExpEliminatorArgs (sexpApplyToAtom xab) (\_, _ => ($.)))

public export
Applicative SExp where
  pure = ($:)
  (<*>) = sexpApply

public export
sexpJoin : {0 a : Type} -> SExp (SExp a) -> SExp a
sexpJoin = sexpConstEliminator (SExpEliminatorArgs id (\_, _ => ($.)))

public export
Monad SExp where
  join = sexpJoin

public export
sexpFoldR : {0 elem, acc : Type} ->
  (elem -> acc -> acc) -> acc -> SExp elem -> acc
sexpFoldR f = flip (sexpConstEliminator (SExpEliminatorArgs f (\_, _ => (.))))

public export
Foldable SExp where
  foldr = sexpFoldR

public export
applySExpPair :
  {0 f : Type -> Type} -> Applicative f => {0 a : Type} ->
  f (SExp a) -> f (SExp a) -> f (SExp a)
applySExpPair fa fa' = map ($..) (applyPair fa fa')

public export
sexpTraverse : {0 a, b : Type} -> {0 f : Type -> Type} ->
  Applicative f => (a -> f b) ->
  SExp a -> f (SExp b)
sexpTraverse {f} g =
  sexpEliminator (SExpEliminatorArgs (map ($:) . g) (\_, _ => applySExpPair))

public export
Traversable SExp where
  traverse = sexpTraverse

public export
sexpSize : {0 atom : Type} -> SExp atom -> Nat
sexpSize =
  sexpConstEliminator
    (SExpEliminatorArgs
      (\_ => 1)
      (\_, _ => (+))
    )

public export
Sized (SExp atom) where
  size = sexpSize

public export
sexpFoundedOnSizeInduction :
  {0 sp : SExpPred atom} ->
  (step :
    (x : SExp atom) ->
    ((y : SExp atom) -> (sexpSize y) `LT` (sexpSize x) -> sp y) ->
    sp x) ->
  SExp atom ~> sp
sexpFoundedOnSizeInduction = sizeInd

public export
data SubSExp : {0 atom : Type} -> SExp atom -> SExp atom -> Type where
  SubSExpLeft : {0 atom : Type} -> (x, x' : SExp atom) ->
    SubSExp x (x $. x')
  SubSExpRight : {0 atom : Type} -> (x, x' : SExp atom) ->
    SubSExp x (x' $. x)
  SubSExpTrans : {0 atom : Type} -> {x, x', x'' : SExp atom} ->
    SubSExp x x' -> SubSExp x' x'' -> SubSExp x x''

public export
superSExpNotAtom : {0 atom : Type} -> (x : SExp atom) -> (a : atom) ->
  Not (SubSExp x ($: a))
superSExpNotAtom x a (SubSExpLeft _ _) impossible
superSExpNotAtom x a (SubSExpRight _ _) impossible
superSExpNotAtom x a (SubSExpTrans sub sub') = superSExpNotAtom _ a sub'

public export
subSExpTransPair : {0 atom : Type} -> {x, x', y, y' : SExp atom} ->
  SubSExp x x' -> SubSExp x' (y $. y') -> Either (SubSExp x y) (SubSExp x y')
subSExpTransPair sub (SubSExpLeft _ _) = Left sub
subSExpTransPair sub (SubSExpRight _ _) = Right sub
subSExpTransPair sub (SubSExpTrans sub' sub'') =
  case subSExpTransPair sub' sub'' of
    Left subl => Left (SubSExpTrans sub subl)
    Right subr => Right (SubSExpTrans sub subr)

public export
data InclusiveSubSExp : {0 atom : Type} -> SExp atom -> SExp atom -> Type where
  ReflexiveSubSExp : {0 atom : Type} ->
    (x : SExp atom) -> InclusiveSubSExp x x
  InclusiveStrictSubSExp : {0 atom : Type} -> {x, x' : SExp atom} ->
    SubSExp x x' -> InclusiveSubSExp x x'

public export
InclusiveSuperSExp : {0 atom : Type} -> SExp atom -> SExp atom -> Type
InclusiveSuperSExp = flip InclusiveSubSExp

public export
SuperSExp : {0 atom : Type} -> SExp atom -> SExp atom -> Type
SuperSExp = flip SubSExp

public export
SExpAccessible : {0 atom : Type} -> SExpPred atom
SExpAccessible = Accessible SubSExp

public export
SExpSizeAccessible : (atom : Type) -> SExpPred atom
SExpSizeAccessible atom = SizeAccessible

public export
interface SExpShaped atom a where
  constructor MkSExpShaped
  total sexpShape : a -> SExp atom

public export
Substructure : {atom, a : Type} -> SExpShaped atom a => a -> a -> Type
Substructure {atom} = \x, y => SubSExp (sexpShape {atom} x) (sexpShape {atom} y)

public export
ShapeAccessible : {atom, a : Type} -> SExpShaped atom a => a -> Type
ShapeAccessible {atom} {a} = Accessible (Substructure {atom} {a})

public export
sexpAccess : {0 atom, a : Type} -> SExpShaped atom a =>
  (shape : SExp atom) -> (y : a) -> SubSExp (sexpShape y) shape ->
  ShapeAccessible {atom} y
sexpAccess ($: _) _ (SubSExpLeft _ _)
  impossible
sexpAccess (_ $. x') y (SubSExpLeft _ _) =
  Access $ \z, subzy => sexpAccess (sexpShape y) z subzy
sexpAccess ($: _) _ (SubSExpRight _ _)
  impossible
sexpAccess (x $. _) y (SubSExpRight _ _) =
  Access $ \z, subzy => sexpAccess (sexpShape y) z subzy
sexpAccess ($: _) _ (SubSExpTrans _ sub') =
  void (superSExpNotAtom _ _ sub')
sexpAccess (sl $. sr) y (SubSExpTrans {x'} {x''=(sl $. sr)} sub sub') =
  Access $ \z, subzy => case subSExpTransPair sub sub' of
    Left subyl => sexpAccess sl z (SubSExpTrans subzy subyl)
    Right subyr => sexpAccess sr z (SubSExpTrans subzy subyr)

public export
sexpShapeAccessible :
  {0 atom, a : Type} -> SExpShaped atom a => a ~> ShapeAccessible {atom}
sexpShapeAccessible x = Access (sexpAccess (sexpShape x))

public export
SExpShaped atom (SExp atom) where
  sexpShape = id

public export
(atom : Type) => WellFounded (SExp atom) (SubSExp {atom}) where
  wellFounded = sexpShapeAccessible {atom} {a=(SExp atom)}

public export
SExpShaped atom a => WellFounded a (Substructure {atom} {a}) where
  wellFounded = sexpShapeAccessible {atom} {a}

public export
sexpAccessInduction :
  {0 atom, a : Type} -> SExpShaped atom a => {0 P : !- a} ->
  (step : (x : a) -> ((y : a) -> Substructure {atom} {a} y x -> P y) -> P x) ->
  (x : a) -> (0 _ : ShapeAccessible {atom} {a} x) -> P x
sexpAccessInduction step x (Access f) =
  step x $ \y, subyx => accInd step y (f y subyx)

public export
sexpWellFoundedInduction :
  {0 atom, a : Type} -> SExpShaped atom a => {0 P : !- a} ->
  (step : (x : a) -> ((y : a) -> Substructure {atom} {a} y x -> P y) -> P x) ->
  a ~> P
sexpWellFoundedInduction {atom} {a} step x =
  sexpAccessInduction step x (sexpShapeAccessible x)

public export
sexpDecEq : {0 atom : Type} -> (deq : DecEqPred atom) -> (x, x' : SExp atom) ->
  Dec (x = x')
sexpDecEq deq ($: a) ($: a') = case deq a a' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl
sexpDecEq _ ($: a) (x $. x') = No $ \eq => case eq of Refl impossible
sexpDecEq _ (x $. x') ($: a) = No $ \eq => case eq of Refl impossible
sexpDecEq deq (x $. y) (x' $. y') =
  case (sexpDecEq deq x x', sexpDecEq deq y y') of
    (Yes Refl, Yes Refl) => Yes Refl
    (No neq, _) => No $ \eq => case eq of Refl => neq Refl
    (_, No neq) => No $ \eq => case eq of Refl => neq Refl

public export
DecEq atom => DecEq (SExp atom) where
  decEq = sexpDecEq decEq

public export
sexpEq : {0 atom : Type} -> (eq : atom -> atom -> Bool) ->
  (x, x' : SExp atom) -> Bool
sexpEq eq ($: a) ($: a') = eq a a'
sexpEq _ ($: a) (x $. x') = False
sexpEq _ (x $. x') ($: a) = False
sexpEq eq (x $. y) (x' $. y') = sexpEq eq x x' && sexpEq eq y y'

public export
Eq atom => Eq (SExp atom) where
  (==) = sexpEq (==)

public export
sexpLessThan : {0 atom : Type} -> (eq, lt : atom -> atom -> Bool) ->
  (x, x' : SExp atom) -> Bool
sexpLessThan eq lt ($: a) ($: a') = lt a a'
sexpLessThan _ _ ($: a) (x $. x') = True
sexpLessThan _ _ (x $. x') ($: a) = False
sexpLessThan eq lt (x $. y) (x' $. y') =
  if sexpLessThan eq lt x x' then
    True
  else
    if sexpEq eq x x' then
      sexpLessThan eq lt y y'
    else
      False

public export
Ord atom => Ord (SExp atom) where
  (<) = sexpLessThan (==) (<)

public export
sexpShow : {0 atom : Type} -> (showAtom : atom -> String) -> SExp atom -> String
sexpShow showAtom ($: a) =
  "($: " ++ showAtom a ++ ")"
sexpShow showAtom (x $. x') =
  "(" ++ sexpShow showAtom x ++ ", " ++ sexpShow showAtom x' ++ ")"

public export
Show atom => Show (SExp atom) where
  show = sexpShow show
