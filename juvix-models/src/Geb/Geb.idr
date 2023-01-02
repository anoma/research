module Geb.Geb

-- “Ah Love! could thou and I with Fate conspire
-- To grasp this sorry Scheme of Things entire,
-- Would not we shatter it to bits -- and then
-- Re-mould it nearer to the Heart's Desire!”
--  - _Rubaiyat of Omar Khayyam_ (tr. Edward FitzGerald)

import Library.FunctionsAndRelations
import Library.Decidability
import public RefinedSExp.List
import public RefinedSExp.SExp
import public Data.SortedSet
import public Data.SortedMap
import public Data.DPair
import public Data.Either
import public Geb.GebAtom

%default total

--------------------------------------------------------------------------------
---- Objects of the "core" logic (which underlies Geb) -------------------------
--------------------------------------------------------------------------------

public export
data CoreObjectOrder : Type where
  CoreFirstOrder : CoreObjectOrder
  CoreSecondOrder : CoreObjectOrder

public export
data CoreObject : CoreObjectOrder -> Type where

    CorePromote : CoreObject CoreFirstOrder -> CoreObject CoreSecondOrder

    CoreInitial : CoreObject CoreFirstOrder

    CoreTerminal : CoreObject CoreFirstOrder

    CoreProduct : {coreOrder : CoreObjectOrder} ->
      (first, second : CoreObject coreOrder) -> CoreObject coreOrder

    CoreCoproduct : {coreOrder : CoreObjectOrder} ->
      (left, right : CoreObject coreOrder) -> CoreObject coreOrder

    CoreExponential : {codomainOrder : CoreObjectOrder} ->
      CoreObject CoreFirstOrder -> CoreObject codomainOrder ->
      CoreObject CoreSecondOrder

    CoreObjectReflector : CoreObjectOrder -> CoreObject CoreFirstOrder

    CoreMorphismReflector : {domainOrder, codomainOrder : CoreObjectOrder} ->
      CoreObject domainOrder -> CoreObject codomainOrder ->
      CoreObject CoreFirstOrder

    {- XXX polymorphic endofunctors -}

    {- XXX initial algebras -}

    {- XXX terminal algebras -}

public export
CoreObjectPred : Type
CoreObjectPred = (coreOrder : CoreObjectOrder) -> CoreObject coreOrder -> Type

public export
record CoreObjectEliminatorSig (pred : CoreObjectPred) where
  constructor CoreObjectEliminatorArgs
  promoteElim : (object : CoreObject CoreFirstOrder) ->
    pred CoreFirstOrder object -> pred CoreSecondOrder (CorePromote object)
  initialElim : pred CoreFirstOrder CoreInitial
  terminalElim : pred CoreFirstOrder CoreTerminal
  productElim : (coreOrder : CoreObjectOrder) ->
    (first, second : CoreObject coreOrder) ->
    pred coreOrder first -> pred coreOrder second ->
    pred coreOrder (CoreProduct first second)
  coproductElim : (coreOrder : CoreObjectOrder) ->
    (left, right : CoreObject coreOrder) ->
    pred coreOrder left -> pred coreOrder right ->
    pred coreOrder (CoreCoproduct left right)
  exponentialElim : (codomainOrder : CoreObjectOrder) ->
    (domain : CoreObject CoreFirstOrder) ->
    (codomain : CoreObject codomainOrder) ->
    pred CoreFirstOrder domain -> pred codomainOrder codomain ->
    pred CoreSecondOrder (CoreExponential domain codomain)
  objectReflectorElim : (objectOrder : CoreObjectOrder) ->
    pred CoreFirstOrder (CoreObjectReflector objectOrder)
  morphismReflectorElim : (domainOrder, codomainOrder : CoreObjectOrder) ->
    (domain : CoreObject domainOrder) ->
    (codomain : CoreObject codomainOrder) ->
    pred domainOrder domain -> pred codomainOrder codomain ->
    pred CoreFirstOrder
      (CoreMorphismReflector {domainOrder} {codomainOrder} domain codomain)

public export
coreObjectEliminator : {pred : CoreObjectPred} ->
  CoreObjectEliminatorSig pred ->
  (coreOrder : CoreObjectOrder) -> (coreObject : CoreObject coreOrder) ->
  pred coreOrder coreObject
coreObjectEliminator signature CoreSecondOrder (CorePromote object) =
  promoteElim signature object $
    coreObjectEliminator signature CoreFirstOrder object
coreObjectEliminator signature CoreFirstOrder CoreInitial =
  initialElim signature
coreObjectEliminator signature CoreFirstOrder CoreTerminal =
  terminalElim signature
coreObjectEliminator signature coreOrder (CoreProduct first second) =
  productElim signature coreOrder first second
    (coreObjectEliminator signature coreOrder first)
    (coreObjectEliminator signature coreOrder second)
coreObjectEliminator signature coreOrder (CoreCoproduct left right) =
  coproductElim signature coreOrder left right
    (coreObjectEliminator signature coreOrder left)
    (coreObjectEliminator signature coreOrder right)
coreObjectEliminator signature
  CoreSecondOrder (CoreExponential {codomainOrder} domain codomain) =
    exponentialElim signature codomainOrder domain codomain
      (coreObjectEliminator signature CoreFirstOrder domain)
      (coreObjectEliminator signature codomainOrder codomain)
coreObjectEliminator signature CoreFirstOrder
  (CoreObjectReflector objectOrder) =
    objectReflectorElim signature objectOrder
coreObjectEliminator signature CoreFirstOrder
  (CoreMorphismReflector {domainOrder} {codomainOrder} domain codomain) =
    morphismReflectorElim signature domainOrder codomainOrder domain codomain
      (coreObjectEliminator signature domainOrder domain)
      (coreObjectEliminator signature codomainOrder codomain)

public export
CoreOrderedObject : Type
CoreOrderedObject = DPair CoreObjectOrder CoreObject

public export
CoreObjectPredIntroPred : CoreObjectPred
CoreObjectPredIntroPred _ _ = Type

public export
CoreObjectPredIntroSig : Type
CoreObjectPredIntroSig = CoreObjectEliminatorSig CoreObjectPredIntroPred

public export
coreObjectPredIntro :
  CoreObjectPredIntroSig ->
  (coreOrder : CoreObjectOrder) -> (coreObject : CoreObject coreOrder) ->
  Type
coreObjectPredIntro = coreObjectEliminator

public export
CoreObjectFunctorPred : CoreObjectPred
CoreObjectFunctorPred _ _ = CoreOrderedObject

public export
CoreObjectFunctorSig : Type
CoreObjectFunctorSig = CoreObjectEliminatorSig CoreObjectFunctorPred

public export
coreObjectFunctor :
  CoreObjectFunctorSig ->
  (coreOrder : CoreObjectOrder) -> (coreObject : CoreObject coreOrder) ->
  CoreOrderedObject
coreObjectFunctor = coreObjectEliminator

public export
CoreObjectDepFunctor :
  (depDomain, depCodomain : CoreObjectPredIntroSig) ->
  CoreObjectFunctorSig ->
  Type
CoreObjectDepFunctor depDomain depCodomain functor =
  (coreOrder : CoreObjectOrder) -> (object : CoreObject coreOrder) ->
  coreObjectPredIntro depDomain coreOrder object ->
  coreObjectPredIntro depCodomain
    (fst $ coreObjectFunctor functor coreOrder object)
    (snd $ coreObjectFunctor functor coreOrder object)

public export
record CoreObjectDepFunctorSig
  (depDomain, depCodomain : CoreObjectPredIntroSig)
  (functor : CoreObjectFunctorSig) where
    constructor CoreObjectDepFunctorArgs

public export
CoreObjectDepFunctorSigToEliminatorSig :
  {depDomain, depCodomain : CoreObjectPredIntroSig} ->
  {functor : CoreObjectFunctorSig} ->
  CoreObjectDepFunctorSig depDomain depCodomain functor ->
  CoreObjectEliminatorSig
    (\coreOrder, object =>
      coreObjectPredIntro depDomain coreOrder object ->
      coreObjectPredIntro depCodomain
        (fst $ coreObjectFunctor functor coreOrder object)
        (snd $ coreObjectFunctor functor coreOrder object))
CoreObjectDepFunctorSigToEliminatorSig {depDomain} {depCodomain} {functor}
  signature =
    ?CoreObjectDepFunctorSigToEliminatorSig_hole

public export
coreObjectDepFunctor :
  {depDomain, depCodomain : CoreObjectPredIntroSig} ->
  {functor : CoreObjectFunctorSig} ->
  CoreObjectDepFunctorSig depDomain depCodomain functor ->
  CoreObjectDepFunctor depDomain depCodomain functor
coreObjectDepFunctor signature =
  coreObjectEliminator (CoreObjectDepFunctorSigToEliminatorSig signature)

--------------------------------------------------------------------------------
---- Morphisms of the "core" logic (which underlies Geb) -----------------------
--------------------------------------------------------------------------------

public export
data CoreMorphism : {domainOrder, codomainOrder : CoreObjectOrder} ->
  CoreObject domainOrder -> CoreObject codomainOrder -> Type where

    CoreIdentity : {coreOrder : CoreObjectOrder} ->
      (object : CoreObject coreOrder) ->
      CoreMorphism object object

    CoreCompose : {orderA, orderB, orderC : CoreObjectOrder} ->
      {a : CoreObject orderA} ->
      {b : CoreObject orderB} ->
      {c : CoreObject orderC} ->
      CoreMorphism b c -> CoreMorphism a b -> CoreMorphism a c

    CoreFromInitial : {codomainOrder : CoreObjectOrder} ->
      (codomain : CoreObject codomainOrder) ->
      CoreMorphism CoreInitial codomain

    CoreToTerminal : {domainOrder : CoreObjectOrder} ->
      (domain : CoreObject domainOrder) ->
      CoreMorphism domain CoreTerminal

    CoreProductIntro : {domainOrder, codomainOrder : CoreObjectOrder} ->
      {domain : CoreObject domainOrder} ->
      {leftCodomain, rightCodomain : CoreObject codomainOrder} ->
      CoreMorphism domain leftCodomain -> CoreMorphism domain rightCodomain ->
      CoreMorphism domain (CoreProduct leftCodomain rightCodomain)

    CoreProductElimLeft :
      {domainOrder : CoreObjectOrder} ->
      (leftDomain, rightDomain : CoreObject domainOrder) ->
      CoreMorphism (CoreProduct leftDomain rightDomain) leftDomain

    CoreProductElimRight :
      {domainOrder : CoreObjectOrder} ->
      (leftDomain, rightDomain : CoreObject domainOrder) ->
      CoreMorphism (CoreProduct leftDomain rightDomain) rightDomain

    CoreCoproductIntroLeft :
      {codomainOrder : CoreObjectOrder} ->
      (leftCodomain, rightCodomain : CoreObject codomainOrder) ->
      CoreMorphism leftCodomain (CoreCoproduct leftCodomain rightCodomain)

    CoreCoproductIntroRight :
      {codomainOrder : CoreObjectOrder} ->
      (leftCodomain, rightCodomain : CoreObject codomainOrder) ->
      CoreMorphism rightCodomain (CoreCoproduct leftCodomain rightCodomain)

    CoreCoproductElim : {domainOrder, codomainOrder : CoreObjectOrder} ->
      {leftDomain, rightDomain : CoreObject domainOrder} ->
      {codomain : CoreObject codomainOrder} ->
      CoreMorphism leftDomain codomain -> CoreMorphism rightDomain codomain ->
      CoreMorphism (CoreCoproduct leftDomain rightDomain) codomain

    CoreAlgebraicEval :
      {codomainOrder : CoreObjectOrder} ->
      (domain : CoreObject CoreFirstOrder) ->
      (codomain : CoreObject codomainOrder) ->
      CoreMorphism
        (CoreProduct
          (CoreExponential domain codomain) (CorePromote domain)) codomain

    CoreAlgebraicCurry :
      {codomainOrder : CoreObjectOrder} ->
      {domainLeft, domainRight : CoreObject CoreFirstOrder} ->
      {codomain : CoreObject codomainOrder} ->
      CoreMorphism (CoreProduct domainLeft domainRight) codomain ->
      CoreMorphism domainLeft (CoreExponential domainRight codomain)

    CoreDecideEquality :
      {domainOrder, codomainOrder : CoreObjectOrder} ->
      {domain : CoreObject domainOrder} ->
      {codomain : CoreObject codomainOrder} ->
      {comparedType : CoreObject CoreFirstOrder} ->
      (leftInput, rightInput : CoreMorphism domain comparedType) ->
      (equalCase, notEqualCase : CoreMorphism domain codomain) ->
      CoreMorphism domain codomain

    CoreReflectedObject : {objectOrder : CoreObjectOrder} ->
      CoreObject objectOrder ->
      CoreMorphism CoreTerminal (CoreObjectReflector objectOrder)

    {- XXX morphism reflector intro (quote) - use CoreObject itself -}

    {- XXX reflector elim (Lisp eval) -}

    {- XXX endofunctor intro (first-order object to reflectors, for
     - object map and fmap) -}

    {- XXX endofunctor elims, which are initial and terminal algebra intros -}

    {- XXX initial and terminal algebra elims through isomorphic evaluators  -}

    {- XXX typecheck type; typecheck term (unit->codomain) against
     - constructor -}

    {- XXX tensor product and coproduct for endofunctors; or are those
     - derivable -}

    {- XXX morphisms which prescribe the input-output behavior of -}
    {- morphisms on first-order objects, at least with first-order -}
    {- domains; must codomains be first-order too - probably; -}
    {- do these require individual rules for each intro/elim pair, -}
    {- or could they be defined by interpretation; or will these be -}
    {- new to the Geb syntax, defined by translation to constructors -}

public export
CoreMorphismPred : Type
CoreMorphismPred = (domainOrder, codomainOrder : CoreObjectOrder) ->
  (domain : CoreObject domainOrder) -> (codomain : CoreObject codomainOrder) ->
  CoreMorphism domain codomain -> Type

public export
record CoreMorphismEliminatorSig (pred : CoreMorphismPred) where
  constructor CoreMorphismEliminatorArgs
  identityElim : (coreOrder : CoreObjectOrder) ->
    (object : CoreObject coreOrder) ->
    pred coreOrder coreOrder object object (CoreIdentity object)
  composeElim : (orderA, orderB, orderC: CoreObjectOrder) ->
    (a : CoreObject orderA) ->
    (b : CoreObject orderB) ->
    (c : CoreObject orderC) ->
    (g : CoreMorphism b c) -> (f : CoreMorphism a b) ->
    pred orderB orderC b c g ->
    pred orderA orderB a b f ->
    pred orderA orderC a c (CoreCompose g f)
  fromInitElim : (codomainOrder : CoreObjectOrder) ->
    (codomain : CoreObject codomainOrder) ->
    pred CoreFirstOrder codomainOrder CoreInitial codomain
      (CoreFromInitial codomain)
  toTerminalElim : (domainOrder : CoreObjectOrder) ->
    (domain : CoreObject domainOrder) ->
    pred domainOrder CoreFirstOrder domain CoreTerminal
      (CoreToTerminal domain)
  productIntroElim :
    (domainOrder, codomainOrder : CoreObjectOrder) ->
    (domain : CoreObject domainOrder) ->
    (leftCodomain, rightCodomain : CoreObject codomainOrder) ->
    (first : CoreMorphism domain leftCodomain) ->
    (second : CoreMorphism domain rightCodomain) ->
    pred domainOrder codomainOrder domain leftCodomain first ->
    pred domainOrder codomainOrder domain rightCodomain second ->
    pred domainOrder codomainOrder domain
      (CoreProduct leftCodomain rightCodomain) (CoreProductIntro first second)
  prodElimLeftElim : (domainOrder : CoreObjectOrder) ->
    (leftDomain, rightDomain : CoreObject domainOrder) ->
    pred domainOrder domainOrder
      (CoreProduct leftDomain rightDomain) leftDomain
      (CoreProductElimLeft leftDomain rightDomain)
  prodElimRightElim : (domainOrder : CoreObjectOrder) ->
    (leftDomain, rightDomain : CoreObject domainOrder) ->
    pred domainOrder domainOrder
      (CoreProduct leftDomain rightDomain) rightDomain
      (CoreProductElimRight leftDomain rightDomain)
  coprodIntroLeftElim : (codomainOrder : CoreObjectOrder) ->
    (leftCodomain, rightCodomain : CoreObject codomainOrder) ->
    pred codomainOrder codomainOrder
      leftCodomain (CoreCoproduct leftCodomain rightCodomain)
      (CoreCoproductIntroLeft leftCodomain rightCodomain)
  coprodIntroRightElim : (codomainOrder : CoreObjectOrder) ->
    (leftCodomain, rightCodomain : CoreObject codomainOrder) ->
    pred codomainOrder codomainOrder
      rightCodomain (CoreCoproduct leftCodomain rightCodomain)
      (CoreCoproductIntroRight leftCodomain rightCodomain)
  coproductElimElim :
    (domainOrder, codomainOrder : CoreObjectOrder) ->
    (leftDomain, rightDomain : CoreObject domainOrder) ->
    (codomain : CoreObject codomainOrder) ->
    (left : CoreMorphism leftDomain codomain) ->
    (right : CoreMorphism rightDomain codomain) ->
    pred domainOrder codomainOrder leftDomain codomain left ->
    pred domainOrder codomainOrder rightDomain codomain right ->
    pred domainOrder codomainOrder
      (CoreCoproduct leftDomain rightDomain) codomain
      (CoreCoproductElim left right)
  algebraicEvalElim :
    (codomainOrder : CoreObjectOrder) ->
    (domain : CoreObject CoreFirstOrder) ->
    (codomain : CoreObject codomainOrder) ->
    pred CoreSecondOrder codomainOrder
      (CoreProduct (CoreExponential domain codomain) (CorePromote domain))
      codomain
      (CoreAlgebraicEval domain codomain)
  curryElim :
    {codomainOrder : CoreObjectOrder} ->
    {domainLeft, domainRight : CoreObject CoreFirstOrder} ->
    {codomain : CoreObject codomainOrder} ->
    (f : CoreMorphism (CoreProduct domainLeft domainRight) codomain) ->
    pred CoreFirstOrder codomainOrder
      (CoreProduct domainLeft domainRight) codomain f ->
    pred CoreFirstOrder CoreSecondOrder
      domainLeft (CoreExponential domainRight codomain) (CoreAlgebraicCurry f)
  decideEqualityElim :
    {domainOrder, codomainOrder : CoreObjectOrder} ->
    {domain : CoreObject domainOrder} ->
    {codomain : CoreObject codomainOrder} ->
    {comparedType : CoreObject CoreFirstOrder} ->
    (leftInput, rightInput : CoreMorphism domain comparedType) ->
    (equalCase, notEqualCase : CoreMorphism domain codomain) ->
    pred domainOrder CoreFirstOrder domain comparedType leftInput ->
    pred domainOrder CoreFirstOrder domain comparedType rightInput ->
    pred domainOrder codomainOrder domain codomain equalCase ->
    pred domainOrder codomainOrder domain codomain notEqualCase ->
    pred domainOrder codomainOrder domain codomain
      (CoreDecideEquality leftInput rightInput equalCase notEqualCase)
  reflectedObjectElim :
    (objectOrder : CoreObjectOrder) ->
    (reflectedObject : CoreObject objectOrder) ->
    pred
      CoreFirstOrder CoreFirstOrder
      CoreTerminal (CoreObjectReflector objectOrder)
      (CoreReflectedObject reflectedObject)

public export
coreMorphismEliminator : {domainOrder, codomainOrder : CoreObjectOrder} ->
  {domain : CoreObject domainOrder} -> {codomain : CoreObject codomainOrder} ->
  {pred : CoreMorphismPred} -> CoreMorphismEliminatorSig pred ->
  (morphism : CoreMorphism domain codomain) ->
  pred domainOrder codomainOrder domain codomain morphism
coreMorphismEliminator signature (CoreIdentity {coreOrder} object) =
  identityElim signature coreOrder object
coreMorphismEliminator
  signature (CoreCompose {orderA} {orderB} {orderC} {a} {b} {c} g f) =
    composeElim signature orderA orderB orderC a b c g f
      (coreMorphismEliminator signature g)
      (coreMorphismEliminator signature f)
coreMorphismEliminator signature (CoreFromInitial {codomainOrder} codomain) =
  fromInitElim signature codomainOrder codomain
coreMorphismEliminator signature (CoreToTerminal {domainOrder} domain) =
  toTerminalElim signature domainOrder domain
coreMorphismEliminator {domainOrder} {codomainOrder} {domain}
  signature (CoreProductIntro {leftCodomain} {rightCodomain} first second) =
    productIntroElim signature
      domainOrder codomainOrder domain leftCodomain rightCodomain first second
      (coreMorphismEliminator signature first)
      (coreMorphismEliminator signature second)
coreMorphismEliminator signature
  (CoreProductElimLeft {domainOrder} leftDomain rightDomain) =
    prodElimLeftElim signature domainOrder leftDomain rightDomain
coreMorphismEliminator signature
  (CoreProductElimRight {domainOrder} leftDomain rightDomain) =
    prodElimRightElim signature domainOrder leftDomain rightDomain
coreMorphismEliminator
  signature (CoreCoproductIntroLeft leftCodomain rightCodomain) =
    coprodIntroLeftElim signature codomainOrder leftCodomain rightCodomain
coreMorphismEliminator
  signature (CoreCoproductIntroRight leftCodomain rightCodomain) =
    coprodIntroRightElim signature codomainOrder leftCodomain rightCodomain
coreMorphismEliminator {domainOrder} {codomainOrder} {codomain}
  signature (CoreCoproductElim {leftDomain} {rightDomain} left right) =
    coproductElimElim signature
      domainOrder codomainOrder leftDomain rightDomain codomain left right
      (coreMorphismEliminator signature left)
      (coreMorphismEliminator signature right)
coreMorphismEliminator {codomainOrder}
  signature (CoreAlgebraicEval domain codomain) =
    algebraicEvalElim signature codomainOrder domain codomain
coreMorphismEliminator {domain}
  signature (CoreAlgebraicCurry f) =
    curryElim signature f (coreMorphismEliminator signature f)
coreMorphismEliminator {domainOrder} {codomainOrder} {domain} {codomain}
  signature (CoreDecideEquality leftInput rightInput equalCase notEqualCase) =
    decideEqualityElim signature leftInput rightInput equalCase notEqualCase
      (coreMorphismEliminator signature leftInput)
      (coreMorphismEliminator signature rightInput)
      (coreMorphismEliminator signature equalCase)
      (coreMorphismEliminator signature notEqualCase)
coreMorphismEliminator signature
  (CoreReflectedObject {objectOrder} reflectedObject) =
    reflectedObjectElim signature objectOrder reflectedObject

public export
CoreSignedMorphism : Type
CoreSignedMorphism =
  (domain : CoreOrderedObject ** codomain : CoreOrderedObject **
   CoreMorphism (snd domain) (snd codomain))

public export
coreSignedMorphismDomain : CoreSignedMorphism -> CoreOrderedObject
coreSignedMorphismDomain (domain ** _ ** _) = domain

public export
coreSignedMorphismCodomain : CoreSignedMorphism -> CoreOrderedObject
coreSignedMorphismCodomain (_ ** codomain ** _) = codomain

public export
coreMorphismFromSigned : (morphism : CoreSignedMorphism) ->
  CoreMorphism
    (snd $ coreSignedMorphismDomain morphism)
    (snd $ coreSignedMorphismCodomain morphism)
coreMorphismFromSigned (_ ** _ ** morphism) = morphism

public export
CoreMorphismPredIntroPred : CoreMorphismPred
CoreMorphismPredIntroPred _ _ _ _ _ = Type

public export
CoreMorphismPredIntroSig : Type
CoreMorphismPredIntroSig = CoreMorphismEliminatorSig CoreMorphismPredIntroPred

public export
coreMorphismPredIntro :
  CoreMorphismPredIntroSig ->
  {domainOrder, codomainOrder : CoreObjectOrder} ->
  {domain : CoreObject domainOrder} -> {codomain : CoreObject codomainOrder} ->
  (morphism : CoreMorphism domain codomain) ->
  Type
coreMorphismPredIntro signature = coreMorphismEliminator signature

public export
CoreMorphismFunctorPred : CoreObjectFunctorSig -> CoreMorphismPred
CoreMorphismFunctorPred
  objectFunctor domainOrder codomainOrder domain codomain morphism =
    CoreMorphism
      {domainOrder=
        (fst $ coreObjectFunctor objectFunctor domainOrder domain)}
      {codomainOrder=
        (fst $ coreObjectFunctor objectFunctor codomainOrder codomain)}
      (snd $ coreObjectFunctor objectFunctor domainOrder domain)
      (snd $ coreObjectFunctor objectFunctor codomainOrder codomain)

public export
CoreMorphismFunctorSig : CoreObjectFunctorSig -> Type
CoreMorphismFunctorSig = CoreMorphismEliminatorSig . CoreMorphismFunctorPred

public export
coreMorphismFunctor :
  (objectFunctor : CoreObjectFunctorSig) ->
  CoreMorphismFunctorSig objectFunctor ->
  {domainOrder, codomainOrder : CoreObjectOrder} ->
  {domain : CoreObject domainOrder} -> {codomain : CoreObject codomainOrder} ->
  (morphism : CoreMorphism domain codomain) ->
  CoreMorphism
    {domainOrder=
      (fst $ coreObjectFunctor objectFunctor domainOrder domain)}
    {codomainOrder=
      (fst $ coreObjectFunctor objectFunctor codomainOrder codomain)}
    (snd $ coreObjectFunctor objectFunctor domainOrder domain)
    (snd $ coreObjectFunctor objectFunctor codomainOrder codomain)
coreMorphismFunctor objectFunctor signature morphism =
  coreMorphismEliminator signature morphism

public export
CoreMorphismDepFunctor :
  (depDomain, depCodomain : CoreMorphismPredIntroSig) ->
  (objectFunctor : CoreObjectFunctorSig) ->
  CoreMorphismFunctorSig objectFunctor ->
  Type
CoreMorphismDepFunctor depDomain depCodomain objectFunctor morphismFunctor =
  {domainOrder, codomainOrder : CoreObjectOrder} ->
  {domain : CoreObject domainOrder} -> {codomain : CoreObject codomainOrder} ->
  (morphism : CoreMorphism domain codomain) ->
  coreMorphismPredIntro depDomain morphism ->
  coreMorphismPredIntro depCodomain
    (coreMorphismFunctor objectFunctor morphismFunctor morphism)

public export
record CoreMorphismDepFunctorSig
  (depDomain, depCodomain : CoreMorphismPredIntroSig)
  (objectFunctor : CoreObjectFunctorSig)
  (morphismFunctor : CoreMorphismFunctorSig objectFunctor)
  where
    constructor CoreMorphismDepFunctorArgs

public export
CoreMorphismDepFunctorSigToEliminatorSig :
  {depDomain, depCodomain : CoreMorphismPredIntroSig} ->
  {objectFunctor : CoreObjectFunctorSig} ->
  {morphismFunctor : CoreMorphismFunctorSig objectFunctor} ->
  CoreMorphismDepFunctorSig
    depDomain depCodomain objectFunctor morphismFunctor ->
  CoreMorphismEliminatorSig
    (\domainOrder, codomainOrder, domain, codomain, morphism =>
      coreMorphismPredIntro depDomain morphism ->
      coreMorphismPredIntro depCodomain
        (coreMorphismFunctor objectFunctor morphismFunctor morphism))
CoreMorphismDepFunctorSigToEliminatorSig
  {depDomain} {depCodomain} {objectFunctor} {morphismFunctor} signature =
    ?CoreMorphismDepFunctorSigToEliminatorSig_hole

public export
coreMorphismDepFunctor :
  {depDomain, depCodomain : CoreMorphismPredIntroSig} ->
  {objectFunctor : CoreObjectFunctorSig} ->
  {morphismFunctor : CoreMorphismFunctorSig objectFunctor} ->
  CoreMorphismDepFunctorSig
    depDomain depCodomain objectFunctor morphismFunctor ->
  CoreMorphismDepFunctor depDomain depCodomain objectFunctor morphismFunctor
coreMorphismDepFunctor signature =
  coreMorphismEliminator (CoreMorphismDepFunctorSigToEliminatorSig signature)

--------------------------------------------------------------------------------
---- S-expression representation of core orders --------------------------------
--------------------------------------------------------------------------------

public export
coreOrderToSExp : CoreObjectOrder -> GebSExp
coreOrderToSExp CoreFirstOrder = $^ GAFirstOrder
coreOrderToSExp CoreSecondOrder = $^ GASecondOrder

public export
coreOrderFromSExp_certified : (x : GebSExp) ->
  Maybe (coreOrder : CoreObjectOrder ** coreOrderToSExp coreOrder = x)
coreOrderFromSExp_certified (GAFirstOrder $* []) =
  Just (CoreFirstOrder ** Refl)
coreOrderFromSExp_certified (GASecondOrder $* []) =
  Just (CoreSecondOrder ** Refl)
coreOrderFromSExp_certified _ = Nothing

public export
coreOrderFromSExp : GebSExp -> Maybe CoreObjectOrder
coreOrderFromSExp =
  certifiedMaybeToMaybe coreOrderToSExp coreOrderFromSExp_certified

public export
coreOrderEncodingCorrect : (x : GebSExp) -> (coreOrder : CoreObjectOrder) ->
  coreOrderFromSExp x = Just coreOrder -> coreOrderToSExp coreOrder = x
coreOrderEncodingCorrect =
  certifiedMaybeToCorrectness coreOrderToSExp coreOrderFromSExp_certified

public export
coreOrderEncodingComplete_certified : (coreOrder : CoreObjectOrder) ->
  coreOrderFromSExp_certified (coreOrderToSExp coreOrder) =
    Just (coreOrder ** Refl)
coreOrderEncodingComplete_certified CoreFirstOrder = Refl
coreOrderEncodingComplete_certified CoreSecondOrder = Refl

public export
coreOrderEncodingComplete : (coreOrder : CoreObjectOrder) ->
  coreOrderFromSExp (coreOrderToSExp coreOrder) = Just coreOrder
coreOrderEncodingComplete coreOrder =
  cong (map DPair.fst) (coreOrderEncodingComplete_certified coreOrder)

--------------------------------------------------------------------------------
---- Instances derived from S-expression order representation ------------------
--------------------------------------------------------------------------------

public export
Show CoreObjectOrder where
  show = show . coreOrderToSExp

public export
Eq CoreObjectOrder where
  o == o' = coreOrderToSExp o == coreOrderToSExp o'

public export
DecEq CoreObjectOrder where
  decEq =
    encodingDecEq
      coreOrderToSExp coreOrderFromSExp
      coreOrderEncodingComplete decEq

public export
Ord CoreObjectOrder where
  o < o' = coreOrderToSExp o < coreOrderToSExp o'

--------------------------------------------------------------------------------
---- S-expression representation of core logic objects -------------------------
--------------------------------------------------------------------------------

public export
MkCoreOrderedObject : {coreOrder : CoreObjectOrder} -> CoreObject coreOrder ->
  CoreOrderedObject
MkCoreOrderedObject {coreOrder} object = (coreOrder ** object)

public export
coreObjectToSExp : {coreOrder : CoreObjectOrder} -> CoreObject coreOrder ->
  GebSExp
coreObjectToSExp (CoreProduct first second) =
  GAProduct $* [coreObjectToSExp first, coreObjectToSExp second]
coreObjectToSExp (CoreCoproduct left right) =
  GACoproduct $* [coreObjectToSExp left, coreObjectToSExp right]
coreObjectToSExp (CoreExponential domain codomain) =
  GAExponential $* [coreObjectToSExp domain, coreObjectToSExp codomain]
coreObjectToSExp (CorePromote object) =
  GAPromoteToSecond $*** coreObjectToSExp object
coreObjectToSExp CoreInitial = $^ GAInitial
coreObjectToSExp CoreTerminal = $^ GATerminal
coreObjectToSExp (CoreObjectReflector coreOrder) =
  GAObjectReflector $*** coreOrderToSExp coreOrder
coreObjectToSExp (CoreMorphismReflector domain codomain) =
  GAMorphismReflector $* [coreObjectToSExp domain, coreObjectToSExp codomain]

public export
coreOrderedObjectToSExp : CoreOrderedObject -> GebSExp
coreOrderedObjectToSExp (_ ** object) = coreObjectToSExp object

public export
coreObjectFromSExp_certified : (x : GebSExp) ->
  Maybe (object : CoreOrderedObject ** coreOrderedObjectToSExp object = x)
coreObjectFromSExp_certified (GAProduct $* [first, second]) =
  case
    (coreObjectFromSExp_certified first,
     coreObjectFromSExp_certified second) of
      (Just ((coreOrder ** firstObject) ** firstCorrect),
       Just ((coreOrder' ** secondObject) ** secondCorrect)) =>
        case decEq coreOrder coreOrder' of
          Yes Refl =>
            Just ((coreOrder ** CoreProduct firstObject secondObject) **
                  rewrite sym firstCorrect in
                  rewrite sym secondCorrect in
                  Refl)
          No _ => Nothing
      _ => Nothing
coreObjectFromSExp_certified (GACoproduct $* [left, right]) =
  case
    (coreObjectFromSExp_certified left,
     coreObjectFromSExp_certified right) of
      (Just ((coreOrder ** leftObject) ** leftCorrect),
       Just ((coreOrder' ** rightObject) ** rightCorrect)) =>
        case decEq coreOrder coreOrder' of
          Yes Refl =>
            Just ((coreOrder ** CoreCoproduct leftObject rightObject) **
                  rewrite sym leftCorrect in
                  rewrite sym rightCorrect in
                  Refl)
          No _ => Nothing
      _ => Nothing
coreObjectFromSExp_certified (GAExponential $* [domain, codomain]) =
  case
    (coreObjectFromSExp_certified domain,
     coreObjectFromSExp_certified codomain) of
      (Just ((CoreFirstOrder ** domainObject) ** domainCorrect),
       Just ((codomainOrder ** codomainObject) ** codomainCorrect)) =>
        Just ((CoreSecondOrder **
               CoreExponential domainObject codomainObject) **
              rewrite sym domainCorrect in
              rewrite sym codomainCorrect in
              Refl)
      _ => Nothing
coreObjectFromSExp_certified (GAPromoteToSecond $* [object]) =
  case coreObjectFromSExp_certified object of
    Just ((CoreFirstOrder ** firstOrderObject) ** correct) =>
      Just
        ((CoreSecondOrder ** CorePromote firstOrderObject) **
         rewrite correct in Refl)
    _ => Nothing
coreObjectFromSExp_certified (GAInitial $* []) =
  Just ((CoreFirstOrder ** CoreInitial) ** Refl)
coreObjectFromSExp_certified (GATerminal $* []) =
  Just ((CoreFirstOrder ** CoreTerminal) ** Refl)
coreObjectFromSExp_certified (GAObjectReflector $* [coreOrder]) =
  case coreOrderFromSExp_certified coreOrder of
    Just (reflectedObjectOrder ** correct) =>
      Just ((CoreFirstOrder ** CoreObjectReflector reflectedObjectOrder) **
            rewrite correct in Refl)
    _ => Nothing
coreObjectFromSExp_certified (GAMorphismReflector $* [domain, codomain]) =
  case
    (coreObjectFromSExp_certified domain,
     coreObjectFromSExp_certified codomain) of
      (Just ((domainOrder ** domainObject) ** domainCorrect),
       Just ((codomainOrder ** codomainObject) ** codomainCorrect)) =>
        Just ((CoreFirstOrder **
               CoreMorphismReflector domainObject codomainObject) **
              rewrite sym domainCorrect in
              rewrite sym codomainCorrect in
              Refl)
      _ => Nothing
coreObjectFromSExp_certified _ = Nothing

public export
coreObjectFromSExp : GebSExp -> Maybe CoreOrderedObject
coreObjectFromSExp =
  certifiedMaybeToMaybe coreOrderedObjectToSExp coreObjectFromSExp_certified

public export
coreObjectEncodingCorrect : (x : GebSExp) -> (object : CoreOrderedObject) ->
  coreObjectFromSExp x = Just object -> coreOrderedObjectToSExp object = x
coreObjectEncodingCorrect =
  certifiedMaybeToCorrectness
    coreOrderedObjectToSExp
    coreObjectFromSExp_certified

public export
coreObjectEncodingComplete : {coreOrder : CoreObjectOrder} ->
  (object : CoreObject coreOrder) ->
  coreObjectFromSExp_certified (coreObjectToSExp object) =
    Just ((MkCoreOrderedObject object) ** Refl)
coreObjectEncodingComplete (CorePromote object) =
  rewrite coreObjectEncodingComplete object in
  Refl
coreObjectEncodingComplete CoreInitial = Refl
coreObjectEncodingComplete CoreTerminal = Refl
coreObjectEncodingComplete (CoreProduct {coreOrder} first second) =
  rewrite coreObjectEncodingComplete first in
  rewrite coreObjectEncodingComplete second in
  rewrite decEqRefl decEq coreOrder in
  Refl
coreObjectEncodingComplete (CoreCoproduct {coreOrder} left right) =
  rewrite coreObjectEncodingComplete left in
  rewrite coreObjectEncodingComplete right in
  rewrite decEqRefl decEq coreOrder in
  Refl
coreObjectEncodingComplete (CoreExponential domain codomain) =
  rewrite coreObjectEncodingComplete domain in
  rewrite coreObjectEncodingComplete codomain in
  Refl
coreObjectEncodingComplete (CoreObjectReflector coreOrder) =
  rewrite coreOrderEncodingComplete_certified coreOrder in
  Refl
coreObjectEncodingComplete (CoreMorphismReflector domain codomain) =
  rewrite coreObjectEncodingComplete domain in
  rewrite coreObjectEncodingComplete codomain in
  Refl

public export
coreOrderedObjectEncodingComplete : (object : CoreOrderedObject) ->
  coreObjectFromSExp (coreOrderedObjectToSExp object) = Just object
coreOrderedObjectEncodingComplete (_ ** object) =
  cong (map DPair.fst) (coreObjectEncodingComplete object)

--------------------------------------------------------------------------------
---- Instances derived from S-expression object representation -----------------
--------------------------------------------------------------------------------

public export
[CoreOrderedObjectShow] Show CoreOrderedObject where
  show = show . coreOrderedObjectToSExp

public export
Eq CoreOrderedObject where
  o == o' = coreOrderedObjectToSExp o == coreOrderedObjectToSExp o'

public export
DecEq CoreOrderedObject where
  decEq =
    encodingDecEq
      coreOrderedObjectToSExp coreObjectFromSExp
      coreOrderedObjectEncodingComplete decEq

public export
Ord CoreOrderedObject where
  o < o' = coreOrderedObjectToSExp o < coreOrderedObjectToSExp o'

public export
coreObjectDecEq : {coreOrder : CoreObjectOrder} ->
  DecEqPred (CoreObject coreOrder)
coreObjectDecEq o o' with
  (decEq (MkCoreOrderedObject o) (MkCoreOrderedObject o'))
    coreObjectDecEq _ _ | Yes Refl = Yes Refl
    coreObjectDecEq o o' | No neq = No $ \eq => case eq of Refl => neq Refl

public export
(coreOrder : CoreObjectOrder) => Show (CoreObject coreOrder)
  using CoreOrderedObjectShow where
    show object = show (MkCoreOrderedObject object)

public export
(coreOrder : CoreObjectOrder) => DecEq (CoreObject coreOrder) where
  decEq = coreObjectDecEq

public export
(coreOrder : CoreObjectOrder) => Eq (CoreObject coreOrder)
  using decEqToEq where
    (==) = (==)

public export
(coreOrder : CoreObjectOrder) => Ord (CoreObject coreOrder) where
  o < o' = MkCoreOrderedObject o < MkCoreOrderedObject o'

--------------------------------------------------------------------------------
---- S-expression representation of core logic morphisms -----------------------
--------------------------------------------------------------------------------

public export
MkCoreSignedMorphism : {domainOrder, codomainOrder : CoreObjectOrder} ->
  {domain : CoreObject domainOrder} -> {codomain : CoreObject codomainOrder} ->
  CoreMorphism domain codomain -> CoreSignedMorphism
MkCoreSignedMorphism {domain} {codomain} morphism =
  (MkCoreOrderedObject domain ** MkCoreOrderedObject codomain ** morphism)

public export
coreMorphismToSExp : {domainOrder, codomainOrder : CoreObjectOrder} ->
  {domain : CoreObject domainOrder} -> {codomain : CoreObject codomainOrder} ->
  CoreMorphism domain codomain -> GebSExp
coreMorphismToSExp (CoreIdentity domain) =
  GAIdentity $*** coreObjectToSExp domain
coreMorphismToSExp (CoreCompose g f) =
  GACompose $* [coreMorphismToSExp g, coreMorphismToSExp f]
coreMorphismToSExp (CoreFromInitial codomain) =
  GAFromInitial $*** coreObjectToSExp codomain
coreMorphismToSExp (CoreToTerminal domain) =
  GAToTerminal $*** coreObjectToSExp domain
coreMorphismToSExp (CoreProductIntro first second) =
  GAProductIntro $* [coreMorphismToSExp first, coreMorphismToSExp second]
coreMorphismToSExp (CoreProductElimLeft leftDomain rightDomain) =
  GAProductElimLeft $*
    [coreObjectToSExp leftDomain, coreObjectToSExp rightDomain]
coreMorphismToSExp (CoreProductElimRight leftDomain rightDomain) =
  GAProductElimRight $*
    [coreObjectToSExp leftDomain, coreObjectToSExp rightDomain]
coreMorphismToSExp (CoreCoproductIntroLeft leftCodomain rightCodomain) =
  GACoproductIntroLeft $*
    [coreObjectToSExp leftCodomain, coreObjectToSExp rightCodomain]
coreMorphismToSExp (CoreCoproductIntroRight leftCodomain rightCodomain) =
  GACoproductIntroRight $*
    [coreObjectToSExp leftCodomain, coreObjectToSExp rightCodomain]
coreMorphismToSExp (CoreCoproductElim left right) =
  GACoproductElim $* [coreMorphismToSExp left, coreMorphismToSExp right]
coreMorphismToSExp (CoreAlgebraicEval domain codomain) =
  GAExponentialEval $* [coreObjectToSExp domain, coreObjectToSExp codomain]
coreMorphismToSExp (CoreAlgebraicCurry f) = GACurry $*** coreMorphismToSExp f
coreMorphismToSExp
  (CoreDecideEquality leftInput rightInput equalCase notEqualCase) =
    GADecideEquality $*
      [coreMorphismToSExp leftInput,
       coreMorphismToSExp rightInput,
       coreMorphismToSExp equalCase,
       coreMorphismToSExp notEqualCase]
coreMorphismToSExp (CoreReflectedObject reflectedObject) =
  GAReflectedObject $*** coreObjectToSExp reflectedObject

public export
coreSignedMorphismToSExp : CoreSignedMorphism -> GebSExp
coreSignedMorphismToSExp (_ ** _ ** morphism) = coreMorphismToSExp morphism

public export
coreMorphismFromSExp_certified : (x : GebSExp) ->
  Maybe (morphism : CoreSignedMorphism ** coreSignedMorphismToSExp morphism = x)
coreMorphismFromSExp_certified (GAIdentity $* [object]) =
  case coreObjectFromSExp_certified object of
    Just ((_ ** coreObject) ** correct) =>
      Just (MkCoreSignedMorphism (CoreIdentity coreObject) **
            rewrite correct in Refl)
    Nothing => Nothing
coreMorphismFromSExp_certified (GACompose $* [g, f]) =
  case (coreMorphismFromSExp_certified g,
        coreMorphismFromSExp_certified f) of
    (Just (((domainOrder ** domain) ** (codomainOrder ** codomain) ** mg) **
           gCorrect),
     Just (((domainOrder' ** domain') ** (codomainOrder' ** codomain') ** mf) **
           fCorrect)) =>
      case decEq domainOrder codomainOrder' of
        Yes Refl => case decEq domain codomain' of
          Yes Refl =>
            Just (MkCoreSignedMorphism (CoreCompose mg mf) **
                  rewrite gCorrect in rewrite fCorrect in Refl)
          No _ => Nothing
        No _ => Nothing
    _ => Nothing
coreMorphismFromSExp_certified (GAFromInitial $* [codomain]) =
  case coreObjectFromSExp_certified codomain of
    Just ((_ ** codomainObject) ** correct) =>
      Just (MkCoreSignedMorphism (CoreFromInitial codomainObject) **
            rewrite correct in Refl)
    Nothing => Nothing
coreMorphismFromSExp_certified (GAToTerminal $* [domain]) =
  case coreObjectFromSExp_certified domain of
    Just ((_ ** domainObject) ** correct) =>
      Just (MkCoreSignedMorphism (CoreToTerminal domainObject) **
            case correct of
              Refl => ?coreMorphismFromSExp_certified_hole_terminal_correct)
    Nothing => Nothing
coreMorphismFromSExp_certified (GAProductIntro $* [left, right]) =
  case (coreMorphismFromSExp_certified left,
        coreMorphismFromSExp_certified right) of
    (Just (((leftDomainOrder ** leftDomain) **
            (leftCodomainOrder ** _) ** leftMorphism) **
           leftCorrect),
     Just (((rightDomainOrder ** rightDomain) **
            (rightCodomainOrder ** _) ** rightMorphism) **
           rightCorrect)) =>
      case (decEq leftDomainOrder rightDomainOrder,
            decEq leftCodomainOrder rightCodomainOrder) of
        (Yes Refl, Yes Refl) => case decEq leftDomain rightDomain of
          Yes Refl =>
            Just (MkCoreSignedMorphism
                    (CoreProductIntro leftMorphism rightMorphism) **
                  case leftCorrect of
                    Refl => case rightCorrect of
                      Refl =>
                        ?coreMorphismFromSExpCertified_hole_prod_intro_correct)
          No _ => Nothing
        _ => Nothing
    _ => Nothing
coreMorphismFromSExp_certified (GAProductElimLeft $* [left, right]) =
  case (coreObjectFromSExp_certified left,
        coreObjectFromSExp_certified right) of
    (Just ((leftDomainOrder ** leftDomain) ** leftCorrect),
     Just ((rightDomainOrder ** rightDomain) ** rightCorrect)) =>
      case decEq leftDomainOrder rightDomainOrder of
        Yes Refl => Just (MkCoreSignedMorphism
                            (CoreProductElimLeft leftDomain rightDomain) **
                          case leftCorrect of
                            Refl => case rightCorrect of
                              Refl =>
                                ?cMFSExp_certified_hole_prod_elim_left_correct)
        No _ => Nothing
    _ => Nothing
coreMorphismFromSExp_certified (GAProductElimRight $* [left, right]) =
  case (coreObjectFromSExp_certified left,
        coreObjectFromSExp_certified right) of
    (Just ((leftDomainOrder ** leftDomain) ** leftCorrect),
     Just ((rightDomainOrder ** rightDomain) ** rightCorrect)) =>
      case decEq leftDomainOrder rightDomainOrder of
        Yes Refl => Just (MkCoreSignedMorphism
                            (CoreProductElimRight leftDomain rightDomain) **
                          case leftCorrect of
                            Refl => case rightCorrect of
                              Refl =>
                                ?cMFSExp_certified_hole_prod_elim_right_correct)
        No _ => Nothing
    _ => Nothing
coreMorphismFromSExp_certified (GACoproductElim $* [left, right]) =
  case (coreMorphismFromSExp_certified left,
        coreMorphismFromSExp_certified right) of
    (Just (((leftDomainOrder ** _) **
            (leftCodomainOrder ** leftCodomain) ** leftMorphism) **
           leftCorrect),
     Just (((rightDomainOrder ** _) **
            (rightCodomainOrder ** rightCodomain) ** rightMorphism) **
           rightCorrect)) =>
      case (decEq leftDomainOrder rightDomainOrder,
            decEq leftCodomainOrder rightCodomainOrder) of
        (Yes Refl, Yes Refl) => case decEq leftCodomain rightCodomain of
          Yes Refl =>
            Just (MkCoreSignedMorphism
                    (CoreCoproductElim leftMorphism rightMorphism) **
                  case leftCorrect of
                    Refl => case rightCorrect of
                      Refl =>
                        ?coreMorphismFromSExpCertified_hole_copr_elim_correct)
          No _ => Nothing
        _ => Nothing
    _ => Nothing
coreMorphismFromSExp_certified (GACoproductIntroLeft $* [left, right]) =
  case (coreObjectFromSExp_certified left,
        coreObjectFromSExp_certified right) of
    (Just ((leftCodomainOrder ** leftCodomain) ** leftCorrect),
     Just ((rightCodomainOrder ** rightCodomain) ** rightCorrect)) =>
      case decEq leftCodomainOrder rightCodomainOrder of
        Yes Refl => Just (MkCoreSignedMorphism
                            (CoreCoproductIntroLeft
                              leftCodomain rightCodomain) **
                          case leftCorrect of
                            Refl => case rightCorrect of
                              Refl =>
                                ?cMFSExp_cert_hole_coprod_intro_left_correct)
        No _ => Nothing
    _ => Nothing
coreMorphismFromSExp_certified (GACoproductIntroRight $* [left, right]) =
  case (coreObjectFromSExp_certified left,
        coreObjectFromSExp_certified right) of
    (Just ((leftCodomainOrder ** leftCodomain) ** leftCorrect),
     Just ((rightCodomainOrder ** rightCodomain) ** rightCorrect)) =>
      case decEq leftCodomainOrder rightCodomainOrder of
        Yes Refl => Just (MkCoreSignedMorphism
                            (CoreCoproductIntroRight
                              leftCodomain rightCodomain) **
                          case leftCorrect of
                            Refl => case rightCorrect of
                              Refl =>
                                ?cMFSExp_cert_hole_coprod_intro_right_correct)
        No _ => Nothing
    _ => Nothing
coreMorphismFromSExp_certified (GAExponentialEval $* [domain, codomain]) =
  case (coreObjectFromSExp_certified domain,
        coreObjectFromSExp_certified codomain) of
    (Just ((domainOrder ** domain) ** domainCorrect),
     Just ((codomainOrder ** codomain) ** codomainCorrect)) =>
      case decEq domainOrder CoreFirstOrder of
        Yes Refl => Just (MkCoreSignedMorphism
                            (CoreAlgebraicEval domain codomain) **
                          case domainCorrect of
                            Refl => case codomainCorrect of
                              Refl =>
                                ?cMFSExp_cert_hole_eval_correct)
        No _ => Nothing
    _ => Nothing
coreMorphismFromSExp_certified (GACurry $* [f]) =
  case (coreMorphismFromSExp_certified f) of
    Just (((domainOrder ** domain) **
           (codomainOrder ** codomain) **
           mf) **
          correct) =>
      case decEq domainOrder CoreFirstOrder of
        Yes Refl => case domain of
          CoreProduct domainLeft domainRight =>
            Just (MkCoreSignedMorphism
                  (CoreAlgebraicCurry mf) **
                  case correct of Refl => ?cMFSExp_cert_hole_curry_correct)
          _ => Nothing
        No _ => Nothing
    _ => Nothing
coreMorphismFromSExp_certified
  (GADecideEquality $*
    [leftInputExp, rightInputExp, equalCaseExp, notEqualCaseExp]) =
  case (coreMorphismFromSExp_certified leftInputExp,
        coreMorphismFromSExp_certified rightInputExp,
        coreMorphismFromSExp_certified equalCaseExp,
        coreMorphismFromSExp_certified notEqualCaseExp) of
    (Just (((leftDomainOrder ** leftDomain) **
            (leftCodomainOrder ** leftCodomain) ** leftInput) **
           leftCorrect),
     Just (((rightDomainOrder ** rightDomain) **
            (rightCodomainOrder ** rightCodomain) ** rightInput) **
           rightCorrect),
     Just (((equalDomainOrder ** equalDomain) **
            (equalCodomainOrder ** equalCodomain) ** equalCase) **
           equalCorrect),
     Just (((notEqualDomainOrder ** notEqualDomain) **
            (notEqualCodomainOrder ** notEqualCodomain) ** notEqualCase) **
           notEqualCorrect)) =>
      case (decEq leftDomainOrder rightDomainOrder,
            decEq leftDomainOrder equalDomainOrder,
            decEq leftDomainOrder notEqualDomainOrder) of
        (Yes Refl, Yes Refl, Yes Refl) =>
          case (decEq leftCodomainOrder CoreFirstOrder,
                decEq rightCodomainOrder CoreFirstOrder,
                decEq equalCodomainOrder notEqualCodomainOrder) of
            (Yes Refl, Yes Refl, Yes Refl) =>
              case (decEq leftDomain rightDomain,
                    decEq leftDomain equalDomain,
                    decEq leftDomain notEqualDomain) of
                (Yes Refl, Yes Refl, Yes Refl) =>
                  case (decEq leftCodomain rightCodomain,
                        decEq equalCodomain notEqualCodomain) of
                    (Yes Refl, Yes Refl) =>
                      Just (MkCoreSignedMorphism
                              (CoreDecideEquality
                                leftInput rightInput
                                equalCase notEqualCase) **
                            case leftCorrect of
                              Refl => case rightCorrect of
                                Refl => case equalCorrect of
                                  Refl => case notEqualCorrect of
                                    Refl =>
                                      ?cMFSExp_cert_hole_dec_equality_correct)
                    _ => Nothing
                _ => Nothing
            _ => Nothing
        _ => Nothing
    _ => Nothing
coreMorphismFromSExp_certified _ = Nothing

public export
coreMorphismFromSExp : GebSExp -> Maybe CoreSignedMorphism
coreMorphismFromSExp =
  certifiedMaybeToMaybe coreSignedMorphismToSExp coreMorphismFromSExp_certified

public export
coreMorphismEncodingCorrect : (x : GebSExp) ->
  (morphism : CoreSignedMorphism) ->
  coreMorphismFromSExp x = Just morphism ->
  coreSignedMorphismToSExp morphism = x
coreMorphismEncodingCorrect =
  certifiedMaybeToCorrectness
    coreSignedMorphismToSExp coreMorphismFromSExp_certified

public export
coreMorphismEncodingComplete : {domainOrder, codomainOrder : CoreObjectOrder} ->
  {domain : CoreObject domainOrder} -> {codomain : CoreObject codomainOrder} ->
  (morphism : CoreMorphism domain codomain) ->
  coreMorphismFromSExp_certified (coreMorphismToSExp morphism) =
    Just ((MkCoreSignedMorphism morphism) ** Refl)
coreMorphismEncodingComplete morphism = ?coreMorphismEncodingComplete_hole

public export
coreSignedMorphismEncodingComplete : (morphism : CoreSignedMorphism) ->
  coreMorphismFromSExp (coreSignedMorphismToSExp morphism) = Just morphism
coreSignedMorphismEncodingComplete ((_ ** _) ** (_ ** _) ** morphism) =
  cong (map DPair.fst) (coreMorphismEncodingComplete morphism)

--------------------------------------------------------------------------------
---- Instances derived from S-expression morphism representation ---------------
--------------------------------------------------------------------------------

public export
Show CoreSignedMorphism where
  show = show . coreSignedMorphismToSExp

public export
Eq CoreSignedMorphism where
  m == m' = coreSignedMorphismToSExp m == coreSignedMorphismToSExp m'

public export
DecEq CoreSignedMorphism where
  decEq =
    encodingDecEq
      coreSignedMorphismToSExp coreMorphismFromSExp
      coreSignedMorphismEncodingComplete decEq

public export
Ord CoreSignedMorphism where
  m < m' = coreSignedMorphismToSExp m < coreSignedMorphismToSExp m'

public export
coreMorphismDecEq : {domainOrder, codomainOrder : CoreObjectOrder} ->
  {domain : CoreObject domainOrder} -> {codomain : CoreObject codomainOrder} ->
  DecEqPred (CoreMorphism domain codomain)
coreMorphismDecEq m m' with
  (decEq (MkCoreSignedMorphism m) (MkCoreSignedMorphism m'))
    coreMorphismDecEq _ _ | Yes Refl = Yes Refl
    coreMorphismDecEq m m' | No neq = No $ \eq => case eq of Refl => neq Refl

public export
showMorphism : {domainOrder, codomainOrder : CoreObjectOrder} ->
  {domain : CoreObject domainOrder} -> {codomain : CoreObject codomainOrder} ->
  CoreMorphism domain codomain -> String
showMorphism morphism = show (MkCoreSignedMorphism morphism)

public export
eqMorphism : {domainOrder, codomainOrder : CoreObjectOrder} ->
  {domain : CoreObject domainOrder} -> {codomain : CoreObject codomainOrder} ->
  (m, m' : CoreMorphism domain codomain) -> Bool
eqMorphism m m' = isYes $ coreMorphismDecEq m m'

public export
ltMorphism : {domainOrder, codomainOrder : CoreObjectOrder} ->
  {domain : CoreObject domainOrder} -> {codomain : CoreObject codomainOrder} ->
  (m, m' : CoreMorphism domain codomain) -> Bool
ltMorphism m m' = MkCoreSignedMorphism m < MkCoreSignedMorphism m'

--------------------------------------------------------------------------------
---- Metalanguage interpretation of core logic objects -------------------------
--------------------------------------------------------------------------------

mutual
  public export
  interpretCoreObject : {coreOrder : CoreObjectOrder} ->
    CoreObject coreOrder -> Type
  interpretCoreObject (CoreProduct {coreOrder} first second) =
    interpretCoreProduct {coreOrder} first second
  interpretCoreObject (CoreCoproduct left right) =
    interpretCoreCoproduct left right
  interpretCoreObject (CoreExponential domain codomain) =
    interpretCoreExponential domain codomain
  interpretCoreObject CoreInitial = Void
  interpretCoreObject CoreTerminal = Unit
  interpretCoreObject (CoreObjectReflector coreOrder) =
    CoreObject coreOrder
  interpretCoreObject (CoreMorphismReflector domain codomain) =
    CoreMorphism domain codomain
  interpretCoreObject (CorePromote object) = interpretCoreObject object

  public export
  interpretCoreProduct : {coreOrder : CoreObjectOrder} ->
    (first, second : CoreObject coreOrder) -> Type
  interpretCoreProduct first second =
    Pair (interpretCoreObject first) (interpretCoreObject second)

  public export
  interpretCoreCoproduct : {coreOrder : CoreObjectOrder} ->
    (left, right : CoreObject coreOrder) -> Type
  interpretCoreCoproduct left right =
    Either (interpretCoreObject left) (interpretCoreObject right)

  public export
  interpretCoreExponential : {domainOrder, codomainOrder : CoreObjectOrder} ->
    CoreObject domainOrder -> CoreObject codomainOrder -> Type
  interpretCoreExponential domain codomain =
    interpretCoreObject domain -> interpretCoreObject codomain

public export
coreDecideFirstOrderEquality : (object : CoreObject CoreFirstOrder) ->
  DecEqPred $ interpretCoreObject object
coreDecideFirstOrderEquality CoreInitial term _ = void term
coreDecideFirstOrderEquality CoreTerminal () () = Yes Refl
coreDecideFirstOrderEquality (CoreProduct first second)
  (left, right) (left', right') =
    case
      (coreDecideFirstOrderEquality first left left',
      coreDecideFirstOrderEquality second right right') of
        (Yes Refl, Yes Refl) => Yes Refl
        (No neq, _) => No $ \eq => case eq of Refl => neq Refl
        (_, No neq) => No $ \eq => case eq of Refl => neq Refl
coreDecideFirstOrderEquality (CoreCoproduct left right)
  (Left leftTerm) (Left leftTerm') =
    case coreDecideFirstOrderEquality left leftTerm leftTerm' of
      Yes Refl => Yes Refl
      No neq => No $ \eq => neq $ injective eq
coreDecideFirstOrderEquality (CoreCoproduct left right)
  (Left _) (Right _) = No $ \eq => case eq of Refl impossible
coreDecideFirstOrderEquality (CoreCoproduct left right)
  (Right _) (Left _) = No $ \eq => case eq of Refl impossible
coreDecideFirstOrderEquality (CoreCoproduct left right)
  (Right rightTerm) (Right rightTerm') =
    case coreDecideFirstOrderEquality right rightTerm rightTerm' of
      Yes Refl => Yes Refl
      No neq => No $ \eq => neq $ rightInjective eq
coreDecideFirstOrderEquality (CoreObjectReflector coreOrder) term term' =
  coreObjectDecEq term term'
coreDecideFirstOrderEquality (CoreMorphismReflector domain codomain)
  term term' =
    coreMorphismDecEq term term'

--------------------------------------------------------------------------------
---- Metalanguage interpretation of core logic morphisms -----------------------
--------------------------------------------------------------------------------

mutual
  public export
  interpretCoreMorphism : {domainOrder, codomainOrder : CoreObjectOrder} ->
    {domain : CoreObject domainOrder} ->
    {codomain : CoreObject codomainOrder} ->
    CoreMorphism domain codomain ->
    interpretCoreExponential domain codomain
  interpretCoreMorphism (CoreIdentity _) =
    id
  interpretCoreMorphism (CoreCompose g f) =
    interpretCoreMorphism g . interpretCoreMorphism f
  interpretCoreMorphism (CoreFromInitial _) =
    \v => void v
  interpretCoreMorphism (CoreToTerminal _) =
    \_ => ()
  interpretCoreMorphism (CoreProductIntro first second) = \term =>
    (interpretCoreMorphism first term, interpretCoreMorphism second term)
  interpretCoreMorphism
    (CoreProductElimLeft {domainOrder} leftDomain codomain) =
      fst
  interpretCoreMorphism
    (CoreProductElimRight rightDomain codomain) =
      snd
  interpretCoreMorphism (CoreCoproductIntroLeft domain leftCodomain) =
    Left
  interpretCoreMorphism (CoreCoproductIntroRight domain rightCodomain) =
    Right
  interpretCoreMorphism (CoreCoproductElim left right) = \term =>
    case term of
      Left leftTerm => interpretCoreMorphism left leftTerm
      Right rightTerm => interpretCoreMorphism right rightTerm
  interpretCoreMorphism (CoreAlgebraicEval _ _) = \p => fst p $ snd p
  interpretCoreMorphism (CoreAlgebraicCurry f) =
    \x, y => interpretCoreMorphism f (x, y)
  interpretCoreMorphism
    (CoreDecideEquality
      {comparedType} leftInput rightInput equalCase notEqualCase) = \term =>
        case coreDecideFirstOrderEquality
          comparedType
          (interpretCoreMorphism leftInput term)
          (interpretCoreMorphism rightInput term) of
            Yes _ => interpretCoreMorphism equalCase term
            No _ => interpretCoreMorphism notEqualCase term
  interpretCoreMorphism (CoreReflectedObject object) = \_ => object

{-
public export
data ConcreteReflection : Type where

public export
data CategoryGenerator : ConcreteReflection -> Type where

public export
data GebOrder : {reflection : ConcreteReflection} ->
  (category : CategoryGenerator reflection) -> Type where

    NatOrder : Nat -> GebOrder category

    HigherOrder : GebOrder category

    TuringComplete : GebOrder category

public export
ZeroOrder : GebOrder category
ZeroOrder = NatOrder 0

public export
FirstOrder : GebOrder category
FirstOrder = NatOrder 1

public export
SecondOrder : GebOrder category
SecondOrder = NatOrder 2

public export
ThirdOrder : GebOrder category
ThirdOrder = NatOrder 3

public export
data CanPromote : {reflection : ConcreteReflection} ->
  (category : CategoryGenerator reflection) ->
  (oldOrder, newOrder : GebOrder category) -> Type where

    PromoteFinite : (n : Nat) ->
      CanPromote category (NatOrder n) (NatOrder $ S n)

    PromoteToHigher : (n : Nat) -> CanPromote category (NatOrder n) HigherOrder

    HigherOrderIsCartesianClosed :
      CanPromote category HigherOrder HigherOrder

    PromoteToTuring : CanPromote category HigherOrder TuringComplete

    TuringCompleteIsCartesianClosed :
      CanPromote category TuringComplete TuringComplete

public export
data GebCategoryObject : {reflection : ConcreteReflection} ->
  (category : CategoryGenerator reflection) -> (gebOrder : GebOrder category) ->
  Type where

    PromoteObject : {oldOrder, newOrder : GebOrder category} ->
      {auto canPromote : CanPromote category oldOrder newOrder} ->
      GebCategoryObject category oldOrder -> GebCategoryObject category newOrder

    GebVoid : GebCategoryObject category gebOrder

    GebUnit : GebCategoryObject category gebOrder

    GebProduct : List (GebCategoryObject category gebOrder) ->
      GebCategoryObject category gebOrder

    GebCoproduct : List (GebCategoryObject category gebOrder) ->
      GebCategoryObject category gebOrder

    GebExponential :
      {oldOrder, newOrder : GebOrder category} ->
      {auto canPromote : CanPromote category oldOrder newOrder} ->
      (domain, codomain : GebCategoryObject category oldOrder) ->
      GebCategoryObject category newOrder

    GebObjectReflection : GebCategoryObject category ZeroOrder

    GebMorphismReflection :
      (domain, codomain : GebCategoryObject category gebOrder) ->
      GebCategoryObject category ZeroOrder

public export
data GebCategoryMorphism : {reflection : ConcreteReflection} ->
  {category : CategoryGenerator reflection} ->
  {domainOrder, codomainOrder : GebOrder category} ->
  (domain : GebCategoryObject {reflection} category domainOrder) ->
  (codomain : GebCategoryObject {reflection} category codomainOrder) ->
  (morphismOrder : GebOrder category) ->
  Type where

    PromoteMorphism : {oldOrder, newOrder : GebOrder category} ->
      {auto canPromote : CanPromote category oldOrder newOrder} ->
      GebCategoryMorphism domain codomain oldOrder ->
      GebCategoryMorphism domain codomain newOrder

    GebIdentity : {objectOrder : GebOrder category} ->
      (object : GebCategoryObject category objectOrder) ->
      (morphismOrder : GebOrder category) ->
      {auto canPromote : CanPromote category objectOrder morphismOrder} ->
      GebCategoryMorphism {category} object object morphismOrder

    GebCompose :
      GebCategoryMorphism b c morphismOrder ->
      GebCategoryMorphism a b morphismOrder ->
      GebCategoryMorphism a c morphismOrder

    GebFromVoid : {codomainOrder : GebOrder category} ->
      {codomain : GebCategoryObject category codomainOrder} ->
      (morphismOrder : GebOrder category) ->
      {auto canPromote : CanPromote category codomainOrder morphismOrder} ->
      GebCategoryMorphism
        {domainOrder=ZeroOrder} GebVoid codomain morphismOrder

    GebToUnit : {domainOrder : GebOrder category} ->
      {domain : GebCategoryObject category domainOrder} ->
      (morphismOrder : GebOrder category) ->
      {auto canPromote : CanPromote category domainOrder morphismOrder} ->
      GebCategoryMorphism
        {codomainOrder=ZeroOrder} domain GebUnit morphismOrder

    GebProductIntro :
      {domain : GebCategoryObject category domainOrder} ->
      (morphisms : List
        (codomain : GebCategoryObject category codomainOrder **
         GebCategoryMorphism domain codomain morphismOrder)) ->
      GebCategoryMorphism
        domain (GebProduct (map DPair.fst morphisms)) morphismOrder

    GebProductElim :
      {objectOrder : GebOrder category} ->
      (domains : List (GebCategoryObject category objectOrder)) ->
      (morphismOrder : GebOrder category) ->
      (projection : Nat) ->
      {auto canPromote : CanPromote category objectOrder morphismOrder} ->
      {auto projectionValid : InBounds projection domains} ->
      GebCategoryMorphism
        (GebProduct domains)
        (index projection domains {ok=projectionValid})
        morphismOrder

    GebCoproductIntro :
      {objectOrder : GebOrder category} ->
      (codomains : List (GebCategoryObject category objectOrder)) ->
      (morphismOrder : GebOrder category) ->
      (injection : Nat) ->
      {auto canPromote : CanPromote category objectOrder morphismOrder} ->
      {auto injectionValid : InBounds injection codomains} ->
      GebCategoryMorphism
        (index injection codomains {ok=injectionValid})
        (GebCoproduct codomains)
        morphismOrder

    GebCoproductElim :
      {codomain : GebCategoryObject category codomainOrder} ->
      (morphisms : List
        (domain : GebCategoryObject category domainOrder **
         GebCategoryMorphism domain codomain morphismOrder)) ->
      GebCategoryMorphism
        (GebCoproduct (map DPair.fst morphisms)) codomain morphismOrder

    GebAlgebraicEval :
      {objectOrder : GebOrder category} ->
      {auto canPromote : CanPromote category objectOrder morphismOrder} ->
      {domain, codomain : GebCategoryObject category objectOrder} ->
      GebCategoryMorphism
        (GebProduct {gebOrder=morphismOrder}
         [GebExponential {canPromote} domain codomain,
          PromoteObject {canPromote} domain])
        codomain morphismOrder

    GebCurry :
      {objectOrder, oldOrder, newOrder : GebOrder category} ->
      {domLeft, domRight, codomain : GebCategoryObject category objectOrder} ->
      GebCategoryMorphism
        (GebProduct [domLeft, domRight]) codomain oldOrder ->
      {auto morphismHigherOrderThanObjects :
        CanPromote category objectOrder oldOrder} ->
      {auto canPromote : CanPromote category oldOrder newOrder} ->
      GebCategoryMorphism domLeft
        (GebExponential {canPromote=morphismHigherOrderThanObjects}
          domRight codomain)
        newOrder

    GebDecideEquality :
      {testQuantity : GebCategoryObject category ZeroOrder} ->
      (leftInput, rightInput : GebCategoryMorphism domain testQuantity
        morphismOrder) ->
      (equalCase : GebCategoryMorphism testQuantity codomain morphismOrder) ->
      (notEqualCase : GebCategoryMorphism
        (GebProduct [testQuantity, testQuantity]) codomain morphismOrder) ->
      GebCategoryMorphism domain codomain morphismOrder

public export
data GebCategoryDependentObject : {reflection : ConcreteReflection} ->
  {category : CategoryGenerator reflection} ->
  (termObject : GebCategoryObject {reflection} category ZeroOrder) ->
  (morphism : GebCategoryMorphism {reflection} {category}
    termObject GebObjectReflection FirstOrder) ->
  Type where

public export
data GebCategoryDependentMorphism : {reflection : ConcreteReflection} ->
  {category : CategoryGenerator reflection} ->
  {domainTermObject, codomainTermObject :
    GebCategoryObject {reflection} category ZeroOrder} ->
  (domainTermMorphism : GebCategoryMorphism {reflection} {category}
    domainTermObject GebObjectReflection FirstOrder) ->
  (codomainTermMorphism : GebCategoryMorphism {reflection} {category}
    codomainTermObject GebObjectReflection FirstOrder) ->
  (termFunctor : GebCategoryMorphism {reflection} {category}
    domainTermObject codomainTermObject FirstOrder) ->
  Type where

-- | Straight from _Representations of First-Order Function Types
-- | as Terminal Coalgebras_.
public export
data BTree : Type where
  BTLeaf : BTree
  BTBranch : BTree -> BTree -> BTree

public export
data BTFun : Type -> Type where
  BTCase : {output : Type} -> (leafCase : output) ->
    (branchCase : Lazy (BTFun (BTFun output))) -> BTFun output

{-
 - Not total.
public export
lamBT : {a : Type} -> (BTree -> a) -> BTFun a
lamBT f = BTCase (f BTLeaf) (lamBT (\t => lamBT (\u => f (BTBranch t u)))
-}

public export
appBT : {output : Type} -> BTFun output -> BTree -> output
appBT (BTCase leafCase _) BTLeaf = leafCase
appBT (BTCase _ f) (BTBranch left right) = appBT (appBT f left) right

-- | Also from the above paper, but for this one they only gave the
-- | math, not the code.  So here's my attempt at the code.  These
-- | strongly resemble S-expressions.
public export
data FTree : Type -> Type where
  FLeaf : {atom : Type} -> atom -> FTree atom
  FBranch : {atom : Type} -> FTree atom -> List (FTree atom) -> FTree atom

mutual
  public export
  data FTFun : Type -> Type -> Type where
    FTCase : {atom, output : Type} -> (leafCase : atom -> output) ->
      (branchCase : Lazy (FTFun atom (LFTFun atom output))) -> FTFun atom output

  public export
  data LFTFun : Type -> Type -> Type where
    LFTCase : {atom, output : Type} -> (nilCase : output) ->
      (consCase : Lazy (FTFun atom (LFTFun atom output))) -> LFTFun atom output

mutual
  public export
  appFT : {atom, output : Type} -> FTFun atom output -> FTree atom -> output
  appFT (FTCase leafCase _) (FLeaf a) = leafCase a
  appFT (FTCase _ f) (FBranch tree list) = appLFT (appFT f tree) list

  public export
  appLFT : {atom, output : Type} -> LFTFun atom output -> List (FTree atom) ->
    output
  appLFT (LFTCase nilCase _) [] = nilCase
  appLFT (LFTCase _ f) (tree :: list) = appLFT (appFT f tree) list

-- | My modifications:
-- | Done below:
-- |   - Add atoms
-- |   - Convert to S-expressions (my atom + list representation)
-- | Still to do:
-- |   - Index them by S-expressions and then write them in S-expressions
-- |     themselves so that I can use "App" and make them manifestly finitary
-- |   - Try to uncurry the type and function
-- |   - Try to make them dependent
-- |     - If that works, add the restriction to refined well-founded
-- |       S-expressions, with the dependent types available to validate
-- |     - If it fails, do refinement to well-founded trees with finite
-- |       pattern matches first, and find out whether that makes
-- |       type dependency easier
-- |   - Interpret them in Idris:
-- |     - Refined S-expressions with big-step evaluation
-- |     - Small-step evaluation for well-typed Turing machines using the
-- |       coinductive version
-- |   - Write them in themselves
-- |   - Use that reflection together with the duality to implement
-- |     algebraic effects (perhaps using models and comodels)

mutual
  public export
  data GExp : Type -> Type where
    GXIntro : {atom : Type} -> atom -> GList atom -> GExp atom

  public export
  data GList : Type -> Type where
    GNil : {atom : Type} -> GList atom
    GCons : {atom : Type} -> GExp atom -> GList atom -> GList atom

mutual
  public export
  data GXFun : (atom, output : Type) -> Type where
    GXCase : {atom, output : Type} ->
      (expCase : atom -> Lazy (GXFun atom (GLFun atom output))) ->
      GXFun atom output

  public export
  data GLFun : (atom, output : Type) -> Type where
    GLCase : {atom, output : Type} -> (nilCase : output) ->
      (consCase : Lazy (GLFun atom (GXFun atom output))) -> GLFun atom output

mutual
  public export
  appGX : {atom, output : Type} -> GXFun atom output -> GExp atom -> output
  appGX (GXCase f) (GXIntro a list) = appGL (appGX (f a) (GXIntro a list)) list

  public export
  appGL : {atom, output : Type} -> GLFun atom output -> GList atom -> output
  appGL (GLCase nilCase _) GNil = nilCase
  appGL (GLCase _ f) (GCons exp list) = appGX (appGL f list) exp

mutual
  public export
  data ZerothOrderType : Type where
    ZerothInitial : ZerothOrderType
    ZerothTerminal : ZerothOrderType
    ZerothProduct : ZerothOrderType -> ZerothOrderType -> ZerothOrderType
    ZerothCoproduct : ZerothOrderType -> ZerothOrderType -> ZerothOrderType

mutual
  public export
  data ZerothOrderTerm : Type where
    ZerothUnit : ZerothOrderTerm
    ZerothPair : ZerothOrderTerm -> ZerothOrderTerm -> ZerothOrderTerm
    ZerothLeft : ZerothOrderTerm -> ZerothOrderTerm
    ZerothRight : ZerothOrderTerm -> ZerothOrderTerm

mutual
  public export
  data MatchesType : ZerothOrderType -> ZerothOrderTerm -> Type where
    MatchesUnit : MatchesType ZerothTerminal ZerothUnit

    MatchesPair : (firstTerm, secondTerm : ZerothOrderTerm) ->
      {firstType, secondType : ZerothOrderType} ->
      {auto firstMatch : MatchesType firstType firstTerm} ->
      {auto secondMatch : MatchesType secondType secondTerm} ->
      MatchesType
        (ZerothProduct firstType secondType) (ZerothPair firstTerm secondTerm)

    MatchesLeft : (term : ZerothOrderTerm) ->
      {leftType, rightType : ZerothOrderType} ->
      {auto leftMatch : MatchesType leftType term} ->
      MatchesType (ZerothCoproduct leftType rightType) (ZerothLeft term)

    MatchesRight : (term : ZerothOrderTerm) ->
      {leftType, rightType : ZerothOrderType} ->
      {auto rightMatch : MatchesType rightType term} ->
      MatchesType (ZerothCoproduct leftType rightType) (ZerothRight term)

----------------------------------------------------------------
---- General definition of programming language / metalogic ----
----------------------------------------------------------------

public export
gebIndexList : Nat -> GebSList
gebIndexList 0 = $*^ GAIndexFirst
gebIndexList (S n) = GAIndexNext $^: gebIndexList n

public export
checkIndexListCertified : (indexList : GebSList) ->
  Maybe (n : Nat ** gebIndexList n = indexList)
checkIndexListCertified [GAIndexFirst $* []] = Just (0 ** Refl)
checkIndexListCertified ((GAIndexNext $* []) :: tail) with
  (checkIndexListCertified tail)
    checkIndexListCertified ((GAIndexNext $* []) :: tail) |
      Just (n ** consistent) =
        case consistent of Refl => Just (S n ** Refl)
    checkIndexListCertified ((GAIndexNext $* []) :: tail) | Nothing = Nothing
checkIndexListCertified _ = Nothing

public export
checkIndexList : (indexList : GebSList) -> Maybe Nat
checkIndexList indexList with (checkIndexListCertified indexList)
  checkIndexList indexList | Just (n ** _) = Just n
  checkIndexList indexList | _ = Nothing

public export
checkIndexListConsistent : {indexList : GebSList} ->
  (consistentIndex : IsJust (checkIndexList indexList)) ->
  gebIndexList (IsJustElim consistentIndex) = indexList
checkIndexListConsistent just with (checkIndexListCertified indexList) proof p
  checkIndexListConsistent ItIsJust | Just (n ** consistentIndex) =
    consistentIndex
  checkIndexListConsistent ItIsJust | Nothing impossible

mutual
  public export
  data GebPOrder : GebSExp -> Type where
    FinitePOrder : (n : Nat) ->
      GebPOrder $ GAFiniteOrder $* (gebIndexList n)
    TuringCompleteP : GebPOrder $ $^ GATuringComplete

  public export
  data GebPType : {order : GebSExp} -> (checkedOrder : GebPOrder order) ->
    (type : GebSExp) -> Type where
      PromoteFiniteP : {order : GebSExp} -> {n : Nat} -> {type : GebSExp} ->
        GebPType (FinitePOrder n) type ->
        GebPType (FinitePOrder (S n)) $ (GAPromoteFinite $*** type)
      PromoteTuringCompleteP : {order : GebSExp} -> {n : Nat} ->
        {type : GebSExp} -> GebPType (FinitePOrder n) type ->
        GebPType TuringCompleteP $ (GAPromoteTuringComplete $*** type)
      PatternType : {matrix : GebSExp} -> {order : GebSExp} ->
        {checkedOrder : GebPOrder order} ->
        GebPTypeMatrix checkedOrder matrix ->
        GebPType checkedOrder $ GAPatternType $*** matrix

  public export
  data GebPTypeList : {order : GebSExp} -> (checkedOrder : GebPOrder order) ->
    (types : GebSExp) -> Type where
      EmptyTypeList : {order : GebSExp} -> (checkedOrder : GebPOrder order) ->
        GebPTypeList checkedOrder ($^ GATypeList)
      ConsTypeList : {type : GebSExp} -> {types : GebSList} ->
        {order : GebSExp} -> {checkedOrder : GebPOrder order} ->
        GebPType checkedOrder type ->
        GebPTypeList checkedOrder (GATypeList $* types) ->
        GebPTypeList checkedOrder $ GATypeList $* (type :: types)

  public export
  data GebPTypeMatrix : {order : GebSExp} -> (checkedOrder : GebPOrder order) ->
    (matrix : GebSExp) -> Type where
      EmptyTypeMatrix : GebPTypeMatrix checkedOrder ($^ GATypeMatrix)
      ConsTypeMatrix : {row : GebSExp} -> {matrix : GebSList} ->
        {order : GebSExp} -> {checkedOrder : GebPOrder order} ->
        GebPTypeList checkedOrder row ->
        GebPTypeMatrix checkedOrder (GATypeMatrix $* matrix) ->
        GebPTypeMatrix checkedOrder $ GATypeMatrix $* (row :: matrix)

  public export
  data GebMatrixIndex : {matrix : GebSExp} -> {order : GebSExp} ->
    {checkedOrder : GebPOrder order} ->
    GebPTypeMatrix checkedOrder matrix -> GebSExp -> Type where
      MatrixFirst : {row : GebSExp} -> {matrix : GebSList} ->
        {order : GebSExp} -> {checkedOrder : GebPOrder order} ->
        {checkedMatrix : GebPTypeMatrix checkedOrder $
          GATypeMatrix $* (row :: matrix)} ->
        GebMatrixIndex checkedMatrix (GAMatrixIndex $**^ GAIndexFirst)
      MatrixNext : {row : GebSExp} -> {matrix : GebSList} ->
        {order : GebSExp} -> {checkedOrder : GebPOrder order} ->
        {checkedTypeList : GebPTypeList checkedOrder row} ->
        {checkedMatrix :
          GebPTypeMatrix checkedOrder $ GATypeMatrix $* matrix} ->
        {indexList : GebSList} ->
        GebMatrixIndex checkedMatrix (GAMatrixIndex $* indexList) ->
        GebMatrixIndex (ConsTypeMatrix checkedTypeList checkedMatrix)
          (GAMatrixIndex $* $^ GAIndexNext :: indexList)

  public export
  matrixIndexTypeListExp : {matrix : GebSExp} ->
    {order : GebSExp} -> {checkedOrder : GebPOrder order} ->
    (checkedMatrix : GebPTypeMatrix checkedOrder matrix) -> {index : GebSExp} ->
    GebMatrixIndex checkedMatrix index ->
    GebSExp
  matrixIndexTypeListExp (ConsTypeMatrix {row} _ _) MatrixFirst = row
  matrixIndexTypeListExp (ConsTypeMatrix _ tail) (MatrixNext index) =
    matrixIndexTypeListExp tail index

  public export
  matrixIndexTypeList : {matrix : GebSExp} ->
    {order : GebSExp} -> {checkedOrder : GebPOrder order} ->
    (checkedMatrix : GebPTypeMatrix checkedOrder matrix) -> {index : GebSExp} ->
    (checkedIndex : GebMatrixIndex checkedMatrix index) ->
    GebPTypeList
      checkedOrder (matrixIndexTypeListExp checkedMatrix checkedIndex)
  matrixIndexTypeList (ConsTypeMatrix head _) MatrixFirst = head
  matrixIndexTypeList (ConsTypeMatrix _ tail) (MatrixNext index) =
    matrixIndexTypeList tail index

  public export
  data GebPTerm : {type : GebSExp} -> {order : GebSExp} ->
    {checkedOrder : GebPOrder order} ->
    GebPType checkedOrder type -> (term : GebSExp) -> Type where
      Inject : {order : GebSExp} -> {checkedOrder : GebPOrder order} ->
        {matrix : GebSExp} ->
        (checkedMatrix : GebPTypeMatrix checkedOrder matrix) ->
        {index : GebSExp} ->
        (checkedIndex : GebMatrixIndex checkedMatrix index) ->
        {terms : GebSExp} ->
        GebPTermList (matrixIndexTypeList checkedMatrix checkedIndex) terms ->
        GebPTerm (PatternType checkedMatrix) $ GAInjectTerm $* [index, terms]

  public export
  data GebPTermList : {order : GebSExp} -> {checkedOrder : GebPOrder order} ->
    {types : GebSExp} ->
    GebPTypeList checkedOrder types -> (terms : GebSExp) -> Type where
      EmptyTermList : {order : GebSExp} -> (checkedOrder : GebPOrder order) ->
        GebPTermList (EmptyTypeList checkedOrder) ($^ GATermList)
      ConsTermList : {order : GebSExp} -> {checkedOrder : GebPOrder order} ->
        {type : GebSExp} -> {checkedType : GebPType checkedOrder type} ->
        {term : GebSExp} -> GebPTerm checkedType term ->
        {types : GebSList} ->
        {checkedTypes : GebPTypeList checkedOrder (GATypeList $* types)} ->
        {terms : GebSList} ->
        GebPTermList checkedTypes (GATermList $* terms) ->
        GebPTermList (ConsTypeList checkedType checkedTypes) $
          GATermList $* (term :: terms)

mutual
  public export
  checkOrder : (order : GebSExp) -> Maybe (GebPOrder order)
  checkOrder (GAFiniteOrder $* indexList) with
    (checkIndexListCertified indexList)
      checkOrder (GAFiniteOrder $* indexList) | Just (n ** consistentIndex) =
        case consistentIndex of Refl => Just $ FinitePOrder n
      checkOrder (GAFiniteOrder $* indexList) | Nothing = Nothing
  checkOrder (GATuringComplete $* []) = Just TuringCompleteP
  checkOrder _ = Nothing

  public export
  checkType : {order : GebSExp} -> (checkedOrder : GebPOrder order) ->
    (type : GebSExp) -> Maybe (GebPType checkedOrder type)
  checkType checkedOrder (GAPatternType $* [GATypeMatrix $* matrix]) with
    (checkTypeMatrix checkedOrder matrix)
      checkType checkedOrder (GAPatternType $* [GATypeMatrix $* matrix]) |
        Just checkedMatrix = Just $ PatternType checkedMatrix
      checkType checkedOrder (GAPatternType $* [GATypeMatrix $* matrix]) | _ =
        Nothing
  checkType _  _= Nothing

  public export
  checkTypeList : {order : GebSExp} -> (checkedOrder : GebPOrder order) ->
    (types : GebSList) ->
    Maybe (GebPTypeList checkedOrder $ GATypeList $* types)
  checkTypeList checkedOrder [] = Just (EmptyTypeList checkedOrder)
  checkTypeList checkedOrder (type :: types) =
    case (checkType checkedOrder type, checkTypeList checkedOrder types) of
      (Just checkedType, Just checkedTypeList) =>
        Just (ConsTypeList checkedType checkedTypeList)
      _ => Nothing

  public export
  checkTypeMatrix : {order : GebSExp} -> (checkedOrder : GebPOrder order) ->
    (matrix : GebSList) ->
    Maybe $ GebPTypeMatrix checkedOrder (GATypeMatrix $* matrix)
  checkTypeMatrix checkedOrder [] = Just $ EmptyTypeMatrix {checkedOrder}
  checkTypeMatrix checkedOrder ((GATypeList $* row) :: matrix) =
    case (checkTypeList checkedOrder row,
      checkTypeMatrix checkedOrder matrix) of
        (Just checkedRow, Just checkedMatrix) =>
          Just $ ConsTypeMatrix checkedRow checkedMatrix
        _ => Nothing
  checkTypeMatrix _ _ = Nothing

  public export
  checkMatrixIndex : {order : GebSExp} -> {checkedOrder : GebPOrder order} ->
    {matrix : GebSExp} ->
    (checkedMatrix : GebPTypeMatrix checkedOrder matrix) ->
    (index : GebSExp) -> Maybe (GebMatrixIndex checkedMatrix index)
  checkMatrixIndex
    (ConsTypeMatrix _ _) (GAMatrixIndex $* [GAIndexFirst $* []]) =
      Just MatrixFirst
  checkMatrixIndex
    (ConsTypeMatrix _ tail) (GAMatrixIndex $* (GAIndexNext $* []) :: next) =
      case checkMatrixIndex tail (GAMatrixIndex $* next) of
        Just checkedIndex => Just $ MatrixNext checkedIndex
        _ => Nothing
  checkMatrixIndex _ _ = Nothing

  public export
  checkAgainstType : {order : GebSExp} -> {checkedOrder : GebPOrder order} ->
    {type : GebSExp} -> (checkedType : GebPType checkedOrder type) ->
    (term : GebSExp) -> Maybe (GebPTerm checkedType term)
  checkAgainstType
    (PatternType checkedMatrix) (GAInjectTerm $* [index, GATermList $* terms]) =
      case checkMatrixIndex checkedMatrix index of
        Just checkedIndex =>
          case checkAgainstTypeList
            (matrixIndexTypeList checkedMatrix checkedIndex) terms of
              Just checkedTerms =>
                Just $ Inject checkedMatrix checkedIndex checkedTerms
              _ => Nothing
        _ => Nothing
  checkAgainstType _ _ = Nothing

  public export
  checkAgainstTypeList : {order : GebSExp} ->
    {checkedOrder : GebPOrder order} -> {types : GebSExp} ->
    (checkedTypes : GebPTypeList checkedOrder types) -> (terms : GebSList) ->
    Maybe $ GebPTermList checkedTypes $ GATermList $* terms
  checkAgainstTypeList (EmptyTypeList checkedOrder) [] =
    Just $ EmptyTermList checkedOrder
  checkAgainstTypeList (EmptyTypeList _) (_ :: _) = Nothing
  checkAgainstTypeList (ConsTypeList _ _) [] = Nothing
  checkAgainstTypeList (ConsTypeList type types) (term :: terms) =
    case (checkAgainstType type term, checkAgainstTypeList types terms) of
      (Just checkedTerm, Just checkedTerms) =>
        Just $ ConsTermList checkedTerm checkedTerms
      _ => Nothing

public export
checkOrderAndType : (order, type : GebSExp) ->
  Maybe (checkedOrder : GebPOrder order ** GebPType checkedOrder type)
checkOrderAndType order type =
  case checkOrder order of
    Just checkedOrder => case checkType checkedOrder type of
      Just checkedType => Just (checkedOrder ** checkedType)
      _ => Nothing
    _ => Nothing

public export
checkTerm : (order, type, term : GebSExp) ->
  Maybe (checkedOrder : GebPOrder order **
         checkedType : GebPType checkedOrder type **
         GebPTerm checkedType term)
checkTerm order type term = case checkOrderAndType order type of
  Just (checkedOrder ** checkedType) =>
    case checkAgainstType checkedType term of
      Just checkedTerm => Just (checkedOrder ** checkedType ** checkedTerm)
      _ => Nothing
  _ => Nothing

public export
checkTermList : (order : GebSExp) -> (types, terms : GebSList) ->
  Maybe (checkedOrder : GebPOrder order **
         checkedTypeList : GebPTypeList checkedOrder (GATypeList $* types) **
         GebPTermList checkedTypeList $ GATermList $* terms)
checkTermList order types terms =
  case checkOrder order of
    Just checkedOrder => case checkTypeList checkedOrder types of
      Just checkedTypes => case checkAgainstTypeList checkedTypes terms of
        Just checkedTerms => Just (checkedOrder ** checkedTypes ** checkedTerms)
        _ => Nothing
      _ => Nothing
    _ => Nothing

public export
compileOrder : (order : GebSExp) ->
  {auto compiles : IsJust $ checkOrder order} -> GebPOrder order
compileOrder _ {compiles} = IsJustElim compiles

public export
compileType : (order, type : GebSExp) ->
  {auto orderCompiles : IsJust $ checkOrder order} ->
  {auto typeCompiles : IsJust $ checkType (IsJustElim orderCompiles) type} ->
  GebPType (IsJustElim orderCompiles) type
compileType _ _ {orderCompiles} {typeCompiles} = IsJustElim typeCompiles

public export
compileTypeList : (order, types : GebSExp) ->
  {auto isTypeList : ($<) types = GATypeList} ->
  {auto orderCompiles : IsJust $ checkOrder order} ->
  {auto typeListCompiles :
    IsJust $ checkTypeList (IsJustElim orderCompiles) $ ($>) types} ->
  GebPTypeList (IsJustElim orderCompiles) types
compileTypeList {isTypeList=Refl} {orderCompiles} {typeListCompiles}
  _ (_ $* _) = IsJustElim typeListCompiles

public export
compileTypeMatrix : (order, matrix : GebSExp) ->
  {auto isTypeMatrix : ($<) matrix = GATypeMatrix} ->
  {auto orderCompiles : IsJust $ checkOrder order} ->
  {auto compiles :
    IsJust $ checkTypeMatrix (IsJustElim orderCompiles) $ ($>) matrix} ->
  GebPTypeMatrix (IsJustElim orderCompiles) matrix
compileTypeMatrix {isTypeMatrix=Refl} {orderCompiles} {compiles} _ (_ $* _) =
  IsJustElim compiles

public export
compileMatrixIndex : {order, matrix : GebSExp} ->
  {auto orderCompiles : IsJust $ checkOrder order} ->
  (checkedMatrix : GebPTypeMatrix (IsJustElim orderCompiles) matrix) ->
  (index : GebSExp) ->
  {auto compiles : IsJust $ checkMatrixIndex checkedMatrix index} ->
  GebMatrixIndex checkedMatrix index
compileMatrixIndex {orderCompiles} {compiles} _ _ = IsJustElim compiles

public export
gebMatrixIndexExp : Nat -> GebSExp
gebMatrixIndexExp n = GAMatrixIndex $* gebIndexList n

public export
compileTerm : {order, type : GebSExp} ->
  {auto orderCompiles : IsJust $ checkOrder order} ->
  (checkedType : GebPType (IsJustElim orderCompiles) type) ->
  (term : GebSExp) ->
  {auto compiles : IsJust $ checkAgainstType checkedType term} ->
  GebPTerm checkedType term
compileTerm _ _ {orderCompiles} {compiles} = IsJustElim compiles

public export
compileTermList : {order, types : GebSExp} ->
  {auto orderCompiles : IsJust $ checkOrder order} ->
  (checkedTypes : GebPTypeList (IsJustElim orderCompiles) types) ->
  (terms : GebSExp) ->
  {auto isTermList : ($<) terms = GATermList} ->
  {auto compiles : IsJust $ checkAgainstTypeList checkedTypes $ ($>) terms} ->
  GebPTermList checkedTypes terms
compileTermList {isTermList=Refl} {orderCompiles} {compiles} _ (_ $* _) =
  IsJustElim compiles

public export
showType : {order, type : GebSExp} -> {checkedOrder : GebPOrder order} ->
  GebPType checkedOrder type -> String
showType {type} _ = show type

public export
showTypeList : {order, types : GebSExp} -> {checkedOrder : GebPOrder order} ->
  GebPTypeList checkedOrder types -> String
showTypeList {types} _ = show types

public export
showTypeMatrix : {order, matrix : GebSExp} ->
  {checkedOrder : GebPOrder order} ->
  GebPTypeMatrix checkedOrder matrix -> String
showTypeMatrix {matrix} _ = show matrix

public export
showTerm : {order, type : GebSExp} -> {checkedOrder : GebPOrder order} ->
  {checkedType : GebPType checkedOrder type} ->
  {term : GebSExp} -> GebPTerm checkedType term -> String
showTerm {type} {term} _ = "(" ++ show term ++ " :: " ++ show type ++ ")"

public export
showTermList : {order, types, terms : GebSExp} ->
  {checkedOrder : GebPOrder order} ->
  {checkedTypes : GebPTypeList checkedOrder types} ->
  GebPTermList checkedTypes terms -> String
showTermList {types} {terms} _ =
  "((" ++ show terms ++ ") :: (" ++ show types ++ "))"

mutual
  public export
  data GebCategory : GebSExp -> Type where
    MinimalReflective : GebCategory ($^ GAMinimal)

  public export
  data GebObject : (representation : GebSExp) -> {catRep : GebSExp} ->
    GebCategory catRep -> Type where

      AtomObject : {catRep : GebSExp} -> (category : GebCategory catRep) ->
        GebObject (GAAtomObject $*** catRep) category
      SExpObject : {catRep : GebSExp} -> (category : GebCategory catRep) ->
        GebObject (GASExpObject $*** catRep) category
      SListObject : {catRep : GebSExp} -> (category : GebCategory catRep) ->
        GebObject (GASListObject $*** catRep) category

      ObjectReflection : {hostCatRep, targetCatRep : GebSExp} ->
        (hostCat : GebCategory hostCatRep) ->
        (targetCat : GebCategory targetCatRep) ->
        GebObject (GAObjectReflector $* [hostCatRep, targetCatRep]) hostCat
      MorphismReflection : {hostCatRep, targetCatRep : GebSExp} ->
        {hostCat : GebCategory hostCatRep} ->
        {targetCat : GebCategory targetCatRep} ->
        {domainRep, codomainRep : GebSExp} ->
        GebObject domainRep targetCat -> GebObject codomainRep targetCat ->
        GebObject
          (GAMorphismReflector $*
            [hostCatRep, targetCatRep, domainRep, codomainRep]) hostCat

  public export
  data GebMorphism : (representation : GebSExp) -> {catRep : GebSExp} ->
    {domainRep, codomainRep : GebSExp} -> {category : GebCategory catRep} ->
    GebObject domainRep category -> GebObject codomainRep category ->
    Type where
      TypecheckObjectElim : {hostCatRep, targetCatRep : GebSExp} ->
        {hostCat : GebCategory hostCatRep} ->
        {targetCat : GebCategory targetCatRep} ->
        {domainRep, codomainRep, inputRep,
         checkCaseRep, failCaseRep : GebSExp} ->
        {domain : GebObject domainRep hostCat} ->
        {codomain : GebObject codomainRep hostCat} ->
        GebMorphism inputRep domain
          (SExpObject hostCat) ->
        GebMorphism checkCaseRep
          (ObjectReflection hostCat targetCat) codomain ->
        GebMorphism failCaseRep (SExpObject hostCat) codomain ->
        GebMorphism (GATypecheckObjectElim $*
          [hostCatRep, targetCatRep, domainRep, codomainRep,
           inputRep, checkCaseRep, failCaseRep]) domain codomain

mutual
  public export
  data WellTypedExp : GebSExp -> Type where
    IsAtomicRefinement : WellTypedExp (GARefinementSort $* [])

  public export
  data WellTypedList : GebSList -> Type where
    EmptyList : WellTypedList []
    ListCons : {x : GebSExp} -> {l : GebSList} ->
      WellTypedExp x -> WellTypedList l -> WellTypedList (x :: l)

  public export
  data WellTypedFunctionExp : GebSExp -> Type where

  public export
  data GebAtomicContext : GebSExp -> Type where

  public export
  data GebParameterizedContext : GebSExp -> Type where
    GebContextFunction :
      {functionRepresentation : GebSExp} ->
      (gebFunction :
        WellTypedFunctionExp $
          GAMorphismRefinement $*
            [GAExpressionObject $**^ GASExpObject,
             GAExpressionObject $* [GAMaybeFunctor $**^ GASExpObject]]) ->
      GebParameterizedContext $
        GAParameterizedContext $*** functionRepresentation

  public export
  data GebContext : GebSExp -> Type where
    AtomicContext : {x : GebSExp} -> GebAtomicContext x -> GebContext x
    ParameterizedContext : {x : GebSExp} ->
      GebParameterizedContext x -> GebContext x

public export
HandledAtomsList : List GebAtom
HandledAtomsList =
  [
    GARefinementSort
  , GASortSort
  ]

mutual
  -- | These types exist to carry validation of the Geb algorithms, as
  -- | opposed to just the expressions, whose validations are carried
  -- | by the "WellTyped" types above.

  public export
  data TypecheckExpSuccess : GebSExp -> Type where
    CheckedTerm : {a : GebAtom} -> {l : GebSList} ->
      (handled : ListContains HandledAtomsList a) ->
      (listSuccess : TypecheckListSuccess l) ->
      WellTypedExp (a $* l) ->
      TypecheckExpSuccess (a $* l)

  public export
  data TypecheckListSuccess : GebSList -> Type where
    CheckedEmptyList : WellTypedList [] -> TypecheckListSuccess []
    CheckedListCons : TypecheckExpSuccess x -> TypecheckListSuccess l ->
      WellTypedList (x :: l) -> TypecheckListSuccess (x :: l)

public export
successAtomSucceeds : {x : GebSExp} -> TypecheckExpSuccess x ->
  ListContains HandledAtomsList (($<) x)
successAtomSucceeds (CheckedTerm handled _ _) = handled

public export
successListSucceeds : {x : GebSExp} -> TypecheckExpSuccess x ->
  TypecheckListSuccess (($>) x)
successListSucceeds (CheckedTerm _ listSuccess _) = listSuccess

public export
checkedExp : {x : GebSExp} -> TypecheckExpSuccess x -> WellTypedExp x
checkedExp (CheckedTerm _ _ exp) = exp

public export
successHeadSucceeds : {x : GebSExp} -> {l : GebSList} ->
  TypecheckListSuccess (x :: l) ->
  TypecheckExpSuccess x
successHeadSucceeds (CheckedEmptyList _) impossible
successHeadSucceeds (CheckedListCons success _ _) = success

public export
successTailSucceeds : {x : GebSExp} -> {l : GebSList} ->
  TypecheckListSuccess (x :: l) ->
  TypecheckListSuccess l
successTailSucceeds (CheckedEmptyList _) impossible
successTailSucceeds (CheckedListCons _ success _) = success

public export
checkedList : {l : GebSList} ->
  TypecheckListSuccess l -> WellTypedList l
checkedList (CheckedEmptyList _) = EmptyList
checkedList (CheckedListCons _ _ list) = list

public export
GebMonad : Type -> Type
GebMonad = Prelude.Basics.id

public export
GebContextMonad : Type -> Type
GebContextMonad = ReaderT (DPair GebSExp GebContext) GebMonad

public export
CompileResult : GebSExp -> Type
CompileResult x = GebContextMonad $ Dec $ TypecheckExpSuccess x

public export
ListCompileResult : GebSList -> Type
ListCompileResult l = GebContextMonad $ Dec $ TypecheckListSuccess l

public export
AtomHandler : GebAtom -> Type
AtomHandler a =
  (l : GebSList) -> GebContextMonad (TypecheckListSuccess l) ->
  ListContains HandledAtomsList a -> CompileResult (a $* l)

public export
GARefinementSortHandled : ListContains HandledAtomsList GARefinementSort
GARefinementSortHandled = Left Refl

public export
gebRefinementHandler : AtomHandler GARefinementSort
gebRefinementHandler [] _ _ =
  pure $ Yes $ CheckedTerm
    GARefinementSortHandled (CheckedEmptyList EmptyList) IsAtomicRefinement
gebRefinementHandler (_ :: _) _ _ = pure $ No $ \success => case success of
  IsAtomicRefinement (_ $* (_ :: _)) impossible

public export
GASortSortHandled : ListContains HandledAtomsList GARefinementSort
GASortSortHandled = Left Refl

public export
gebSortSortHandler : AtomHandler GASortSort
gebSortSortHandler _ _ _ = pure $ No $ \success =>
  case success of (IsAtomicRefinement _) impossible

public export
AtomHandlerList : ListForAll AtomHandler HandledAtomsList
AtomHandlerList =
  (
    gebRefinementHandler
  , gebSortSortHandler
  , ()
  )

public export
gebHandlesOnlySpecifiedAtoms : (a : GebAtom) -> (l : GebSList) ->
  GebContextMonad (TypecheckExpSuccess (a $* l) -> ListContains HandledAtomsList a)
gebHandlesOnlySpecifiedAtoms a l = pure successAtomSucceeds

public export
gebCompileNotListElim :
  (a : GebAtom) -> (l : GebSList) ->
  GebContextMonad $
    Not (TypecheckListSuccess l) -> Not (TypecheckExpSuccess (a $* l))
gebCompileNotListElim a l = let _ = IdentityIsMonad in do
  pure $ \listFail, expSuccess => listFail $ successListSucceeds expSuccess

public export
gebCompileNilElim : ListCompileResult []
gebCompileNilElim = pure $ Yes (CheckedEmptyList EmptyList)

public export
gebCompileCertifiedConsElim :
  (x : GebSExp) -> (l : GebSList) ->
  GebContextMonad (TypecheckExpSuccess x) ->
  GebContextMonad (TypecheckListSuccess l) ->
  ListCompileResult (x :: l)
gebCompileCertifiedConsElim x l mi mli = let _ = IdentityIsMonad in do
  i <- mi
  li <- mli
  pure $ Yes $ CheckedListCons i li (ListCons (checkedExp i) (checkedList li))

public export
gebCompileNotHeadElim : (x : GebSExp) -> (l : GebSList) ->
  GebContextMonad $
    Not (TypecheckExpSuccess x) -> Not (TypecheckListSuccess (x :: l))
gebCompileNotHeadElim x l =
  pure $ \headFail, listSuccess => headFail $ successHeadSucceeds listSuccess

public export
gebCompileNotTailElim : (x : GebSExp) -> (l : GebSList) ->
  GebContextMonad $
    Not (TypecheckListSuccess l) -> Not (TypecheckListSuccess (x :: l))
gebCompileNotTailElim x l =
  pure $ \tailFail, listSuccess => tailFail $ successTailSucceeds listSuccess

public export
GebCompileSignature :
  SExpRefinePerAtomHandlerSig
    GebContextMonad
    TypecheckExpSuccess
    TypecheckListSuccess
GebCompileSignature =
  SExpRefinePerAtomHandlerArgs
    HandledAtomsList
    AtomHandlerList
    gebHandlesOnlySpecifiedAtoms
    gebCompileNotListElim
    gebCompileNilElim
    gebCompileCertifiedConsElim
    gebCompileNotHeadElim
    gebCompileNotTailElim

public export
gebCompile : GebSExp ~> CompileResult
gebCompile =
  let _ = IdentityIsMonad in sexpRefinePerAtomHandlerReader GebCompileSignature

public export
AnyErased : Type
AnyErased = Exists {type=Type} id

public export
idrisInterpretWellTypedExp : (a : GebAtom) -> (l : GebSList) ->
  (TypecheckListSuccess l -> List AnyErased) ->
  (handled : ListContains HandledAtomsList a) ->
  (listSuccess : TypecheckListSuccess l) ->
  WellTypedExp (a $* l) ->
  AnyErased
idrisInterpretWellTypedExp GARefinementSort [] successToAnyErased _ _
  IsAtomicRefinement =
    Evidence Type (GebSExp -> Bool)

public export
idrisInterpretExpElim : (a : GebAtom) -> (l : GebSList) ->
  (TypecheckListSuccess l -> List AnyErased) ->
  TypecheckExpSuccess (a $* l) ->
  AnyErased
idrisInterpretExpElim a l success
  (CheckedTerm handled listSuccess refinement) =
    idrisInterpretWellTypedExp
      a l success handled listSuccess refinement

public export
idrisInterpretNilElim : TypecheckListSuccess [] -> List AnyErased
idrisInterpretNilElim (CheckedEmptyList _) = []

public export
idrisInterpretConsElim : (x : GebSExp) -> (l : GebSList) ->
  (TypecheckExpSuccess x -> AnyErased) ->
  (TypecheckListSuccess l -> List AnyErased) ->
  TypecheckListSuccess (x :: l) ->
  List AnyErased
idrisInterpretConsElim x l i li (CheckedListCons sx sl _) = i sx :: li sl

public export
idrisInterpretations :
  ((x : GebSExp) -> TypecheckExpSuccess x -> AnyErased,
   (l : GebSList) -> TypecheckListSuccess l -> List AnyErased)
idrisInterpretations =
  sexpEliminators
    {sp=(\x => TypecheckExpSuccess x -> AnyErased)}
    {lp=(\l => TypecheckListSuccess l -> List AnyErased)}
    $ SExpEliminatorArgs
      idrisInterpretExpElim
      idrisInterpretNilElim
      idrisInterpretConsElim

public export
GebSExpTransform : GebSExp -> Type
GebSExpTransform x = WellTypedExp x -> DPair GebSExp WellTypedExp

public export
GebSListTransform : GebSList -> Type
GebSListTransform l = WellTypedList l -> DPair GebSList WellTypedList

public export
record GebTransformSig where
  constructor GebTransformArgs
  transformRefinementSort : DPair GebSExp WellTypedExp
  transformNil : WellTypedList [] -> DPair GebSList WellTypedList
  transformCons : (x : GebSExp) -> (l : GebSList) ->
    WellTypedList (x :: l) -> DPair GebSList WellTypedList

mutual
  public export
  gebSExpTransform : GebTransformSig -> GebSExp ~> GebSExpTransform
  gebSExpTransform signature (GARefinementSort $* []) IsAtomicRefinement =
    transformRefinementSort signature

  public export
  gebSListTransform : GebTransformSig -> GebSList ~> GebSListTransform
  gebSListTransform signature [] EmptyList = transformNil signature EmptyList
  gebSListTransform signature (x :: l) (ListCons typedExp typedList) =
    let transformedExp = gebSExpTransform signature x typedExp in
    let transformedList = gebSListTransform signature l typedList in
    transformCons signature (fst transformedExp) (fst transformedList) $
      ListCons (snd transformedExp) (snd transformedList)

public export
gebTransforms : GebTransformSig ->
  (GebSExp ~> GebSExpTransform, GebSList ~> GebSListTransform)
gebTransforms signature =
  (gebSExpTransform signature, gebSListTransform signature)
-}

{-

----------------------------------------------------------------
---- General definition of programming language / metalogic ----
----------------------------------------------------------------

-- | A "Language" (short in this case for "programming language") is a category
-- | which is capable of performing computation and can be defined solely by
-- | computation.  It can be viewed as having morphisms which represent
-- | computable functions with computably-representable effects.
-- |
-- | By "capable of performing computation", we mean that Gödel's
-- | incompleteness theorems apply to the category.  In other words, it can
-- | express metalogic; we could also say that it can reflect itself, in that
-- | it can define functions on its own expressions.  (So perhaps we might
-- | say something like "computable metacategory" rather than "programming
-- | language".)  A combination of products, coproducts, and decidable
-- | equality gives us the ability to perform substitution, which in turn
-- | allows us to represent function application -- the fundamental
-- | computation in any programming language.
-- |
-- | A language is unsuitable as a metalogic if it is inconsistent -- if its
-- | operational semantics allow non-termination, or if it has any partial
-- | functions.  Of course, one consequence of Gödel's incompleteness theorems
-- | is that we can never be sure that there _are_ any languages that are
-- | suitable as metalogics in that sense!
-- |
-- | So there is a minimal programming language, with this definition:  just
-- | what is required for Gödel's incompleteness theorems to apply.  There is
-- | also a maximal programming language:  the universal Turing machine,
-- | with non-terminating and partial functions.
-- |
-- | Our definitions of languages below all take the form of a
-- | category-theoretical, point-free (termless) definition of syntax and
-- | type system, and an operational definition of semantics using an
-- | interpretation of objects as the types and morphisms as the functions
-- | of a programming language which does have terms.  The functions of the
-- | language are general computable functions with effects, the terms are
-- | S-expressions, and the types are specifications of the domains,
-- | codomains, input-output behavior, and the effects of functions.

mutual
  -- | Takes no parameters.
  public export
  data Language : GebSExp -> GebSList -> Type where
    Minimal : Language ($^ GAMinimal) []
    HigherOrder : Language ($^ GAHigherOrder) []

  public export
  data LanguageHasExponentials : {lang : GebSExp} ->
    Language lang [] -> Type where
      HigherOrderHasExponentials : LanguageHasExponentials HigherOrder

  -- | Takes one parameter, a language.
  public export
  data Object : GebSExp -> GebSList -> Type where
    Initial :
      {lang : GebSExp} -> Language lang [] ->
      Object (GAInitial $*** lang) [lang]
    Terminal :
      {lang : GebSExp} -> Language lang [] ->
      Object (GATerminal $*** lang) [lang]
    Product :
      {lang, left, right : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      Object left [lang] -> Object right [lang] ->
      Object (GAProduct $* [left, right]) [lang]
    Coproduct :
      {lang, left, right : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      Object left [lang] -> Object right [lang] ->
      Object (GACoproduct $* [left, right]) [lang]
    Exponential : {lang, left, right : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      {auto hasExponentials : LanguageHasExponentials isLanguage} ->
      Object left [lang] -> Object right [lang] ->
      Object (GAExponential $* [left, right]) [lang]

    RefinementObject : {lang, refined, pass, fail, test : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      {refinedObject : Object refined [lang]} ->
      {passObject : Object pass [lang]} ->
      {failObject : Object fail [lang]} ->
      (testMorphism :
        Morphism test [lang, refined, GACoproduct $* [pass, fail]]) ->
      Object (GARefinementObject $* [refined, pass, fail, test]) [lang]

    -- | Reflects expressions of each refinement into each language.
    -- | (In particular, this might reflect into language X an expression
    -- | of language Y, or an expression of Geb itself.)
    ExpressionObject : {lang, sort, refinement : GebSExp} ->
      Language lang [] -> Sort sort [] -> Refinement refinement [sort] ->
      Object (GAExpressionObject $* [lang, refinement]) [lang]

  -- | Takes an "implicit" language parameter and two explicit
  -- | object parameters, which must have the same language.
  public export
  data Morphism : GebSExp -> GebSList -> Type where
    Identity : {lang, obj : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      Object obj [lang] -> Morphism (GAIdentity $*** obj) [lang, obj, obj]
    Compose : {lang, a, b, c, g, f : GebSExp} ->
      {auto isLanguage : Language lang []} -> {objA : Object a [lang]} ->
      {objB : Object b [lang]} -> {objC : Object c [lang]} ->
      Morphism g [lang, b, c] -> Morphism f [lang, a, b] ->
      Morphism (GACompose $* [g, f]) [lang, a, c]
    FromInitial : {lang, obj : GebSExp} ->
      {auto isLanguage : Language lang []} -> Object obj [lang] ->
      Morphism (GAFromInitial $*** obj) [lang, GAInitial $*** lang, obj]
    ToTerminal : {lang, obj : GebSExp} ->
      {auto isLanguage : Language lang []} -> Object obj [lang] ->
      Morphism (GAToTerminal $*** obj) [lang, obj, GATerminal $*** lang]
    ProductIntro : {lang, domain, codomainLeft, codomainRight,
        left, right : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      {domainObject : Object domain [lang]} ->
      {codomainLeftObject : Object codomainLeft [lang]} ->
      {codomainRightObject : Object codomainRight [lang]} ->
      Morphism left [lang, domain, codomainLeft] ->
      Morphism right [lang, domain, codomainRight] ->
      Morphism (GAProductIntro $* [left, right])
        [lang, domain, GAProduct $* [codomainLeft, codomainRight]]
    ProductElimLeft : {lang, left, right : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      Object left [lang] -> Object right [lang] ->
      Morphism (GAProductElimLeft $* [left, right])
        [lang, GAProduct $* [left, right], left]
    ProductElimRight : {lang, left, right : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      Object left [lang] -> Object right [lang] ->
      Morphism (GAProductElimRight $* [left, right])
        [lang, GAProduct $* [left, right], right]
    CoproductIntroLeft : {lang, left, right : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      Object left [lang] -> Object right [lang] ->
      Morphism (GACoproductIntroLeft $* [left, right])
        [lang, left, GACoproduct $* [left, right]]
    CoproductIntroRight : {lang, left, right : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      Object left [lang] -> Object right [lang] ->
      Morphism (GACoproductIntroRight $* [left, right])
        [lang, right, GACoproduct $* [left, right]]
    CoproductElim : {lang, domainLeft, domainRight, codomain,
        left, right : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      {domainLeftObject : Object domainLeft [lang]} ->
      {domainRightObject : Object domainRight [lang]} ->
      {codomainObject : Object codomain [lang]} ->
      Morphism left [lang, domainLeft, codomain] ->
      Morphism right [lang, domainRight, codomain] ->
      Morphism (GACoproductElim $* [left, right])
        [lang, GACoproduct $* [domainLeft, domainRight], codomain]
    ExponentialEval : {lang, domain, codomain : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      {hasExponentials : LanguageHasExponentials isLanguage} ->
      Object domain [lang] -> Object codomain [lang] ->
      Morphism (GAExponentialEval $* [domain, codomain])
        [lang,
         GAProduct $* [GAExponential $* [domain, codomain], domain], codomain]
    Curry : {lang, domainLeft, domainRight, codomain, morphism : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      {hasExponentials : LanguageHasExponentials isLanguage} ->
      {domainLeftObject : Object domainLeft [lang]} ->
      {domainRightObject : Object domainRight [lang]} ->
      {codomainObject : Object codomain [lang]} ->
      Morphism morphism
        [lang, GAProduct $* [domainLeft, domainRight], codomain] ->
      Morphism (GACurry $*** morphism)
        [lang, domainLeft, GAExponential $* [domainRight, codomain]]

  -- | Takes no parameters.
  -- | These are "refinement families" (by analogy to "type families").
  public export
  data Sort : GebSExp -> GebSList -> Type where
    SortSort : Sort ($^ GASortSort) []
    RefinementSort : Sort ($^ GARefinementSort) []
    ExpressionSort : Sort ($^ GAExpressionSort) []
    LanguageSort : Sort ($^ GALanguageSort) []
    ObjectSort : Sort ($^ GAObjectSort) []
    MorphismSort : Sort ($^ GAMorphismSort) []

  -- | Takes one parameter, a sort.  Refinements are analogous to types --
  -- | a refinement may be viewed as the type of S-expressions which
  -- | are selected by it (the refinement in this view is a characteristic
  -- | function on S-expressions).
  public export
  data Refinement : GebSExp -> GebSList -> Type where
    SortRefinement : Refinement ($^ GASortRefinement) [$^ GASortSort]
    RefinementRefinement : {s : GebSExp} -> Sort s [] ->
      Refinement (GARefinementRefinement $*** s) [$^ GARefinementSort]
    ExpressionRefinement : {s, r : GebSExp} ->
      Refinement r [s] ->
      Refinement (GAExpressionRefinement $* [s, r]) [$^ GAExpressionSort]
    LanguageRefinement :
      Refinement ($^ GALanguageRefinement) [$^ GALanguageSort]
    ObjectRefinement : {lang : GebSExp} ->
      Language lang [] ->
      Refinement (GAObjectRefinement $*** lang) [$^ GAObjectSort]
    MorphismRefinement : {lang, domain, codomain : GebSExp} ->
      Object domain [lang] -> Object codomain [lang] ->
      Refinement
        (GAMorphismRefinement $* [lang, domain, codomain]) [$^ GAMorphismSort]

  -- | Takes two parameters, an "implicit" sort and a refinement of
  -- | that sort.  An expression consists of refinement _constructors_;
  -- | it may be viewed as an S-expression which is selected by its
  -- | refinement parameter.
  public export
  data Expression : GebSExp -> GebSList -> Type where
    SortExpression : {s : GebSExp} -> Sort s [] ->
      Expression (GASortExpression $*** s) [$^ GASortSort, $^ GASortRefinement]
    RefinementExpression : {s, r : GebSExp} ->
      Refinement r [GARefinementRefinement $*** s] ->
      Expression (GARefinementExpression $*** r)
        [$^ GARefinementSort, GARefinementRefinement $*** s]
    LanguageExpression : {lang : GebSExp} ->
      Language lang [] ->
      Expression (GALanguageExpression $*** lang)
        [$^ GALanguageSort, $^ GALanguageRefinement]
    ObjectExpression : {lang, object : GebSExp} ->
      Object object [lang] ->
      Expression (GAObjectExpression $*** object)
        [$^ GAObjectSort, GAObjectRefinement $*** lang]
    MorphismExpression : {lang, domain, codomain, morphism : GebSExp} ->
      Morphism morphism [lang, domain, codomain] ->
      Expression (GAMorphismExpression $*** morphism)
        [$^ GAMorphismSort, GAMorphismRefinement $* [lang, domain, codomain]]

-----------------------------------------------------
---- Type-checking in Idris-2 of Geb expressions ----
-----------------------------------------------------

mutual
  public export
  objectUnique : {lang, object : GebSExp} ->
    (obj, obj' : Object object [lang]) ->
    obj = obj'
  objectUnique obj obj' = objectUnique_hole

  public export
  checkExpression : (expression : GebSExp) -> (refinement : GebSList) ->
    Dec $ Expression expression refinement
  checkExpression x r = checkExpression_hole

  public export
  checkExpressionCorrect : {x : GebSExp} -> {l : GebSList} ->
    (exp : Expression x l) -> checkExpression x l = Yes exp
  checkExpressionCorrect {x} {l} exp = checkExpressionCorrect_hole

  public export
  expressionUnique : {x : GebSExp} -> {l : GebSList} ->
    (exp, exp' : Expression x l) -> exp = exp'
  expressionUnique {x} {l} exp exp' = expressionUnique_hole

--------------------------------------------------------
---- Interpretation into Idris-2 of Geb expressions ----
--------------------------------------------------------

mutual
  public export
  interpretObject : {lang, obj : GebSExp} ->
    {isLanguage : Language lang []} -> Object obj [lang] -> Type
  interpretObject (Initial _) = Void
  interpretObject (Terminal _) = ()
  interpretObject (Product left right) =
    (interpretObject {isLanguage} left, interpretObject {isLanguage} right)
  interpretObject (Coproduct left right) =
    Either
      (interpretObject {isLanguage} left)
      (interpretObject {isLanguage} right)
  interpretObject (Exponential domain codomain) =
    interpretObject {isLanguage} domain -> interpretObject {isLanguage} codomain
  interpretObject (RefinementObject
    {refinedObject} {passObject} {failObject} testMorphism) =
      interpretRefinementObject {isLanguage}
        refinedObject passObject failObject testMorphism
  interpretObject (ExpressionObject {sort} {refinement} _ _ _) =
    (x : GebSExp ** Expression x [sort, refinement])

  public export
  interpretRefinementObject : {lang, refined, pass, fail, morphism : GebSExp} ->
    {isLanguage : Language lang []} ->
    Object refined [lang] -> Object pass [lang] -> Object fail [lang] ->
    (testMorphism :
      Morphism morphism [lang, refined, GACoproduct $* [pass,fail]]) -> Type
  interpretRefinementObject {isLanguage}
    refinedObject passObject failObject testMorphism =
      (x : interpretObject {isLanguage} refinedObject **
       IsLeft {a=(interpretObject passObject)} {b=(interpretObject failObject)}
        $ interpretMorphism
            {domainObject=refinedObject}
            {codomainObject=(Coproduct passObject failObject)}
            testMorphism x)

  public export
  interpretMorphism : {lang, domain, codomain, morphism : GebSExp} ->
    {isLanguage : Language lang []} ->
    {domainObject : Object domain [lang]} ->
    {codomainObject : Object codomain [lang]} ->
    (isMorphism : Morphism morphism [lang, domain, codomain]) ->
    interpretObject {isLanguage} domainObject ->
    interpretObject {isLanguage} codomainObject
  interpretMorphism m = interpretMorphism_hole

  public export
  interpretRefinement : {s, r : GebSExp} ->
    Refinement r [s] -> (GebSExp -> Bool)
  interpretRefinement {s} {r} isRefinement x = interpretRefinement_hole

------------------------------------------------------
---- Morphism transformations ("compiler passes") ----
------------------------------------------------------

ObjectMap : {sourceLang, targetLang : GebSExp} ->
  Language sourceLang [] -> Language targetLang [] ->
  Type
ObjectMap {sourceLang} {targetLang} _ _ =
  (sourceObj : GebSExp) -> Object sourceObj [sourceLang] ->
  (targetObj : GebSExp ** Object targetObj [targetLang])

LanguageFunctor : {sourceLang, targetLang : GebSExp} ->
  {sourceIsLanguage : Language sourceLang []} ->
  {targetIsLanguage : Language targetLang []} ->
  (objectMap : ObjectMap sourceIsLanguage targetIsLanguage) ->
  Type
LanguageFunctor {sourceLang} {targetLang} {sourceIsLanguage} {targetIsLanguage}
  objectMap =
    (domain, codomain : GebSExp) ->
    (domainObject : Object domain [sourceLang]) ->
    (codomainObject : Object codomain [sourceLang]) ->
    (morphism : GebSExp) ->
    (isMorphism : Morphism morphism [sourceLang, domain, codomain]) ->
    (transformed : GebSExp **
     Morphism transformed
      [targetLang,
       fst (objectMap domain domainObject),
       fst (objectMap codomain codomainObject)])

-- | A correct compiler pass is a functor whose morphism map
-- | preserves extensional equality.
-- |
-- | It might be a useful generalization for this definition to require only
-- | isomorphism, not equality.

ObjectMapPreservesInterpretation : {sourceLang, targetLang : GebSExp} ->
  {sourceIsLanguage : Language sourceLang []} ->
  {targetIsLanguage : Language targetLang []} ->
  ObjectMap sourceIsLanguage targetIsLanguage ->
  Type
ObjectMapPreservesInterpretation {sourceLang} {targetLang}
  {sourceIsLanguage} {targetIsLanguage} objectMap =
    (object : GebSExp) -> (isObject : Object object [sourceLang]) ->
    interpretObject {isLanguage=sourceIsLanguage} isObject =
      interpretObject {isLanguage=targetIsLanguage}
        (snd (objectMap object isObject))

FunctorPreservesInterpretation : {sourceLang, targetLang : GebSExp} ->
  {sourceIsLanguage : Language sourceLang []} ->
  {targetIsLanguage : Language targetLang []} ->
  (objectMap : ObjectMap sourceIsLanguage targetIsLanguage) ->
  (preservesObjects : ObjectMapPreservesInterpretation
    {sourceIsLanguage} {targetIsLanguage} objectMap) ->
  LanguageFunctor {sourceIsLanguage} {targetIsLanguage} objectMap ->
  Type
FunctorPreservesInterpretation {sourceLang} {targetLang}
  {sourceIsLanguage} {targetIsLanguage} objectMap preservesObjects functor =
    (domain, codomain : GebSExp) ->
    (domainObject : Object domain [sourceLang]) ->
    (codomainObject : Object codomain [sourceLang]) ->
    (morphism : GebSExp) ->
    (isMorphism : Morphism
      morphism [sourceLang, domain, codomain]) ->
    (x : interpretObject {isLanguage=sourceIsLanguage} domainObject) ->
    interpretMorphism {isLanguage=sourceIsLanguage}
     {domainObject} {codomainObject} isMorphism x =
      (rewrite preservesObjects codomain codomainObject in
       (interpretMorphism
        {isLanguage=targetIsLanguage}
        {domainObject=(snd (objectMap domain domainObject))}
        (snd (functor
          domain codomain domainObject codomainObject morphism isMorphism))
        (rewrite sym (preservesObjects domain domainObject) in x)))

------------------------------------------------------
---- Operational semantics through term reduction ----
------------------------------------------------------

-- | Above, we define the semantics of Geb through interpretation into
-- | Idris-2.  Here, we do so through more explicit operational semantics,
-- | with representation of terms.  This allows us to examine interpretation
-- | step-by-step, and also, through small-step semantics, to interpret
-- | non-terminating functions.

public export
data TermSort : {lang : GebSExp} -> Language lang [] -> Type where
  TermSortType :
    {lang, object : GebSExp} -> {auto isLanguage : Language lang []} ->
    (isObject : Object object [lang]) -> TermSort isLanguage
  TermSortFunction :
    {lang, domain, codomain : GebSExp} ->
    {auto isLanguage : Language lang []} ->
    (domainObject : Object domain [lang]) ->
    (codomainObject : Object codomain [lang]) ->
    TermSort isLanguage

public export
data Term : {lang : GebSExp} -> {auto isLanguage : Language lang []} ->
  (numApplications : Nat) -> TermSort isLanguage -> Type where
    UnappliedMorphismTerm :
      {lang, domain, codomain, morphism : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      {domainObject : Object domain [lang]} ->
      {codomainObject : Object codomain [lang]} ->
      (isMorphism : Morphism morphism [lang, domain, codomain]) ->
      Term 0 $ TermSortFunction domainObject codomainObject
    Application :
      {lang, domain, codomain : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      {domainObject : Object domain [lang]} ->
      {codomainObject : Object codomain [lang]} ->
      {morphismApplications, termApplications : Nat} ->
      Term morphismApplications
        (TermSortFunction domainObject codomainObject) ->
      Term termApplications (TermSortType domainObject) ->
      Term
        (S $ morphismApplications + termApplications)
        (TermSortType codomainObject)
    UnitTerm : {lang : GebSExp} -> (isLanguage : Language lang []) ->
      Term 0 $ TermSortType (Terminal isLanguage)

public export
FullyAppliedTerm : {lang : GebSExp} -> {auto isLanguage : Language lang []} ->
  TermSort isLanguage -> Type
FullyAppliedTerm = Term 0

public export
termSortToExp : {lang : GebSExp} -> {auto isLanguage : Language lang []} ->
  TermSort isLanguage -> GebSExp
termSortToExp sort = termSortToExp_hole

public export
termToExp : {lang : GebSExp} -> {auto isLanguage : Language lang []} ->
  {numApplications : Nat} -> {sort : TermSort isLanguage} ->
  Term numApplications sort -> GebSExp
termToExp term = termToExp_hole

public export
(lang : GebSExp) => (isLanguage : Language lang []) =>
  Show (TermSort isLanguage) where
    show = show . termSortToExp

public export
(lang : GebSExp) => (isLanguage : Language lang []) =>
  (s : TermSort isLanguage) => (n : Nat) => Show (Term n s) where
    show = show . termToExp

public export
interpretTermSort :
  {lang : GebSExp} -> {auto isLanguage : Language lang []} ->
  TermSort isLanguage -> Type
interpretTermSort {isLanguage} (TermSortType object) =
  interpretObject {isLanguage} object
interpretTermSort {isLanguage} (TermSortFunction domain codomain) =
  interpretObject {isLanguage} domain -> interpretObject {isLanguage} codomain

public export
interpretTerm :
  {lang : GebSExp} -> {auto isLanguage : Language lang []} ->
  {sort : TermSort isLanguage} -> {numApplications : Nat} ->
  Term numApplications sort ->
  interpretTermSort sort
interpretTerm term = interpretTerm_hole

public export
smallStepMorphismReduction :
  {lang, domain, codomain, morphism : GebSExp} ->
  {auto isLanguage : Language lang []} ->
  {domainObject : Object domain [lang]} ->
  {codomainObject : Object codomain [lang]} ->
  (isMorphism : Morphism morphism [lang, domain, codomain]) ->
  {numApplications : Nat} ->
  Term numApplications (TermSortType domainObject) ->
  (remainingApplications : Nat **
   Term remainingApplications (TermSortType codomainObject))
smallStepMorphismReduction = smallStepMorphismReduction_hole

public export
smallStepTermReduction : {lang : GebSExp} ->
  {auto isLanguage : Language lang []} ->
  {sort : TermSort isLanguage} -> {numApplications : Nat} ->
  Term numApplications sort ->
  (remainingApplications : Nat ** Term remainingApplications sort)
smallStepTermReduction = smallStepTermReduction_hole

public export
data SmallStepTermReductionCompletes :
  {lang : GebSExp} -> {auto isLanguage : Language lang []} ->
  {sort : TermSort isLanguage} -> {numApplications : Nat} ->
  (term : Term numApplications sort) ->
  (reduced : FullyAppliedTerm sort) -> Type
  where
    SmallStepReductionLastStep :
      {lang : GebSExp} -> {auto isLanguage : Language lang []} ->
      {sort : TermSort isLanguage} -> {numApplications : Nat} ->
      {term : Term numApplications sort} ->
      {reduced : FullyAppliedTerm sort} ->
      smallStepTermReduction term = Left reduced ->
      SmallStepTermReductionCompletes term reduced
    SmallStepReductionPreviousStep :
      {lang : GebSExp} -> {auto isLanguage : Language lang []} ->
      {sort : TermSort isLanguage} ->
      {numApplications, intermediateNumApplications : Nat} ->
      {term : Term numApplications sort} ->
      {intermediateTerm : Term intermediateNumApplications sort} ->
      {reduced : FullyAppliedTerm sort} ->
      smallStepTermReduction term = Right intermediateTerm ->
      SmallStepTermReductionCompletes intermediateTerm reduced ->
      SmallStepTermReductionCompletes term reduced

public export
data IsNormalizing : {lang : GebSExp} -> Language lang [] -> Type where
  MinimalIsNormalizing : IsNormalizing Minimal
  HigherOrderIsNormalizing : IsNormalizing HigherOrder

public export
smallStepTermReductionCompletes :
  {lang : GebSExp} -> {auto isLanguage : Language lang []} ->
  {isNormalizing : IsNormalizing isLanguage} ->
  {sort : TermSort isLanguage} -> {numApplications : Nat} ->
  (term : Term numApplications sort) ->
  Subset (FullyAppliedTerm sort) (SmallStepTermReductionCompletes term)
smallStepTermReductionCompletes {sort} {numApplications} term =
  smallStepTermReductionCompletes_hole

public export
smallStepTermReductionCorrect :
  {lang : GebSExp} -> {auto isLanguage : Language lang []} ->
  {isNormalizing : IsNormalizing isLanguage} ->
  {sort : TermSort isLanguage} -> {numApplications : Nat} ->
  (term : Term numApplications sort) ->
  interpretTerm (fst (smallStepTermReductionCompletes {isNormalizing} term)) =
    interpretTerm term
smallStepTermReductionCorrect term = smallStepTermReductionCorrect_hole

-}
