module Category.Category

import public Library.FunctionsAndRelations
import public Library.Decidability
import Library.TypesAndFunctions

%default total

{- Often needed to do category theory in Idris. -}
public export
functionalExtensionality : {a, b : Type} -> FunctionalExtensionality a b
functionalExtensionality = believe_me

public export
record Category where
  constructor MkCategory
  Object : Type
  Morphism : Object -> Object -> Type
  Identity : (a : Object) -> Morphism a a
  After : {a, b, c : Object} -> Morphism b c -> Morphism a b -> Morphism a c
  LeftIdentity : {a, b : Object} -> (m : Morphism a b) ->
    After (Identity b) m = m
  RightIdentity : {a, b : Object} -> (m : Morphism a b) ->
    After m (Identity a) = m
  Associativity : {a, b, c, d : Object} ->
    (h : Morphism c d) -> (g : Morphism b c) -> (f : Morphism a b) ->
    After (After h g) f = After h {a} {b=c} {c=d} (After {a} {b} {c} g f)

public export
catId : {cat : Category} -> (a : Object cat) -> Morphism cat a a
catId {cat} a = Identity cat a

infix 25 .*
public export
(.*) : {cat : Category} -> {a, b, c : Object cat} ->
  Morphism cat b c -> Morphism cat a b -> Morphism cat a c
g .* f = After cat g f

public export
postCompose : {cat : Category} -> {a, b, c : Object cat} ->
  Morphism cat b c -> Morphism cat a b -> Morphism cat a c
postCompose f = (.*) f

public export
preCompose : {cat : Category} -> {a, b, c : Object cat} ->
  Morphism cat a b -> Morphism cat b c -> Morphism cat a c
preCompose f = \h => h .* f

eqapp : {a, b : Type} -> {f, g : a -> b} -> {x : a} -> f = g -> f x = g x
eqapp Refl = Refl

public export
IsTerminal : {cat : Category} -> (a : Object cat) -> Type
IsTerminal {cat} a = (b : Object cat) ->
  (m : Morphism cat b a ** ((m' : Morphism cat b a) -> m' = m))

public export
TerminalObject : Category -> Type
TerminalObject cat = DPair (Object cat) IsTerminal

public export
CompositionIsIdentity : {cat : Category} -> {a, b : Object cat} ->
  (f : Morphism cat b a) -> (g : Morphism cat a b) -> Type
CompositionIsIdentity f g = f .* g = Identity cat a

public export
Inverses : {cat : Category} -> {a, b : Object cat} ->
  (f : Morphism cat a b) -> (g : Morphism cat b a) ->
  Type
Inverses f g = (CompositionIsIdentity f g, CompositionIsIdentity g f)

public export
IsIsomorphism : {cat : Category} -> {a, b: Object cat} ->
  (f : Morphism cat a b) -> Type
IsIsomorphism f = (g : Morphism cat b a ** Inverses f g)

public export
AreIsomorphic : {cat : Category} -> (a, b : Object cat) -> Type
AreIsomorphic {cat} a b = (f : Morphism cat a b ** IsIsomorphism f)

public export
IsUniqueMorphismWithProperty : {cat : Category} -> {a, b : Object cat} ->
  (property : Morphism cat a b -> Type) -> (m : Morphism cat a b) -> Type
IsUniqueMorphismWithProperty property m =
  (property m, (m' : Morphism cat a b) -> property m' -> m' = m)

public export
AreUniquelyIsomorphic : {cat : Category} -> (a, b : Object cat) -> Type
AreUniquelyIsomorphic {cat} a b =
  (iso : AreIsomorphic a b **
   IsUniqueMorphismWithProperty IsIsomorphism (fst iso))

public export
IsUniqueUpToUniqueIsomorphism : {cat : Category} ->
  (property : Object cat -> Type) -> Object cat -> Type
IsUniqueUpToUniqueIsomorphism {cat} property a =
  (property a,
   (b : Object cat) -> property b -> AreUniquelyIsomorphic a b)

public export
ProjectionsFrom : {cat : Category} -> (source, target, target' : Object cat) ->
  Type
ProjectionsFrom {cat} source target target' =
  (Morphism cat source target, Morphism cat source target')

public export
InjectionsTo : {cat : Category} -> (target, source, source' : Object cat) ->
  Type
InjectionsTo {cat} target source source' =
  (Morphism cat source target, Morphism cat source' target)

public export
CandidateProduct : {cat : Category} -> (a, b : Object cat) -> Type
CandidateProduct {cat} a b = (c : Object cat ** ProjectionsFrom c a b)

public export
CandidateCoproduct : {cat : Category} -> (a, b : Object cat) -> Type
CandidateCoproduct {cat} a b = (c : Object cat ** InjectionsTo c a b)

public export
IsProduct : {cat : Category} -> (a, b : Object cat) ->
  CandidateProduct {cat} a b -> Type
IsProduct {cat} a b c =
  (c' : CandidateProduct a b) ->
    (m : Morphism cat (fst c') (fst c) **
     IsUniqueMorphismWithProperty
       (\m' =>
         ((fst (snd c)) .* m = (fst (snd c')),
          (snd (snd c)) .* m = (snd (snd c')))) m)

public export
IsCoproduct : {cat : Category} -> (a, b : Object cat) ->
  CandidateCoproduct {cat} a b -> Type
IsCoproduct {cat} a b c =
  (c' : CandidateCoproduct a b) ->
    (m : Morphism cat (fst c) (fst c') **
     IsUniqueMorphismWithProperty
       (\m' =>
         (m .* (fst (snd c)) = (fst (snd c')),
          m .* (snd (snd c)) = (snd (snd c')))) m)

public export
Product : {cat : Category} -> (a, b : Object cat) -> Type
Product a b = DPair (CandidateProduct a b) (IsProduct a b)

public export
candidateProduct : {cat : Category} -> {a, b : Object cat} ->
  Product {cat} a b -> CandidateProduct {cat} a b
candidateProduct {cat} prod = fst prod

public export
productObject : {cat : Category} -> {a, b : Object cat} ->
  Product {cat} a b -> Object cat
productObject {cat} prod = fst (candidateProduct prod)

public export
productProjections : {cat : Category} -> {a, b : Object cat} ->
  (prod : Product {cat} a b) ->
  ProjectionsFrom {cat} (productObject {cat} {a} {b} prod) a b
productProjections {cat} {a} {b} prod = snd (candidateProduct {a} {b} prod)

public export
productProperty : {cat : Category} -> {a, b : Object cat} ->
  (prod : Product {cat} a b) ->
  IsProduct {cat} a b (candidateProduct {cat} {a} {b} prod)
productProperty {cat} prod = snd prod

public export
Coproduct : {cat : Category} -> (a, b : Object cat) -> Type
Coproduct a b = DPair (CandidateCoproduct a b) (IsCoproduct a b)

public export
candidateCoproduct : {cat : Category} -> {a, b : Object cat} ->
  Coproduct {cat} a b -> CandidateCoproduct {cat} a b
candidateCoproduct {cat} prod = fst prod

public export
coproductObject : {cat : Category} -> {a, b : Object cat} ->
  Coproduct {cat} a b -> Object cat
coproductObject {cat} coprod = fst (candidateCoproduct coprod)

public export
coproductInjections : {cat : Category} -> {a, b : Object cat} ->
  (coprod : Coproduct {cat} a b) ->
  InjectionsTo {cat} (coproductObject {cat} {a} {b} coprod) a b
coproductInjections {cat} {a} {b} coprod =
  snd (candidateCoproduct {a} {b} coprod)

public export
coproductProperty : {cat : Category} -> {a, b : Object cat} ->
  (coprod : Coproduct {cat} a b) ->
  IsCoproduct {cat} a b (candidateCoproduct {cat} {a} {b} coprod)
coproductProperty {cat} coprod = snd coprod

public export
HasAllProducts : Category -> Type
HasAllProducts cat = (a, b : Object cat) -> Product a b

public export
HasAllCoproducts : Category -> Type
HasAllCoproducts cat = (a, b : Object cat) -> Coproduct a b

public export
morphismProduct : {c : Category} ->
  {a, b, b' : Object c} ->
  (prodb : Product {cat=c} b b') ->
  (m : Morphism c a b) -> (m' : Morphism c a b') ->
  Morphism c a (productObject {cat=c} {a=b} {b=b'} prodb)
morphismProduct prodb {a} {b} m m' = fst (productProperty prodb (a ** (m, m')))

parallelMorphismProduct : {c : Category} ->
  {a, a', b, b' : Object c} ->
  (proda : Product {cat=c} a a') ->
  (prodb : Product {cat=c} b b') ->
  (m : Morphism c a b) -> (m' : Morphism c a' b') ->
  Morphism c
    (productObject {cat=c} {a=a} {b=a'} proda)
    (productObject {cat=c} {a=b} {b=b'} prodb)
parallelMorphismProduct {c} proda prodb m m' =
  let
    projFromA = productProjections proda
    leftProj = m .* (fst projFromA)
    rightProj = m' .* (snd projFromA)
  in
  morphismProduct prodb leftProj rightProj

public export
morphismCoproduct : {c : Category} ->
  {a, a', b : Object c} ->
  (coprodb : Coproduct {cat=c} a a') ->
  (m : Morphism c a b) -> (m' : Morphism c a' b) ->
  Morphism c (coproductObject {cat=c} {a=a} {b=a'} coprodb) b
morphismCoproduct coprodb {a} {b} m m' =
  fst (coproductProperty coprodb (b ** (m, m')))

parallelMorphismCoproduct : {c : Category} ->
  {a, a', b, b' : Object c} ->
  (coproda : Coproduct {cat=c} a a') ->
  (coprodb : Coproduct {cat=c} b b') ->
  (m : Morphism c a b) -> (m' : Morphism c a' b') ->
  Morphism c
    (coproductObject {cat=c} {a=a} {b=a'} coproda)
    (coproductObject {cat=c} {a=b} {b=b'} coprodb)
parallelMorphismCoproduct {c} coproda coprodb m m' =
  let
    injToB = coproductInjections coprodb
    leftInj = (fst injToB) .* m
    rightInj = (snd injToB) .* m'
  in
  morphismCoproduct coproda leftInj rightInj

public export
CandidatePullback : {cat : Category} -> {x, y, z : Object cat} ->
  (f : Morphism cat x z) -> (g : Morphism cat y z) ->
  Type
CandidatePullback {cat} {x} {y} {z} f g =
  (obj : Object cat ** proj : ProjectionsFrom obj x y **
   f .* (fst proj) = g .* (snd proj))

public export
IsPullback : {cat : Category} -> {x, y, z : Object cat} ->
  {f : Morphism cat x z} -> {g : Morphism cat y z} ->
  CandidatePullback {cat} {x} {y} {z} f g -> Type
IsPullback {cat} {x} {y} {z} {f} {g} (obj ** (proj ** commutes)) =
  (q : CandidatePullback {cat} {x} {y} {z} f g) ->
    (u : Morphism cat (fst q) obj **
     IsUniqueMorphismWithProperty
       (\u' =>
         ((fst proj) .* u' = fst (fst (snd q)),
          (snd proj) .* u' = snd (fst (snd q)))
       ) u
    )

public export
Pullback : {cat : Category} -> {x, y, z : Object cat} ->
  (f : Morphism cat x z) -> (g : Morphism cat y z) -> Type
Pullback f g = DPair (CandidatePullback f g) IsPullback

public export
TypeCategory : Category
TypeCategory = MkCategory
  Type
  (\a, b => a -> b)
  (\_ => id)
  (\g, f => g . f)
  (\m => functionalExtensionality (\_ => Refl))
  (\m => functionalExtensionality (\_ => Refl))
  (\h, g, f => Refl)

public export
record Functor (C, D : Category) where
  constructor MkFunctor
  mapObj : Object C -> Object D
  mapMorphism : {a, b : Object C} ->
    Morphism C a b -> Morphism D (mapObj a) (mapObj b)
  mapsIdentity : {a : Object C} ->
    mapMorphism {a} {b=a} (Identity C a) = Identity D (mapObj a)
  preservesComposition : {a, b, c : Object C} ->
    (f : Morphism C b c) -> (g : Morphism C a b) ->
    mapMorphism {a=a} {b=c} (After C {a} {b} {c} f g) =
      After D {a=(mapObj a)} {b=(mapObj b)} {c=(mapObj c)}
        (mapMorphism {a=b} {b=c} f) (mapMorphism {a} {b} g)

public export
IdentityFunctor : (C : Category) -> Functor C C
IdentityFunctor _ = MkFunctor
  id
  id
  Refl
  (\_, _ => Refl)

public export
allMorphismProduct : {c : Category} -> (allProducts : HasAllProducts c) ->
  {a, a', b, b' : Object c} ->
  (m : Morphism c a b) -> (m' : Morphism c a' b') ->
  Morphism c
    (productObject {cat=c} {a=a} {b=a'} (allProducts a a'))
    (productObject {cat=c} {a=b} {b=b'} (allProducts b b'))
allMorphismProduct allProducts {c} {a} {a'} {b} {b'} m m' =
  parallelMorphismProduct (allProducts a a') (allProducts b b') m m'

public export
CandidateExponential : {cat : Category} -> HasAllProducts cat ->
  (a, b : Object cat) -> Type
CandidateExponential {cat} allProducts a b =
  (exp : Object cat ** Morphism cat (productObject (allProducts exp a)) b)

public export
candidateExponential : {cat : Category} -> {allProducts : HasAllProducts cat} ->
  {a, b : Object cat} -> CandidateExponential {cat} allProducts a b ->
  Object cat
candidateExponential candidate = fst candidate

public export
evalFunction : {cat : Category} -> {allProducts : HasAllProducts cat} ->
  {a, b : Object cat} ->
  (candidate : CandidateExponential {cat} allProducts a b) ->
  Morphism cat
    (productObject
      {cat}
      {a=(candidateExponential {cat} {a} {b} {allProducts} candidate)}
      {b=a}
      (allProducts (candidateExponential {cat} {a} {b} {allProducts} candidate) a)) b
evalFunction {a} {b} candidate = snd candidate

public export
IsExponential : {cat : Category} -> {allProducts : HasAllProducts cat} ->
  {a, b : Object cat} -> CandidateExponential {cat} allProducts a b -> Type
IsExponential {cat} {allProducts} {a} {b} exp =
  (z : CandidateExponential allProducts a b) ->
    (h :
      Morphism cat
        (candidateExponential {allProducts} z)
        (candidateExponential {allProducts} exp) **
     IsUniqueMorphismWithProperty
       (\h' =>
         evalFunction {allProducts} z =
             (evalFunction {allProducts} exp) .*
             (allMorphismProduct allProducts h' (Identity cat a)))
       h)

public export
Exponential : {cat : Category} -> (allProducts : HasAllProducts cat) ->
  (a, b : Object cat) -> Type
Exponential {cat} allProducts a b =
  DPair
    (CandidateExponential {cat} allProducts a b)
    (IsExponential {allProducts})

public export
HasAllExponentials : Category -> Type
HasAllExponentials cat =
  (allProducts : HasAllProducts cat **
   ((a, b : Object cat) -> Exponential allProducts a b))

public export
IsCartesianClosed : Category -> Type
IsCartesianClosed cat =
  (TerminalObject cat, HasAllProducts cat, HasAllExponentials cat)

public export
record NaturalTransformation {C, D: Category} (F, G : Functor C D) where
  constructor MkNaturalTransformation
  component : (o : Object C) -> Morphism D (mapObj F o) (mapObj G o)
  naturalityCondition : {x, y : Object C} -> (f : Morphism C x y) ->
    After D {a=(mapObj F x)} {b=(mapObj F y)} {c=(mapObj G y)}
      (component y) (mapMorphism {a=x} {b=y} F f) =
    After D {a=(mapObj F x)} {b=(mapObj G x)} {c=(mapObj G y)}
      (mapMorphism {a=x} {b=y} G f) (component x)

public export
SliceCategoryObjects : (C : Category) -> Object C -> Type
SliceCategoryObjects c o = (a : Object c ** Morphism c a o)

public export
SliceCategoryMorphisms : (C : Category) -> (o : Object C) ->
  (domain, codomain : SliceCategoryObjects C o) -> Type
SliceCategoryMorphisms c o (x ** f) (x' ** f') =
  (g : Morphism c x x' ** f' .* g = f)

public export
SliceCategoryIdentity : {C : Category} -> {o : Object C} ->
  (g : SliceCategoryObjects C o) -> SliceCategoryMorphisms C o g g
SliceCategoryIdentity {C=c} {o} (a ** f) =
  (Identity c a ** RightIdentity c f)

public export
SliceCategoryComposition : {C : Category} -> {o : Object C} ->
  {f, g, h : SliceCategoryObjects C o} ->
  SliceCategoryMorphisms C o g h ->
  SliceCategoryMorphisms C o f g ->
  SliceCategoryMorphisms C o f h
SliceCategoryComposition {C=c} {o} {f=(fo ** fm)} {g=(go ** gm)} {h=(ho ** hm)}
  (uo ** um) (vo ** vm) =
    (uo .* vo ** trans (sym (Associativity c hm uo vo)) (case um of Refl => vm))

public export
SliceCategoryLeftIdentity : {c : Category} -> {o : Object c} ->
  {f, g : SliceCategoryObjects c o} ->
  (m : SliceCategoryMorphisms c o f g) ->
  SliceCategoryComposition {C=c} {o} {f} {g} {h=g}
    (SliceCategoryIdentity {C=c} {o} g) m = m
SliceCategoryLeftIdentity {c} {o} {f=(fo ** fm)} {g=(go ** gm)}
  (m ** composes) =
    UniqueHeterogeneousDPairInjective (\_ => uip) (LeftIdentity c m)

public export
SliceCategoryRightIdentity : {c : Category} -> {o : Object c} ->
  {f, g : SliceCategoryObjects c o} ->
  (m : SliceCategoryMorphisms c o f g) ->
  SliceCategoryComposition {C=c} {o} {f} {g=f} {h=g}
    m (SliceCategoryIdentity {C=c} {o} f) = m
SliceCategoryRightIdentity {c} {o} {f=(fo ** fm)} {g=(go ** gm)}
  (m ** composes) =
    UniqueHeterogeneousDPairInjective (\_ => uip) (RightIdentity c m)

public export
SliceCategoryAssociativity : {cat : Category} -> {o : Object cat} ->
  {a, b, c, d : SliceCategoryObjects cat o} ->
  (m : SliceCategoryMorphisms cat o c d) ->
  (m' : SliceCategoryMorphisms cat o b c) ->
  (m'' : SliceCategoryMorphisms cat o a b) ->
  SliceCategoryComposition {C=cat} {o} {f=a} {g=b} {h=d}
    (SliceCategoryComposition {C=cat} {o} {f=b} {g=c} {h=d} m m') m'' =
  SliceCategoryComposition {C=cat} {o} {f=a} {g=c} {h=d} m
    (SliceCategoryComposition {C=cat} {o} {f=a} {g=b} {h=c} m' m'')
SliceCategoryAssociativity {cat} {o}
  {a=(ao ** am)} {b=(bo ** bm)}
  {c=(co ** cm)} {d=(do' ** dm)}
  (m ** composes) (m' ** composes') (m'' ** composes'') =
    UniqueHeterogeneousDPairInjective (\_ => uip)
      (Associativity cat m m' m'')

public export
SliceCategory : (C : Category) -> (o : Object C) -> Category
SliceCategory cat o = MkCategory
  (a : Object cat ** Morphism cat a o)
  (SliceCategoryMorphisms cat o)
  SliceCategoryIdentity
  SliceCategoryComposition
  SliceCategoryLeftIdentity
  SliceCategoryRightIdentity
  (SliceCategoryAssociativity {cat})

public export
IsLocallyCartesianClosed : Category -> Type
IsLocallyCartesianClosed cat =
  (a : Object cat) -> IsCartesianClosed (SliceCategory cat a)

public export
Arrow : {obj: Type} -> (arrow : BinaryPredicate obj) -> Type
Arrow {obj} arrow = DPair (obj, obj) arrow

public export
ArrowTranslation : {object: Type} ->
                   BinaryPredicate object ->
                   ConstructiveRelation (object, object) ->
                   Type
ArrowTranslation = DependentFunctionBetweenRelatedTypes {a=(PairOf object)}

public export
ArrowRelationMap : {object : Type} -> BinaryPredicate object -> Type
ArrowRelationMap = DepRelationMap {a=(PairOf object)}

public export
ArrowMorphism : {object : Type} -> (arrow : BinaryPredicate object) -> Type
ArrowMorphism = DepRelationMorphism {a=(PairOf object)}

public export
IsArrowEquivalence : {object: Type} ->
                     {objEquiv : ConstructiveRelation object} ->
                     {arrow : BinaryPredicate object} ->
                     ArrowRelationMap arrow -> Type
IsArrowEquivalence {objEquiv} map =
  (IsEquivalence objEquiv,
   IsDPairEquivalence map,
   SubRelationEquivalence (SymmetricProduct objEquiv, fst (fst map)))

public export
ArrowEquivalence : {object: Type} ->
                   (objEquiv : ConstructiveRelation object) ->
                   (Arrow: BinaryPredicate object) ->
                           Type
ArrowEquivalence objEquiv arrow =
  DPair (ArrowRelationMap arrow) (IsArrowEquivalence {objEquiv})

public export
record CategoryComponents where
  object : Type
  objEquiv : BinaryPredicate object
  arrow : BinaryPredicate object
  arrowEquiv : BinaryPredicate (DPair (PairOf object) arrow)
  arrowConvert : ArrowTranslation arrow (SymmetricProduct objEquiv)
  id : (a: object) -> arrow (a, a)
  compose : {a, b, c: object} -> (arrow (b, c), arrow (a, b)) -> arrow (a, c)

public export
Algebra : (f : Type -> Type) -> (a : Type) -> Type
Algebra f a = f a -> a
