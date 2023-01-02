module QCWF.CWF

import Category.Category
import Category.Universality
import IdrisSTL.Semiring
import Category.Naturality

%default total

-- Following definition 2.2.1 of the category of "Families of Sets"
-- in _Categories With Families: Unityped, Simply Typed, and Dependently
-- Typed_, by Castellan, Clairambault, and Dybjer.

FamiliesOfSetsObject : Type
FamiliesOfSetsObject = (setX : Type ** setX -> Type)

FamiliesOfSetsMorphism : FamiliesOfSetsObject -> FamiliesOfSetsObject -> Type
FamiliesOfSetsMorphism a b =
  (f : (fst a) -> (fst b) ** ((x : fst a) -> snd a x -> snd b (f x)))

FamiliesOfSetsIdentity :
  (obj : FamiliesOfSetsObject) -> FamiliesOfSetsMorphism obj obj
FamiliesOfSetsIdentity a = (\x => x ** \_ => \u => u)

FamiliesOfSetsCompose :
  {a, b, c : FamiliesOfSetsObject} ->
  FamiliesOfSetsMorphism b c ->
  FamiliesOfSetsMorphism a b ->
  FamiliesOfSetsMorphism a c
FamiliesOfSetsCompose {a} {b} {c} (g ** mg) (f ** mf) =
  ((g . f) ** (\x, u => mg (f x) (mf x u)))

FamiliesOfSetsLeftIdentity : {a, b : FamiliesOfSetsObject} ->
  (m : FamiliesOfSetsMorphism a b) ->
  FamiliesOfSetsCompose {a} {b} {c=b} (FamiliesOfSetsIdentity b) m = m
FamiliesOfSetsLeftIdentity (_ ** _) = Refl

FamiliesOfSetsRightIdentity : {a, b : FamiliesOfSetsObject} ->
  (m : FamiliesOfSetsMorphism a b) ->
  FamiliesOfSetsCompose {a} {b=a} {c=b} m (FamiliesOfSetsIdentity a) = m
FamiliesOfSetsRightIdentity (_ ** _) = Refl

FamiliesOfSetsAssociative : {a, b, c, d : FamiliesOfSetsObject} ->
  (w : FamiliesOfSetsMorphism c d) ->
  (v : FamiliesOfSetsMorphism b c) ->
  (u : FamiliesOfSetsMorphism a b) ->
  FamiliesOfSetsCompose {a} {b} {c=d}
    (FamiliesOfSetsCompose {a=b} {b=c} {c=d} w v) u =
  FamiliesOfSetsCompose {a} {b=c} {c=d} w
    (FamiliesOfSetsCompose {a} {b} {c} v u)
FamiliesOfSetsAssociative {a} {b} {c} {d} (h ** mh) (g ** mg) (f ** mf) = Refl

FamiliesOfSetsCategory : Category
FamiliesOfSetsCategory = MkCategory
  FamiliesOfSetsObject
  FamiliesOfSetsMorphism
  FamiliesOfSetsIdentity
  FamiliesOfSetsCompose
  FamiliesOfSetsLeftIdentity
  FamiliesOfSetsRightIdentity
  FamiliesOfSetsAssociative

-- Following Definition 3.1, of "Categories with Families (CwFs)",
-- in _Syntax and Semantics of Quantitative Type Theory_.
record CwF where
  constructor MkCwF
  -- "C is a category..."
  ContextCat : Category
  -- "...with a chosen terminal object T"
  EmptyContext : Object ContextCat
  EmptyContextIsTerminal : Universality.IsTerminal {cat=ContextCat} EmptyContext
  -- "For delta in Ob(C), a collection Ty(delta) of semantic types"
  SemanticType : Object ContextCat -> Type
  -- "For delta in Ob(c) and S in Ty(delta), a collection Tm(delta, S) of
  -- semantic terms"
  SemanticTerm : (object : Object ContextCat) -> SemanticType object -> Type
  -- "For every f : delta -> delta' in C, a function
  -- -{f} : Ty(delta') -> Ty(delta)..."
  MapType : (obj, obj' : Object ContextCat) ->
            Morphism ContextCat obj obj' ->
            SemanticType obj' -> SemanticType obj
  -- "...and for S in Ty(delta') a function
  -- -{f} : Tm(delta', S) -> Tm(delta, S{f})..."
  -- (Implementer's note:  I don't understand why both MapType and MapTerm
  -- (as I'm calling them) are referred to in the paper as "-{f}".  Is that
  -- a typo, or maybe they will just distinguish between MapType and MapTerm by
  -- context)
  MapTerm : (obj, obj' : Object ContextCat) ->
            (f : Morphism ContextCat obj obj') ->
            (S : SemanticType obj') ->
            SemanticTerm obj' S ->
            SemanticTerm obj (MapType obj obj' f S)
  -- "Such that both assignments preserve identity and composition"
  MapTypePreservesIdentity : (obj : Object ContextCat) ->
                             (S : SemanticType obj) ->
                             MapType obj obj (Identity ContextCat obj) S = S
  MapTypePreservesComposition : (a, b, c : Object ContextCat) ->
                                (f : Morphism ContextCat a b) ->
                                (g : Morphism ContextCat b c) ->
                                MapType a c
                                  ((.*) {cat=ContextCat} {a} {b} {c} g f) =
                                (MapType a b f) . (MapType b c g)
  MapTermPreservesIdentity : (obj : Object ContextCat) ->
                             (S : SemanticType obj) ->
                             MapTerm obj obj (Identity ContextCat obj) S = S
  MapTermPreservesComposition : (a, b, c : Object ContextCat) ->
                                (f : Morphism ContextCat a b) ->
                                (g : Morphism ContextCat b c) ->
                                (S : SemanticType c) ->
                                (t : SemanticTerm c S) ->
                                MapTerm a c
                                  ((.*) {cat=ContextCat} {a} {b} {c} g f) S t =
                                MapTerm a b f (MapType b c g S)
                                  (MapTerm b c g S t)
  -- "For each object delta in C and S in Ty(delta) an object delta.S (called
  --  the _comprehension of S_)..."
  Comprehension : (obj : Object ContextCat) ->
    SemanticType obj -> Object ContextCat
  -- "...such that there is a bijection natural in delta':"
  ComprehensionToMorphism :
    (obj : Object ContextCat) -> (S : SemanticType obj) ->
    (obj' : Object ContextCat) ->
    Morphism ContextCat obj' (Comprehension obj S) ->
    Morphism ContextCat obj' obj
  ComprehensionToTerm :
    (obj : Object ContextCat) -> (S : SemanticType obj) ->
    (obj' : Object ContextCat) ->
    (f : Morphism ContextCat obj' (Comprehension obj S)) ->
    SemanticTerm obj'
      (MapType obj' obj (ComprehensionToMorphism obj S obj' f) S)
  TermToComprehension :
    (obj : Object ContextCat) -> (S : SemanticType obj) ->
    (obj' : Object ContextCat) ->
    (m : Morphism ContextCat obj' obj) ->
    SemanticTerm obj' (MapType obj' obj m S) ->
    Morphism ContextCat obj' (Comprehension obj S)
  ComprehensionToTermToComprehension_id :
    (obj : Object ContextCat) -> (S : SemanticType obj) ->
    (obj' : Object ContextCat) ->
    (f : Morphism ContextCat obj' (Comprehension obj S)) ->
    TermToComprehension obj S obj'
      (ComprehensionToMorphism obj S obj' f)
      (ComprehensionToTerm obj S obj' f) =
    f
  TermToComprehensionToTerm_id_morphism :
    (obj : Object ContextCat) -> (S : SemanticType obj) ->
    (obj' : Object ContextCat) ->
    (m : Morphism ContextCat obj' obj) ->
    (term : SemanticTerm obj' (MapType obj' obj m S)) ->
    ComprehensionToMorphism obj S obj' (TermToComprehension obj S obj' m term) =
    m
  TermToComprehensionToTerm_id_term :
    (obj : Object ContextCat) -> (S : SemanticType obj) ->
    (obj' : Object ContextCat) ->
    (m : Morphism ContextCat obj' obj) ->
    (term : SemanticTerm obj' (MapType obj' obj m S)) ->
    ComprehensionToTerm obj S obj' (TermToComprehension obj S obj' m term) =
    replace {p=(\m' => SemanticTerm obj' (MapType obj' obj m' S))}
      (sym (TermToComprehensionToTerm_id_morphism obj S obj' m term)) term
  ComprehensionToMorphismIsNatural :
    (obj : Object ContextCat) -> (S : SemanticType obj) ->
    (obj', obj'' : Object ContextCat) ->
    (observerChange : ObserverChange {cat=ContextCat} obj' obj'') ->
    -- I'm not sure whether it is necessary to impose naturality on the
    -- observer change in order to ensure it on the comprehension-to-morphism
    -- bijection; that's just a guess.  We could find out whether proofs would
    -- go through without it.
    (isNatural : ObserverChangeIsNatural
      {cat=ContextCat} {observerA=obj'} {observerB=obj''} observerChange) ->
    (f : Morphism ContextCat obj' (Comprehension obj S)) ->
    ComprehensionToMorphism obj S obj''
      (observerChange (Comprehension obj S) f) =
    observerChange obj (ComprehensionToMorphism obj S obj' f)
  ComprehensionToTermIsNatural :
    (obj : Object ContextCat) -> (S : SemanticType obj) ->
    (obj', obj'' : Object ContextCat) ->
    (observerChange : ObserverChange {cat=ContextCat} obj' obj'') ->
    -- I'm not sure whether it is necessary to impose naturality on the
    -- observer change in order to ensure it on the comprehension-to-term
    -- bijection; that's just a guess.  We could find out whether proofs would
    -- go through without it.
    (isNatural : ObserverChangeIsNatural
      {cat=ContextCat} {observerA=obj'} {observerB=obj''} observerChange) ->
    (f : Morphism ContextCat obj' (Comprehension obj S)) ->
    ComprehensionToTerm obj S obj''
      (observerChange (Comprehension obj S) f) =
    MapTerm obj'' obj'
      (ObserverChangeInducedMorphism
        {cat=ContextCat} {observerA=obj'} {observerB=obj''} observerChange)
      (MapType obj' obj (ComprehensionToMorphism obj S obj' f) S)
      (ComprehensionToTerm obj S obj' f)

Context : CwF -> Type
Context = Object . ContextCat

Substitution : (cwf : CwF) -> (ctx, ctx' : Context cwf) -> Type
Substitution cwf ctx ctx' = Morphism (ContextCat cwf) ctx ctx'

emptySubstitution : (cwf : CwF) -> (ctx : Context cwf) ->
  Substitution cwf ctx (EmptyContext cwf)
emptySubstitution cwf ctx = TerminalMap (EmptyContextIsTerminal cwf) ctx
