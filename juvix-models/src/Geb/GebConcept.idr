module Geb.GebConcept

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
import public Geb.GebAtom
import Category.Composition

%default total

--------------------------------------------------------------------------------

mutual
  public export
  data GebConceptRepresentation : Type where
    GebConceptCategoryRepresentation :
      GebCategoryRepresentation ->
      GebConceptRepresentation
    GebConceptObjectRepresentation :
      GebObjectRepresentation ->
      GebCategoryRepresentation ->
      GebConceptRepresentation
    GebConceptMorphismRepresentation :
      GebMorphismRepresentation ->
      GebCategoryRepresentation ->
      GebObjectRepresentation -> GebObjectRepresentation ->
      GebConceptRepresentation
    GebConceptDependentTypeRepresentation :
      GebDependentTypeRepresentation ->
      GebCategoryRepresentation ->
      GebObjectRepresentation ->
      GebMorphismRepresentation ->
      GebConceptRepresentation

  public export
  data GebCategoryRepresentation : Type where
    GebSelfRepresentation : GebCategoryRepresentation

  public export
  data GebObjectRepresentation : Type where
    GebObjectReflectorRepresentation :
      GebCategoryRepresentation -> GebObjectRepresentation

  public export
  data GebMorphismRepresentation : Type where

  public export
  data GebDependentTypeRepresentation : Type where

--------------------------------------------------------------------------------

public export
record GebConceptRepresentationFunctor where
  constructor GebConceptRepresentationMaps
  GebCategoryRepresentationMap :
    GebCategoryRepresentation -> GebCategoryRepresentation
  GebObjectRepresentationMap :
    GebObjectRepresentation -> GebObjectRepresentation
  GebMorphismRepresentationMap :
    GebMorphismRepresentation -> GebMorphismRepresentation
  GebDependentTypeRepresentationMap :
    GebDependentTypeRepresentation -> GebDependentTypeRepresentation

--------------------------------------------------------------------------------

mutual
  public export
  gebConceptRepToSExp : GebConceptRepresentation -> GebSExp
  gebConceptRepToSExp (GebConceptCategoryRepresentation catRep) =
    GAConceptCategory $*** gebCategoryRepToSExp catRep
  gebConceptRepToSExp (GebConceptObjectRepresentation objRep catRep) =
    GAConceptObject $* [gebObjectRepToSExp objRep, gebCategoryRepToSExp catRep]
  gebConceptRepToSExp (GebConceptMorphismRepresentation
    morphismRep catRep domainRep codomainRep) =
      GAConceptMorphism $*
        [gebMorphismRepToSExp morphismRep,
         gebCategoryRepToSExp catRep,
         gebObjectRepToSExp domainRep,
         gebObjectRepToSExp codomainRep]
  gebConceptRepToSExp (GebConceptDependentTypeRepresentation
    dependentTypeRep catRep domainRep morphismRep) =
      GAConceptDependentType $*
        [gebDependentTypeRepToSExp dependentTypeRep,
         gebCategoryRepToSExp catRep,
         gebObjectRepToSExp domainRep,
         gebMorphismRepToSExp morphismRep]

  public export
  gebCategoryRepToSExp : GebCategoryRepresentation -> GebSExp
  gebCategoryRepToSExp GebSelfRepresentation = $^ GAGeb

  public export
  gebObjectRepToSExp : GebObjectRepresentation -> GebSExp
  gebObjectRepToSExp (GebObjectReflectorRepresentation catRep) =
    GAObjectReflector $*** gebCategoryRepToSExp catRep

  public export
  gebMorphismRepToSExp : GebMorphismRepresentation -> GebSExp
  gebMorphismRepToSExp morphismRep impossible

  public export
  gebDependentTypeRepToSExp : GebDependentTypeRepresentation -> GebSExp
  gebDependentTypeRepToSExp depTypeRep impossible

--------------------------------------------------------------------------------

mutual
  public export
  gebSExpToCategoryRepCertified :
    (x : GebSExp) ->
    Dec (rep : GebCategoryRepresentation ** gebCategoryRepToSExp rep = x)
  gebSExpToCategoryRepCertified (a $* l) =
    case decEq a GAGeb of
      Yes Refl => case decEq l [] of
        Yes Refl => Yes $ (GebSelfRepresentation ** Refl)
        No isNotNil => No $ \p => case p of
          (GebSelfRepresentation ** repIsGeb) => case repIsGeb of
            Refl => void $ isNotNil Refl
      No isNotGeb => No $ \p => case p of
        (GebSelfRepresentation ** repIsGeb) => case repIsGeb of
          Refl => void $ isNotGeb Refl

  public export
  gebCategoryRepToSExpToCategoryRepCertified_correct :
    (rep : GebCategoryRepresentation) ->
    gebSExpToCategoryRepCertified (gebCategoryRepToSExp rep) = Yes (rep ** Refl)
  gebCategoryRepToSExpToCategoryRepCertified_correct GebSelfRepresentation =
    rewrite decEqRefl decEq GAGeb in Refl

  public export
  gebSExpToCategoryRep : GebSExp -> Maybe GebCategoryRepresentation
  gebSExpToCategoryRep = decMapToMaybe gebSExpToCategoryRepCertified

  public export
  gebCategoryRepToSExpToCategoryRep_correct :
    (rep : GebCategoryRepresentation) ->
    gebSExpToCategoryRep (gebCategoryRepToSExp rep) = Just rep
  gebCategoryRepToSExpToCategoryRep_correct rep =
    rewrite gebCategoryRepToSExpToCategoryRepCertified_correct rep in
    Refl

  public export
  gebSExpToCategoryRepToSExp_correct :
    (x : GebSExp) -> (rep : GebCategoryRepresentation) ->
    gebSExpToCategoryRep x = Just rep -> gebCategoryRepToSExp rep = x
  gebSExpToCategoryRepToSExp_correct =
    decMapToMaybe_correct gebSExpToCategoryRepCertified

  public export
  gebCategoryRepToSExp_injective : (rep, rep' : GebCategoryRepresentation) ->
    gebCategoryRepToSExp rep = gebCategoryRepToSExp rep' ->
    rep = rep'
  gebCategoryRepToSExp_injective =
    decMapToMaybe_injective
      gebSExpToCategoryRepCertified
      gebCategoryRepToSExpToCategoryRep_correct

--------------------------------------------------------------------------------

  public export
  gebSExpToObjectRepCertified :
    (x : GebSExp) ->
    Dec (rep : GebObjectRepresentation ** gebObjectRepToSExp rep = x)
  gebSExpToObjectRepCertified (a $* l) =
    case decEq a GAObjectReflector of
      Yes Refl => case l of
        [] => No $ \p => case p of
          ((GebConceptCategoryRepresentation _) ** Refl) impossible
        [cat] => case gebSExpToCategoryRepCertified cat of
          Yes (catRep ** Refl) =>
            Yes (GebObjectReflectorRepresentation catRep ** Refl)
          No notCategory => No $ \p => case p of
            ((GebConceptCategoryRepresentation _) ** Refl) impossible
        (_ :: _ :: _) => No $ \p => case p of
          ((GebConceptCategoryRepresentation _) ** Refl) impossible
      No isNotReflective => No $ \p => case p of
        (GebObjectReflectorRepresentation category ** repIsReflective) =>
          case repIsReflective of Refl => void $ isNotReflective Refl

  public export
  gebObjectRepToSExpToObjectRepCertified_correct :
    (rep : GebObjectRepresentation) ->
    gebSExpToObjectRepCertified (gebObjectRepToSExp rep) = Yes (rep ** Refl)
  gebObjectRepToSExpToObjectRepCertified_correct
    (GebObjectReflectorRepresentation catRep) =
      rewrite decEqRefl decEq GAObjectReflector in
      rewrite gebCategoryRepToSExpToCategoryRepCertified_correct catRep in
      Refl

  public export
  gebSExpToObjectRep : GebSExp -> Maybe GebObjectRepresentation
  gebSExpToObjectRep = decMapToMaybe gebSExpToObjectRepCertified

  public export
  gebObjectRepToSExpToObjectRep_correct :
    (rep : GebObjectRepresentation) ->
    gebSExpToObjectRep (gebObjectRepToSExp rep) = Just rep
  gebObjectRepToSExpToObjectRep_correct rep =
    rewrite gebObjectRepToSExpToObjectRepCertified_correct rep in
    Refl

  public export
  gebSExpToObjectRepToSExp_correct :
    (x : GebSExp) -> (rep : GebObjectRepresentation) ->
    gebSExpToObjectRep x = Just rep -> gebObjectRepToSExp rep = x
  gebSExpToObjectRepToSExp_correct =
    decMapToMaybe_correct gebSExpToObjectRepCertified

  public export
  gebObjectRepToSExp_injective : (rep, rep' : GebObjectRepresentation) ->
    gebObjectRepToSExp rep = gebObjectRepToSExp rep' ->
    rep = rep'
  gebObjectRepToSExp_injective =
    decMapToMaybe_injective
      gebSExpToObjectRepCertified
      gebObjectRepToSExpToObjectRep_correct

--------------------------------------------------------------------------------

  public export
  gebSExpToMorphismRepCertified :
    (x : GebSExp) ->
    Dec (rep : GebMorphismRepresentation ** gebMorphismRepToSExp rep = x)
  gebSExpToMorphismRepCertified (a $* l) = No $ \p => case p of
    ((GebConceptMorphismRepresentation _ _ _ _) ** Refl) impossible

  public export
  gebMorphismRepToSExpToMorphismRepCertified_correct :
    (rep : GebMorphismRepresentation) ->
    gebSExpToMorphismRepCertified (gebMorphismRepToSExp rep) = Yes (rep ** Refl)
  gebMorphismRepToSExpToMorphismRepCertified_correct _ impossible

  public export
  gebSExpToMorphismRep : GebSExp -> Maybe GebMorphismRepresentation
  gebSExpToMorphismRep = decMapToMaybe gebSExpToMorphismRepCertified

  public export
  gebMorphismRepToSExpToMorphismRep_correct :
    (rep : GebMorphismRepresentation) ->
    gebSExpToMorphismRep (gebMorphismRepToSExp rep) = Just rep
  gebMorphismRepToSExpToMorphismRep_correct rep =
    rewrite gebMorphismRepToSExpToMorphismRepCertified_correct rep in
    Refl

  public export
  gebSExpToMorphismRepToSExp_correct :
    (x : GebSExp) -> (rep : GebMorphismRepresentation) ->
    gebSExpToMorphismRep x = Just rep -> gebMorphismRepToSExp rep = x
  gebSExpToMorphismRepToSExp_correct =
    decMapToMaybe_correct gebSExpToMorphismRepCertified

  public export
  gebMorphismRepToSExp_injective : (rep, rep' : GebMorphismRepresentation) ->
    gebMorphismRepToSExp rep = gebMorphismRepToSExp rep' ->
    rep = rep'
  gebMorphismRepToSExp_injective =
    decMapToMaybe_injective
      gebSExpToMorphismRepCertified
      gebMorphismRepToSExpToMorphismRep_correct

--------------------------------------------------------------------------------

  public export
  gebSExpToDependentTypeRepCertified :
    (x : GebSExp) ->
    Dec (rep : GebDependentTypeRepresentation **
         gebDependentTypeRepToSExp rep = x)
  gebSExpToDependentTypeRepCertified (a $* l) = No $ \p => case p of
    ((GebConceptDependentTypeRepresentation _ _ _ _) ** Refl) impossible

  public export
  gebDependentTypeRepToSExpToDependentTypeRepCertified_correct :
    (rep : GebDependentTypeRepresentation) ->
    gebSExpToDependentTypeRepCertified (gebDependentTypeRepToSExp rep) =
      Yes (rep ** Refl)
  gebDependentTypeRepToSExpToDependentTypeRepCertified_correct _ impossible

  public export
  gebSExpToDependentTypeRep : GebSExp -> Maybe GebDependentTypeRepresentation
  gebSExpToDependentTypeRep = decMapToMaybe gebSExpToDependentTypeRepCertified

  public export
  gebDependentTypeRepToSExpToDependentTypeRep_correct :
    (rep : GebDependentTypeRepresentation) ->
    gebSExpToDependentTypeRep (gebDependentTypeRepToSExp rep) = Just rep
  gebDependentTypeRepToSExpToDependentTypeRep_correct rep =
    rewrite gebDependentTypeRepToSExpToDependentTypeRepCertified_correct rep in
    Refl

  public export
  gebSExpToDependentTypeRepToSExp_correct :
    (x : GebSExp) -> (rep : GebDependentTypeRepresentation) ->
    gebSExpToDependentTypeRep x = Just rep -> gebDependentTypeRepToSExp rep = x
  gebSExpToDependentTypeRepToSExp_correct =
    decMapToMaybe_correct gebSExpToDependentTypeRepCertified

  public export
  gebDependentTypeRepToSExp_injective :
    (rep, rep' : GebDependentTypeRepresentation) ->
    gebDependentTypeRepToSExp rep = gebDependentTypeRepToSExp rep' ->
    rep = rep'
  gebDependentTypeRepToSExp_injective =
    decMapToMaybe_injective
      gebSExpToDependentTypeRepCertified
      gebDependentTypeRepToSExpToDependentTypeRep_correct

--------------------------------------------------------------------------------

  public export
  gebSExpToConceptRepCertified :
    (x : GebSExp) ->
    Dec (rep : GebConceptRepresentation ** gebConceptRepToSExp rep = x)
  gebSExpToConceptRepCertified (a $* l) =
    case decEq a GAConceptCategory of
      Yes Refl => case l of
        [] => No $ \p => case p of
          ((GebConceptCategoryRepresentation _) ** Refl) impossible
        [category] => case gebSExpToCategoryRepCertified category of
          Yes (catRep ** Refl) =>
            Yes (GebConceptCategoryRepresentation catRep ** Refl)
          No notCategory => No $ \p => case p of
            ((GebConceptCategoryRepresentation catRep) ** correct) =>
              void $ notCategory (catRep **
                rewrite (fst (consInjective (sexpInjectiveList correct))) in
                Refl)
        (_ :: _ :: _) => No $ \p => case p of
          ((GebConceptCategoryRepresentation _) ** Refl) impossible
      No notCategory => case decEq a GAConceptObject of
        Yes Refl => case l of
          [] => No $ \p => case p of
            ((GebConceptCategoryRepresentation _) ** Refl) impossible
          ([_]) => No $ \p => case p of
            ((GebConceptCategoryRepresentation _) ** Refl) impossible
          (object :: category :: []) =>
            case gebSExpToObjectRepCertified object of
              Yes (objRep ** Refl) =>
                case gebSExpToCategoryRepCertified category of
                  Yes (catRep ** Refl) =>
                    Yes (GebConceptObjectRepresentation objRep catRep ** Refl)
                  No notCategory => No $ \p => case p of
                    ((GebConceptCategoryRepresentation _) ** Refl)
                      impossible
                    ((GebConceptObjectRepresentation objRep catRep) ** correct) =>
                      void $ notCategory (catRep **
                        fst (consInjective (snd
                           (consInjective (sexpInjectiveList correct)))))
                    ((GebConceptMorphismRepresentation _ _ _ _) ** Refl)
                      impossible
              No notObject => No $ \p => case p of
                ((GebConceptCategoryRepresentation _) ** Refl) impossible
                ((GebConceptObjectRepresentation objRep catRep) ** Refl) =>
                  notObject $ (objRep ** Refl)
                ((GebConceptMorphismRepresentation _ _ _ _) ** Refl) impossible
          (_ :: _ :: _ :: _) => No $ \p => case p of
            ((GebConceptCategoryRepresentation _) ** Refl) impossible
        No notObject => case decEq a GAConceptMorphism of
          Yes Refl => case l of
            [] => No $ \p => case p of
              ((GebConceptCategoryRepresentation _) ** Refl) impossible
            ([_]) => No $ \p => case p of
              ((GebConceptCategoryRepresentation _) ** Refl) impossible
            ([_, _]) => No $ \p => case p of
              ((GebConceptCategoryRepresentation _) ** Refl) impossible
            ([_, _, _]) => No $ \p => case p of
              ((GebConceptCategoryRepresentation _) ** Refl) impossible
            ([morphism, category, domain, codomain]) =>
              case (gebSExpToMorphismRepCertified morphism,
                    gebSExpToCategoryRepCertified category,
                    gebSExpToObjectRepCertified domain,
                    gebSExpToObjectRepCertified codomain) of
                (Yes (morphismRep ** Refl),
                 Yes (catRep ** Refl),
                 Yes (domainRep ** Refl),
                 Yes (codomainRep ** Refl)) => No $ \p => case p of
                  ((GebConceptCategoryRepresentation _) ** Refl)
                    impossible
                (No notMorphism, _, _, _) => No $ \p => case p of
                  ((GebConceptCategoryRepresentation _) ** Refl)
                    impossible
                (_, No notCategory, _, _) => No $ \p => case p of
                  ((GebConceptCategoryRepresentation _) ** Refl)
                    impossible
                (_, _, No domainNotObject, _) => No $ \p => case p of
                  ((GebConceptCategoryRepresentation _) ** Refl)
                    impossible
                (_, _, _, No codomainNotObject) => No $ \p => case p of
                  ((GebConceptCategoryRepresentation _) ** Refl)
                    impossible
            (_ :: _ :: _ :: _ :: _ :: _) => No $ \p => case p of
              ((GebConceptCategoryRepresentation _) ** Refl) impossible
          No notMorphism => case decEq a GAConceptDependentType of
            Yes Refl => No $ \p => case p of
              ((GebDependentTypeRepresentation _ _ _ _) ** Refl) impossible
            No notDependentType => No $ \p => case p of
              ((GebConceptCategoryRepresentation _) ** Refl) => notCategory Refl
              ((GebConceptObjectRepresentation _ _) ** Refl) => notObject Refl
              ((GebConceptMorphismRepresentation _ _ _ _) ** correct) =>
                notMorphism $ sym $ sexpInjectiveAtom correct

  public export
  gebConceptRepToSExp_injective : (rep, rep' : GebConceptRepresentation) ->
    gebConceptRepToSExp rep = gebConceptRepToSExp rep' ->
    rep = rep'
  gebConceptRepToSExp_injective
    (GebConceptCategoryRepresentation cat)
    (GebConceptCategoryRepresentation cat')
    eq =
      rewrite gebCategoryRepToSExp_injective cat cat'
        (fst (consInjective (sexpInjectiveList eq))) in
      Refl
  gebConceptRepToSExp_injective
    (GebConceptObjectRepresentation obj cat)
    (GebConceptObjectRepresentation obj' cat')
    eq =
      let listEq = sexpInjectiveList eq in
      rewrite gebObjectRepToSExp_injective obj obj'
        (fst (consInjective listEq)) in
      rewrite gebCategoryRepToSExp_injective cat cat'
        (fst (consInjective (snd (consInjective listEq)))) in
      Refl
  gebConceptRepToSExp_injective
    (GebConceptMorphismRepresentation morphism cat domain codomain)
    (GebConceptMorphismRepresentation morphism' cat' domain' codomain')
    eq =
      let listEq = sexpInjectiveList eq in
      rewrite gebMorphismRepToSExp_injective morphism morphism'
        (fst (consInjective listEq)) in
      rewrite gebCategoryRepToSExp_injective cat cat'
        (fst (consInjective (snd (consInjective listEq)))) in
      rewrite gebObjectRepToSExp_injective domain domain'
        (fst (consInjective (snd (consInjective
          (snd (consInjective listEq)))))) in
      rewrite gebObjectRepToSExp_injective codomain codomain'
        (fst (consInjective (snd (consInjective
          (snd (consInjective (snd (consInjective listEq)))))))) in
      Refl

  public export
  gebSExpToConceptRep : GebSExp -> Maybe GebConceptRepresentation
  gebSExpToConceptRep = decMapToMaybe gebSExpToConceptRepCertified

  public export
  gebConceptRepToSExpToConceptRepCertified_correct :
    (rep : GebConceptRepresentation) ->
    gebSExpToConceptRepCertified (gebConceptRepToSExp rep) = Yes (rep ** Refl)
  gebConceptRepToSExpToConceptRepCertified_correct rep with
    (gebConceptRepToSExp rep,
     gebSExpToConceptRepCertified (gebConceptRepToSExp rep)) proof p
      gebConceptRepToSExpToConceptRepCertified_correct rep |
        (x, Yes (rep' ** correct)) =
          rewrite PairSndEq p in
          rewrite gebConceptRepToSExp_injective rep' rep correct in
          cong Yes $ UniqueDPairInjective (\r, eq, eq' => uip eq eq')
      gebConceptRepToSExpToConceptRepCertified_correct rep |
        (x, No neq) = void $ neq (rep ** Refl)

  public export
  gebConceptRepToSExpToConceptRep_correct :
    (rep : GebConceptRepresentation) ->
    gebSExpToConceptRep (gebConceptRepToSExp rep) = Just rep
  gebConceptRepToSExpToConceptRep_correct rep with
    (gebConceptRepToSExp rep,
     gebSExpToConceptRepCertified (gebConceptRepToSExp rep)) proof p
      gebConceptRepToSExpToConceptRep_correct rep |
        (x, Yes (rep' ** correct)) =
          rewrite PairSndEq p in
          rewrite gebConceptRepToSExp_injective rep' rep correct in
          Refl
      gebConceptRepToSExpToConceptRep_correct rep |
        (x, No neq) = void $ neq (rep ** Refl)

  public export
  gebSExpToConceptRepToSExp_correct :
    (x : GebSExp) -> (rep : GebConceptRepresentation) ->
    gebSExpToConceptRep x = Just rep -> gebConceptRepToSExp rep = x
  gebSExpToConceptRepToSExp_correct =
    decMapToMaybe_correct gebSExpToConceptRepCertified

--------------------------------------------------------------------------------

public export
Show GebCategoryRepresentation where
  show = show . gebCategoryRepToSExp

public export
Eq GebCategoryRepresentation where
  rep == rep' = gebCategoryRepToSExp rep == gebCategoryRepToSExp rep'

public export
DecEq GebCategoryRepresentation where
  decEq =
    encodingDecEq
      gebCategoryRepToSExp gebSExpToCategoryRep
      gebCategoryRepToSExpToCategoryRep_correct decEq

public export
Ord GebCategoryRepresentation where
  rep < rep' = gebCategoryRepToSExp rep < gebCategoryRepToSExp rep'

--------------------------------------------------------------------------------

public export
Show GebObjectRepresentation where
  show = show . gebObjectRepToSExp

public export
Eq GebObjectRepresentation where
  rep == rep' = gebObjectRepToSExp rep == gebObjectRepToSExp rep'

public export
DecEq GebObjectRepresentation where
  decEq =
    encodingDecEq
      gebObjectRepToSExp gebSExpToObjectRep
      gebObjectRepToSExpToObjectRep_correct decEq

public export
Ord GebObjectRepresentation where
  rep < rep' = gebObjectRepToSExp rep < gebObjectRepToSExp rep'

--------------------------------------------------------------------------------

public export
Show GebMorphismRepresentation where
  show = show . gebMorphismRepToSExp

public export
Eq GebMorphismRepresentation where
  rep == rep' = gebMorphismRepToSExp rep == gebMorphismRepToSExp rep'

public export
DecEq GebMorphismRepresentation where
  decEq =
    encodingDecEq
      gebMorphismRepToSExp gebSExpToMorphismRep
      gebMorphismRepToSExpToMorphismRep_correct decEq

public export
Ord GebMorphismRepresentation where
  rep < rep' = gebMorphismRepToSExp rep < gebMorphismRepToSExp rep'

--------------------------------------------------------------------------------

public export
Show GebDependentTypeRepresentation where
  show = show . gebDependentTypeRepToSExp

public export
Eq GebDependentTypeRepresentation where
  rep == rep' = gebDependentTypeRepToSExp rep == gebDependentTypeRepToSExp rep'

public export
DecEq GebDependentTypeRepresentation where
  decEq =
    encodingDecEq
      gebDependentTypeRepToSExp gebSExpToDependentTypeRep
      gebDependentTypeRepToSExpToDependentTypeRep_correct decEq

public export
Ord GebDependentTypeRepresentation where
  rep < rep' = gebDependentTypeRepToSExp rep < gebDependentTypeRepToSExp rep'

--------------------------------------------------------------------------------

--------------------------------------------------------------------------------

public export
Show GebConceptRepresentation where
  show = show . gebConceptRepToSExp

public export
Eq GebConceptRepresentation where
  rep == rep' = gebConceptRepToSExp rep == gebConceptRepToSExp rep'

public export
DecEq GebConceptRepresentation where
  decEq =
    encodingDecEq
      gebConceptRepToSExp gebSExpToConceptRep
      gebConceptRepToSExpToConceptRep_correct decEq

public export
Ord GebConceptRepresentation where
  rep < rep' = gebConceptRepToSExp rep < gebConceptRepToSExp rep'

--------------------------------------------------------------------------------

mutual
  public export
  data GebConcept : GebConceptRepresentation -> Type
    where
      GebConceptCategory : {representation : GebCategoryRepresentation} ->
        GebCategory representation ->
        GebConcept (GebConceptCategoryRepresentation representation)
      GebConceptObject : {objRep : GebObjectRepresentation} ->
        {catRep : GebCategoryRepresentation} ->
        GebObject objRep catRep ->
        GebConcept (GebConceptObjectRepresentation objRep catRep)
      GebConceptMorphism : {morphismRep : GebMorphismRepresentation} ->
        {catRep : GebCategoryRepresentation} ->
        {domainRep, codomainRep : GebObjectRepresentation} ->
        GebMorphism morphismRep catRep domainRep codomainRep ->
        GebConcept (GebConceptMorphismRepresentation
          morphismRep catRep domainRep codomainRep)
      GebConceptDependentType : {depTypeRep : GebDependentTypeRepresentation} ->
        {catRep : GebCategoryRepresentation} ->
        {domainRep : GebObjectRepresentation} ->
        {morphismRep : GebMorphismRepresentation} ->
        GebDependentType depTypeRep catRep domainRep morphismRep ->
        GebConcept (GebConceptDependentTypeRepresentation
          depTypeRep catRep domainRep morphismRep)

  public export
  data GebCategory : GebCategoryRepresentation -> Type
    where
      GebInGeb : GebCategory GebSelfRepresentation

  public export
  data GebObject : GebObjectRepresentation -> GebCategoryRepresentation -> Type
    where
      GebObjectReflector : {catRep : GebCategoryRepresentation} ->
        GebCategory catRep ->
        GebObject (GebObjectReflectorRepresentation catRep) catRep

  public export
  data GebMorphism : GebMorphismRepresentation -> GebCategoryRepresentation ->
    (domain, codomain : GebObjectRepresentation) -> Type
    where

  public export
  data GebDependentType : GebDependentTypeRepresentation ->
    GebCategoryRepresentation -> GebObjectRepresentation ->
    GebMorphismRepresentation -> Type
    where

--------------------------------------------------------------------------------

public export
record GebConceptFunctor
  (representationFunctor : GebConceptRepresentationFunctor) where
    constructor GebConceptMaps
    GebCategoryMap : (catRep : GebCategoryRepresentation) ->
      GebCategory catRep ->
      GebCategory (GebCategoryRepresentationMap representationFunctor catRep)
    GebObjectMap : (catRep : GebCategoryRepresentation) ->
      (category : GebCategory catRep) ->
      (objRep : GebObjectRepresentation) ->
      GebObject objRep catRep ->
      GebObject
        (GebObjectRepresentationMap representationFunctor objRep)
        (GebCategoryRepresentationMap representationFunctor catRep)
    GebMorphismMap : (catRep : GebCategoryRepresentation) ->
      (category : GebCategory catRep) ->
      (domainRep, codomainRep : GebObjectRepresentation) ->
      (domain : GebObject domainRep catRep) ->
      (codomain : GebObject codomainRep catRep) ->
      (morphimRep : GebMorphismRepresentation) ->
      GebMorphism morphismRep catRep domainRep codomainRep ->
      GebMorphism
        (GebMorphismRepresentationMap representationFunctor morphismRep)
        (GebCategoryRepresentationMap representationFunctor catRep)
        (GebObjectRepresentationMap representationFunctor domainRep)
        (GebObjectRepresentationMap representationFunctor codomainRep)

--------------------------------------------------------------------------------

public export
gebObjectCategory : {objRep : GebObjectRepresentation} ->
  {catRep : GebCategoryRepresentation} ->
  GebObject objRep catRep ->
  GebCategory catRep
gebObjectCategory (GebObjectReflector category) = category

public export
gebMorphismCategory : {morphismRep : GebMorphismRepresentation} ->
  {catRep : GebCategoryRepresentation} ->
  {domainRep, codomainRep : GebObjectRepresentation} ->
  GebMorphism morphismRep catRep domainRep codomainRep ->
  GebCategory catRep
gebMorphismCategory morphism impossible

public export
gebMorphismDomain : {morphismRep : GebMorphismRepresentation} ->
  {catRep : GebCategoryRepresentation} ->
  {domainRep, codomainRep : GebObjectRepresentation} ->
  GebMorphism morphismRep catRep domainRep codomainRep ->
  GebObject domainRep catRep
gebMorphismDomain morphism impossible

public export
gebMorphismCodomain : {morphismRep : GebMorphismRepresentation} ->
  {catRep : GebCategoryRepresentation} ->
  {domainRep, codomainRep : GebObjectRepresentation} ->
  GebMorphism morphismRep catRep domainRep codomainRep ->
  GebObject codomainRep catRep
gebMorphismCodomain morphism impossible

--------------------------------------------------------------------------------

mutual
  public export
  checkGebCategoryRepresentation :
    (representation : GebCategoryRepresentation) ->
    Dec (GebCategory representation)
  checkGebCategoryRepresentation GebSelfRepresentation = Yes GebInGeb

  public export
  checkGebCategoryRepresentation_complete :
    {representation : GebCategoryRepresentation} ->
    (category : GebCategory representation) ->
    checkGebCategoryRepresentation representation = Yes category
  checkGebCategoryRepresentation_complete GebInGeb = Refl

--------------------------------------------------------------------------------

  public export
  checkGebObjectRepresentation :
    (objRep : GebObjectRepresentation) ->
    (catRep : GebCategoryRepresentation) ->
    Dec (GebObject objRep catRep)
  checkGebObjectRepresentation
    (GebObjectReflectorRepresentation catRep) catRep' =
      case decEq catRep catRep' of
        Yes Refl => case checkGebCategoryRepresentation catRep' of
          Yes category => Yes $ GebObjectReflector category
          No notCategory => No $ \category =>
            void $ notCategory $ gebObjectCategory category
        No neq => No $ \object => case object of
          GebObjectReflector catRep'' => void $ neq Refl

  public export
  checkGebObjectRepresentation_complete :
    {objRep : GebObjectRepresentation} ->
    {catRep : GebCategoryRepresentation} ->
    (object : GebObject objRep catRep) ->
    checkGebObjectRepresentation objRep catRep = Yes object
  checkGebObjectRepresentation_complete
    (GebObjectReflector {catRep} category) =
      rewrite decEqRefl decEq catRep in
      rewrite checkGebCategoryRepresentation_complete category in
      Refl

--------------------------------------------------------------------------------

  public export
  checkGebMorphismRepresentation :
    (morphismRep : GebMorphismRepresentation) ->
    (catRep : GebCategoryRepresentation) ->
    (domainRep, codomainRep : GebObjectRepresentation) ->
    Dec (GebMorphism morphismRep catRep domainRep codomainRep)
  checkGebMorphismRepresentation _ _ _ _ impossible

  public export
  checkGebMorphismRepresentation_complete :
    {morphismRep : GebMorphismRepresentation} ->
    {catRep : GebCategoryRepresentation} ->
    {domainRep, codomainRep : GebObjectRepresentation} ->
    (morphism : GebMorphism morphismRep catRep domainRep codomainRep) ->
    checkGebMorphismRepresentation morphismRep catRep domainRep codomainRep =
      Yes morphism
  checkGebMorphismRepresentation_complete _ impossible

--------------------------------------------------------------------------------

  public export
  checkGebConceptRepresentation : (representation : GebConceptRepresentation) ->
    Dec (GebConcept representation)
  checkGebConceptRepresentation (GebConceptCategoryRepresentation catRep) =
    case checkGebCategoryRepresentation catRep of
      Yes category => Yes $ GebConceptCategory category
      No notCategory => No $ \concept => case concept of
        GebConceptCategory category => void $ notCategory category
  checkGebConceptRepresentation (GebConceptObjectRepresentation objRep catRep) =
    case checkGebObjectRepresentation objRep catRep of
      Yes object => Yes $ GebConceptObject object
      No notObject => No $ \concept => case concept of
        GebConceptObject object => void $ notObject object
  checkGebConceptRepresentation
    (GebConceptMorphismRepresentation
      morphismRep catRep domainRep codomainRep) =
        case checkGebMorphismRepresentation
          morphismRep catRep domainRep codomainRep of
            Yes morphism => Yes $ GebConceptMorphism morphism
            No notMorphism => No $ \concept => case concept of
              GebConceptMorphism morphism => void $ notMorphism morphism

  public export
  checkGebConceptRepresentation_complete :
    {representation : GebConceptRepresentation} ->
    (concept : GebConcept representation) ->
    checkGebConceptRepresentation representation = Yes concept
  checkGebConceptRepresentation_complete (GebConceptCategory category) =
    rewrite checkGebCategoryRepresentation_complete category in
    Refl
  checkGebConceptRepresentation_complete (GebConceptObject object) =
    rewrite checkGebObjectRepresentation_complete object in
    Refl
  checkGebConceptRepresentation_complete (GebConceptMorphism morphism) =
    rewrite checkGebMorphismRepresentation_complete morphism in
    Refl

--------------------------------------------------------------------------------

public export
gebCategory_uniquelyDeterminedByRepresentation :
  {representation : GebCategoryRepresentation} ->
  (category, category' : GebCategory representation) ->
  category = category'
gebCategory_uniquelyDeterminedByRepresentation =
  depDecComplete_implies_unique
    checkGebCategoryRepresentation
    checkGebCategoryRepresentation_complete

public export
gebObject_uniquelyDeterminedByRepresentation :
  {objRep : GebObjectRepresentation} ->
  {catRep : GebCategoryRepresentation} ->
  (object, object' : GebObject objRep catRep) ->
  object = object'
gebObject_uniquelyDeterminedByRepresentation object object' with
  (checkGebObjectRepresentation_complete object,
   checkGebObjectRepresentation_complete object')
    gebObject_uniquelyDeterminedByRepresentation object object' |
      (complete, complete') =
        yesInjective $ trans (sym complete) complete'

public export
gebMorphism_uniquelyDeterminedByRepresentation :
  {morphismRep : GebMorphismRepresentation} ->
  {catRep : GebCategoryRepresentation} ->
  {domainRep, codomainRep : GebObjectRepresentation} ->
  (morphism, morphism' :
    GebMorphism morphismRep catRep domainRep codomainRep) ->
  morphism = morphism'
gebMorphism_uniquelyDeterminedByRepresentation morphism morphism' with
  (checkGebMorphismRepresentation_complete morphism,
   checkGebMorphismRepresentation_complete morphism')
    gebMorphism_uniquelyDeterminedByRepresentation morphism morphism' |
      (complete, complete') =
        yesInjective $ trans (sym complete) complete'

public export
gebConcept_uniquelyDeterminedByRepresentation :
  {representation : GebConceptRepresentation} ->
  (category, category' : GebConcept representation) ->
  category = category'
gebConcept_uniquelyDeterminedByRepresentation =
  depDecComplete_implies_unique
    checkGebConceptRepresentation
    checkGebConceptRepresentation_complete

--------------------------------------------------------------------------------

mutual
  public export
  interpretGebConceptType : {conceptRep : GebConceptRepresentation} ->
    GebConcept conceptRep ->
    Type
  interpretGebConceptType (GebConceptCategory _) = Type
  interpretGebConceptType (GebConceptObject _) = Type
  interpretGebConceptType (GebConceptMorphism morphism) =
    (rewrite
      sym (interpretGebCategory_isUniverse (gebMorphismCategory morphism)) in
     interpretGebObject (gebMorphismCategory morphism)
      (gebMorphismDomain morphism)) ->
    (rewrite
      sym (interpretGebCategory_isUniverse (gebMorphismCategory morphism)) in
     interpretGebObject (gebMorphismCategory morphism)
      (gebMorphismCodomain morphism))

  public export
  interpretGebCategory : {catRep : GebCategoryRepresentation} ->
    -- This should really be "Universe", but Idris doesn't have that as a type.
    GebCategory catRep ->
    Type
  interpretGebCategory _ = Type

  public export
  interpretGebCategory_isUniverse : {catRep : GebCategoryRepresentation} ->
    (category : GebCategory catRep) ->
    interpretGebCategory category = Type
  interpretGebCategory_isUniverse _ = Refl

  public export
  interpretGebConcept : {conceptRep : GebConceptRepresentation} ->
    (concept : GebConcept conceptRep) ->
    interpretGebConceptType concept
  interpretGebConcept (GebConceptCategory category) =
    interpretGebCategory category
  interpretGebConcept (GebConceptObject object) =
    interpretGebObject (gebObjectCategory object) object
  interpretGebConcept (GebConceptMorphism morphism) =
    interpretGebMorphism
      (gebMorphismCategory morphism)
      (gebMorphismDomain morphism)
      (gebMorphismCodomain morphism)
      morphism

  public export
  interpretGebObject : {objRep : GebObjectRepresentation} ->
    {catRep : GebCategoryRepresentation} ->
    (category : GebCategory catRep) ->
    GebObject objRep catRep ->
    interpretGebCategory category
  interpretGebObject _ (GebObjectReflector _) =
    GebObjectRepresentation

  public export
  interpretGebMorphism : {morphismRep : GebMorphismRepresentation} ->
    {catRep : GebCategoryRepresentation} ->
    {domainRep, codomainRep : GebObjectRepresentation} ->
    (category : GebCategory catRep) ->
    (domain : GebObject domainRep catRep) ->
    (codomain : GebObject codomainRep catRep) ->
    GebMorphism morphismRep catRep domainRep codomainRep ->
    (rewrite sym (interpretGebCategory_isUniverse category) in
     interpretGebObject category domain) ->
    (rewrite sym (interpretGebCategory_isUniverse category) in
     interpretGebObject category codomain)
  interpretGebMorphism _ impossible

--------------------------------------------------------------------------------
