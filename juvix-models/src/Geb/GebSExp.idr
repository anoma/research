module Geb.GebSExp

import Library.FunctionsAndRelations
import Library.Decidability
import public RefinedSExp.SExp
import public RefinedSExp.List
import public Geb.GebAtom

%default total

mutual
  {- XXX generalize over order -}
  {- XXX generalize over a newly-defined generator type, AKA over free category -}
  {- XXX switch to uniform 3-sexp-parameter form: representation, 1st-order-datatype parameter, output-type parameter -}
  public export
  data ZerothOrderType :
    (representation : GebSExp) -> (interpretation : Type) -> Type where
      ZerothOrderInitial : ZerothOrderType ($^ GAInitial) Void
      ZerothOrderTerminal : ZerothOrderType ($^ GATerminal) ()

  public export
  data ZerothOrderTerm : (termRep : GebSExp) -> {typeRep : GebSExp} ->
    {typeInterpretation : Type} -> ZerothOrderType typeRep typeInterpretation ->
    (termInterpretation : typeInterpretation) -> Type where
      ZerothOrderUnit : ZerothOrderTerm ($^ GAUnitTerm) ZerothOrderTerminal ()

  public export
  data WellTypedExpression : (representation : GebSExp) ->
    (typeInterpretation : Type) -> (expressionInterpretation : type) ->
    Type where
      ZerothOrderTypeExpression : {typeRep : GebSExp} ->
        {interpretation : Type} -> ZerothOrderType typeRep interpretation ->
        WellTypedExpression (GAZerothOrderType $*** typeRep) Type interpretation
      ZerothOrderTermExpression : {termRep, typeRep : GebSExp} ->
        {typeInterpretation : Type} ->
        {zerothOrderType : ZerothOrderType typeRep typeInterpretation} ->
        {termInterpretation : typeInterpretation} ->
        ZerothOrderTerm termRep zerothOrderType termInterpretation ->
        WellTypedExpression
          (GAZerothOrderTerm $*** termRep) typeInterpretation termInterpretation

mutual
  {- XXX factor out into individual checks -}
  {- XXX fill in holes before checking in -}
  public export
  checkGebSExp : (x : GebSExp) ->
    Maybe $
      (typeInterpretation : Type **
       expressionInterpretation : typeInterpretation **
       WellTypedExpression x typeInterpretation expressionInterpretation)
  checkGebSExp (GAZerothOrderType $* [GAInitial $* []]) =
    Just (Type ** Void ** ZerothOrderTypeExpression ZerothOrderInitial)
  checkGebSExp _ = Nothing

  public export
  gebSExpRepresentationComplete : {x : GebSExp} ->
    {typeInterpretation : Type} ->
    {expressionInterpretation : typeInterpretation} ->
    (wellTypedExpression :
      WellTypedExpression x typeInterpretation expressionInterpretation) ->
    checkGebSExp x = Just
      (typeInterpretation **
       expressionInterpretation **
       wellTypedExpression)
  gebSExpRepresentationComplete
    {typeInterpretation = (Type)} {expressionInterpretation = expressionInterpretation} (ZerothOrderTypeExpression y) =
      ?gebSExpRepresentationComplete_hole_2
  gebSExpRepresentationComplete
    {typeInterpretation = typeInterpretation} {expressionInterpretation = expressionInterpretation} (ZerothOrderTermExpression y) =
      ?gebSExpRepresentationComplete_hole

{-

public export
data GebAtom : Type where
  -- | The notion of a category.
  GACategory : GebAtom

  -- | The notion of a reflective category.
  GAReflective : GebAtom

  -- | The object in a reflective category which can represent the
  -- | category itself.
  GAObjectReflector : GebAtom

  -- | The minimal reflective category, with substitution (pattern-matching)
  -- | only.
  GAMinimalReflective : GebAtom

  -- | A language with fixed points of substitution.
  GAHigherOrder : GebAtom

  -- | The notion of an object of any category.
  GAObject : GebAtom

  -- | Objects common to all reflective categories.
  GAPromoteObject : GebAtom
  GAAtom : GebAtom
  GASExp : GebAtom
  GASList : GebAtom

  -- | The notion of a morphism of any programming language.
  GAMorphism : GebAtom

  -- | Morphisms common to all programming languages.
  GAPromoteMorphism : GebAtom
  GAIdentity : GebAtom
  GACompose : GebAtom
  GASExpIntro : GebAtom
  GASExpElim : GebAtom

  -- | The notion of a term of any programming language.
  GATerm : GebAtom

  -- | Terms common to all programming languages.
  GAAtomTerm : GebAtom
  GASExpTerm : GebAtom
  GASListTerm : GebAtom

  -- | The notion of a refinement.
  GARefinement : GebAtom

public export
gaEncode : GebAtom -> Nat
gaEncode GACategory = 0
gaEncode GAMinimalReflective = 1
gaEncode GAHigherOrder = 2
gaEncode GAObject = 3
gaEncode GAPromoteObject = 4
gaEncode GAAtom = 5
gaEncode GASExp = 6
gaEncode GASList = 7
gaEncode GAMorphism = 8
gaEncode GAPromoteMorphism = 9
gaEncode GAIdentity = 10
gaEncode GACompose = 11
gaEncode GASExpIntro = 12
gaEncode GASExpElim = 13
gaEncode GATerm = 14
gaEncode GAAtomTerm = 15
gaEncode GASExpTerm = 16
gaEncode GASListTerm = 17
gaEncode GAReflective = 18
gaEncode GAObjectReflector = 19
gaEncode GARefinement = 20

public export
gaDecode : Nat -> Maybe GebAtom
gaDecode 0 = Just GACategory
gaDecode 1 = Just GAMinimalReflective
gaDecode 2 = Just GAHigherOrder
gaDecode 3 = Just GAObject
gaDecode 4 = Just GAPromoteObject
gaDecode 5 = Just GAAtom
gaDecode 6 = Just GASExp
gaDecode 7 = Just GASList
gaDecode 8 = Just GAMorphism
gaDecode 9 = Just GAPromoteMorphism
gaDecode 10 = Just GAIdentity
gaDecode 11 = Just GACompose
gaDecode 12 = Just GASExpIntro
gaDecode 13 = Just GASExpElim
gaDecode 14 = Just GATerm
gaDecode 15 = Just GAAtomTerm
gaDecode 16 = Just GASExpTerm
gaDecode 17 = Just GASListTerm
gaDecode 18 = Just GAReflective
gaDecode 19 = Just GAObjectReflector
gaDecode 20 = Just GARefinement
gaDecode _ = Nothing

export
gaDecodeEncodeIsJust : (a : GebAtom) -> gaDecode (gaEncode a) = Just a
gaDecodeEncodeIsJust GACategory = Refl
gaDecodeEncodeIsJust GAMinimalReflective = Refl
gaDecodeEncodeIsJust GAHigherOrder = Refl
gaDecodeEncodeIsJust GAObject = Refl
gaDecodeEncodeIsJust GAPromoteObject = Refl
gaDecodeEncodeIsJust GAAtom = Refl
gaDecodeEncodeIsJust GASExp = Refl
gaDecodeEncodeIsJust GASList = Refl
gaDecodeEncodeIsJust GAMorphism = Refl
gaDecodeEncodeIsJust GAPromoteMorphism = Refl
gaDecodeEncodeIsJust GAIdentity = Refl
gaDecodeEncodeIsJust GACompose = Refl
gaDecodeEncodeIsJust GASExpIntro = Refl
gaDecodeEncodeIsJust GASExpElim = Refl
gaDecodeEncodeIsJust GATerm = Refl
gaDecodeEncodeIsJust GAAtomTerm = Refl
gaDecodeEncodeIsJust GASExpTerm = Refl
gaDecodeEncodeIsJust GASListTerm = Refl
gaDecodeEncodeIsJust GAReflective = Refl
gaDecodeEncodeIsJust GAObjectReflector = Refl
gaDecodeEncodeIsJust GARefinement = Refl

public export
gebAtomToString : GebAtom -> String
gebAtomToString GACategory = "Category"
gebAtomToString GAMinimalReflective = "MinimalReflective"
gebAtomToString GAHigherOrder = "HigherOrder"
gebAtomToString GAObject = "Object"
gebAtomToString GAPromoteObject = "PromoteObject"
gebAtomToString GAAtom = "Atom"
gebAtomToString GASExp = "SExp"
gebAtomToString GASList = "SList"
gebAtomToString GAMorphism = "Morphism"
gebAtomToString GAPromoteMorphism = "PromoteMorphism"
gebAtomToString GAIdentity = "Identity"
gebAtomToString GACompose = "Compose"
gebAtomToString GASExpIntro = "SExpIntro"
gebAtomToString GASExpElim = "SExpElim"
gebAtomToString GATerm = "Term"
gebAtomToString GAAtomTerm = "AtomTerm"
gebAtomToString GASExpTerm = "SExpTerm"
gebAtomToString GASListTerm = "SListTerm"
gebAtomToString GAReflective = "Reflective"
gebAtomToString GAObjectReflector = "ReflectiveObject"
gebAtomToString GARefinement = "Refinement"

public export
Show GebAtom where
  show a = ":" ++ gebAtomToString a

public export
gaEq : GebAtom -> GebAtom -> Bool
gaEq a a' = gaEncode a == gaEncode a'

public export
Eq GebAtom where
  (==) = gaEq

public export
Ord GebAtom where
  a < a' = gaEncode a < gaEncode a'

export
gaDecEq : (a, a' : GebAtom) -> Dec (a = a')
gaDecEq a a' with (decEq (gaEncode a) (gaEncode a'))
  gaDecEq a a' | Yes eq = Yes $
    injective $
      trans
        (sym (gaDecodeEncodeIsJust a))
        (trans (cong gaDecode eq) (gaDecodeEncodeIsJust a'))
  gaDecEq a a' | No neq = No $ \aeq => neq $ cong gaEncode aeq

public export
DecEq GebAtom where
  decEq = gaDecEq

public export
GebSExp : Type
GebSExp = SExp GebAtom

public export
GebSList : Type
GebSList = SList GebAtom

public export
Show GebSExp where
  show = fst (sexpShows show)

public export
Show GebSList where
  show l = "(" ++ snd (sexpShows show) l ++ ")"

public export
gsDecEq : DecEqPred GebSExp
gsDecEq = sexpDecEq gaDecEq

public export
gslDecEq : DecEqPred GebSList
gslDecEq = slistDecEq gaDecEq

public export
DecEq GebSExp where
  decEq = gsDecEq

public export
DecEq GebSList where
  decEq = gslDecEq

public export
Eq GebSExp using decEqToEq where
  (==) = (==)

public export
Ord GebSExp where
  (<) = sexpLessThan (<)

public export
Ord GebSList where
  (<) = slistLessThan (<)

public export
GebSet : Type
GebSet = SortedSet GebSExp

public export
gebSet : GebSList -> GebSet
gebSet = fromList

public export
GebMap : Type
GebMap = SortedMap GebAtom GebSList

public export
gebMap : List (GebAtom, GebSList) -> GebMap
gebMap = fromList

----------------------------------------------------------------
---- General definition of programming language / metalogic ----
----------------------------------------------------------------

mutual

-- | A "Category" (short in this case for "programming language") is a category
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
  public export
  data IsCategory : GebSExp -> Type where
    MinimalReflective : IsCategory ($^ GAMinimalReflective)
    HigherOrder : IsCategory ($^ GAHigherOrder)

  public export
  Category : Type
  Category = DPair GebSExp IsCategory

  public export
  data IsObject : GebSExp -> Type where
    ReflectiveObject : {x : GebSExp} ->
      (IsCategory x) -> IsObject (GAObjectReflector $*** x)

  public export
  Object : Type
  Object = DPair GebSExp IsObject

  public export
  data HasCategory : (object, category : GebSExp) -> Type where
    ReflectiveObjectCategory : (category : GebSExp) ->
      {auto isCategory : IsCategory category} ->
      HasCategory (GAObjectReflector $*** category) category

  public export
  data IsMorphism : GebSExp -> Type where
    IsIdentity : {x : GebSExp} -> IsObject x -> IsMorphism (GAIdentity $*** x)
    IsCompose : {a, b, c, g, f : GebSExp} ->
      {oa : IsObject a} ->
      {ob : IsObject b} ->
      {oc : IsObject c} ->
      (mg : IsMorphism g) -> (mf : IsMorphism f) ->
      {domf : HasDomain f a} ->
      {codf : HasCodomain f b} ->
      {domg : HasDomain g b} ->
      {codg : HasCodomain g c} ->
      IsMorphism $ GACompose $* [g, f]

  public export
  Morphism : Type
  Morphism = DPair GebSExp IsMorphism

  public export
  data HasDomain : (morphism, domain : GebSExp) -> Type where
    IdentityDomain : (domain : GebSExp) ->
      {auto isObject : IsObject domain} ->
      HasDomain (GAIdentity $*** domain) domain
    MorphismDomain : {a, b, c, g, f : GebSExp} ->
      {oa : IsObject a} ->
      {ob : IsObject b} ->
      {oc : IsObject c} ->
      (mg : IsMorphism g) -> (mf : IsMorphism f) ->
      {domf : HasDomain f a} ->
      {codf : HasCodomain f b} ->
      {domg : HasDomain g b} ->
      {codg : HasCodomain g c} ->
      HasDomain (GACompose $* [g, f]) a

  public export
  data HasCodomain : (morphism, codomain : GebSExp) -> Type where
    IdentityCodomain : (codomain : GebSExp) ->
      {auto isObject : IsObject codomain} ->
      HasCodomain (GAIdentity $*** codomain) codomain

  public export
  data IsReflective : GebSExp -> Type where
    MinimalIsReflective : IsReflective (GAReflective $**^ GAMinimalReflective)
    HigherOrderIsReflective : IsReflective (GAReflective $**^ GAHigherOrder)

  public export
  ReflectiveCategory : Type
  ReflectiveCategory = DPair GebSExp IsReflective

  public export
  reflectiveCategory : {x : GebSExp} -> IsReflective x -> Category
  reflectiveCategory {x=(GAReflective $* [$^ GAMinimalReflective])}
    MinimalIsReflective = (GAMinimalReflective $* [] ** MinimalReflective)
  reflectiveCategory {x=(GAReflective $* [$^ GAHigherOrder])}
    HigherOrderIsReflective = (GAHigherOrder $* [] ** HigherOrder)

  public export
  data IsRefinement : GebSExp -> Type where
    CategoryRefinement : (x : GebSExp) -> IsCategory x ->
      IsRefinement (GARefinement $*** x)
    ObjectRefinement : (x : GebSExp) -> IsObject x ->
      IsRefinement (GARefinement $*** x)
    MorphismRefinement : (x : GebSExp) -> IsMorphism x ->
      IsRefinement (GARefinement $*** x)
    ReflectiveRefinement : (x : GebSExp) -> IsReflective x ->
      IsRefinement (GARefinement $*** x)

  public export
  Refinement : Type
  Refinement = DPair GebSExp IsRefinement

---------------------------------------------------------------------
---- Completeness and uniqueness of S-expression representations ----
---------------------------------------------------------------------

mutual

  public export
  gebSExpToIsCategory : (x : GebSExp) -> Maybe (IsCategory x)
  gebSExpToIsCategory (GAMinimalReflective $* []) = Just MinimalReflective
  gebSExpToIsCategory (GAHigherOrder $* []) = Just HigherOrder
  gebSExpToIsCategory _ = Nothing

  public export
  gebSExpToCategory : GebSExp -> Maybe Category
  gebSExpToCategory x with (gebSExpToIsCategory x)
    gebSExpToCategory x | Just l = Just $ (x ** l)
    gebSExpToCategory x | Nothing = Nothing

  export
  gebCategoryRepresentationComplete : (l : Category) ->
    gebSExpToCategory (fst l) = Just l
  gebCategoryRepresentationComplete (_ ** MinimalReflective) = Refl
  gebCategoryRepresentationComplete (_ ** HigherOrder) = Refl

  export
  gebCategoryRepresentationUnique : {x : GebSExp} ->
    (l, l' : IsCategory x) -> l = l'
  gebCategoryRepresentationUnique
    {x=(GAMinimalReflective $* [])} MinimalReflective MinimalReflective =
    Refl
  gebCategoryRepresentationUnique
    {x=(GAHigherOrder $* [])} HigherOrder HigherOrder =
    Refl

  export
  categoryDecEq : DecEqPred Category
  categoryDecEq =
    encodingDecEq
      fst
      gebSExpToCategory
      gebCategoryRepresentationComplete
      decEq

  public export
  objectCategory : {x : GebSExp} -> IsObject x -> Category
  objectCategory {x=(GAObjectReflector $* [cat])}
    (ReflectiveObject isCategory) = (cat ** isCategory)

  public export
  morphismDomain : {x : GebSExp} -> IsMorphism x -> Object
  morphismDomain {x=(GAIdentity $* [obj])} (IsIdentity isObject) =
    (obj ** isObject)
  morphismDomain {x=(GACompose $* [g, f])} (IsCompose {a} {oa} _ _) =
    (a ** oa)

  public export
  morphismCodomain : {x : GebSExp} -> IsMorphism x -> Object
  morphismCodomain {x=(GAIdentity $* [obj])} (IsIdentity isObject) =
    (obj ** isObject)
  morphismCodomain {x=(GACompose $* [g, f])} (IsCompose {c} {oc} _ _) =
    (c ** oc)

  public export
  morphismDomainConsistent : (m, o : GebSExp) ->
    {isMorphism : IsMorphism m} -> {isObject : IsObject o} ->
    morphismDomain isMorphism = (o ** isObject) ->
    HasDomain m o
  morphismDomainConsistent (GAIdentity $* [o]) o
    {isMorphism=(IsIdentity isObject)} {isObject} Refl =
      IdentityDomain o
  morphismDomainConsistent (GACompose $* [g, f]) a
    {isMorphism=(IsCompose {oa} {ob} {oc} {domf} {codf} {domg} {codg} {a} {b}
     {c} mg mf)} Refl =
      MorphismDomain {oa} {ob} {oc} {domf} {codf} {domg} {codg} {a} {b} {c}
        mg mf

  public export
  morphismCodomainConsistent : (m, o : GebSExp) ->
    {isMorphism : IsMorphism m} -> {isObject : IsObject o} ->
    morphismCodomain isMorphism = (o ** isObject) ->
    HasCodomain m o
  morphismCodomainConsistent m o {isMorphism} {isObject} eq =
    morphismCodomainConsistent_hole

  public export
  morphismDomainComplete : (m, o : GebSExp) ->
    {isMorphism : IsMorphism m} -> {isObject : IsObject o} ->
    HasDomain m o ->
    morphismDomain isMorphism = (o ** isObject)
  morphismDomainComplete m o {isMorphism} {isObject} eq =
    morphismDomainComplete_hole

  public export
  morphismCodomainComplete : (m, o : GebSExp) ->
    {isMorphism : IsMorphism m} -> {isObject : IsObject o} ->
    HasCodomain m o ->
    morphismCodomain isMorphism = (o ** isObject)
  morphismCodomainComplete m o {isMorphism} {isObject} eq =
    morphismCodomainComplete_hole

  public export
  morphismDomainCategory : {x : GebSExp} -> IsMorphism x -> Category
  morphismDomainCategory m = objectCategory (snd $ morphismDomain m)

  public export
  morphismCodomainCategory : {x : GebSExp} -> IsMorphism x -> Category
  morphismCodomainCategory m = objectCategory (snd $ morphismCodomain m)

  public export
  morphismCategoryConsistent : {x : GebSExp} -> (m : IsMorphism x) ->
    morphismDomainCategory m = morphismCodomainCategory m
  morphismCategoryConsistent {x=(GAIdentity $* [obj])}
    (IsIdentity isObject) =
      Refl
  morphismCategoryConsistent {x=(GACompose $* [g, f])}
    (IsCompose {a} {b} {c} {oa} {ob} {oc} {domf} {codf} {domg} {codg} mg mf) =
      let
        mcatconsf = morphismCategoryConsistent mf
        mcatconsg = morphismCategoryConsistent mg
        mdomcompf = morphismDomainComplete f a domf
          {isMorphism=mf} {isObject=oa}
        mcodcompf = morphismCodomainComplete f b codf
          {isMorphism=mf} {isObject=ob}
        mdomcompg = morphismDomainComplete g b domg
          {isMorphism=mg} {isObject=ob}
        mcodcompg = morphismCodomainComplete g c codg
          {isMorphism=mg} {isObject=oc}
        mfcodcata = replace
          {p=(\a' => (objectCategory $ snd a') =
            (objectCategory $ snd $ morphismCodomain mf))}
          mdomcompf mcatconsf
        mgcodcatb = replace
          {p=(\b' => (objectCategory $ snd b') =
            (objectCategory $ snd $ morphismCodomain mg))}
          mdomcompg mcatconsg
        mgdomcatc = replace
          {p=(\c' => (objectCategory $ snd $ morphismDomain mg) =
            (objectCategory $ snd c'))}
          mcodcompg mcatconsg
        mfdomcatb = replace
          {p=(\b' => (objectCategory $ snd $ morphismDomain mf) =
            (objectCategory $ snd b'))}
          mcodcompf mcatconsf
      in
      trans (trans (trans (trans (trans mfcodcata (sym mcatconsf)) mfdomcatb)
        mgcodcatb) (sym mcatconsg)) mgdomcatc

  public export
  morphismCategory : {x : GebSExp} -> IsMorphism x -> Category
  morphismCategory = morphismDomainCategory

-------------------------------------------------------------
---- Instances derived from S-expression representations ----
-------------------------------------------------------------

public export
DecEq Category where
  decEq = categoryDecEq

public export
Eq Category using decEqToEq where
  (==) = (==)

public export
Show Category where
  show = show . fst

------------------------------------------------------------------
---- Objects of reflective (SExp-based) programming languages ----
------------------------------------------------------------------

public export
data LanguageObject : Language -> Type where
  PromoteObject : LanguageObject MinimalReflective -> LanguageObject HigherOrder
  AtomObject : (l : Language) -> LanguageObject l
  SExpObject : (l : Language) -> LanguageObject l
  SListObject : (l : Language) -> LanguageObject l

public export
Object : Type
Object = DPair Language LanguageObject

public export
gebLanguageObjectToExp : {l : Language} -> LanguageObject l -> GebSExp
gebLanguageObjectToExp {l} (AtomObject l) =
  GAAtom $* [gebLanguageToExp l]
gebLanguageObjectToExp {l} (SExpObject l) =
  GASExp $* [gebLanguageToExp l]
gebLanguageObjectToExp {l} (SListObject l) =
  GASList $* [gebLanguageToExp l]
gebLanguageObjectToExp {l=MinimalReflective} (PromoteObject o) impossible
gebLanguageObjectToExp {l=HigherOrder} (PromoteObject o) =
  GAPromoteObject $*
    [gebLanguageToExp MinimalReflective, gebLanguageToExp HigherOrder,
     gebLanguageObjectToExp o]

public export
gebObjectToExp : Object -> GebSExp
gebObjectToExp (l ** o) = gebLanguageObjectToExp {l} o

public export
gebExpToObject : GebSExp -> Maybe Object
gebExpToObject (GAPromoteObject $* [oldlx, newlx, ox]) =
  case (gebExpToLanguage oldlx, gebExpToLanguage newlx, gebExpToObject ox) of
    (Just MinimalReflective, Just HigherOrder,
     Just (MinimalReflective ** o)) =>
      Just $ (HigherOrder ** PromoteObject o)
    _ => Nothing
gebExpToObject (GAAtom $* [x]) = case gebExpToLanguage x of
  Just l => Just (l ** AtomObject l)
  _ => Nothing
gebExpToObject (GASExp $* [lx]) =
  case (gebExpToLanguage lx) of
    (Just l) => Just (l ** SExpObject l)
    _ => Nothing
gebExpToObject (GASList $* [lx]) =
  case (gebExpToLanguage lx) of
    (Just l) => Just (l ** SListObject l)
    _ => Nothing
gebExpToObject _ = Nothing

public export
gebLanguageObjectRepresentationComplete : {l : Language} ->
  (o : LanguageObject l) ->
  gebExpToObject (gebLanguageObjectToExp {l} o) = Just (l ** o)
gebLanguageObjectRepresentationComplete
  {l=HigherOrder} (PromoteObject o) =
    rewrite gebLanguageObjectRepresentationComplete o in
    Refl
gebLanguageObjectRepresentationComplete {l} (AtomObject l) =
  rewrite gebLanguageRepresentationComplete l in
  Refl
gebLanguageObjectRepresentationComplete {l} (SExpObject l) =
  rewrite gebLanguageRepresentationComplete l in
  Refl
gebLanguageObjectRepresentationComplete {l} (SListObject l) =
  rewrite gebLanguageRepresentationComplete l in
  Refl

public export
gebObjectRepresentationComplete : (o : Object) ->
  gebExpToObject (gebObjectToExp o) = Just o
gebObjectRepresentationComplete (l ** o) =
  gebLanguageObjectRepresentationComplete {l} o

public export
Show Object where
  show = show . gebObjectToExp

export
objectDecEq : DecEqPred Object
objectDecEq =
  encodingDecEq
    gebObjectToExp
    gebExpToObject
    gebObjectRepresentationComplete
    decEq

public export
DecEq Object where
  decEq = objectDecEq

public export
Eq Object using decEqToEq where
  (==) = (==)

--------------------------------------------------------------------
---- Morphisms of reflective (SExp-based) programming languages ----
--------------------------------------------------------------------

public export
data LanguageMorphism : {l : Language} ->
  (domain, codomain : LanguageObject l) -> Type where
    PromoteMorphism : {domain, codomain : LanguageObject MinimalReflective} ->
      LanguageMorphism {l=MinimalReflective}
        domain codomain ->
      LanguageMorphism {l=HigherOrder}
        (PromoteObject domain) (PromoteObject codomain)
    Identity : {l : Language} -> (o : LanguageObject l) -> LanguageMorphism o o
    Compose : {l : Language} -> (o : LanguageObject l) -> LanguageMorphism o o

public export
Morphism : Type
Morphism = (l : Language **
            domain : LanguageObject l ** codomain : LanguageObject l **
            LanguageMorphism {l} domain codomain)

public export
gebLanguageMorphismToExp :
  {l : Language} -> {domain, codomain : LanguageObject l} ->
  LanguageMorphism domain codomain -> GebSExp
gebLanguageMorphismToExp m = gebLanguageMorphismToExp_hole

public export
gebMorphismToExp : Morphism -> GebSExp
gebMorphismToExp (l ** domain ** codomain ** m) =
  gebLanguageMorphismToExp {l} {domain} {codomain} m

public export
gebExpToMorphism : GebSExp -> Maybe Morphism
gebExpToMorphism x = gebExpToMorphism_hole

public export
gebLanguageMorphismRepresentationComplete : {l : Language} ->
  {domain, codomain : LanguageObject l} ->
  (m : LanguageMorphism domain codomain) ->
  gebExpToMorphism (gebLanguageMorphismToExp {l} {domain} {codomain} m) =
    Just (l ** domain ** codomain ** m)
gebLanguageMorphismRepresentationComplete {l} {domain} {codomain} m =
  gebLanguageMorphismRepresentationComplete_hole

public export
gebMorphismRepresentationComplete : (m : Morphism) ->
  gebExpToMorphism (gebMorphismToExp m) = Just m
gebMorphismRepresentationComplete (l ** domain ** codomain ** m) =
  gebLanguageMorphismRepresentationComplete {l} {domain} {codomain} m

public export
Show Morphism where
  show = show . gebMorphismToExp

export
morphismDecEq : DecEqPred Morphism
morphismDecEq =
  encodingDecEq
    gebMorphismToExp
    gebExpToMorphism
    gebMorphismRepresentationComplete
    decEq

public export
DecEq Morphism where
  decEq = morphismDecEq

public export
Eq Morphism using decEqToEq where
  (==) = (==)

----------------------------------------------------------------------
---- Refinements of reflective (SExp-based) programming languages ----
----------------------------------------------------------------------

public export
data LanguageRefinement : Language -> Type where

public export
Refinement : Type
Refinement = DPair Language LanguageRefinement

public export
gebLanguageRefinementToExp : {l : Language} -> LanguageRefinement l -> GebSExp
gebLanguageRefinementToExp {l} r = gebLanguageRefinement_hole

public export
gebRefinementToExp : Refinement -> GebSExp
gebRefinementToExp (l ** r) = gebLanguageRefinementToExp {l} r

public export
gebExpToRefinement : GebSExp -> Maybe Refinement
gebExpToRefinement x = gebExpToRefinement_hole

public export
gebLanguageRefinementRepresentationComplete : {l : Language} ->
  (r : LanguageRefinement l) ->
  gebExpToRefinement (gebLanguageRefinementToExp {l} r) = Just (l ** r)
gebLanguageRefinementRepresentationComplete {l} r =
  gebLanguageRefinementRepresentationComplete_hole

public export
gebRefinementRepresentationComplete : (r : Refinement) ->
  gebExpToRefinement (gebRefinementToExp r) = Just r
gebRefinementRepresentationComplete (l ** r) =
  gebLanguageRefinementRepresentationComplete {l} r

public export
Show Refinement where
  show = show . gebRefinementToExp

export
refinementDecEq : DecEqPred Refinement
refinementDecEq =
  encodingDecEq
    gebRefinementToExp
    gebExpToRefinement
    gebRefinementRepresentationComplete
    decEq

public export
DecEq Refinement where
  decEq = refinementDecEq

public export
Eq Refinement using decEqToEq where
  (==) = (==)

mutual
  public export
  data Morphism : Type where
    Identity : Object -> Morphism
    Compose : (g, f : Morphism) ->
      {auto composable :
        (morphismCodomain f) = (morphismDomain g)} ->
      Morphism
    FromInitial : Object -> Morphism
    ToTerminal : Object -> Morphism
    ProductIntro : (f, g : Morphism) ->
      {auto domainsMatch :
        (morphismDomain f) = (morphismDomain g)} ->
      Morphism
    ProductElimLeft : (a, b : Object) -> Morphism
    ProductElimRight : (a, b : Object) -> Morphism
    CoproductElim : (f, g : Morphism) ->
      {auto codomainsMatch :
        (morphismCodomain f) = (morphismCodomain g)} ->
      Morphism
    CoproductIntroLeft : (a, b : Object) -> Morphism
    CoproductIntroRight : (a, b : Object) -> Morphism
    ExpressionIntro : Object -> Morphism
    ExpressionElim : (exp, exp', eqCase, neqCase : Morphism) ->
      {auto expDomainsMatch :
        (morphismDomain exp) = (morphismDomain exp')} ->
      {auto expCodomainIsExpression :
        (morphismCodomain exp) = ObjectExpression} ->
      {auto expCodomainsMatch :
        (morphismCodomain exp) = (morphismCodomain exp')} ->
      {auto eqDomainMatches :
        (morphismDomain exp) = (morphismDomain eqCase)} ->
      {auto neqDomainMatches :
        (morphismDomain exp) = (morphismDomain neqCase)} ->
      {auto eqCodomainsMatch :
        (morphismCodomain eqCase) = (morphismCodomain neqCase)} ->
      Morphism

  public export
  data MinimalReflectiveExpression : Type where
    ObjectExp : Object -> MinimalReflectiveExpression
    MorphismExp : Morphism -> MinimalReflectiveExpression

  public export
  morphismDomain : Morphism -> Object
  morphismDomain (Identity object) = object
  morphismDomain (Compose g f) = morphismDomain f
  morphismDomain (FromInitial _) = Initial
  morphismDomain (ToTerminal domain) = domain
  morphismDomain (ProductIntro f g) = morphismDomain f
  morphismDomain (ProductElimLeft a b) = Product a b
  morphismDomain (ProductElimRight a b) = Product a b
  morphismDomain (CoproductElim f g) =
    Coproduct (morphismDomain f) (morphismDomain g)
  morphismDomain (CoproductIntroLeft a b) = a
  morphismDomain (CoproductIntroRight a b) = b
  morphismDomain (ExpressionIntro _) = Terminal
  morphismDomain (ExpressionElim exp _ _ _) = morphismDomain exp

  public export
  morphismCodomain : Morphism -> Object
  morphismCodomain (Identity object) = object
  morphismCodomain (Compose g f) = morphismCodomain g
  morphismCodomain (FromInitial codomain) = codomain
  morphismCodomain (ToTerminal _) = Terminal
  morphismCodomain (ProductIntro f g) =
    Product (morphismCodomain f) (morphismCodomain g)
  morphismCodomain (ProductElimLeft a b) = a
  morphismCodomain (ProductElimRight a b) = b
  morphismCodomain (CoproductElim f g) = morphismCodomain f
  morphismCodomain (CoproductIntroLeft a b) = Coproduct a b
  morphismCodomain (CoproductIntroRight a b) = Coproduct a b
  morphismCodomain (ExpressionIntro _) = ObjectExpression
  morphismCodomain (ExpressionElim _ _ eqCase _) =
    morphismCodomain eqCase

mutual
  public export
  gebMinimalReflectiveExpressionToExp : MinimalReflectiveExpression -> GebSExp
  gebMinimalReflectiveExpressionToExp (ObjectExp o) = gebObjectToExp o
  gebMinimalReflectiveExpressionToExp (MorphismExp m) = gebMorphismToExp m

  public export
  gebMorphismToExp : Morphism -> GebSExp
  gebMorphismToExp (Identity object) =
    GAIdentity $* [gebObjectToExp object]
  gebMorphismToExp (Compose g f) =
    GACompose $* [gebMorphismToExp g, gebMorphismToExp f]
  gebMorphismToExp (FromInitial codomain) =
    GAFromInitial $* [gebObjectToExp codomain]
  gebMorphismToExp (ToTerminal domain) =
    GAToTerminal $* [gebObjectToExp domain]
  gebMorphismToExp (ProductIntro f g) =
    GAProductIntro $* [gebMorphismToExp f, gebMorphismToExp g]
  gebMorphismToExp (ProductElimLeft a b) =
    GAProductElimLeft $* [gebObjectToExp a, gebObjectToExp b]
  gebMorphismToExp (ProductElimRight a b) =
    GAProductElimRight $* [gebObjectToExp a, gebObjectToExp b]
  gebMorphismToExp (CoproductElim f g) =
    GACoproductElim $* [gebMorphismToExp f, gebMorphismToExp g]
  gebMorphismToExp (CoproductIntroLeft a b) =
    GACoproductIntroLeft $* [gebObjectToExp a, gebObjectToExp b]
  gebMorphismToExp (CoproductIntroRight a b) =
    GACoproductIntroRight $* [gebObjectToExp a, gebObjectToExp b]
  gebMorphismToExp (ExpressionIntro x) =
    GAExpressionIntro $* [gebObjectToExp x]
  gebMorphismToExp (ExpressionElim exp exp' eqCase neqCase) =
    GAExpressionElim $*
      [gebMorphismToExp exp,
       gebMorphismToExp exp',
       gebMorphismToExp eqCase,
       gebMorphismToExp neqCase]

public export
gebMorphismExpIsNotObject : (m : Morphism) ->
  gebExpToObject (gebMorphismToExp m) = Nothing
gebMorphismExpIsNotObject (Identity _) = Refl
gebMorphismExpIsNotObject (Compose _ _) = Refl
gebMorphismExpIsNotObject (FromInitial _) = Refl
gebMorphismExpIsNotObject (ToTerminal _) = Refl
gebMorphismExpIsNotObject (ProductIntro _ _) = Refl
gebMorphismExpIsNotObject (ProductElimLeft _ _) = Refl
gebMorphismExpIsNotObject (ProductElimRight _ _) = Refl
gebMorphismExpIsNotObject (CoproductElim _ _) = Refl
gebMorphismExpIsNotObject (CoproductIntroLeft _ _) = Refl
gebMorphismExpIsNotObject (CoproductIntroRight _ _) = Refl
gebMorphismExpIsNotObject (ExpressionIntro _) = Refl
gebMorphismExpIsNotObject (ExpressionElim _ _ _ _) = Refl

mutual
  public export
  gebExpToMinimalReflectiveExp : GebSExp -> Maybe MinimalReflectiveExpression
  gebExpToMinimalReflectiveExp x with (gebExpToObject x, gebExpToMorphism x)
    proof p
      gebExpToMinimalReflectiveExp x | (Just o, Just m) =
        let pfst = PairFstEq p in
        let psnd = PairSndEq p in
        void (gebExpIsNotBothObjectAndMorphism x o m pfst psnd)
      gebExpToMinimalReflectiveExp x | (Just o, Nothing) = Just $ ObjectExp o
      gebExpToMinimalReflectiveExp x | (Nothing, Just m) = Just $ MorphismExp m
      gebExpToMinimalReflectiveExp x | (Nothing, Nothing) = Nothing

  public export
  gebExpToMorphism : GebSExp -> Maybe Morphism
  gebExpToMorphism (GAIdentity $* [objectExp]) =
    case gebExpToObject objectExp of
      Just object => Just $ Identity object
      _ => Nothing
  gebExpToMorphism (GACompose $* [gExp, fExp]) =
    case (gebExpToMorphism gExp, gebExpToMorphism fExp) of
      (Just g, Just f) =>
        case (objectDecEq
          (morphismCodomain f) (morphismDomain g)) of
            Yes composable => Just $ Compose g f {composable}
            No _ => Nothing
      _ => Nothing
  gebExpToMorphism (GAFromInitial $* [codomainExp]) =
    case gebExpToObject codomainExp of
      Just codomain => Just $ FromInitial codomain
      _ => Nothing
  gebExpToMorphism (GAToTerminal $* [domainExp]) =
    case gebExpToObject domainExp of
      Just domain => Just $ ToTerminal domain
      _ => Nothing
  gebExpToMorphism (GAProductIntro $* [fExp, gExp]) =
    case (gebExpToMorphism fExp, gebExpToMorphism gExp) of
      (Just f, Just g) =>
        case (objectDecEq
          (morphismDomain f) (morphismDomain g)) of
            Yes domainsMatch => Just $ ProductIntro f g {domainsMatch}
            No _ => Nothing
      _ => Nothing
  gebExpToMorphism (GAProductElimLeft $* [aExp, bExp]) =
    case (gebExpToObject aExp, gebExpToObject bExp) of
      (Just a, Just b) => Just $ ProductElimLeft a b
      _ => Nothing
  gebExpToMorphism (GAProductElimRight $* [aExp, bExp]) =
    case (gebExpToObject aExp, gebExpToObject bExp) of
      (Just a, Just b) => Just $ ProductElimRight a b
      _ => Nothing
  gebExpToMorphism (GACoproductElim $* [fExp, gExp]) =
    case (gebExpToMorphism fExp, gebExpToMorphism gExp) of
      (Just f, Just g) =>
        case (objectDecEq
          (morphismCodomain f) (morphismCodomain g)) of
            Yes codomainsMatch => Just $ CoproductElim f g {codomainsMatch}
            No _ => Nothing
      _ => Nothing
  gebExpToMorphism (GACoproductIntroLeft $* [aExp, bExp]) =
    case (gebExpToObject aExp, gebExpToObject bExp) of
      (Just a, Just b) => Just $ CoproductIntroLeft a b
      _ => Nothing
  gebExpToMorphism (GACoproductIntroRight $* [aExp, bExp]) =
    case (gebExpToObject aExp, gebExpToObject bExp) of
      (Just a, Just b) => Just $ CoproductIntroRight a b
      _ => Nothing
  gebExpToMorphism (GAExpressionIntro $* [x]) =
    case gebExpToObject x of
      Just minimalObj => Just $ ExpressionIntro minimalObj
      _ => Nothing
  gebExpToMorphism (GAExpressionElim $* [exp, exp', eqExp, neqExp]) =
    case (gebExpToMorphism exp, gebExpToMorphism exp',
          gebExpToMorphism eqExp, gebExpToMorphism neqExp) of
      (Just exp, Just exp', Just eqCase, Just neqCase) =>
        case
          (objectDecEq
            (morphismDomain exp) (morphismDomain exp'),
           objectDecEq (morphismCodomain exp) ObjectExpression,
           objectDecEq
            (morphismCodomain exp) (morphismCodomain exp')) of
              (Yes domainsMatch, Yes expCodomainIsExpression,
              Yes expCodomainsMatch) =>
                case
                  (objectDecEq
                    (morphismDomain exp)
                    (morphismDomain eqCase),
                  objectDecEq
                    (morphismDomain exp)
                    (morphismDomain neqCase),
                  objectDecEq
                    (morphismCodomain eqCase)
                    (morphismCodomain neqCase)) of
                (Yes eqDomainsMatch, Yes neqDomainsMatch, Yes codomainsMatch) =>
                  Just $ ExpressionElim exp exp' eqCase neqCase
                _ => Nothing
              _ => Nothing
      _ => Nothing
  gebExpToMorphism _ = Nothing

  public export
  gebExpIsNotBothObjectAndMorphism : (x : GebSExp) ->
    (o : Object) -> (m : Morphism) ->
    gebExpToObject x = Just o -> gebExpToMorphism x = Just m ->
    Void
  gebExpIsNotBothObjectAndMorphism (GALanguage $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAMinimalReflective $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAObject $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAInitial $* _) _ _ eqo eqm =
    case eqm of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GATerminal $* _) _ _ eqo eqm =
    case eqm of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAProduct $* _) _ _ eqo eqm =
    case eqm of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GACoproduct $* _) _ _ eqo eqm =
    case eqm of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAObjectExpression $* _) _ _ eqo eqm =
    case eqm of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAMorphismExpression $* _) _ _ eqo eqm =
    case eqm of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAMorphism $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GATerm $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAUnitTerm $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAExFalsoTerm $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAMorphismTerm $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAApplication $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAFromInitial $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAToTerminal $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAIdentity $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GACompose $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAProductIntro $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAProductElimLeft $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAProductElimRight $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GACoproductElim $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GACoproductIntroLeft $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GACoproductIntroRight $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAExpressionIntro $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAExpressionElim $* _) _ _ eqo eqm =
    case eqo of Refl impossible

public export
gebObjectExpIsNotMorphism : (o : Object) ->
  gebExpToMorphism (gebObjectToExp o) = Nothing
gebObjectExpIsNotMorphism Initial = Refl
gebObjectExpIsNotMorphism Terminal = Refl
gebObjectExpIsNotMorphism (Product _ _) = Refl
gebObjectExpIsNotMorphism (Coproduct _ _) = Refl
gebObjectExpIsNotMorphism ObjectExpression = Refl
gebObjectExpIsNotMorphism (MorphismExpression _ _) = Refl

public export
gebMorphismRepresentationComplete : (r : Morphism) ->
  gebExpToMorphism (gebMorphismToExp r) = Just r
gebMorphismRepresentationComplete (Identity object) =
  rewrite gebObjectRepresentationComplete object in
  Refl
gebMorphismRepresentationComplete (Compose g f {composable}) =
  rewrite gebMorphismRepresentationComplete g in
  rewrite gebMorphismRepresentationComplete f in
  rewrite composable in
  rewrite decEqRefl objectDecEq (morphismDomain g) in
  rewrite uip composable _ in
  Refl
gebMorphismRepresentationComplete (FromInitial codomain) =
  rewrite gebObjectRepresentationComplete codomain in
  Refl
gebMorphismRepresentationComplete (ToTerminal domain) =
  rewrite gebObjectRepresentationComplete domain in
  Refl
gebMorphismRepresentationComplete (ProductIntro f g {domainsMatch}) =
  rewrite gebMorphismRepresentationComplete f in
  rewrite gebMorphismRepresentationComplete g in
  rewrite domainsMatch in
  rewrite decEqRefl objectDecEq (morphismDomain g) in
  rewrite uip domainsMatch _ in
  Refl
gebMorphismRepresentationComplete (ProductElimLeft a b) =
  rewrite gebObjectRepresentationComplete a in
  rewrite gebObjectRepresentationComplete b in
  Refl
gebMorphismRepresentationComplete (ProductElimRight a b) =
  rewrite gebObjectRepresentationComplete a in
  rewrite gebObjectRepresentationComplete b in
  Refl
gebMorphismRepresentationComplete (CoproductElim f g {codomainsMatch}) =
  rewrite gebMorphismRepresentationComplete f in
  rewrite gebMorphismRepresentationComplete g in
  rewrite codomainsMatch in
  rewrite decEqRefl objectDecEq (morphismCodomain g) in
  rewrite uip codomainsMatch _ in
  Refl
gebMorphismRepresentationComplete (CoproductIntroLeft a b) =
  rewrite gebObjectRepresentationComplete a in
  rewrite gebObjectRepresentationComplete b in
  Refl
gebMorphismRepresentationComplete (CoproductIntroRight a b) =
  rewrite gebObjectRepresentationComplete a in
  rewrite gebObjectRepresentationComplete b in
  Refl
gebMorphismRepresentationComplete (ExpressionIntro o) =
  rewrite gebObjectRepresentationComplete o in
  Refl
gebMorphismRepresentationComplete
  (ExpressionElim exp exp' eqCase neqCase
    {expDomainsMatch} {expCodomainIsExpression} {expCodomainsMatch}
    {eqDomainMatches} {neqDomainMatches} {eqCodomainsMatch}) =
      rewrite gebMorphismRepresentationComplete exp in
      rewrite gebMorphismRepresentationComplete exp' in
      rewrite gebMorphismRepresentationComplete eqCase in
      rewrite gebMorphismRepresentationComplete neqCase in
      rewrite sym expDomainsMatch in
      rewrite sym expCodomainIsExpression in
      rewrite expCodomainsMatch in
      rewrite decEqRefl objectDecEq (morphismDomain exp) in
      rewrite decEqRefl objectDecEq (morphismCodomain exp') in
      rewrite sym eqDomainMatches in
      rewrite decEqRefl objectDecEq (morphismDomain exp) in
      rewrite sym neqDomainMatches in
      rewrite decEqRefl objectDecEq (morphismDomain exp) in
      rewrite sym eqCodomainsMatch in
      rewrite decEqRefl objectDecEq (morphismCodomain eqCase) in
      rewrite uip eqCodomainsMatch _ in
      rewrite uip neqDomainMatches _ in
      rewrite uip eqDomainMatches _ in
      rewrite uip expCodomainsMatch _ in
      rewrite uip expCodomainIsExpression _ in
      rewrite uip expDomainsMatch _ in
      Refl

export
morphismDecEq : DecEqPred Morphism
morphismDecEq =
  encodingDecEq
    gebMorphismToExp
    gebExpToMorphism
    gebMorphismRepresentationComplete
    decEq

public export
gebMinimalReflectiveExpRepresentationComplete : (r : MinimalReflectiveExpression) ->
  gebExpToMinimalReflectiveExp (gebMinimalReflectiveExpressionToExp r) = Just r
gebMinimalReflectiveExpRepresentationComplete (ObjectExp o) =
  rewrite gebObjectExpIsNotMorphism o in
  rewrite gebObjectRepresentationComplete o in
  Refl
gebMinimalReflectiveExpRepresentationComplete (MorphismExp m) =
  rewrite gebMorphismExpIsNotObject m in
  rewrite gebMorphismRepresentationComplete m in
  Refl

public export
DecEq Morphism where
  decEq = morphismDecEq

public export
Eq Morphism using decEqToEq where
  (==) = (==)

public export
Show Morphism where
  show m = show (gebMorphismToExp m)

public export
minimalExpressionDecEq : DecEqPred MinimalReflectiveExpression
minimalExpressionDecEq (ObjectExp x) (ObjectExp x') =
  case decEq x x' of
    Yes Refl => Yes Refl
    No neq => No $ \eq => case eq of Refl => neq Refl
minimalExpressionDecEq (ObjectExp x) (MorphismExp x') =
  No $ \eq => case eq of Refl impossible
minimalExpressionDecEq (MorphismExp x) (ObjectExp x') =
  No $ \eq => case eq of Refl impossible
minimalExpressionDecEq (MorphismExp x) (MorphismExp x') =
  case decEq x x' of
    Yes Refl => Yes Refl
    No neq => No $ \eq => case eq of Refl => neq Refl

public export
DecEq MinimalReflectiveExpression where
  decEq = minimalExpressionDecEq

public export
Eq MinimalReflectiveExpression using decEqToEq where
  (==) = (==)

-----------------------------------------------------------------------------
---- The interpretation into Idris-2 of the minimal programming language ----
-----------------------------------------------------------------------------

public export
interpretObject : Object -> Type
interpretObject Initial = Void
interpretObject Terminal = ()
interpretObject (Product r r') =
  (interpretObject r, interpretObject r')
interpretObject (Coproduct r r') =
  Either (interpretObject r) (interpretObject r')
interpretObject ObjectExpression = Object
interpretObject (MorphismExpression domain codomain) =
  (m : Morphism **
   (morphismDomain m = domain, morphismCodomain m = codomain))

public export
interpretMorphismDomain : Morphism -> Type
interpretMorphismDomain r =
  interpretObject (morphismDomain r)

public export
interpretMorphismCodomain : Morphism -> Type
interpretMorphismCodomain r =
  interpretObject (morphismCodomain r)

public export
interpretMorphismType : Morphism -> Type
interpretMorphismType r =
  interpretMorphismDomain r -> interpretMorphismCodomain r

public export
interpretMorphism : (r : Morphism) ->
  interpretMorphismType r
interpretMorphism (Identity o) x = x
interpretMorphism (Compose g f {composable}) x =
  interpretMorphism g $
    replace {p=interpretObject} composable $
      interpretMorphism f x
interpretMorphism (FromInitial _) x = void x
interpretMorphism (ToTerminal _) _ = ()
interpretMorphism (ProductIntro f g {domainsMatch}) x =
  (interpretMorphism f x,
   interpretMorphism g (rewrite sym domainsMatch in x))
interpretMorphism (ProductElimLeft a b) x = fst x
interpretMorphism (ProductElimRight a b) x = snd x
interpretMorphism (CoproductElim f g {codomainsMatch}) x =
  case x of
    Left x' => interpretMorphism f x'
    Right x' => rewrite codomainsMatch in interpretMorphism g x'
interpretMorphism (CoproductIntroLeft a b) x = Left x
interpretMorphism (CoproductIntroRight a b) x = Right x
interpretMorphism (ExpressionIntro exp) () = exp
interpretMorphism (ExpressionElim exp exp' eqCase neqCase
  {expDomainsMatch} {expCodomainIsExpression} {expCodomainsMatch}
  {eqDomainMatches} {neqDomainMatches} {eqCodomainsMatch}) x =
    let
      y = interpretMorphism exp x
      y' = replace {p=interpretObject} expCodomainIsExpression y
      z = interpretMorphism exp' (rewrite sym expDomainsMatch in x)
      z' = replace {p=interpretObject} (sym expCodomainsMatch) z
      z'' = replace {p=interpretObject} expCodomainIsExpression z'
    in
    if y' == z'' then
      interpretMorphism eqCase (rewrite sym eqDomainMatches in x)
    else
      rewrite eqCodomainsMatch in
      interpretMorphism neqCase (rewrite sym neqDomainMatches in x)

-----------------------------------
---- Correctness of reflection ----
-----------------------------------

public export
objectQuote : Object -> interpretObject ObjectExpression
objectQuote = Prelude.id

public export
objectUnquote : interpretObject ObjectExpression -> Object
objectUnquote = Prelude.id

export
objectUnquoteQuoteCorrect : (r : Object) ->
  objectUnquote (objectQuote r) = r
objectUnquoteQuoteCorrect r = Refl

------------------------------------------------------
---- Morphism transformations ("compiler passes") ----
------------------------------------------------------

public export
MorphismTransform : Type
MorphismTransform = Morphism -> Morphism

-- | A correct morphism transformation preserves the morphism's domain.
public export
MorphismTransformDomainCorrect : MorphismTransform -> Type
MorphismTransformDomainCorrect transform = (m : Morphism) ->
  interpretMorphismDomain (transform m) =
    interpretMorphismDomain m

-- | A correct morphism transformation preserves the morphism's codomain.
public export
MorphismTransformCodomainCorrect : MorphismTransform -> Type
MorphismTransformCodomainCorrect transform = (m : Morphism) ->
  interpretMorphismCodomain (transform m) =
    interpretMorphismCodomain m

-- | A correct morphism transformation preserves extensional equality.
public export
MorphismTransformCorrect : (transform : MorphismTransform) ->
  (domainTransformCorrect :
    MorphismTransformDomainCorrect transform) ->
  (codomainTransformCorrect :
    MorphismTransformCodomainCorrect transform) ->
  Type
MorphismTransformCorrect
  transform domainTransformCorrect codomainTransformCorrect =
    (m : Morphism) ->
    (x : interpretMorphismDomain m) ->
      (rewrite sym (codomainTransformCorrect m) in
       interpretMorphism (transform m)
         (rewrite domainTransformCorrect m in x)) =
       interpretMorphism m x

------------------------------------------------------------
---- Term reduction in the minimal programming language ----
------------------------------------------------------------

-- | Terms are used to define operational semantics for the category-theoretical
-- | representations of programming languages.  We have a well-typed
-- | representation of terms in Idris defined by the interpretation of objects
-- | as types -- together with the notion of function application, which we
-- | do not have in the category-theoretical representation.

public export
data MinimalReflectiveTermType : Type where
  MinimalReflectiveTypeTerm : (type : Object) -> MinimalReflectiveTermType
  MorphismTerm : (domain, codomain : Object) -> MinimalReflectiveTermType

public export
data MinimalReflectiveTerm : (numApplications : Nat) -> MinimalReflectiveTermType -> Type where
  UnappliedMorphismTerm : (morphism : Morphism) ->
    MinimalReflectiveTerm 0 $
      MorphismTerm
        (morphismDomain morphism)
        (morphismCodomain morphism)
  Application : {morphismApplications, termApplications : Nat} ->
    {domain, codomain : Object} ->
    MinimalReflectiveTerm morphismApplications (MorphismTerm domain codomain) ->
    MinimalReflectiveTerm termApplications (MinimalReflectiveTypeTerm domain) ->
    MinimalReflectiveTerm
      (S $ morphismApplications + termApplications) (MinimalReflectiveTypeTerm codomain)
  ExFalsoTerm : {numApplications : Nat} -> {type : Object} ->
    MinimalReflectiveTerm numApplications (MinimalReflectiveTypeTerm Initial) ->
    MinimalReflectiveTerm numApplications $ MinimalReflectiveTypeTerm type
  UnitTerm : MinimalReflectiveTerm 0 $ MinimalReflectiveTypeTerm Terminal
  PairTerm : {leftApplications, rightApplications : Nat} ->
    {left, right : Object} ->
    MinimalReflectiveTerm leftApplications (MinimalReflectiveTypeTerm left) ->
    MinimalReflectiveTerm rightApplications (MinimalReflectiveTypeTerm right) ->
    MinimalReflectiveTerm (leftApplications + rightApplications) $
      MinimalReflectiveTypeTerm $ Product left right
  MinimalReflectiveLeft :
    {leftApplications : Nat} -> {left : Object} ->
    MinimalReflectiveTerm leftApplications (MinimalReflectiveTypeTerm left) ->
    (right : Object) ->
    MinimalReflectiveTerm leftApplications $ MinimalReflectiveTypeTerm $ Coproduct left right
  MinimalReflectiveRight :
    (left : Object) ->
    {rightApplications : Nat} -> {right : Object} ->
    MinimalReflectiveTerm rightApplications (MinimalReflectiveTypeTerm right) ->
    MinimalReflectiveTerm rightApplications $ MinimalReflectiveTypeTerm $ Coproduct left right
  ExpressionTerm : Object ->
    MinimalReflectiveTerm 0 $ MinimalReflectiveTypeTerm $ ObjectExpression

public export
MinimalReflectiveFullyAppliedTerm : MinimalReflectiveTermType -> Type
MinimalReflectiveFullyAppliedTerm = MinimalReflectiveTerm 0

public export
gebMinimalReflectiveTermToExp : {type: MinimalReflectiveTermType} -> {numApplications : Nat} ->
  MinimalReflectiveTerm numApplications type -> GebSExp
gebMinimalReflectiveTermToExp (Application f x) =
  GAApplication $* [gebMinimalReflectiveTermToExp f, gebMinimalReflectiveTermToExp x]
gebMinimalReflectiveTermToExp (UnappliedMorphismTerm morphism) =
  GAMorphismTerm $* [gebMorphismToExp morphism]
gebMinimalReflectiveTermToExp {type=(MinimalReflectiveTypeTerm type)} (ExFalsoTerm ti) =
  GAExFalsoTerm $* [gebMinimalReflectiveTermToExp ti, gebObjectToExp type]
gebMinimalReflectiveTermToExp UnitTerm = $^ GAUnitTerm
gebMinimalReflectiveTermToExp
  (PairTerm {leftApplications} {rightApplications} {left} {right}
   leftTerm rightTerm) =
    GAPairTerm $* [gebMinimalReflectiveTermToExp leftTerm, gebMinimalReflectiveTermToExp rightTerm]
gebMinimalReflectiveTermToExp {numApplications} (MinimalReflectiveLeft left right) =
  GALeftTerm $* [gebMinimalReflectiveTermToExp left, gebObjectToExp right]
gebMinimalReflectiveTermToExp {numApplications} (MinimalReflectiveRight left right) =
  GARightTerm $* [gebObjectToExp left, gebMinimalReflectiveTermToExp right]
gebMinimalReflectiveTermToExp (ExpressionTerm x) =
  GAExpressionTerm $* [gebObjectToExp x]

public export
gebExpToMinimalReflectiveTerm :
  GebSExp -> Maybe (type : MinimalReflectiveTermType ** n : Nat ** MinimalReflectiveTerm n type)
gebExpToMinimalReflectiveTerm (GAMorphismTerm $* [x]) =
  case gebExpToMorphism x of
    Just morphism => Just
      (MorphismTerm
        (morphismDomain morphism)
        (morphismCodomain morphism) **
       0 **
       (UnappliedMorphismTerm morphism))
    Nothing => Nothing
gebExpToMinimalReflectiveTerm (GAExFalsoTerm $* [ti, ty]) =
  case (gebExpToMinimalReflectiveTerm ti, gebExpToObject ty) of
    (Just (MinimalReflectiveTypeTerm Initial ** n ** initialTerm), Just type) =>
      Just (MinimalReflectiveTypeTerm type ** n ** ExFalsoTerm initialTerm)
    _ => Nothing
gebExpToMinimalReflectiveTerm (GAUnitTerm $* []) =
  Just (MinimalReflectiveTypeTerm Terminal ** 0 ** UnitTerm)
gebExpToMinimalReflectiveTerm (GAPairTerm $* [left, right]) with
  (gebExpToMinimalReflectiveTerm left, gebExpToMinimalReflectiveTerm right)
    gebExpToMinimalReflectiveTerm (GAPairTerm $* [left, right]) |
      (Just (MinimalReflectiveTypeTerm leftObject ** nLeft ** leftTerm),
       Just (MinimalReflectiveTypeTerm rightObject ** nRight ** rightTerm)) =
        Just
          (MinimalReflectiveTypeTerm (Product leftObject rightObject) **
           nLeft + nRight **
           (PairTerm leftTerm rightTerm))
    gebExpToMinimalReflectiveTerm (GAPairTerm $* [left, right]) |
      _ = Nothing
gebExpToMinimalReflectiveTerm (GAApplication $* [fExp, xExp]) =
  case (gebExpToMinimalReflectiveTerm fExp, gebExpToMinimalReflectiveTerm xExp) of
    (Just (fType ** nLeft ** f), Just (xType ** nRight ** x)) =>
      case fType of
        MorphismTerm domain codomain =>
          case xType of
            MinimalReflectiveTypeTerm domain' => case decEq domain domain' of
              Yes Refl =>
                Just
                  (MinimalReflectiveTypeTerm codomain **
                   S (nLeft + nRight) **
                   Application f x)
              No _ => Nothing
            _ => Nothing
        _ => Nothing
    _ => Nothing
gebExpToMinimalReflectiveTerm (GAExpressionTerm $* [exp]) = gebExpToMinimalReflectiveTerm exp
gebExpToMinimalReflectiveTerm (GALeftTerm $* [leftExp, rightExp]) =
  case (gebExpToMinimalReflectiveTerm leftExp, gebExpToObject rightExp) of
    (Just (MinimalReflectiveTypeTerm leftObject ** nLeft ** leftTerm),
     Just rightObject) =>
      Just
        (MinimalReflectiveTypeTerm (Coproduct leftObject rightObject) **
         nLeft **
         MinimalReflectiveLeft leftTerm rightObject)
    _ => Nothing
gebExpToMinimalReflectiveTerm (GARightTerm $* [leftExp, rightExp]) =
  case (gebExpToObject leftExp, gebExpToMinimalReflectiveTerm rightExp) of
    (Just leftObject,
     Just (MinimalReflectiveTypeTerm rightObject ** nRight ** rightTerm)) =>
      Just
        (MinimalReflectiveTypeTerm (Coproduct leftObject rightObject) **
         nRight **
         MinimalReflectiveRight leftObject rightTerm)
    _ => Nothing
gebExpToMinimalReflectiveTerm _ = Nothing

public export
gebMinimalReflectiveTermRepresentationComplete :
  {type : MinimalReflectiveTermType} -> {numApplications : Nat} ->
  (term : MinimalReflectiveTerm numApplications type) ->
  gebExpToMinimalReflectiveTerm
    (gebMinimalReflectiveTermToExp {type} {numApplications} term) =
      Just (type ** numApplications ** term)
gebMinimalReflectiveTermRepresentationComplete (Application {domain} f x) =
  rewrite gebMinimalReflectiveTermRepresentationComplete f in
  rewrite gebMinimalReflectiveTermRepresentationComplete x in
  rewrite decEqRefl objectDecEq domain in
  Refl
gebMinimalReflectiveTermRepresentationComplete
  (UnappliedMorphismTerm morphism) =
    rewrite gebMorphismRepresentationComplete morphism in
    Refl
gebMinimalReflectiveTermRepresentationComplete (ExFalsoTerm ti) =
  let tiComplete = gebMinimalReflectiveTermRepresentationComplete ti in
  gebMinimalReflectiveTermRepresentationComplete_hole_exfalso
gebMinimalReflectiveTermRepresentationComplete UnitTerm =
  Refl
gebMinimalReflectiveTermRepresentationComplete (PairTerm left right) =
  gebMinimalReflectiveTermRepresentationComplete_hole_pair
gebMinimalReflectiveTermRepresentationComplete
  (MinimalReflectiveLeft left right) =
    gebMinimalReflectiveTermRepresentationComplete_hole_left
gebMinimalReflectiveTermRepresentationComplete
  (MinimalReflectiveRight left right) =
    gebMinimalReflectiveTermRepresentationComplete_hole_right
gebMinimalReflectiveTermRepresentationComplete (ExpressionTerm x) =
  gebMinimalReflectiveTermRepresentationComplete_hole_expression

public export
(type : MinimalReflectiveTermType) => (n : Nat) => Show (MinimalReflectiveTerm n type) where
  show term = show (gebMinimalReflectiveTermToExp term)

public export
interpretMinimalReflectiveTermType : MinimalReflectiveTermType -> Type
interpretMinimalReflectiveTermType (MinimalReflectiveTypeTerm type) = interpretObject type
interpretMinimalReflectiveTermType (MorphismTerm domain codomain) =
  interpretObject domain -> interpretObject codomain

public export
interpretMinimalReflectiveTerm : {type : MinimalReflectiveTermType} -> {numApplications : Nat} ->
  (term : MinimalReflectiveTerm numApplications type) -> interpretMinimalReflectiveTermType type
interpretMinimalReflectiveTerm (Application f x) =
  interpretMinimalReflectiveTerm f $ interpretMinimalReflectiveTerm x
interpretMinimalReflectiveTerm (UnappliedMorphismTerm morphism) =
  interpretMorphism morphism
interpretMinimalReflectiveTerm (ExFalsoTerm v) = void $ interpretMinimalReflectiveTerm v
interpretMinimalReflectiveTerm UnitTerm = ()
interpretMinimalReflectiveTerm (PairTerm left right) =
  (interpretMinimalReflectiveTerm left, interpretMinimalReflectiveTerm right)
interpretMinimalReflectiveTerm (MinimalReflectiveLeft left right) =
  Left $ interpretMinimalReflectiveTerm left
interpretMinimalReflectiveTerm (MinimalReflectiveRight left right) =
  Right $ interpretMinimalReflectiveTerm right
interpretMinimalReflectiveTerm (ExpressionTerm x) = x

public export
gebNoExFalsoTerm : {numApplications : Nat} ->
  (ti : MinimalReflectiveTerm numApplications (MinimalReflectiveTypeTerm Initial)) ->
  Void
gebNoExFalsoTerm ti = void $ interpretMinimalReflectiveTerm ti

-- | A correct morphism transformation preserves the interpretation of
-- | term application.
public export
correctMorphismTransformPreservesTermInterpretation :
  (transform : MorphismTransform) ->
  {domainTransformCorrect :
    MorphismTransformDomainCorrect transform} ->
  {codomainTransformCorrect :
    MorphismTransformCodomainCorrect transform} ->
  MorphismTransformCorrect
    transform domainTransformCorrect codomainTransformCorrect ->
  (m : Morphism) ->
  {numApplications : Nat} ->
  (term :
    MinimalReflectiveTerm numApplications
      (MinimalReflectiveTypeTerm (morphismDomain m))) ->
  (term' :
    MinimalReflectiveTerm numApplications
      (MinimalReflectiveTypeTerm (morphismDomain (transform m)))) ->
  interpretMinimalReflectiveTerm term =
    (rewrite sym (domainTransformCorrect m) in (interpretMinimalReflectiveTerm term')) ->
  interpretMinimalReflectiveTerm
    (Application (UnappliedMorphismTerm m) term) =
  (rewrite sym (codomainTransformCorrect m) in (interpretMinimalReflectiveTerm
    (Application (UnappliedMorphismTerm (transform m)) term')))
correctMorphismTransformPreservesTermInterpretation
  transform transformCorrect m {numApplications} term term' termEq =
    correctMorphismTransformPreservesTermInterpretation_hole

public export
bigStepMorphismReduction :
  (m : Morphism) ->
  MinimalReflectiveFullyAppliedTerm (MinimalReflectiveTypeTerm (morphismDomain m)) ->
  MinimalReflectiveFullyAppliedTerm (MinimalReflectiveTypeTerm (morphismCodomain m))
bigStepMorphismReduction (Identity _) x = x
bigStepMorphismReduction (Compose g f {composable}) x =
  bigStepMorphismReduction g $
    rewrite sym composable in (bigStepMorphismReduction f x)
bigStepMorphismReduction (FromInitial _) x = ExFalsoTerm x
bigStepMorphismReduction (ToTerminal y) x = UnitTerm
bigStepMorphismReduction (ProductIntro f g {domainsMatch}) x =
  PairTerm
    (bigStepMorphismReduction f x)
    (bigStepMorphismReduction g $ rewrite sym domainsMatch in x)
bigStepMorphismReduction (ProductElimLeft a b) x = case x of
  PairTerm {leftApplications=0} {rightApplications=0} left right => left
  ExFalsoTerm ti => ExFalsoTerm ti
bigStepMorphismReduction (ProductElimRight a b) x = case x of
  PairTerm {leftApplications=0} {rightApplications=0} left right => right
  ExFalsoTerm ti => ExFalsoTerm ti
bigStepMorphismReduction (CoproductElim f g {codomainsMatch}) x =
  case x of
    MinimalReflectiveLeft left _ =>
      bigStepMorphismReduction f left
    MinimalReflectiveRight _ right =>
      rewrite codomainsMatch in bigStepMorphismReduction g right
    ExFalsoTerm ti => ExFalsoTerm ti
bigStepMorphismReduction (CoproductIntroLeft left right) x =
  MinimalReflectiveLeft x right
bigStepMorphismReduction (CoproductIntroRight left right) x =
  MinimalReflectiveRight left x
bigStepMorphismReduction (ExpressionIntro exp) _ = ExpressionTerm exp
bigStepMorphismReduction (ExpressionElim exp exp' eqCase neqCase
  {expDomainsMatch} {expCodomainIsExpression} {expCodomainsMatch}
  {eqDomainMatches} {neqDomainMatches} {eqCodomainsMatch}) x =
    let
      xReduced = bigStepMorphismReduction exp x
      xReduced' = bigStepMorphismReduction exp'
        (rewrite sym expDomainsMatch in x)
      xReducedRewritten =
        replace {p=(MinimalReflectiveTerm 0 . MinimalReflectiveTypeTerm)}
          expCodomainIsExpression xReduced
      xReducedRewritten' =
        replace {p=(MinimalReflectiveTerm 0 . MinimalReflectiveTypeTerm)}
          expCodomainIsExpression (rewrite expCodomainsMatch in xReduced')
      xInterpreted = interpretMinimalReflectiveTerm xReducedRewritten
      xInterpreted' = interpretMinimalReflectiveTerm xReducedRewritten'
      eqCaseReduced =
        bigStepMorphismReduction
          eqCase (rewrite sym eqDomainMatches in x)
      eqCaseReduced' =
        bigStepMorphismReduction
          neqCase (rewrite sym neqDomainMatches in x)
    in
    if xInterpreted == xInterpreted' then
      eqCaseReduced else
    (replace {p=(MinimalReflectiveTerm 0. MinimalReflectiveTypeTerm)}
      (sym eqCodomainsMatch) eqCaseReduced')

public export
bigStepMinimalReflectiveTermReduction :
  {type : MinimalReflectiveTermType} -> {numApplications : Nat} ->
  MinimalReflectiveTerm numApplications type ->
  MinimalReflectiveFullyAppliedTerm type
bigStepMinimalReflectiveTermReduction (Application f x) with
  (bigStepMinimalReflectiveTermReduction f, bigStepMinimalReflectiveTermReduction x)
    bigStepMinimalReflectiveTermReduction (Application f x) |
      (UnappliedMorphismTerm m, xReduced) =
        bigStepMorphismReduction m xReduced
bigStepMinimalReflectiveTermReduction (UnappliedMorphismTerm m) = UnappliedMorphismTerm m
bigStepMinimalReflectiveTermReduction (ExFalsoTerm ti) =
  ExFalsoTerm $ bigStepMinimalReflectiveTermReduction ti
bigStepMinimalReflectiveTermReduction UnitTerm = UnitTerm
bigStepMinimalReflectiveTermReduction (PairTerm left right) =
  PairTerm
    (bigStepMinimalReflectiveTermReduction left)
    (bigStepMinimalReflectiveTermReduction right)
bigStepMinimalReflectiveTermReduction (MinimalReflectiveLeft left right) =
  MinimalReflectiveLeft (bigStepMinimalReflectiveTermReduction left) right
bigStepMinimalReflectiveTermReduction (MinimalReflectiveRight left right) =
  MinimalReflectiveRight left (bigStepMinimalReflectiveTermReduction right)
bigStepMinimalReflectiveTermReduction (ExpressionTerm x) = ExpressionTerm x

mutual
  public export
  bigStepMorphismReductionCorrect :
    (m : Morphism) ->
    (x : MinimalReflectiveFullyAppliedTerm (MinimalReflectiveTypeTerm (morphismDomain m))) ->
    interpretMinimalReflectiveTerm (bigStepMorphismReduction m x) =
      interpretMinimalReflectiveTerm (UnappliedMorphismTerm m) (interpretMinimalReflectiveTerm x)
  bigStepMorphismReductionCorrect m x =
    bigStepMorphismReductionCorrect_hole

  public export
  bigStepMinimalReflectiveTermReductionCorrect :
    {type : MinimalReflectiveTermType} -> {numApplications : Nat} ->
    (term : MinimalReflectiveTerm numApplications type) ->
    interpretMinimalReflectiveTerm (bigStepMinimalReflectiveTermReduction term) =
      interpretMinimalReflectiveTerm term
  bigStepMinimalReflectiveTermReductionCorrect {type} term =
    bigStepMinimalReflectiveTermReductionCorrect_hole

public export
smallStepMorphismReduction :
  (m : Morphism) ->
  {numApplications : Nat} ->
  MinimalReflectiveTerm numApplications (MinimalReflectiveTypeTerm (morphismDomain m)) ->
  (remainingApplications : Nat **
   MinimalReflectiveTerm
    remainingApplications (MinimalReflectiveTypeTerm (morphismCodomain m)))
smallStepMorphismReduction (Identity x) term =
  smallStepMorphismReduction_hole_ident
smallStepMorphismReduction (Compose g f) term =
  smallStepMorphismReduction_hole_compose
smallStepMorphismReduction (FromInitial x) term =
  smallStepMorphismReduction_hole_frominit
smallStepMorphismReduction (ToTerminal x) term =
  smallStepMorphismReduction_hole_toterm
smallStepMorphismReduction (ProductIntro f g) term =
  smallStepMorphismReduction_hole_prodintro
smallStepMorphismReduction (ProductElimLeft a b) term =
  smallStepMorphismReduction_hole_prodleft
smallStepMorphismReduction (ProductElimRight a b) term =
  smallStepMorphismReduction_hole_prodright
smallStepMorphismReduction (CoproductElim f g) term =
  smallStepMorphismReduction_hole_coelim
smallStepMorphismReduction (CoproductIntroLeft a b) term =
  smallStepMorphismReduction_hole_cointroleft
smallStepMorphismReduction (CoproductIntroRight a b) term =
  smallStepMorphismReduction_hole_cointroright
smallStepMorphismReduction (ExpressionIntro x) term =
  smallStepMorphismReduction_hole_expIntro
smallStepMorphismReduction
  (ExpressionElim exp exp' eqCase neqCase) term =
    smallStepMorphismReduction_hole_expElim

public export
smallStepMinimalReflectiveTermReduction :
  {type : MinimalReflectiveTermType} -> {numApplications : Nat} ->
  MinimalReflectiveTerm numApplications type ->
  (remainingApplications : Nat ** MinimalReflectiveTerm remainingApplications type)
smallStepMinimalReflectiveTermReduction (UnappliedMorphismTerm morphism) =
  smallStepMinimalReflectiveTermReduction_hole_unapplied
smallStepMinimalReflectiveTermReduction (Application x y) =
  smallStepMinimalReflectiveTermReduction_hole_app
smallStepMinimalReflectiveTermReduction (ExFalsoTerm ti) =
  smallStepMinimalReflectiveTermReduction_hole_exfalso
smallStepMinimalReflectiveTermReduction UnitTerm =
  smallStepMinimalReflectiveTermReduction_hole_unit
smallStepMinimalReflectiveTermReduction (PairTerm x y) =
  smallStepMinimalReflectiveTermReduction_hole_pair
smallStepMinimalReflectiveTermReduction (MinimalReflectiveLeft x right) =
  smallStepMinimalReflectiveTermReduction_hole_left
smallStepMinimalReflectiveTermReduction (MinimalReflectiveRight left x) =
  smallStepMinimalReflectiveTermReduction_hole_right
smallStepMinimalReflectiveTermReduction (ExpressionTerm x) =
  smallStepMinimalReflectiveTermReduction_hole_exp

public export
data SmallStepMinimalReflectiveTermReductionCompletes :
  {type : MinimalReflectiveTermType} -> {numApplications : Nat} ->
  (term : MinimalReflectiveTerm numApplications type) ->
  (reduced : MinimalReflectiveFullyAppliedTerm type) -> Type
  where
    SmallStepMinimalReflectiveReductionLastStep :
      {type : MinimalReflectiveTermType} -> {numApplications : Nat} ->
      {term : MinimalReflectiveTerm numApplications type} ->
      {reduced : MinimalReflectiveFullyAppliedTerm type} ->
      smallStepMinimalReflectiveTermReduction term = Left reduced ->
      SmallStepMinimalReflectiveTermReductionCompletes term reduced
    SmallStepMinimalReflectiveReductionPreviousStep :
      {type : MinimalReflectiveTermType} ->
      {numApplications, intermediateNumApplications : Nat} ->
      {term : MinimalReflectiveTerm numApplications type} ->
      {intermediateTerm : MinimalReflectiveTerm intermediateNumApplications type} ->
      {reduced : MinimalReflectiveFullyAppliedTerm type} ->
      smallStepMinimalReflectiveTermReduction term = Right intermediateTerm ->
      SmallStepMinimalReflectiveTermReductionCompletes intermediateTerm reduced ->
      SmallStepMinimalReflectiveTermReductionCompletes term reduced

public export
smallStepMinimalReflectiveTermReductionCompletes :
  {type : MinimalReflectiveTermType} -> {numApplications : Nat} ->
  (term : MinimalReflectiveTerm numApplications type) ->
  DPair
    (MinimalReflectiveFullyAppliedTerm type)
    (SmallStepMinimalReflectiveTermReductionCompletes term)
smallStepMinimalReflectiveTermReductionCompletes {type} term =
  smallStepMinimalReflectiveTermReductionCompletes_hole

public export
smallStepMinimalReflectiveTermReductionCorrect :
  {type : MinimalReflectiveTermType} -> {numApplications : Nat} ->
  (term : MinimalReflectiveTerm numApplications type) ->
  interpretMinimalReflectiveTerm
    (fst (smallStepMinimalReflectiveTermReductionCompletes term)) =
      interpretMinimalReflectiveTerm term
smallStepMinimalReflectiveTermReductionCorrect {type} term =
  smallStepMinimalReflectiveTermReductionCorrect_hole

public export
minimalTermReductionsConsistent :
  {type : MinimalReflectiveTermType} -> {numApplications : Nat} ->
  (term : MinimalReflectiveTerm numApplications type) ->
  bigStepMinimalReflectiveTermReduction term =
    snd (smallStepMinimalReflectiveTermReductionCompletes term)
minimalTermReductionsConsistent term = minimalTermReductionsConsistent_hole

-}

---------------------------------------------------------------------------
---- Work for after self-hosting: parameterized user-defined languages ----
---------------------------------------------------------------------------

public export
data LanguageSort : Type where
  LogicSort : LanguageSort
  MachineSort : LanguageSort
  GeneralSort : LanguageSort

public export
data Kind : Type where
  KStar : LanguageSort -> Kind
  KArrow : Kind -> Kind -> Kind

public export
data ParameterizedLanguage : Kind -> Type where
  ParameterizedMinimalReflective : ParameterizedLanguage (KStar LogicSort)
  ParameterizedHigherOrder : ParameterizedLanguage (KStar LogicSort)
