module Category.Composition

import public Library.FunctionsAndRelations
import RefinedSExp.List
import Library.Decidability

%default total

namespace
FreeCategories
    public export
    Morphism : Type -> Type
    Morphism = BinaryPredicate

    public export
    Signature : Type -> Type
    Signature = PairOf

    public export
    data
    GeneratedMorphism : {object : Type} ->
            (morphism : Morphism object) -> (signature : Signature object) ->
            Type where

        GeneratedIdentity :
            {object : Type} -> {morphism : Morphism object} ->
            {domain_and_codomain : object} ->
            GeneratedMorphism morphism
                (domain_and_codomain, domain_and_codomain)

        GeneratedComposition :
            {object : Type} -> {morphism : Morphism object} ->
            {head_domain_and_tail_codomain, head_codomain : object} ->
            (head_morphism : morphism
                (head_domain_and_tail_codomain, head_codomain)) ->
            {tail_domain : object} ->
            (tail_morphism : GeneratedMorphism morphism
                (tail_domain, head_domain_and_tail_codomain)) ->
            GeneratedMorphism morphism
                (tail_domain, head_codomain)

    public export
    SignedMorphism : {object : Type} -> Morphism object -> Type
    SignedMorphism {object} morphism = DPair (Signature object) morphism

    public export
    GeneratorList : {object : Type} -> Morphism object -> Type
    GeneratorList morphism = List (SignedMorphism morphism)

    morphismGenerators : {object : Type} ->
        {morphism : Morphism object} -> {signature : Signature object} ->
        GeneratedMorphism morphism signature ->
        GeneratorList morphism
    morphismGenerators GeneratedIdentity = []
    morphismGenerators (GeneratedComposition head_morphism tail_morphism) =
        (_ ** head_morphism) :: morphismGenerators tail_morphism

    generatorsDetermineMorphism : {object : Type} ->
        {morphism : Morphism object} -> {signature : Signature object} ->
        (m, m' : GeneratedMorphism morphism signature) ->
        morphismGenerators m = morphismGenerators m' ->
        m = m'
    generatorsDetermineMorphism
        GeneratedIdentity GeneratedIdentity Refl =
            Refl
    generatorsDetermineMorphism
        GeneratedIdentity (GeneratedComposition left' right') Refl
            impossible
    generatorsDetermineMorphism
        (GeneratedComposition left right) GeneratedIdentity Refl
            impossible
    generatorsDetermineMorphism
        (GeneratedComposition left right) (GeneratedComposition left' right')
        generatorsEqual =
            let (headEqual, tailEqual) = consInjective generatorsEqual in
            case headEqual of
                Refl => rewrite
                    generatorsDetermineMorphism right right' tailEqual in Refl

    public export
    generatorListDomain : {object : Type} -> {morphism : Morphism object} ->
        SignedMorphism morphism -> GeneratorList morphism ->
        object
    generatorListDomain ((domain, codomain) ** first) [] = domain
    generatorListDomain (signature ** first) (second :: tail) =
        generatorListDomain second tail

    public export
    generatorListCodomain : {object : Type} -> {morphism : Morphism object} ->
        SignedMorphism morphism -> GeneratorList morphism ->
        object
    generatorListCodomain ((domain, codomain) ** head) tail = codomain

    public export
    generatorListSignature : {object : Type} -> {morphism : Morphism object} ->
        SignedMorphism morphism -> GeneratorList morphism ->
        Signature object
    generatorListSignature head tail =
        (generatorListDomain head tail, generatorListCodomain head tail)

    public export
    composeGenerated : {object : Type} -> {morphism : Morphism object} ->
        {left_domain_and_right_codomain, left_codomain : object} ->
        (left_morphism : GeneratedMorphism morphism
            (left_domain_and_right_codomain, left_codomain)) ->
        {right_domain : object} ->
        (right_morphism : GeneratedMorphism morphism
            (right_domain, left_domain_and_right_codomain)) ->
        GeneratedMorphism morphism
            (right_domain, left_codomain)
    composeGenerated GeneratedIdentity right_morphism =
        right_morphism
    composeGenerated
        (GeneratedComposition left_head_morphism left_tail_morphism)
        right_morphism =
            GeneratedComposition
                left_head_morphism
                (composeGenerated left_tail_morphism right_morphism)

    infixr 15 ^<~
    public export
    (^<~) :
        {object : Type} -> {morphism : Morphism object} ->
        {head_domain_and_tail_codomain, head_codomain : object} ->
        (head_morphism : morphism
            (head_domain_and_tail_codomain, head_codomain)) ->
        {tail_domain : object} ->
        (tail_morphism : GeneratedMorphism morphism
            (tail_domain, head_domain_and_tail_codomain)) ->
        GeneratedMorphism morphism
            (tail_domain, head_codomain)
    (^<~) = GeneratedComposition

    public export
    (^~^) : {object : Type} -> {morphism : Morphism object} ->
        {domain, codomain : object} ->
        (head : morphism (domain, codomain)) ->
        GeneratedMorphism morphism (domain, codomain)
    (^~^) head = head ^<~ GeneratedIdentity

    infixr 16 ^<~^
    public export
    (^<~^) :
        {object : Type} -> {morphism : Morphism object} ->
        {head_domain_and_tail_codomain, head_codomain : object} ->
        (head_morphism : morphism
            (head_domain_and_tail_codomain, head_codomain)) ->
        {tail_domain : object} ->
        (tail_morphism : morphism
            (tail_domain, head_domain_and_tail_codomain)) ->
        GeneratedMorphism morphism
            (tail_domain, head_codomain)
    (^<~^) head_morphism tail_morphism = head_morphism ^<~ (^~^) tail_morphism

    infixl 14 <~
    public export
    (<~) :
        {object : Type} -> {morphism : Morphism object} ->
        {left_domain_and_right_codomain, left_codomain : object} ->
        (left_morphism : GeneratedMorphism morphism
            (left_domain_and_right_codomain, left_codomain)) ->
        {right_domain : object} ->
        (right_morphism : GeneratedMorphism morphism
            (right_domain, left_domain_and_right_codomain)) ->
        GeneratedMorphism morphism
            (right_domain, left_codomain)
    (<~) = composeGenerated

    compositionListAppend : {object : Type} -> {morphism : Morphism object} ->
        {left_domain_and_right_codomain, left_codomain : object} ->
        (left_morphism : GeneratedMorphism morphism
            (left_domain_and_right_codomain, left_codomain)) ->
        {right_domain : object} ->
        (right_morphism : GeneratedMorphism morphism
            (right_domain, left_domain_and_right_codomain)) ->
        morphismGenerators (left_morphism <~ right_morphism) =
            morphismGenerators left_morphism ++
            morphismGenerators right_morphism
    compositionListAppend GeneratedIdentity right_morphism = Refl
    compositionListAppend
        (GeneratedComposition left_head_morphism left_tail_morphism)
        right_morphism =
            rewrite (compositionListAppend left_tail_morphism right_morphism) in
            Refl

    composeAssociative :
        {object : Type} -> {morphism : Morphism object} ->
        {a, b, c, d : object} ->
        (h : GeneratedMorphism morphism (c, d)) ->
        (g : GeneratedMorphism morphism (b, c)) ->
        (f : GeneratedMorphism morphism (a, b)) ->
        h <~ (g <~ f) = (h <~ g) <~ f
    composeAssociative h g f =
        let
            hg_generators = compositionListAppend h g
            gf_generators = compositionListAppend g f
            left_generators = compositionListAppend h (g <~ f)
            right_generators = compositionListAppend (h <~ g) f
        in
        generatorsDetermineMorphism _ _
            (trans left_generators
                (trans (rewrite gf_generators in rewrite hg_generators in
                    (appendAssociative _ _ _)) (sym right_generators)))

    public export
    foldMorphism : {object : Type} ->
        {morphism : Morphism object} ->
        {predicate : (signature : Signature object) ->
            GeneratedMorphism morphism signature -> Type} ->
        (predicateIdentity : {domain_and_codomain : object} ->
            predicate (domain_and_codomain, domain_and_codomain)
                GeneratedIdentity) ->
        (predicateComposition :
            (head_domain_and_tail_codomain, head_codomain : object) ->
            (head_morphism : morphism
                (head_domain_and_tail_codomain, head_codomain)) ->
            (tail_domain : object) ->
            (tail_morphism : GeneratedMorphism morphism
                (tail_domain, head_domain_and_tail_codomain)) ->
            predicate _ tail_morphism ->
            predicate _ (head_morphism ^<~ tail_morphism)) ->
        {signature : Signature object} ->
        (generatedMorphism : GeneratedMorphism morphism signature) ->
        predicate signature generatedMorphism
    foldMorphism {predicate} predicateIdentity predicateComposition
        GeneratedIdentity =
            predicateIdentity
    foldMorphism {predicate} predicateIdentity predicateComposition
        (GeneratedComposition head_morphism tail_morphism) =
            predicateComposition _ _ head_morphism _ tail_morphism
                (foldMorphism {predicate}
                    predicateIdentity predicateComposition tail_morphism)

    public export
    data GeneratorListValid : {object : Type} -> {morphism : Morphism object} ->
            GeneratorList morphism -> Type where
        GeneratorNilValid : GeneratorListValid []
        GeneratorSingletonValid :
            {object : Type} -> {morphism : Morphism object} ->
            {domain, codomain : object} ->
            (generator : morphism (domain, codomain)) ->
            GeneratorListValid {morphism} [((domain, codomain) ** generator)]
        GeneratorMultipleValid :
            {object : Type} -> {morphism : Morphism object} ->
            {first_domain, first_codomain, second_domain, second_codomain :
                object} ->
            (first :
                morphism (first_domain, first_codomain)) ->
            (second :
                morphism (second_domain, second_codomain)) ->
            (composable : first_domain = second_codomain) ->
            {tail : GeneratorList morphism} ->
            (tailValid : GeneratorListValid {morphism}
                (((second_domain, second_codomain) ** second) :: tail)) ->
            GeneratorListValid {morphism}
                (((first_domain, first_codomain) ** first) ::
                 ((second_domain, second_codomain) ** second) :: tail)

    public export
    validGeneratorListTail : {object : Type} -> {morphism : Morphism object} ->
        {head_domain, head_codomain : object} ->
        {head : morphism (head_domain, head_codomain)} ->
        {tail : GeneratorList morphism} ->
        GeneratorListValid (((head_domain, head_codomain) ** head) :: tail) ->
        GeneratorListValid tail
    validGeneratorListTail GeneratorNilValid impossible
    validGeneratorListTail (GeneratorSingletonValid _) = GeneratorNilValid
    validGeneratorListTail (GeneratorMultipleValid _ _ _ tailValid) = tailValid

    public export
    (-~) : {object : Type} -> {morphism : Morphism object} ->
        {head : SignedMorphism morphism} ->
        {tail : GeneratorList morphism} ->
        GeneratorListValid (head :: tail) ->
        GeneratedMorphism morphism (generatorListSignature head tail)
    (-~) GeneratorNilValid
        impossible
    (-~) (GeneratorSingletonValid head) =
        (^~^) head
    (-~) {head=((domain, codomain) ** first)}
        (GeneratorMultipleValid
            {first_domain=domain} {first_codomain=codomain}
            {second_domain} {second_codomain=domain}
            first second (Refl {x=domain}) tailValid) =
                first ^<~ (-~) tailValid

    public export
    (^-^) : {object : Type} -> {morphism : Morphism object} ->
        {domain, codomain : object} ->
        (head : morphism (domain, codomain)) ->
        GeneratorListValid {morphism} [((domain, codomain) ** head)]
    (^-^) = GeneratorSingletonValid

    infixr 17 <-^
    public export
    (<-^) : {object : Type} -> {morphism : Morphism object} ->
        {head_domain_and_tail_codomain, head_codomain, tail_domain : object} ->
        (head : morphism (head_domain_and_tail_codomain, head_codomain)) ->
        (tail : morphism (tail_domain, head_domain_and_tail_codomain)) ->
        GeneratorListValid {morphism}
            [((head_domain_and_tail_codomain, head_codomain) ** head),
             ((tail_domain, head_domain_and_tail_codomain) ** tail)]
    (<-^) head tail =
        GeneratorMultipleValid head tail Refl (GeneratorSingletonValid tail)

    public export
    record FreeCategory where
        constructor MkFreeCategory
        FreeObject : Type
        FreeGenerator : Morphism FreeObject

    public export
    FreeGeneratorList : FreeCategory -> Type
    FreeGeneratorList cat = GeneratorList (FreeGenerator cat)

    public export
    FreeSignature : FreeCategory -> Type
    FreeSignature cat = Signature (FreeObject cat)

    public export
    FreeMorphism : {cat : FreeCategory} -> Signature (FreeObject cat) -> Type
    FreeMorphism {cat} = GeneratedMorphism (FreeGenerator cat)

{-
    public export
    generatorListValidDec :
        {object : Type} -> DecEqPred object -> {morphism : Morphism object} ->
        (generators : GeneratorList morphism) ->
        Dec (GeneratorListValid generators)
    generatorListValidDec decEqObject [] =
        Yes GeneratorNilValid
    generatorListValidDec decEqObject [((domain, codomain) ** generator)] =
        Yes (GeneratorSingletonValid generator)
    generatorListValidDec decEqObject
        (((first_domain, first_codomain) ** first) ::
        ((second_domain, second_codomain) ** second) ::
        tail) =
            case decEqObject first_domain second_codomain of
                Yes (Refl {x=common_object}) => case generatorListValidDec
                    decEqObject (((_, common_object) ** second) :: tail) of
                        Yes valid => Yes (GeneratorMultipleValid
                            first second (Refl {x=common_object}) valid)
                        No notValid => No (\valid =>
                            notValid (validGeneratorListTail valid))
                No neq => No (\valid => case valid of
                    GeneratorNilValid impossible
                    GeneratorSingletonValid _ impossible
                    GeneratorMultipleValid _ _ Refl _ => neq Refl)

    public export
    ValidGeneratorListType : {object : Type} -> DecEq object =>
        {morphism : Morphism object} ->
        (generators : GeneratorList morphism) ->
        Type
    ValidGeneratorListType generators with
            (generatorListValidDec decEq generators)
        ValidGeneratorListType generators | Yes _ =
            GeneratorListValid generators
        ValidGeneratorListType generators | No _ =
            ()

    infixr 19 ^<-~
    public export
    (^<-~) : {object : Type} -> DecEq object => {morphism : Morphism object} ->
        {domain, codomain : object} ->
        (head : morphism (domain, codomain)) ->
        (tail : GeneratorList morphism) ->
        ValidGeneratorListType (((domain, codomain) ** head) :: tail)
    (^<-~) {domain} {codomain} head tail with
            (generatorListValidDec decEq (((domain, codomain) ** head) :: tail))
        (^<-~) {domain} {codomain} head tail | Yes valid = valid
        (^<-~) {domain} {codomain} head tail | No _ = ()

    public export
    GeneratorListMorphismType : {object : Type} -> DecEq object =>
        {morphism : Morphism object} ->
        {domain, codomain : object} ->
        (head : morphism (domain, codomain)) ->
        (tail : GeneratorList morphism) ->
        Type
    GeneratorListMorphismType {domain} {codomain} head tail with
            (generatorListValidDec decEq (((domain, codomain) ** head) :: tail))
        GeneratorListMorphismType {domain} {codomain} head tail | Yes valid =
            GeneratedMorphism morphism
                (generatorListSignature ((domain, codomain) ** head) tail)
        GeneratorListMorphismType {domain} {codomain} head tail | No _ =
            ()

    infixr 18 ^<~~
    public export
    (^<~~) : {object : Type} -> DecEq object => {morphism : Morphism object} ->
        {domain, codomain : object} ->
        (head : morphism (domain, codomain)) ->
        (tail : GeneratorList morphism) ->
        GeneratorListMorphismType head tail
    (^<~~) {domain} {codomain} head tail with
            (generatorListValidDec decEq (((domain, codomain) ** head) :: tail))
        (^<~~) {domain} {codomain} head tail | Yes valid = (-~) valid
        (^<~~) {domain} {codomain} head tail | No _ = ()
-}

namespace
ContractCategories
    Slice : {cat : FreeCategory} -> FreeObject cat -> Type
    Slice {cat} object =
        (source : FreeObject cat ** FreeMorphism (source, object))

    SlicePredicate : {cat : FreeCategory} -> FreeObject cat -> Type
    SlicePredicate object = Slice object -> Type

    record
    Contract {cat : FreeCategory} (domain, codomain : FreeObject cat) where
        constructor MkContract
        Precondition : SlicePredicate {cat} domain
        Postcondition : SlicePredicate {cat} codomain

    MorphismFulfillsContract :
        {cat : FreeCategory} ->
        {domain, codomain : FreeObject cat} ->
        Contract {cat} domain codomain ->
        FreeMorphism {cat} (domain, codomain) ->
        Type
    MorphismFulfillsContract {cat} {domain}
        (MkContract precondition postcondition) morphism =
            (source : FreeObject cat) ->
            (slice_morphism : FreeMorphism (source, domain)) ->
            precondition (source ** slice_morphism) ->
            postcondition (source ** (morphism <~ slice_morphism))

    ContractsCompose :
        {cat : FreeCategory} ->
        {left_domain_and_right_codomain, left_codomain, right_domain :
            FreeObject cat} ->
        {right_predicate : SlicePredicate {cat} right_domain} ->
        {middle_predicate :
            SlicePredicate {cat} left_domain_and_right_codomain} ->
        {left_predicate : SlicePredicate {cat} left_codomain} ->
        {left_morphism :
            FreeMorphism {cat}
                (left_domain_and_right_codomain, left_codomain)} ->
        {right_morphism :
            FreeMorphism {cat}
                (right_domain, left_domain_and_right_codomain)} ->
        MorphismFulfillsContract {cat}
            (MkContract middle_predicate left_predicate)
            left_morphism ->
        MorphismFulfillsContract {cat}
            (MkContract right_predicate middle_predicate)
            right_morphism ->
        MorphismFulfillsContract {cat}
            (MkContract right_predicate left_predicate)
            (left_morphism <~ right_morphism)
    ContractsCompose {left_morphism} {right_morphism}
        left_fulfills right_fulfills source slice_morphism precondition =
            let
                middle_predicate =
                    right_fulfills source slice_morphism precondition
                postcondition =
                    left_fulfills
                        source
                        (composeGenerated right_morphism slice_morphism)
                        middle_predicate
                associative =
                    composeAssociative
                        left_morphism right_morphism slice_morphism
            in
            rewrite (sym associative) in postcondition

    ContractCategoryObject : (cat : FreeCategory) -> Type
    ContractCategoryObject cat = DPair (FreeObject cat) SlicePredicate

    ContractCategorySignature : FreeCategory -> Type
    ContractCategorySignature cat = Signature (ContractCategoryObject cat)

    ContractCategoryMorphism : {cat : FreeCategory} ->
       ContractCategorySignature cat -> Type
    ContractCategoryMorphism {cat} signature =
        DPair
            (FreeMorphism {cat} (fst (fst signature), fst (snd signature)))
            (MorphismFulfillsContract {cat}
                 (MkContract (snd (fst signature)) (snd (snd signature))))

    ContractCategory : FreeCategory -> FreeCategory
    ContractCategory cat =
        MkFreeCategory
            (ContractCategoryObject cat) (ContractCategoryMorphism {cat})

    foldContract : {cat : FreeCategory} ->
        {signature : ContractCategorySignature cat} ->
        GeneratedMorphism
            {object=(ContractCategoryObject cat)}
            (ContractCategoryMorphism {cat})
            signature ->
        ContractCategoryMorphism {cat} signature
    foldContract GeneratedIdentity = (GeneratedIdentity ** \_, _ => id)
    foldContract
        (GeneratedComposition
            {head_codomain}
            {head_domain_and_tail_codomain}
            {tail_domain}
            head_morphism tail_morphism) =
        let tail_predicate = foldContract tail_morphism in
        (fst head_morphism <~ fst tail_predicate **
         ContractsCompose
            {left_predicate=(snd head_codomain)}
            {middle_predicate=(snd head_domain_and_tail_codomain)}
            {right_predicate=(snd tail_domain)}
            (snd head_morphism) (snd tail_predicate))

    MorphismPredicate :
        {cat : FreeCategory} ->
        {domain, codomain : FreeObject cat} ->
        Contract {cat} domain codomain ->
        Type
    MorphismPredicate {cat} {domain} contract =
        (morphism : FreeMorphism {cat} (domain, codomain)) ->
        MorphismFulfillsContract contract morphism

namespace
MetaLanguages
    public export
    record MetaLanguage (cat : FreeCategory) where
        constructor MkMetaLanguage
        Condition : FreeObject cat -> Type
        FulfillmentProof : {domain, codomain : FreeObject cat} ->
            (precondition : Condition domain) ->
            (postcondition : Condition codomain) ->
            (subjectMorphism : FreeMorphism {cat} (domain, codomain)) ->
            Type

    public export
    MetaLanguageCategoryObject : {cat : FreeCategory} -> MetaLanguage cat ->
        Type
    MetaLanguageCategoryObject {cat} metaCat =
        DPair (FreeObject cat) (Condition metaCat)

    public export
    MetaLanguageCategoryMorphism : {cat : FreeCategory} ->
        (metaCat : MetaLanguage cat) ->
        Signature (MetaLanguageCategoryObject metaCat) ->
        Type
    MetaLanguageCategoryMorphism metaCat (meta_domain, meta_codomain) =
        DPair
            (FreeMorphism (fst meta_domain, fst meta_codomain))
            (FulfillmentProof metaCat (snd meta_domain) (snd meta_codomain))

    public export
    MetaLanguageCategory : {cat : FreeCategory} -> MetaLanguage cat ->
        FreeCategory
    MetaLanguageCategory {cat} metaCat =
        MkFreeCategory
            (MetaLanguageCategoryObject metaCat)
            (MetaLanguageCategoryMorphism metaCat)

namespace FreeFunctors
    record FreeFunctor (sourceCategory, targetCategory : FreeCategory) where
        constructor MkFreeFunctor
        ObjectMap : FreeObject sourceCategory -> FreeObject targetCategory
        MorphismMap : {domain, codomain : FreeObject sourceCategory} ->
            FreeGenerator sourceCategory
                (domain, codomain) ->
            FreeMorphism {cat=targetCategory}
                (ObjectMap domain, ObjectMap codomain)

    FreeMorphismMap : {sourceCategory, targetCategory : FreeCategory} ->
        (functor : FreeFunctor sourceCategory targetCategory) ->
        {domain, codomain : FreeObject sourceCategory} ->
        FreeMorphism {cat=sourceCategory}
            (domain, codomain) ->
        FreeMorphism {cat=targetCategory}
            (ObjectMap functor domain, ObjectMap functor codomain)
    FreeMorphismMap _ GeneratedIdentity = GeneratedIdentity
    FreeMorphismMap functor (GeneratedComposition head_morphism tail_morphism) =
        (MorphismMap functor head_morphism) <~
            (FreeMorphismMap functor tail_morphism)

namespace HigherOrderLanguages
    data
    HigherOrderMetaLanguage :
            (zerothOrderCategory : FreeCategory -> Type) ->
            (higherOrderCategory :
                (objectCategory : FreeCategory) ->
                MetaLanguage objectCategory ->
                Type) ->
            (underlyingCategory : FreeCategory) ->
            Type where
        ZerothOrderCategory : {cat : FreeCategory} ->
            zerothOrderCategory cat ->
            HigherOrderMetaLanguage zerothOrderCategory higherOrderCategory cat
        HigherOrderCategory : {objectCategory : FreeCategory} ->
            HigherOrderMetaLanguage zerothOrderCategory higherOrderCategory
                objectCategory ->
            (metaLanguage : MetaLanguage objectCategory) ->
            higherOrderCategory objectCategory metaLanguage ->
            HigherOrderMetaLanguage zerothOrderCategory higherOrderCategory
                (MetaLanguageCategory metaLanguage)

    HigherOrderLanguageObject :
        (zerothOrderCategory : FreeCategory -> Type) ->
        (higherOrderCategory :
            (objectCategory : FreeCategory) ->
            MetaLanguage objectCategory ->
            Type) ->
        Type
    HigherOrderLanguageObject zerothOrderCategory higherOrderCategory =
        DPair FreeCategory
            (HigherOrderMetaLanguage zerothOrderCategory higherOrderCategory)

    HigherOrderLanguageGenerator :
        (zerothOrderCategory : FreeCategory -> Type) ->
        (higherOrderCategory :
            (objectCategory : FreeCategory) ->
            MetaLanguage objectCategory ->
            Type) ->
        Morphism
            (HigherOrderLanguageObject zerothOrderCategory higherOrderCategory)
    HigherOrderLanguageGenerator zerothOrderCategory higherOrderCategory
        signature =
            FreeFunctor (fst (fst signature)) (fst (snd signature)) -> Type

    HigherOrderLanguageCategory :
        (zerothOrderCategory : FreeCategory -> Type) ->
        (higherOrderCategory :
            (objectCategory : FreeCategory) ->
            MetaLanguage objectCategory ->
            Type) ->
        FreeCategory
    HigherOrderLanguageCategory zerothOrderCategory higherOrderCategory =
        MkFreeCategory
            (HigherOrderLanguageObject
                zerothOrderCategory higherOrderCategory)
            (HigherOrderLanguageGenerator
                zerothOrderCategory higherOrderCategory)

    HigherOrderLanguageMorphism :
        {zerothOrderCategory : FreeCategory -> Type} ->
        (higherOrderCategory :
            (objectCategory : FreeCategory) ->
            MetaLanguage objectCategory ->
            Type) ->
        (signature : Signature
            (HigherOrderLanguageObject
                zerothOrderCategory higherOrderCategory)) ->
        Type
    HigherOrderLanguageMorphism {zerothOrderCategory} higherOrderCategory =
        FreeMorphism {cat=(HigherOrderLanguageCategory
            zerothOrderCategory higherOrderCategory)}

namespace Products
    export
    ProductObject : FreeCategory -> Type
    ProductObject cat = PairOf (FreeObject cat) -> FreeObject cat

    export
    ProductSignature : {cat : FreeCategory} -> ProductObject cat ->
        PairOf (FreeSignature cat) -> FreeSignature cat
    ProductSignature productObj
        ((left_domain, left_codomain), (right_domain, right_codomain)) =
            (productObj (left_domain, right_domain),
             productObj (left_codomain, right_codomain))

namespace CategoryNotations
    record PrefixNotationStack (cat : FreeCategory) where
        constructor MkPrefixNotationStack
        PrefixNotationTop : FreeSignature cat
        PrefixNotationTail : List (FreeSignature cat)

    data PrefixNotationGenerator : (cat : FreeCategory) ->
            (productObj : ProductObject cat) ->
            Signature (PrefixNotationStack cat) -> Type where
        PrefixNotationTargetGenerator :
            {head_codomain, head_domain_and_tail_codomain, tail_domain :
                FreeObject cat} ->
            FreeGenerator cat (head_domain_and_tail_codomain, head_codomain) ->
            (stack : List (FreeSignature cat)) ->
            PrefixNotationGenerator cat productObj
                (MkPrefixNotationStack
                    (tail_domain, head_domain_and_tail_codomain) stack,
                 MkPrefixNotationStack
                    (tail_domain, head_codomain) stack)
        PrefixNotationPush :
            (newTop : FreeObject cat) ->
            (oldTop : FreeSignature cat) ->
            (oldStack : List (FreeSignature cat)) ->
            PrefixNotationGenerator cat productObj
                (MkPrefixNotationStack oldTop oldStack,
                 MkPrefixNotationStack (newTop, newTop) (oldTop :: oldStack))
        PrefixNotationPair :
            (oldTop : FreeSignature cat) ->
            (oldStackHead : FreeSignature cat) ->
            (oldStackTail : List (FreeSignature cat)) ->
            PrefixNotationGenerator cat productObj
                (MkPrefixNotationStack oldTop (oldStackHead :: oldStackTail),
                 MkPrefixNotationStack
                    (ProductSignature {cat} productObj
                        (oldTop, oldStackHead)) oldStackTail)

namespace Subcategories
    record CategorySelection (cat : FreeCategory) where
        ObjectSelected : FreeObject cat -> Type
        GeneratorSelected :
            (signature : PairOf (DPair (FreeObject cat) ObjectSelected)) ->
            FreeGenerator cat (fst (fst signature), fst (snd signature)) ->
            Type

    SubcategoryObject : {cat : FreeCategory} -> CategorySelection cat -> Type
    SubcategoryObject {cat} selection =
        DPair (FreeObject cat) (ObjectSelected selection)

    SubcategoryMorphism : {cat : FreeCategory} ->
        (selection : CategorySelection cat) ->
        (signature : Signature (SubcategoryObject selection)) ->
        Type
    SubcategoryMorphism {cat} selection signature =
        DPair
            (FreeGenerator cat (fst (fst signature), fst (snd signature)))
            (GeneratorSelected selection signature)

    Subcategory : {cat : FreeCategory} -> CategorySelection cat -> FreeCategory
    Subcategory selection = MkFreeCategory
        (SubcategoryObject selection) (SubcategoryMorphism selection)
