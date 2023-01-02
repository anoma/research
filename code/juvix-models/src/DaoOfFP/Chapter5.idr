module DaoOfFP.Chapter5

import Category.Naturality
import Category.SumsAndProducts

%default total

Exercise_5_1_1_product_unit_as_subject : {ccc : CartesianClosedCategory} ->
    {x, a : CCC_object ccc} ->
    CCC_morphism {ccc} x a ->
    CCC_morphism {ccc} x (CCC_product {ccc} (CCC_terminal ccc) a)
Exercise_5_1_1_product_unit_as_subject f =
    CCC_morphism_product (fst (CCC_is_terminal ccc x)) f

Exercise_5_1_1_product_unit_subject_change : {ccc : CartesianClosedCategory} ->
    (a : CCC_object ccc) ->
    SubjectChange {cat=(CCC_cat ccc)} (CCC_product {ccc} (CCC_terminal ccc) a) a
Exercise_5_1_1_product_unit_subject_change {ccc} a x f =
    After (CCC_cat ccc) (CCC_second _ _) f

Exercise_5_1_1_product_unit_subject_change_is_natural :
    {ccc : CartesianClosedCategory} ->
    (a : CCC_object ccc) ->
    SubjectChangeIsNatural {cat=CCC_cat ccc}
        {subjectA=(CCC_product {ccc} (CCC_terminal ccc) a)}
        {subjectB=a}
        (Exercise_5_1_1_product_unit_subject_change {ccc} a)
Exercise_5_1_1_product_unit_subject_change_is_natural {ccc} a y x g =
    functionalExtensionality (\f => sym (Associativity _ _ _ _))

Exercise_5_1_1_product_unit_isomorphism : {ccc : CartesianClosedCategory} ->
    (a : CCC_object ccc) ->
    CCC_morphism {ccc} (CCC_product {ccc} (CCC_terminal ccc) a) a
Exercise_5_1_1_product_unit_isomorphism {ccc} a =
    SubjectChangeInducedMorphism (Exercise_5_1_1_product_unit_subject_change a)

{- This is not the only choice of arrow with this domain and codomain --
 - see Exercise 5.1.4 below. -}
Exercise_5_1_2 : {ccc : CartesianClosedCategory} -> (a, b : CCC_object ccc) ->
    CCC_morphism {ccc}
        (CCC_sum {ccc} b (CCC_product {ccc} a b))
        (CCC_product {ccc} (CCC_sum {ccc} (CCC_terminal ccc) a) b)
Exercise_5_1_2 {ccc} a b =
    CCC_morphism_product
        (CCC_morphism_sum
            ((CCC_left (CCC_terminal ccc) a) .* fst (CCC_is_terminal ccc b))
            ((CCC_right _ _) .* (CCC_first a b)))
        (CCC_morphism_sum
            (CCC_id b)
            (CCC_second a b))

Exercise_5_1_3 : {ccc : CartesianClosedCategory} -> (a, b : CCC_object ccc) ->
    CCC_morphism {ccc}
        (CCC_sum {ccc} b (CCC_product {ccc} a b))
        (CCC_product {ccc} (CCC_sum {ccc} (CCC_terminal ccc) a) b)
Exercise_5_1_3 a b =
    CCC_morphism_sum
        (CCC_morphism_product
            ((CCC_left (CCC_terminal ccc) a) .* fst (CCC_is_terminal ccc b))
            (CCC_id b))
        (CCC_morphism_product
            ((CCC_right _ _) .* (CCC_first a b))
            (CCC_second a b))

Exercise_5_1_4_maybe_AB : {a, b : Type} -> Either b (a, b) -> (Maybe a, b)
Exercise_5_1_4_maybe_AB (Left y) = (Nothing, y)
Exercise_5_1_4_maybe_AB (Right (x, y)) = (Just x, y)

{- The type signature for Exercise 5.1.4 allows a bit of leeway --
 - but not much: -}
Exercise_5_1_4_maybe_AB_alternate :
    {a, b : Type} -> Either b (a, b) -> (Maybe a, b)
{- We have no choice aboue this one:  we have no witness for type "a", so the
 - only "Maybe a" we can come up with is "Nothing". And we have only one
 - witness for type "b", so we have to choose that. -}
Exercise_5_1_4_maybe_AB_alternate (Left y) = (Nothing, y)
{- Here we do have one alternative: even though we have a witness for type "a"
 - in this case, we could choose not to use it, and to return "Nothing"
 - anyway. -}
Exercise_5_1_4_maybe_AB_alternate (Right (_, y)) = (Nothing, y)
