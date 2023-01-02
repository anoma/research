module DaoOfFP.Chapter4

import Library.TypesAndFunctions
import Category.Naturality

%default total

Exercise_4_1_1_not : Bool -> Bool
Exercise_4_1_1_not b = if b then False else True

Exercise_4_1_1_id : Bool -> Bool
Exercise_4_1_1_id b = b

Exercise_4_1_1_const_true : Bool -> Bool
Exercise_4_1_1_const_true _ = True

Exercise_4_1_1_const_false : Bool -> Bool
Exercise_4_1_1_const_false _ = False

Exercise_4_4_1_Either_a_Void_To_a : {a : Type} -> Either a Void -> a
Exercise_4_4_1_Either_a_Void_To_a (Left x) = x
Exercise_4_4_1_Either_a_Void_To_a (Right y) = void y

Exercise_4_4_1_a_To_Either_a_Void : {a : Type} -> a -> Either a Void
Exercise_4_4_1_a_To_Either_a_Void x = Left x

Exericse_4_4_1_Either_a_Void_to_a_To_Either_a_Void_id : (a : Type) ->
    IsLeftInverse
        (Exercise_4_4_1_Either_a_Void_To_a {a})
        (Exercise_4_4_1_a_To_Either_a_Void {a})
Exericse_4_4_1_Either_a_Void_to_a_To_Either_a_Void_id a (Left _) = Refl
Exericse_4_4_1_Either_a_Void_to_a_To_Either_a_Void_id a (Right _) impossible

Exercise_4_4_1_a_To_Either_a_Void_to_a_id : (a : Type) ->
    IsRightInverse
        (Exercise_4_4_1_Either_a_Void_To_a {a})
        (Exercise_4_4_1_a_To_Either_a_Void {a})
Exercise_4_4_1_a_To_Either_a_Void_to_a_id a _ = Refl

Exercise_4_4_1_are_inverses : (a : Type) ->
    IsInverse
        (Exercise_4_4_1_Either_a_Void_To_a {a})
        (Exercise_4_4_1_a_To_Either_a_Void {a})
Exercise_4_4_1_are_inverses a =
    (Exericse_4_4_1_Either_a_Void_to_a_To_Either_a_Void_id a,
     Exercise_4_4_1_a_To_Either_a_Void_to_a_id a)

SumElimination : {a, b, x : Type} -> (f : a -> x) -> (g : b -> x) ->
    Either a b -> x
SumElimination f g (Left e) = f e
SumElimination f g (Right e) = g e

CommuteSumElimination : {a, b : Type} ->
  ObserverChange {cat=TypeCategory} (Either a b) (Either b a)
CommuteSumElimination _ h (Left e) = h (Right e)
CommuteSumElimination _ h (Right e) = h (Left e)

Exercise_4_4_2_CommuteSumEliminationIsOwnInverse : {a, b : Type} ->
    IsBijectionForEach (CommuteSumElimination {a} {b})
Exercise_4_4_2_CommuteSumEliminationIsOwnInverse x =
    (CommuteSumElimination {a=b} {b=a} x **
     (\h => functionalExtensionality (\e => case e of
        Left _ => Refl
        Right _ => Refl),
      \h => functionalExtensionality (\e => case e of
        Left _ => Refl
        Right _ => Refl)))

Exercise_4_4_2_CommuteSumEliminationIsNatural : {a, b : Type} ->
    ObserverChangeIsNatural {cat=TypeCategory} (CommuteSumElimination {a} {b})
Exercise_4_4_2_CommuteSumEliminationIsNatural {a} {b} x y g =
    functionalExtensionality
        (\h => functionalExtensionality
            (\e => case e of
                Left _ => Refl
                Right _ => Refl))

Exercise_4_4_3_CommuteSum : {a, b : Type} -> Either a b -> Either b a
Exercise_4_4_3_CommuteSum (Left e) = Right e
Exercise_4_4_3_CommuteSum (Right e) = Left e

Exercise_4_4_3_CommuteSumIsOwnLeftInverse : (a, b : Type) ->
    IsLeftInverse
        (Exercise_4_4_3_CommuteSum {a} {b})
        (Exercise_4_4_3_CommuteSum {a=b} {b=a})
Exercise_4_4_3_CommuteSumIsOwnLeftInverse a b (Left _) = Refl
Exercise_4_4_3_CommuteSumIsOwnLeftInverse a b (Right _) = Refl

Exercise_4_4_3_CommuteSumIsOwnRightInverse : (a, b : Type) ->
    IsRightInverse
        (Exercise_4_4_3_CommuteSum {a} {b})
        (Exercise_4_4_3_CommuteSum {a=b} {b=a})
Exercise_4_4_3_CommuteSumIsOwnRightInverse a b (Left _) = Refl
Exercise_4_4_3_CommuteSumIsOwnRightInverse a b (Right _) = Refl

Exercise_4_4_3_CommuteSumIsOwnInverse : (a, b : Type) ->
    IsInverse
        (Exercise_4_4_3_CommuteSum {a} {b})
        (Exercise_4_4_3_CommuteSum {a=b} {b=a})
Exercise_4_4_3_CommuteSumIsOwnInverse a b =
    (Exercise_4_4_3_CommuteSumIsOwnLeftInverse a b,
     Exercise_4_4_3_CommuteSumIsOwnRightInverse a b)

Exercise_4_4_4_Functoriality : {a, a', b, b' : Type} ->
    (f : a -> a') -> (g : b -> b') -> ((Either a b) -> (Either a' b'))
Exercise_4_4_4_Functoriality f g (Left e) = Left (f e)
Exercise_4_4_4_Functoriality f g (Right e) = Right (g e)

Exercise_4_4_4_Functoriality_Preserves_Composition :
    {a, a', a'', b, b', b'' : Type} ->
    (f : a -> a') -> (f' : a' -> a'') ->
    (g : b -> b') -> (g' : b' -> b'') ->
        Exercise_4_4_4_Functoriality (f' . f) (g' . g) =
        Exercise_4_4_4_Functoriality f' g' . Exercise_4_4_4_Functoriality f g
Exercise_4_4_4_Functoriality_Preserves_Composition f f' g g' =
    functionalExtensionality
        (\e => case e of
            Left _ => Refl
            Right _ => Refl)

Exercise_4_4_5_Functoriality_Preserves_Identity :
    (a, b : Type) ->
    Exercise_4_4_4_Functoriality (id {a}) (id {a=b}) = id {a=(Either a b)}
Exercise_4_4_5_Functoriality_Preserves_Identity a b =
    functionalExtensionality
        (\e => case e of
            Left _ => Refl
            Right _ => Refl)
