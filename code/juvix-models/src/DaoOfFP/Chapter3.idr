module DaoOfFP.Chapter3

import Library.TypesAndFunctions
import Category.Category
import Category.Isomorphism
import Category.Universality
import Category.Naturality

%default total

Exercise_3_1_1 : {cat : Category} -> {a, b, c : Object cat} ->
  Isomorphic {cat} a b -> Bijection (Morphism cat a c) (Morphism cat b c)
Exercise_3_1_1 {cat}
  (abIsomorphism ** (baIsomorphism ** ((isLeftInverse, isRightInverse)))) =
    ((\f : Morphism cat a c => f .* baIsomorphism) **
     ((\g : Morphism cat b c => g .* abIsomorphism) **
     ((\f' : Morphism cat a c =>
       let
         assoc = Associativity cat f' baIsomorphism abIsomorphism
         rightId = RightIdentity cat f'
       in
       replace {p=(\f'' => f'' = f')} (sym assoc)
         (replace {p=(\z => f' .* z = f')} (sym isLeftInverse) rightId),
      \g' : Morphism cat b c =>
       let
         assoc = Associativity cat g' abIsomorphism baIsomorphism
         rightId = RightIdentity cat g'
       in
       replace {p=(\g'' => g'' = g')} (sym assoc)
         (replace {p=(\z => g' .* z = g')} (sym isRightInverse) rightId)))))

Exercise_3_1_2 : {cat : Category} -> (a : Object cat) -> Isomorphic {cat} a a
Exercise_3_1_2 a =
  (catId a ** (catId a ** (LeftIdentity _ _, LeftIdentity _ _)))

Exercise_3_1_3 : {cat : Category} -> {a, b : Object cat} ->
  Universality.IsTerminal {cat} a -> Universality.IsTerminal {cat} b ->
  Isomorphic {cat} a b
Exercise_3_1_3 aIsTerminal bIsTerminal =
  (fst (bIsTerminal a) ** (fst (aIsTerminal b) **
    (IdOnlyTerminalEndomorphism aIsTerminal
      (fst (aIsTerminal b) .* fst (bIsTerminal a)),
    (IdOnlyTerminalEndomorphism bIsTerminal
      (fst (bIsTerminal a) .* fst (aIsTerminal b))))))

Exercise_3_1_4 : {cat : Category} -> {a, b : Object cat} ->
  (aIsTerminal : Universality.IsTerminal {cat} a) ->
  (bIsTerminal : Universality.IsTerminal {cat} b) ->
  IsUnique {cat} {a} {b}
    (Isomorphism.IsIsomorphism {cat} {a} {b})
    (fst (Exercise_3_1_3 {cat} {a} {b} aIsTerminal bIsTerminal))
Exercise_3_1_4 {cat} {a} {b} aIsTerminal bIsTerminal =
  ((fst (aIsTerminal b) **
   (IdOnlyTerminalEndomorphism aIsTerminal _,
    IdOnlyTerminalEndomorphism bIsTerminal _)),
   \g : Morphism cat a b,
    g' : DPair (Morphism cat b a) (IsInverse {cat} g) =>
      snd (snd (bIsTerminal a)) g ())

Exercise_3_2_1_left : {cat : Category} -> {a, b, x, y : Object cat} ->
  (fInv : Morphism cat b a) -> (g : Morphism cat x y) ->
  (h : Morphism cat a x) ->
  ((preCompose {cat} {a=b} {b=a} {c=y} fInv) .
    (postCompose {cat} {a} {b=x} {c=y} g)) h =
  After cat {a=b} {b=x} {c=y} g (After cat {a=b} {b=a} {c=x} h fInv)
Exercise_3_2_1_left fInv g h = Associativity cat g h fInv

Exercise_3_2_1_right : {cat : Category} -> {a, b, x, y : Object cat} ->
  (fInv : Morphism cat b a) -> (g : Morphism cat x y) ->
  (h : Morphism cat a x) ->
  ((postCompose {cat} {a=b} {b=x} {c=y} g) .
    (preCompose {cat} {a=b} {b=a} {c=x} fInv)) h =
  After cat {a=b} {b=x} {c=y} g (After cat {a=b} {b=a} {c=x} h fInv)
Exercise_3_2_1_right fInv g h = Refl

Exercise_3_3_1 : {cat : Category} ->
  {observerA, observerB : Object cat} ->
  (beta : ObserverChange {cat} observerA observerB) ->
  Morphism cat observerB observerA
Exercise_3_3_1 = ObserverChangeInducedMorphism

Exercise_3_3_2 : {cat : Category} ->
  {observerA, observerB : Object cat} ->
  (beta : ObserverChange {cat} observerA observerB) ->
  (natural : ObserverChangeIsNatural {cat} {observerA} {observerB} beta) ->
  (y : Object cat) -> (g : Morphism cat observerA y) ->
  beta y g =
    After cat {a=observerB} {b=observerA} {c=y}
      g (Exercise_3_3_1 {cat} {observerA} {observerB} beta)
Exercise_3_3_2 beta natural y g =
  appEq {x=g} (ObserverChangeIsPreComposition beta natural y)
