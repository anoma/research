module DaoOfFP.Chapter2

import Library.TypesAndFunctions
import Category.Category

%default total

Exercise_2_1_1 : {cat : Category} -> {a, b, c, d : Object cat} ->
  (g : Morphism cat c d) -> (f : Morphism cat b c) ->
  postCompose {cat} {a} {b} {c=d} ((.*) {cat} {a=b} {b=c} {c=d} g f) =
    (postCompose {cat} {a} {b=c} {c=d} g) . (postCompose {cat} {a} {b} {c} f)
Exercise_2_1_1 {cat} _ _ = functionalExtensionality (Associativity cat _ _)

Exercise_2_1_2 : {cat : Category} -> {a, b, c, d : Object cat} ->
  (h : Morphism cat c d) -> (g : Morphism cat b c) -> (f : Morphism cat a b) ->
  postCompose {cat} {a} {b} {c=d} (postCompose {cat} {a=b} {b=c} {c=d} h g) f =
    postCompose h {cat} {a} {b=c} {c=d} (postCompose {cat} {a} {b} {c} g f)
Exercise_2_1_2 {cat} = Associativity cat

Exercise_2_1_3 : {cat : Category} -> {a, b, c, d : Object cat} ->
  (g : Morphism cat b c) -> (f : Morphism cat a b) ->
  preCompose {cat} {a} {b=c} {c=d} ((.*) {cat} {a} {b} {c} g f) =
    (preCompose {cat} {a} {b} {c=d} f) .
      (preCompose {cat} {a=b} {b=c} {c=d} g)
Exercise_2_1_3 {a} {b} {c} {d} {cat} _ _ =
  functionalExtensionality (\_ => sym (Associativity cat _ _ _))

{- Post-composition with the identity leaves arrows unchanged.
 - (So post-composition with the identity is itself the identity on
 - the type of arrows terminating in a.) -}
Exercise_2_3_1_post : {cat : Category} -> {a, b : Object cat} ->
  (f : Morphism cat b a) ->
  postCompose {cat} {a=b} {b=a} {c=a} (catId {cat} a) f = f
Exercise_2_3_1_post f = LeftIdentity cat f

{- Pre-composition with the identity leaves arrows unchanged.
 - (So pre-composition with the identity is itself the identity on
 - the type of arrows originating in a.) -}
Exercise_2_3_1_pre : {cat : Category} -> {a, b : Object cat} ->
  (f : Morphism cat a b) ->
  preCompose {cat} {a} {b=a} {c=b} (catId {cat} a) f = f
Exercise_2_3_1_pre f = RightIdentity cat f
