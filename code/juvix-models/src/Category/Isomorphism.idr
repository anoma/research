module Category.Isomorphism

import Library.TypesAndFunctions
import public Category.Category

%default total

public export
IsInverse : {cat : Category} -> {a, b: Object cat} ->
    Morphism cat a b -> Morphism cat b a -> Type
IsInverse f g = (g .* f = catId a, f .* g = catId b)

public export
IsIsomorphism : {cat : Category} -> {a, b: Object cat} ->
  Morphism cat a b -> Type
IsIsomorphism f = DPair (Morphism cat b a) (Isomorphism.IsInverse f)

public export
Isomorphic : {cat : Category} -> (a, b: Object cat) -> Type
Isomorphic a b = DPair (Morphism cat a b) Isomorphism.IsIsomorphism

public export
inversePostComposeIsPostComposeInverse :
  {cat : Category} -> {a, b, c : Object cat} ->
  (f : Morphism cat b c) ->
  (isIsomorphism : Isomorphism.IsIsomorphism {cat} {a=b} {b=c} f) ->
  IsBijection (postCompose {cat} {a} {b} {c} f)
inversePostComposeIsPostComposeInverse f (fInv ** (isLeftInv, isRightInv)) =
  (postCompose fInv **
   (\g =>
     let
       assoc = Associativity cat fInv f g
       cancelInverse =
         replace {p=(\f' => After cat f' g = After cat fInv (After cat f g))}
           isLeftInv assoc
       cancelId =
         replace {p=(\g' => g' = After cat fInv (After cat f g))}
           (LeftIdentity cat g) cancelInverse
     in
     sym cancelId,
    \g =>
     let
       assoc = Associativity cat f fInv g
       cancelInverse =
         replace {p=(\f' => After cat f' g = After cat f (After cat fInv g))}
           isRightInv assoc
       cancelId =
         replace {p=(\g' => g' = After cat f (After cat fInv g))}
           (LeftIdentity cat g) cancelInverse
     in
     sym cancelId))

public export
inversePreComposeIsPreComposeInverse :
  {cat : Category} -> {a, b, c : Object cat} ->
  (f : Morphism cat a b) ->
  (isIsomorphism : Isomorphism.IsIsomorphism {cat} {a} {b} f) ->
  IsBijection (preCompose {cat} {a} {b} {c} f)
inversePreComposeIsPreComposeInverse f (fInv ** (isLeftInv, isRightInv)) =
  (preCompose fInv **
   (\g =>
     let
       assoc = Associativity cat g f fInv
       cancelInverse =
         replace {p=(\f' => After cat (After cat g f) fInv = After cat g f')}
           isRightInv assoc
       cancelId =
         replace {p=(\g' => After cat (After cat g f) fInv = g')}
           (RightIdentity cat g) cancelInverse
     in
     cancelId,
    \g =>
     let
       assoc = Associativity cat g fInv f
       cancelInverse =
         replace {p=(\f' => After cat (After cat g fInv) f = After cat g f')}
           isLeftInv assoc
       cancelId =
         replace {p=(\g' => After cat (After cat g fInv) f = g')}
           (RightIdentity cat g) cancelInverse
     in
     cancelId))
