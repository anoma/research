module Library.TypesAndFunctions

%default total

public export
appEq : {a, b : Type} -> {f, g : a -> b} -> {x : a} -> f = g -> f x = g x
appEq Refl = Refl

public export
FunctionalExtensionality : (a, b : Type) -> Type
FunctionalExtensionality a b =
  {f, g : a -> b} -> ((x : a) -> f x = g x) -> f = g

public export
IsLeftInverse : {a, b : Type} -> (a -> b) -> (b -> a) -> Type
IsLeftInverse f g = (x : a) -> g (f x) = x

public export
HasLeftInverseImpliesInjective :
  {a, b : Type} -> {f : a -> b} -> {g : b -> a} ->
  IsLeftInverse f g ->
  {x, x' : a} -> f x = f x' -> x = x'
HasLeftInverseImpliesInjective isLeftInv {x} {x'} fxeq =
  trans (sym (isLeftInv x)) (trans (cong g fxeq) (isLeftInv x'))

public export
IsRightInverse : {a, b : Type} -> (a -> b) -> (b -> a) -> Type
IsRightInverse {a} {b} f g = IsLeftInverse {b=a} {a=b} g f

public export
IsInverse : {a, b : Type} -> (a -> b) -> (b -> a) -> Type
IsInverse f g = (IsLeftInverse f g, IsRightInverse f g)

public export
isInverseSym : {a, b : Type} -> {f : a -> b} -> {g : b -> a} ->
               IsInverse f g -> IsInverse g f
isInverseSym (isLeftInv, isRightInv) = (isRightInv, isLeftInv)

public export
IsBijection : {a, b : Type} -> (a -> b) -> Type
IsBijection {a} {b} f = DPair (b -> a) (IsInverse f)

public export
Bijection : (a, b : Type) -> Type
Bijection a b = DPair (a -> b) IsBijection

public export
IsBijectionForEach : {a : Type} -> {b, c : a -> Type} ->
  ((x : a) -> b x -> c x) -> Type
IsBijectionForEach f = (x : a) -> IsBijection (f x)

public export
ForEachInverse : {a : Type} -> {b, c : a -> Type} ->
  {f : (x : a) -> b x -> c x} -> IsBijectionForEach f ->
  ((x : a) -> c x -> b x)
ForEachInverse isBijection x cx = fst (isBijection x) cx

public export
ForEachInverseIsInverse : {a : Type} -> {b, c : a -> Type} ->
  {f : (x : a) -> b x -> c x} -> (isBijection : IsBijectionForEach f) ->
  ((x : a) -> IsInverse (f x) (ForEachInverse {f} isBijection x))
ForEachInverseIsInverse isBijection x =
  let isBijectionX = snd (isBijection x) in
  (\bx => fst isBijectionX bx, \cx => snd isBijectionX cx)

public export
forEachInverseSym : {a : Type} -> {b, c : a -> Type} ->
  {f : (x : a) -> b x -> c x} -> (isBijection : IsBijectionForEach f) ->
  IsBijectionForEach {a} {b=c} {c=b} (ForEachInverse {f} isBijection)
forEachInverseSym isBijection x =
  (f x ** (snd (snd (isBijection x)), fst (snd (isBijection x))))
