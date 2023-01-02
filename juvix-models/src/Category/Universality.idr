module Category.Universality

import public Category.Category
import public Category.Isomorphism

%default total

public export
IsUnique : {cat : Category} -> {a, b : Object cat} ->
  (property : Morphism cat a b -> Type) -> (f : Morphism cat a b) -> Type
IsUnique {cat} {a} {b} property f =
    (property f, (g : Morphism cat a b) -> property g -> g = f)

public export
IsOnlyMorphism : {cat : Category} -> {a, b : Object cat} ->
    Morphism cat a b -> Type
IsOnlyMorphism f = IsUnique (\_ => ()) f

public export
OnlyMorphismIsUnique : {cat : Category} -> {a, b : Object cat} ->
    {f : Morphism cat a b} -> IsOnlyMorphism {cat} {a} {b} f ->
    (g, h : Morphism cat a b) -> g = h
OnlyMorphismIsUnique (_, onlyAB) g h = rewrite (onlyAB h ()) in (onlyAB g ())

public export
IsTerminal : {cat : Category} -> (a : Object cat) -> Type
IsTerminal {cat} a = (b : Object cat) -> DPair (Morphism cat b a) IsOnlyMorphism

public export
TerminalMap : {cat : Category} -> {a : Object cat} ->
  Universality.IsTerminal {cat} a -> (b : Object cat) -> Morphism cat b a
TerminalMap isTerminal b = fst (isTerminal b)

public export
IdOnlyTerminalEndomorphism : {cat : Category} -> {a : Object cat} ->
  (aIsTerminal : Universality.IsTerminal {cat} a) -> (f : Morphism cat a a) ->
  f = Identity cat a
IdOnlyTerminalEndomorphism {cat} {a} aIsTerminal f =
  OnlyMorphismIsUnique (snd (aIsTerminal a)) f (Identity cat a)

public export
IsInitial : {cat : Category} -> (a : Object cat) -> Type
IsInitial {cat} a = (b : Object cat) -> DPair (Morphism cat a b) IsOnlyMorphism

public export
IdOnlyInitialEndomorphism : {cat : Category} -> {a : Object cat} ->
  (aIsInitial : IsInitial {cat} a) -> (f : Morphism cat a a) ->
  f = Identity cat a
IdOnlyInitialEndomorphism {cat} {a} aIsInitial f =
  OnlyMorphismIsUnique (snd (aIsInitial a)) f (Identity cat a)

public export
IsUniqueMorphismWithProperty : {cat : Category} -> {a, b : Object cat} ->
  (property : Morphism cat a b -> Type) -> (m : Morphism cat a b) -> Type
IsUniqueMorphismWithProperty property m =
  (property m, (m' : Morphism cat a b) -> property m' -> m' = m)

public export
AreUniquelyIsomorphic : {cat : Category} -> (a, b : Object cat) -> Type
AreUniquelyIsomorphic {cat} a b =
  (iso : Isomorphic a b **
   Universality.IsUniqueMorphismWithProperty
     Isomorphism.IsIsomorphism (fst iso))

public export
IsUniqueUpToUniqueIsomorphism : {cat : Category} ->
  (property : Object cat -> Type) -> Object cat -> Type
IsUniqueUpToUniqueIsomorphism {cat} property a =
  (property a,
   (b : Object cat) -> property b -> Universality.AreUniquelyIsomorphic a b)
