module RefinedSExp.Naming

import public Library.FunctionsAndRelations
import public Library.Decidability
import public Library.List
import public Data.SortedMap

%default total

mutual
  public export
  data NamingContext : (name, term : Type) -> Type where
    ClosureMap : {name, term : Type} ->
      SortedMap name (Closure name term) -> NamingContext name term

  public export partial -- Show instance
  (Show name, Show term) => Show (NamingContext name term) where
    show (ClosureMap m) = show m

  public export
  record Closure (name, term : Type) where
    constructor NamedContext
    closureTerm : term
    closureContext : NamingContext name term

  public export partial -- Show instance
  (Show name, Show term) => Show (Closure name term) where
    show (NamedContext t c) = "(" ++ show t ++ ", " ++ show c ++ ")"
