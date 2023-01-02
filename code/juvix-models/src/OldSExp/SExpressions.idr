module OldSExp.SExpressions

%default total

{- A simple model of S-Expressions:  an S-Expression is either an
 - atom (the S-expression type is parameterized on the type of atoms)
 - or a pair of S-expressions. -}
public export
data SExpr : (Atom: Type) -> Type where
  SAtom : {Atom: Type} -> Atom -> SExpr Atom
  SPair : {Atom: Type} -> SExpr Atom -> SExpr Atom -> SExpr Atom

public export
SExprPair : Type -> Type
SExprPair atom = (SExpr atom, SExpr atom)

export sexprMapAtom : {A, B: Type} -> (A -> B) -> SExpr A -> SExpr B
sexprMapAtom f (SAtom a) =
  SAtom (f a)
sexprMapAtom f (SPair first second) =
  SPair (sexprMapAtom f first) (sexprMapAtom f second)

sexprSubst : {A, B: Type} -> (A -> SExpr B) -> SExpr A -> SExpr B
sexprSubst f (SAtom a) = f a
sexprSubst f (SPair s s') = SPair (sexprSubst f s) (sexprSubst f s')

public export
data SPos : {atom : Type} -> SExpr atom -> Type where
  SHere : {atom : Type} -> (s : SExpr atom) -> SPos s
  SLeft : {atom : Type} -> (l, r : SExpr atom) -> SPos (SPair l r)
  SRight : {atom : Type} -> (l, r : SExpr atom) -> SPos (SPair l r)

public export
spos_get : {atom : Type} -> {s : SExpr atom} -> (pos : SPos s) -> SExpr atom
spos_get (SHere s) = s
spos_get (SLeft l r) = l
spos_get (SRight l r) = r
