{- Heyting arithmetic and Fast Integer Square Root.
   Author: Siva Somayyajula -}

{- Modified from https://gist.github.com/ssomayyajula/2b3c60ad4c671b2f8989d2c59a2a67fe -}

module External.IntegerSquareRoot

import Data.Nat

%default total

induction : (predicate : Nat -> Type)
         -> predicate Z
         -> ((x : Nat) -> predicate x -> predicate (S x))
         -> (n : Nat)
         -> predicate n
induction predicate pz ps n = case n of
  Z    => pz
  S n' => ps n' (induction predicate pz ps n')

natEq : (x, y, z : Nat) -> x = y -> x = z -> y = z
natEq _ _ _ Refl Refl = Refl

succPlusSucc : (x, y : Nat) -> x + S y = S (x + y)
succPlusSucc x y =
  {- Proceed by induction on x -}
  induction
    (\x => x + S y = S (x + y))
    {- Typechecker can infer Z + S y = S (Z + y) => S y = S y -}
    Refl
    {- Assuming x + S y = S (x + y), show S x + S y = S (S x + y).
       Typechecker infers that S x + S y = S (S x + y) ~ S (x + S y) = S (S (x + y))
       Proof:
         We have
           px   : x + S y = S (x + y),
           Refl : S (S (x + y)) = S (S (x + y)),
         Given that sym px : S (x + y) = x + S y,
         rewrite (sym px) in Refl replaces the first instance of
         S (x + y) with x + S y in S (S (x + y)) = S (S (x + y))
         to yield Refl : S (x + S y) = S (S (x + y)), as desired. -}
    (\x => \px => rewrite (sym px) in Refl)
    x

multPlusSucc : (x, y : Nat) -> x * S y = x * y + x
multPlusSucc x y =
  {- Proof by induction on x. -}
  induction
    (\x => x * S y = x * y + x)
    {- Typechecker can infer Z * S y = Z * y + Z => Z = Z -}
    Refl
    {- Assuming x * S y = x * y + x, show S x * S y = S x * y + S x.
       Typechecker rewrites goal as S (y + x * S y) = (y + x * y) + S x,
       and infers that Refl :
         (y + x * y) + S x = (y + x * y) + S x
       Transform the goal by the inductive hypothesis:
         => S (y + (x * y + x)) = (y + x * y) + S x
       Use the theorem S (y + (x * y + x)) = y + S (x * y + x)
         => y + S (x * y + x) = (y + x * y) + S x
       Use the theorem S (x * y + x) = x * y + S x
         => y + (x * y + S x) = (y + x * y) + S x
       Use the theorem y + (x * y + S x) = (y + x * y) + S x
         => (y + x * y) + S x = (y + x * y) + S x
       Since they're now the same type, their proof is reflexivity.
     -}
    (\x, px =>
       rewrite px in
       rewrite sym (succPlusSucc y (x * y + x)) in
       rewrite sym (succPlusSucc (x * y) x)     in
       rewrite plusAssociative y (x * y) (S x)  in
       Refl)
    x

notLteLt : {x, y : Nat} -> Not (x `LTE` y) -> y `LT` x
notLteLt {x=Z} {y} nlte = void (nlte (LTEZero))
notLteLt {x=(S x')} {y=Z} nlte = LTESucc LTEZero
notLteLt {x=(S x')} {y=(S y')} nlte =
  LTESucc $ notLteLt {x=x'} {y=y'} (nlte . LTESucc)

export
{- forall n. exists r. r * r <= n < (r + 1) * (r + 1) -}
intSqrtPf : (n : Nat) -> (r : Nat ** ((r * r) `LTE` n, n `LT` (S r * S r)))
intSqrtPf n =
  induction
    {- Proof by induction on n. -}
    (\n => (r : Nat ** ((r * r) `LTE` n, n `LT` (S r * S r))))
    {- Base case: n = Z. Choose r = Z.
       Z * Z <= Z and Z < 1 * 1, trivially.
       Typechecker infers:
         Z * Z <= Z => Z <= Z,
           whose proof is LTEZero : Z `LTE` Z
         Z < 1 * 1 => Z < 1,
           whose proof is LTESucc LTEZero : 1 `LTE` 1 ~ Z `LT` 1 -}
    (Z ** (LTEZero, LTESucc LTEZero))
    {- Given
         lte : r * r <= n
         lt  : n < (r + 1) * (r + 1) i.e. n + 1 <= r^2 + 2r + 1, show
         exists r'. r' * r' <= n + 1 < (r' + 1) * (r' + 1)
       Proof. By case analysis.
         if (r + 1) * (r + 1) <= n + 1, then
            r' = r + 1.
            We get (r + 1) * (r + 1) <= n + 1 by the conditional.
            If we add 1 to the LHS and 2r + 3 to the RHS of lt,
            we get n + 1 < (r + 2) * (r + 2).
         else
           r' = r.
           We get r * r <= n => r * r <= n + 1.
           Since we know ~((r + 1) * (r + 1) <= n + 1),
             we get n + 1 < (r + 1) * (r + 1). -}
    (\n, (r ** (lte, lt)) =>
      case isLTE (S r * S r) (S n) of
        Yes lte' => (S r ** (lte',
          let lt' =
            LTESucc (transitive {rel=LTE} lt (lteAddRight (S r * S r) {m = r + r})) in
          let lt'' = lteSuccRight (lteSuccRight lt') in
          {- Rewrite lt'' to match the goal type. -}
          let lt1 =
            replace {p = \x => LTE (S (S n)) (S (S (S (S x))))} (plusAssociative (r + r * S r) r r) lt'' in
          let lt2 =
            replace {p = \x => LTE (S (S n)) (S (S (S (S (x + r + r)))))} (sym (multRightSuccPlus r (S r))) lt1 in
          let lt3 =
            replace {p = \x => LTE (S (S n)) (S (S (S (S (x + r)))))} (plusCommutative (r * S (S r)) r) lt2 in
          let lt4 =
            replace {p = \x => LTE (S (S n)) (S (S (S (S x))))} (plusCommutative (r + r * S (S r)) r) lt3 in
          let lt5 =
            replace {p = \x => LTE (S (S n)) (S (S (S x)))} (plusSuccRightSucc r (r + r * S (S r))) lt4 in
          let lt6 =
            replace {p = \x => LTE (S (S n)) (S (S x))} (plusSuccRightSucc r (S (r + r * S (S r)))) lt5 in
            lt6))
        No nlte => (r ** (lteSuccRight lte, notLteLt nlte)))
    n

public export
intSqrt : Nat -> Nat
intSqrt n = fst (intSqrtPf n)
