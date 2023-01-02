module RefinedSExp.Data

import public Library.Decidability

%default total

-- | Data with no structure besides a decidable equality -- a "type of
-- | individuals" for particular use when _interpreting_ expressions as
-- | representing computable functions.
public export
data Data : Type where
  DNat : Nat -> Data
  DString : String -> Data

public export
Show Data where
  show (DNat n) = show n
  show (DString s) = "'" ++ s

export
dDecEq : DecEqPred Data
dDecEq (DNat n) (DNat n') = case decEq n n' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl
dDecEq (DNat _) (DString _) =
  No $ \eq => case eq of Refl impossible
dDecEq (DString _) (DNat _) =
  No $ \eq => case eq of Refl impossible
dDecEq (DString s) (DString s') = case decEq s s' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl

public export
DecEq Data where
  decEq = dDecEq

public export
Eq Data using decEqToEq where
  (==) = (==)

public export
Ord Data where
  DNat n < DNat n' = n < n'
  DNat _ < DString _ = True
  DString _ < DNat _ = False
  DString s < DString s' = s < s'
