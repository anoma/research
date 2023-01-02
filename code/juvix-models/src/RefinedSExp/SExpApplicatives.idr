module RefinedSExp.SExpApplicatives

import Library.FunctionsAndRelations
import Library.Decidability
import Library.List
import RefinedSExp.List
import RefinedSExp.PairVariant.SExp

%default total

public export
SExpPairOfApplicativeEncodingSig :
  (atom : Type) -> SExpApplicativeEncodingSig {f=PairOf} PairOfApplicative atom
SExpPairOfApplicativeEncodingSig atom =
  SExpApplicativeEncodingArgs
    (\type, sig =>
      SExpEncodingArgs
        (\(y, y') => encode sig y $. encode sig y')
        (\(y, y'), (z, z'), eqpair =>
          let (eqyz, eqyz') = sexpPairInjective eqpair in
          pairInjective
            (injective sig y z eqyz)
            (injective sig y' z' eqyz')
        )
    )
