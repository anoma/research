module ReflectiveLanguages.Test.SubstitutiveTest

import ReflectiveLanguages.Substitutive
import ReflectiveLanguages.Interpretations.SubstitutiveInterpretation
import Library.FunctionsAndRelations
import Library.Test.TestLibrary
import Library.Decidability
import Datatypes.DependentAlgebraicTypes

%default total

export
isAtom : (index : Nat) -> CSPred
isAtom givenIndex _ (*^ foundIndex) = givenIndex == foundIndex
isAtom _ _ (*| _) = False

export
isSuccLike : (carrier, succ : Nat) ->
  {auto noDups : NoDuplicates [ carrier, succ ]} -> CSPred
isSuccLike carrier succ _ (*| ( (*^ i) *~ ((*^ i') *~ (*-)) ) ) =
    i == succ && i' == carrier
isSuccLike _ _ _ _ = False

export
isNatFLike : (carrier, zero, succ : Nat) ->
  {auto noDups : NoDuplicates [ zero, carrier, succ ]} -> CSLPred
isNatFLike carrier zero succ {noDups} contextSize
  ( zeroClause *~ (succClause *~ (*-)) ) =
    isAtom zero contextSize zeroClause &&
    isSuccLike
      carrier succ
        {noDups=(noDuplicatesTail {l=([ carrier, succ ])} noDups)}
        (S contextSize) succClause
isNatFLike _ _ _ _ _ = False

export
isNatLike : (zero, succ : Nat) -> {auto noDups : NoDuplicates [ zero, succ ]} ->
  CSPred
isNatLike zero succ contextSize (*^ i) = zero == i
isNatLike zero succ contextSize (*| ( (*^ i) *~ (n *~ (*-)) ) ) =
  succ == i && isNatLike zero succ (S contextSize) n
isNatLike _ _ _ _ = False

export
substitutiveTests : IO ()
substitutiveTests = pure ()
