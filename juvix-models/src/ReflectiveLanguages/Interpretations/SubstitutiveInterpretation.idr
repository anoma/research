module ReflectiveLanguages.Interpretations.SubstitutiveInterpretation

import ReflectiveLanguages.Substitutive
import Library.FunctionsAndRelations
import Datatypes.DependentAlgebraicTypes
import Library.List
import Data.Vect

%default total

-- We can interpret Substitutive datatypes as the characteristic functions
-- of S-expressions with the unit atom.

public export
UnitSExp : Type
UnitSExp = SExp ()

public export
UnitSList : Type
UnitSList = SList ()
