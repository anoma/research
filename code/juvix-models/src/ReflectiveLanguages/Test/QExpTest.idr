module ReflectiveLanguages.Test.QExpTest

import ReflectiveLanguages.QExp
import Library.FunctionsAndRelations
import Library.Test.TestLibrary
import Library.Decidability

%default total

public export
qexpNotationTest : QExp Nat 2
qexpNotationTest =
  $> (0 $*
    $> (1 $* 2 $^^ 3) :: (4 $*** $> (5 $* (6 $*** (7 $**^ 8)) $:^ 9)) $:^ 10)

export
qexpTests : IO ()
qexpTests = pure ()
