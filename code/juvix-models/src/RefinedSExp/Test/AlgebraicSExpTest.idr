module RefinedSExp.Test.AlgebraicSExpTest

import public Library.Test.TestLibrary
import public RefinedSExp.AlgebraicSExp

%default total

Show (SExp Nat) where
  show = fst $ sexpShows show

Show (SList Nat) where
  show = snd $ sexpShows show

public export
sexpNotationTest : SExp Nat
sexpNotationTest =
  0 $* (1 $* 2 $^^ 3) :: (4 $*** (5 $* (6 $*** (7 $**^ 8)) $:^ 9)) $:^ 10

export
algebraicSExpTests : IO ()
algebraicSExpTests = do
  -- printLn "Begin algebraicSExpTests:"
  -- printLn $ show sexpNotationTest
  -- printLn "End algebraicSExpTests."
  pure ()
