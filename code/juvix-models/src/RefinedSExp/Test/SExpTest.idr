module RefinedSExp.Test.SExpTest

import public Library.Test.TestLibrary
import public RefinedSExp.SExp
import public RefinedSExp.Data

%default total

public export
DExp : Type
DExp = SExp Data

public export
DList : Type
DList = SList Data

public export
Show DExp where
  show = fst (sexpShows show)

public export
Show DList where
  show l = "(" ++ snd (sexpShows show) l ++ ")"

public export
sexpNotationTest : DExp
sexpNotationTest =
  DNat 0 $* (DString ":Curry" $* DString "two" $^^ DNat 3) ::
    (DNat 4 $*** (DNat 5 $* (DNat 6 $*** (DString "seven" $**^ DNat 8)) $:^
      DString "~Turing")) $:^ DString "*Record"

natFromData : Data -> Nat
natFromData (DNat n) = n
natFromData (DString s) = length s

natPred : DExp -> Type
natPred _ = Nat

natSig : SExpForAllIntroSig SExpTest.natPred
natSig = SExpForAllIntroArgs (\d, l, forAll => natFromData d)

natExp : SExpForAll SExpTest.natPred SExpTest.sexpNotationTest
natExp = sexpForAllIntro natSig sexpNotationTest

export
sexpTests : IO ()
sexpTests = do
  printLn "Begin sexpTests:"
  printLn $ show sexpNotationTest
  printLn $ show natExp
  printLn "End sexpTests."
  pure ()
