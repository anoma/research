module RefinedSExp.PairVariant.Test.SExpTest

import public RefinedSExp.PairVariant.SExp
import public Library.Test.TestLibrary
import public RefinedSExp.Data

sexpNotationTest : SExp Data
sexpNotationTest =
  (($: DNat 3) $. $: DString "three") $. (($: DNat 2) $. $: DString "two")

export
sExpTests : IO ()
sExpTests = do
  printLn "Starting PairVariant SExp tests..."
  printLn $ show sexpNotationTest
  printLn "...Done with PairVariant SExp tests."
  pure ()
