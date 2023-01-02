module Geb.Test.GebTest

import public Library.Test.TestLibrary
import public Geb.Geb

%default total

{-

zerothOrderExp : GebSExp
zerothOrderExp = GAFiniteOrder $**^ GAIndexFirst

zerothOrder : GebPOrder GebTest.zerothOrderExp
zerothOrder = compileOrder zerothOrderExp

emptyTypeListExp : GebSExp
emptyTypeListExp = $^ GATypeList

emptyTypeList : GebPTypeList GebTest.zerothOrder GebTest.emptyTypeListExp
emptyTypeList = compileTypeList zerothOrderExp emptyTypeListExp

emptyTypeMatrixExp : GebSExp
emptyTypeMatrixExp = $^ GATypeMatrix

emptyTypeMatrix : GebPTypeMatrix GebTest.zerothOrder GebTest.emptyTypeMatrixExp
emptyTypeMatrix = compileTypeMatrix zerothOrderExp emptyTypeMatrixExp

voidTypeExp : GebSExp
voidTypeExp = GAPatternType $*** emptyTypeMatrixExp

voidType : GebPType GebTest.zerothOrder GebTest.voidTypeExp
voidType = compileType zerothOrderExp voidTypeExp

singletonTypeMatrixExp : GebSExp
singletonTypeMatrixExp = GATypeMatrix $*** emptyTypeListExp

singletonTypeMatrix : GebPTypeMatrix
  GebTest.zerothOrder GebTest.singletonTypeMatrixExp
singletonTypeMatrix = compileTypeMatrix zerothOrderExp singletonTypeMatrixExp

unitTypeExp : GebSExp
unitTypeExp = GAPatternType $*** singletonTypeMatrixExp

unitType : GebPType GebTest.zerothOrder GebTest.unitTypeExp
unitType = compileType zerothOrderExp unitTypeExp

unitTermIndexExp : GebSExp
unitTermIndexExp = gebMatrixIndexExp 0

unitTermExp : GebSExp
unitTermExp = GAInjectTerm $* [unitTermIndexExp, $^ GATermList]

unitTerm : GebPTerm GebTest.unitType GebTest.unitTermExp
unitTerm = compileTerm unitType unitTermExp

unitTypeListExp : GebSExp
unitTypeListExp = GATypeList $*** unitTypeExp

boolTypeMatrixExp : GebSExp
boolTypeMatrixExp = GATypeMatrix $* [unitTypeListExp, unitTypeListExp]

boolTypeMatrix : GebPTypeMatrix GebTest.zerothOrder GebTest.boolTypeMatrixExp
boolTypeMatrix = compileTypeMatrix zerothOrderExp boolTypeMatrixExp

boolTypeExp : GebSExp
boolTypeExp = GAPatternType $*** boolTypeMatrixExp

boolType : GebPType GebTest.zerothOrder GebTest.boolTypeExp
boolType = compileType zerothOrderExp boolTypeExp

unitTermList : GebSExp
unitTermList = GATermList $* [unitTermExp]

falseTermIndexExp : GebSExp
falseTermIndexExp = gebMatrixIndexExp 0

trueTermIndexExp : GebSExp
trueTermIndexExp = gebMatrixIndexExp 1

falseTermIndex : GebMatrixIndex GebTest.boolTypeMatrix (gebMatrixIndexExp 0)
falseTermIndex = compileMatrixIndex boolTypeMatrix (gebMatrixIndexExp 0)

falseTermExp : GebSExp
falseTermExp = GAInjectTerm $* [falseTermIndexExp, unitTermList]

trueTermExp : GebSExp
trueTermExp = GAInjectTerm $* [trueTermIndexExp, unitTermList]

falseTerm : GebPTerm GebTest.boolType GebTest.falseTermExp
falseTerm = compileTerm boolType falseTermExp

trueTerm : GebPTerm GebTest.boolType GebTest.trueTermExp
trueTerm = compileTerm boolType trueTermExp

pairBoolTypeListExp : GebSExp
pairBoolTypeListExp = GATypeList $* [boolTypeExp, boolTypeExp]

pairBoolTypeMatrixExp : GebSExp
pairBoolTypeMatrixExp = GATypeMatrix $*** pairBoolTypeListExp

pairBoolTypeMatrix :
  GebPTypeMatrix GebTest.zerothOrder GebTest.pairBoolTypeMatrixExp
pairBoolTypeMatrix = compileTypeMatrix zerothOrderExp pairBoolTypeMatrixExp

pairBoolTypeExp : GebSExp
pairBoolTypeExp = GAPatternType $*** pairBoolTypeMatrixExp

pairBoolType : GebPType GebTest.zerothOrder GebTest.pairBoolTypeExp
pairBoolType = compileType zerothOrderExp pairBoolTypeExp
-}

coreConstUnit : CoreMorphism CoreTerminal CoreTerminal
coreConstUnit = CoreToTerminal CoreTerminal

coreConstUnitToSExpAndBackCorrect :
  Geb.coreMorphismFromSExp (Geb.coreMorphismToSExp GebTest.coreConstUnit) =
    Just (MkCoreSignedMorphism GebTest.coreConstUnit)
coreConstUnitToSExpAndBackCorrect = Refl

FirstOrderReflector : CoreObject CoreFirstOrder
FirstOrderReflector = CoreObjectReflector CoreFirstOrder

SecondOrderReflector : CoreObject CoreFirstOrder
SecondOrderReflector = CoreObjectReflector CoreSecondOrder

endoIdentity : CoreMorphism FirstOrderReflector FirstOrderReflector
endoIdentity = CoreIdentity _

endoIdentityExp : GebSExp
endoIdentityExp = GAIdentity $*** GAObjectReflector $**^ GAFirstOrder

endoIdentityExpIsCorrect :
  Geb.coreMorphismToSExp GebTest.endoIdentity = GebTest.endoIdentityExp
endoIdentityExpIsCorrect = Refl

endoIdentityCompiles :
  Geb.coreMorphismFromSExp (Geb.coreMorphismToSExp GebTest.endoIdentity) =
    Just (MkCoreSignedMorphism GebTest.endoIdentity)
endoIdentityCompiles = Refl

export
gebTests : IO ()
gebTests = do
  printLn "Begin gebTests:"
  printLn $ "Core const unit = " ++ showMorphism coreConstUnit
  printLn $ "Core first-order reflector ID = " ++ showMorphism endoIdentity
  {-
  printLn $ "Empty type list = " ++ showTypeList emptyTypeList
  printLn $ "Empty type matrix = " ++ showTypeMatrix emptyTypeMatrix
  printLn $ "Singleton type matrix = " ++ showTypeMatrix singletonTypeMatrix
  printLn $ "Bool type matrix = " ++ showTypeMatrix boolTypeMatrix
  printLn $ "Pair-of-bool type matrix = " ++ showTypeMatrix pairBoolTypeMatrix
  printLn $ "Pair-of-bool type = " ++ showType pairBoolType
  -}
  printLn "End gebTests."
  pure ()
