module Category.ComputableCategories

import Category.Composition
import Library.Decidability
import Library.FunctionsAndRelations
import OldSExp.SExpressions

public export
IsLeftInverseOf : {a, b : Type} -> (f : a -> b) -> (b -> a) -> Type
IsLeftInverseOf {a} f g = (x : a) -> g (f x) = x

public export
IsInjective : {a, b : Type} -> (f : a -> b) -> Type
IsInjective {a} f = (x, x': a) -> f x = f x' -> x = x'

public export
leftInverseImpliesInjective : {a, b : Type} -> (f : a -> b) -> {g : b -> a} ->
  IsLeftInverseOf f g -> IsInjective f
leftInverseImpliesInjective {a} f {g} isLeftInverse x x' fxeq =
  trans
    (sym (replace fxeq {p=(\y => g y = x)} (isLeftInverse x)))
    (isLeftInverse x')

public export
Injection : Type -> Type -> Type
Injection a b = DPair (a -> b) IsInjective

public export
IsEnumeration : {type : Type} -> (enumeration : type -> Nat) -> Type
IsEnumeration = IsInjective

public export
Enumeration : (type : Type) -> Type
Enumeration a = Injection a Nat

public export
Countable : Type
Countable = DPair Type Enumeration

public export
underlyingSet : Countable -> Type
underlyingSet (set ** _) = set

public export
enumeration : (countable : Countable) -> underlyingSet countable -> Nat
enumeration (_ ** (injection ** _)) = injection

public export
fromUnderlying : Countable -> Type -> Type
fromUnderlying countable type = underlyingSet countable -> type

public export
countableEq : (countable : Countable) -> DecEqPred (underlyingSet countable)
countableEq (_ ** (injection ** isInjective)) x x' =
  case decEq (injection x) (injection x') of
    Yes eq => Yes (isInjective x x' eq)
    No neq => No (neq . (cong injection))

public export
[countableDecEq] (countable : Countable) =>
  DecEq (underlyingSet countable) where
    decEq = countableEq countable

public export
listUnderlying : Countable -> Type
listUnderlying = List . underlyingSet

public export
[listCountableDecEq] (countable : Countable) =>
  DecEq (listUnderlying countable) where
    decEq = let underlyingDecEq = countableDecEq in decEq

public export
listCountableEq :
  (countable : Countable) -> DecEqPred (listUnderlying countable)
listCountableEq countable = let listDecEq = listCountableDecEq in decEq

{-

TotalComputableFunction : Type
TotalComputableFunction = Nat -> Nat

record ComputableLogicInIdris where
  constructor MkCLII
  FunctionGenerator : Countable
  GeneratedFunction : fromUnderlying FunctionGenerator TotalComputableFunction

generatorSet : ComputableLogicInIdris -> Type
generatorSet = underlyingSet . FunctionGenerator

CLIICategory : ComputableLogicInIdris -> FreeCategory
CLIICategory clii =
  MkFreeCategory () (\_ => generatorSet clii)

interpretCTIIMorphism : {clii : ComputableLogicInIdris} ->
  FreeMorphism {cat=(CLIICategory clii)} ((), ()) ->
  TotalComputableFunction
interpretCTIIMorphism {clii} =
  foldMorphism {predicate=(\_, _ => TotalComputableFunction)}
  id
  (\_, _, f, _, _, g => GeneratedFunction clii f . g)

NatCharacteristic : Type
NatCharacteristic = Nat -> Bool

NatCharacteristicTrue : NatCharacteristic -> Nat -> Type
NatCharacteristicTrue characteristic n = IsTrue (characteristic n)

NatCharacteristicSignature : Type
NatCharacteristicSignature = PairOf NatCharacteristic

record ComputableTypeAssignmentInIdris where
  constructor MkCTAII
  computableLogic : ComputableLogicInIdris
  typeGenerator :
    fromUnderlying
      (FunctionGenerator computableLogic) NatCharacteristicSignature
  typeGeneratorCorrect :
    (gen : underlyingSet (FunctionGenerator computableLogic)) -> (n : Nat) ->
     IsTrue (fst (typeGenerator gen) n) ->
     IsTrue (snd (typeGenerator gen) (GeneratedFunction computableLogic gen n))

CTAIIMorphismGenerator : {ctaii : ComputableTypeAssignmentInIdris} ->
  NatCharacteristicSignature -> Type
CTAIIMorphismGenerator signature =
  (generator : generatorSet (computableLogic ctaii) **
   (typeGenerator ctaii generator = signature))

interpretCTAIIGenerator : {ctaii: ComputableTypeAssignmentInIdris} ->
  {signature : NatCharacteristicSignature} ->
  CTAIIMorphismGenerator {ctaii} signature ->
  TotalComputableFunction
interpretCTAIIGenerator {ctaii} f =
  GeneratedFunction (computableLogic ctaii) (fst f)

ctaiiGeneratorCompose : (ctaii : ComputableTypeAssignmentInIdris) ->
  {a, b, c : NatCharacteristic} ->
  (f : CTAIIMorphismGenerator {ctaii} (b, c)) ->
  (g : CTAIIMorphismGenerator {ctaii} (a, b)) ->
  TotalComputableFunction
ctaiiGeneratorCompose ctaii {a} {b} {c} f g =
  (interpretCTAIIGenerator {ctaii} f) .  (interpretCTAIIGenerator {ctaii} g)

ctaiiComposeCorrect : (ctaii : ComputableTypeAssignmentInIdris) ->
  {a, b, c : NatCharacteristic} ->
  (f : CTAIIMorphismGenerator {ctaii} (b, c)) ->
  (g : CTAIIMorphismGenerator {ctaii} (a, b)) ->
  (n : Nat) ->
  IsTrue (a n) ->
  IsTrue (c (ctaiiGeneratorCompose ctaii f g n))
ctaiiComposeCorrect ctaii (f_gen ** f_sig) (g_gen ** g_sig) n inDomain =
  let
    f_dom = PairFstEq f_sig
    f_cod = PairSndEq f_sig
    g_dom = PairFstEq g_sig
    g_cod = PairSndEq g_sig
    n_in_domain_g = replace {p=(\func => func n = True)} (sym g_dom) inDomain
    g_n_correct = typeGeneratorCorrect ctaii g_gen n n_in_domain_g
    b_n =
      replace
        {p=(\func =>
             func (GeneratedFunction (computableLogic ctaii) g_gen n) = True)}
      g_cod
      g_n_correct
    g_n_in_domain_f =
      replace
        {p=(\func =>
             func (GeneratedFunction (computableLogic ctaii) g_gen n) = True)}
      (sym f_dom)
      b_n
    f_g_n_correct =
      typeGeneratorCorrect ctaii f_gen
        (GeneratedFunction (computableLogic ctaii) g_gen n)
        g_n_in_domain_f
  in
  rewrite (sym f_cod) in f_g_n_correct

CTAIICategory : ComputableTypeAssignmentInIdris -> FreeCategory
CTAIICategory ctaii =
  MkFreeCategory NatCharacteristic (CTAIIMorphismGenerator {ctaii})

record MetaLogicInIdris where
  constructor MkMLII
  ObjectLogic : ComputableLogicInIdris
  AssertionGenerator : Countable
  GeneratedAssertion :
    fromUnderlying AssertionGenerator
      (morphism : FreeMorphism {cat=(CLIICategory ObjectLogic)} ((), ()) **
       precondition : NatCharacteristic **
       postcondition : NatCharacteristic **
       ((n : Nat) ->
        NatCharacteristicTrue precondition n ->
        NatCharacteristicTrue postcondition
          (interpretCTIIMorphism {clii=ObjectLogic} morphism n)))

mutual
  data NSExp : Type where
    NSNat : Nat -> NSExp
    NSTuple : NSList -> NSExp

  NSList : Type
  NSList = List NSExp

NSFunc : Type
NSFunc = NSExp -> NSExp

BNSPred : Type
BNSPred = (exp : NSExp) -> Bool

NSPair : Type
NSPair = PairOf NSExp

BNSPPred : Type
BNSPPred = (pair : NSPair) -> Bool

BNSLPred : Type
BNSLPred = (list : NSList) -> Bool

NSPairExp : NSExp -> NSExp -> NSExp
NSPairExp exp exp' = NSTuple [ exp , exp' ]

CheckType : Type
CheckType = (type : NSExp) -> BNSPred

HasType : (checkType : CheckType) -> (type, exp : NSExp) -> Type
HasType checkType type exp = IsTrue (checkType type exp)

decHasType : (checkType : CheckType) -> (type, exp : NSExp) ->
             Dec (HasType checkType type exp)
decHasType checkType type exp = decEq (checkType type exp) True

-- XXX factor out a general definition for WellTyped

ExpTypeIndex : Nat
ExpTypeIndex = 0

ExpTypeRep : NSExp
ExpTypeRep = NSNat ExpTypeIndex

ExpTyped : NSExp -> NSExp
ExpTyped = NSPairExp ExpTypeRep

ObjTypeIndex : Nat
ObjTypeIndex = S ExpTypeIndex

ObjTypeRep : NSExp
ObjTypeRep = NSNat ObjTypeIndex

ObjTyped : NSExp -> NSExp
ObjTyped = NSPairExp ObjTypeRep

HomObjTypeIndex : Nat
HomObjTypeIndex = S ObjTypeIndex

HomObjTypeRep : NSExp
HomObjTypeRep = NSNat HomObjTypeIndex

HomObjTyped : NSExp -> NSExp
HomObjTyped = NSPairExp HomObjTypeRep

FuncTypeIndex : Nat
FuncTypeIndex = S HomObjTypeIndex

FuncTypeRep : NSExp
FuncTypeRep = NSNat FuncTypeIndex

FuncTyped : (domain, codomain : NSExp) -> NSExp
FuncTyped domain codomain = NSPairExp FuncTypeRep (NSPairExp domain codomain)

mutual
  -- XXX pass in generators for functions from PSExp to PSExp
  -- XXX will that replace checkType altogether

  data TSNType :
    (checkType : CheckType) -> (representative : NSExp) -> Type where
      -- XXX does ExpType only need to be in a metalanguage
      ExpType : {checkType : CheckType} ->
                TSNType checkType ExpTypeRep
      ObjType : (checkType : CheckType) ->
                (exp : NSExp) ->
                HasType checkType ObjTypeRep exp ->
                TSNType checkType (ObjTyped exp)
      -- XXX does HomObj only need to be in a metalanguage
      HomObj : (checkType : CheckType) ->
               (exp : NSExp) ->
               TSNFuncType checkType exp ->
               TSNType checkType (HomObjTyped exp)
      -- XXX application of type constructor to type

  data TSNFuncType :
    (checkType : CheckType) -> (representative : NSExp) -> Type where
      FuncType : (checkType : CheckType) ->
                 {domainRep, codomainRep : NSExp} ->
                 (domain : TSNType checkType domainRep) ->
                 (codomain : TSNType checkType codomainRep) ->
                 TSNFuncType checkType (FuncTyped domainRep codomainRep)

  data TSNFunction :
    {checkType : CheckType} ->
    TSNFuncType checkType representative ->
    (representative : NSExp) ->
    Type where
      CheckedFunc : (checkType : CheckType) ->
                    {domainRep, codomainRep : NSExp} ->
                    (domain : TSNType checkType domainRep) ->
                    (codomain : TSNType checkType codomainRep) ->
                    (func : NSExp -> NSExp) ->
                    (representative : NSExp) ->
                    (wellTyped : (exp : NSExp) ->
                                 HasType checkType domainRep exp ->
                                 HasType checkType codomainRep (func exp)) ->
                    TSNFunction
                      {checkType}
                      (FuncType checkType domain codomain)
                      representative
      -- XXX once we have generators, split up into generator & composition --
      -- maybe just using FreeCategory
-}
