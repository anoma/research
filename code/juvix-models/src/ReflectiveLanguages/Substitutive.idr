module ReflectiveLanguages.Substitutive

import Library.FunctionsAndRelations
import Library.Decidability
import RefinedSExp.List
import RefinedSExp.SExp
import public Data.Nat

%default total

prefix 11 *^
prefix 11 *|
infixl 7 *~

mutual
  -- | An S-expression whose only atoms are de Bruijn indices.
  -- | The "C" prefix is for "Context"; de Bruijn indices are references
  -- | to variables in a context.
  -- |
  -- | An S-expression may be either an atom or a list of S-expressions.
  public export
  data CSExp : (contextSize : Nat) -> Type where
    -- | An atom, which is a de Bruijn index.
    (*^) : {contextSize : Nat} -> (index : Nat) ->
      {auto indexValid : index `LT` contextSize} -> CSExp contextSize
    -- | A list of S-expressions.
    (*|) : {contextSize : Nat} -> CSList contextSize -> CSExp contextSize

  -- | The list form of S-expressions whose only atoms are de Bruijn indices.
  public export
  data CSList : (contextSize : Nat) -> Type where
    -- | The empty list, which may be formed in any context.
    (*-) : {contextSize : Nat} -> CSList contextSize
    -- | A non-empty list whose tail's context includes the head.
    -- | This is a dependent list, also known as a telescope.
    (*~) : {contextSize : Nat} ->
      CSExp contextSize -> CSList (S contextSize) -> CSList contextSize

mutual
  public export
  -- | Introduce an unused variable into the context of an S-expression.
  csIntroOne : {origContextSize : Nat} -> CSExp origContextSize ->
    CSExp (S origContextSize)
  csIntroOne ((*^) index {indexValid}) =
    (*^) index {indexValid=(lteSuccRight indexValid)}
  csIntroOne (*| l) = *| (cslIntroOne l)

  public export
  -- | Introduce an unused variable into the context of an S-list.
  cslIntroOne : {origContextSize : Nat} -> CSList origContextSize ->
    CSList (S origContextSize)
  cslIntroOne (*-) = (*-)
  cslIntroOne (hd *~ tl) = csIntroOne hd *~ cslIntroOne tl

-- | Introduce unused variables into the context of an S-expression.
public export
csIntro : {newVars, origContextSize : Nat} ->
  CSExp origContextSize -> CSExp (newVars + origContextSize)
csIntro {newVars=Z} x = x
csIntro {newVars=(S Z)} x = csIntroOne x
csIntro {newVars=(S (S n))} x = csIntroOne (csIntro {newVars=(S n)} x)

-- | Introduce unused variables into the context of an S-list.
public export
cslIntro : {newVars, origContextSize : Nat} ->
  CSList origContextSize -> CSList (newVars + origContextSize)
cslIntro {newVars=Z} x = x
cslIntro {newVars=(S Z)} x = cslIntroOne x
cslIntro {newVars=(S (S n))} x = cslIntroOne (cslIntro {newVars=(S n)} x)

-- | A non-empty list whose tail's context does not include the head.
-- | This is a non-dependent cons.
infixr 7 *:
public export
(*:) : {contextSize : Nat} ->
  CSExp contextSize -> CSList contextSize -> CSList contextSize
hd *: tl = hd *~ (cslIntro {newVars=1} tl)

-- | A non-dependent list.
public export
csList : {contextSize : Nat} -> List (CSExp contextSize) -> CSList contextSize
csList [] = (*-)
csList (x :: xs) = x *: (csList xs)

-- | Decide whether all members of a list of indices are in bounds.
public export
isValidIndexList : (contextSize : Nat) -> List Nat -> Bool
isValidIndexList contextSize [] = True
isValidIndexList contextSize (index :: indices) =
  index < contextSize && isValidIndexList contextSize indices

-- | A proof that all members of a list of indices are in bounds.
public export
IsValidIndexList : (contextSize : Nat) -> List Nat -> Type
IsValidIndexList contextSize indices =
  IsTrue (isValidIndexList contextSize indices)

public export
CSNPred : Nat -> Type
CSNPred contextSize = CSExp contextSize -> Bool

public export
CSPred : Type
CSPred = (contextSize : Nat) -> CSNPred contextSize

public export
CSLNPred : Nat -> Type
CSLNPred contextSize = CSList contextSize -> Bool

public export
CSLPred : Type
CSLPred = (contextSize : Nat) -> CSLNPred contextSize

{-
-- | Keyword atoms of S-expressions which represent refinements.
public export
data Keyword : Type where
  -- | The initial refinement.
  KInitial : Keyword
  -- | The terminal refinement.
  KTerminal : Keyword
  -- | The unique expression which satisfies the terminal refinement.
  KUnit : Keyword
  -- | A primitive expression in a particular refined S-expression language.
  KPrimitive : Keyword

-- | Atoms of S-expressions which represent refinements.
public export
data RAtom : (symbol : Type) -> Type where
  -- | A keyword atom.
  RKeyword : {symbol : Type} -> Keyword -> RAtom symbol
  -- | A symbol specific to a particular language.
  RSymbol : {symbol : Type} -> symbol -> RAtom symbol

-- | Shorthand for the initial refinement in a particular refined S-expression
-- | language.
public export
RKInitial : {symbol : Type} -> RAtom symbol
RKInitial = RKeyword KInitial

-- | Shorthand for the terminal refinement in a particular refined S-expression
-- | language.
public export
RKTerminal : {symbol : Type} -> RAtom symbol
RKTerminal = RKeyword KTerminal

-- | Shorthand for the unique expression which satisfies the terminal refinement
-- | in a particular refined S-expression language.
public export
RKUnit : {symbol : Type} -> RAtom symbol
RKUnit = RKeyword KUnit

-- | Shorthand for a primitive atom in a particular refined S-expression
-- | language.
public export
RKPrimitive : {symbol : Type} -> RAtom symbol
RKPrimitive = RKeyword KPrimitive

-- | S-expressions using the symbols of a particular refined S-expression
-- | language, along with keywords, as atoms.
public export
RExp : (symbol : Type) -> Type
RExp = SExp . RAtom

-- | S-lists using the symbols of a particular refined S-expression
-- | language, along with keywords, as atoms.
public export
RList : (symbol : Type) -> Type
RList = SList . RAtom

-- | The definition of a particular refined S-expression language.
public export
record RefinementLanguage where
  constructor RefinementLanguageArgs
  rlApplicative : Type -> Type
  rlIsApplicative : Applicative rlApplicative
  rlContext : Type
  rlPrimitive : Type
  rlBadPrimitive : rlContext -> rlPrimitive -> Type
  rlPrimitiveType : (context : rlContext) -> (primitive : rlPrimitive) ->
    rlApplicative $ Either (RExp rlPrimitive) (rlBadPrimitive context primitive)

-- | The atoms of a particular S-expression language.
public export
RLAtom : RefinementLanguage -> Type
RLAtom = RAtom . rlPrimitive

-- | The S-expressions of a particular language.
public export
RLExp : RefinementLanguage -> Type
RLExp = RExp . rlPrimitive

-- | The S-lists of a particular language.
public export
RLList : RefinementLanguage -> Type
RLList = RList . rlPrimitive

-- | Shorthand for a primitive expression in a particular refined S-expression
-- | language.
public export
RKLPrimitive : (rl : RefinementLanguage) -> rl.rlPrimitive -> RLExp rl
RKLPrimitive rl primitive = RKPrimitive $:^ RSymbol primitive

mutual
  -- | An individual typecheck error for a particular refined S-expression
  -- | language.
  public export
  data TypecheckError : (rl : RefinementLanguage) ->
    (context : rl.rlContext) -> (x : RLExp rl) -> Type where
      BadPrimitive : rl.rlBadPrimitive context primitive ->
        TypecheckError rl context $ RKLPrimitive rl primitive

  -- | The result of a successful typecheck of @x, returning type @type.
  public export
  data TypecheckSuccess : (rl : RefinementLanguage) ->
    (context : rl.rlContext) -> (type : RLExp rl) -> (x : RLExp rl) ->
    Type where
      TerminalSuccess :
        (rl : RefinementLanguage) -> (context : rl.rlContext) ->
        TypecheckSuccess rl context ($^ RKTerminal) ($^ RKUnit)
      PrimitiveSuccess :
        (rl : RefinementLanguage) -> (context : rl.rlContext) ->
        (type : RLExp rl) -> (primitive : rl.rlPrimitive) ->
        TypecheckSuccess rl context type $ RKLPrimitive rl primitive

  -- | The result of successful typechecks of all members of a list of
  -- | refined S-expressions.
  public export
  data TypecheckSuccesses : (rl : RefinementLanguage) ->
    (context : rl.rlContext) -> List (PairOf (RLExp rl)) ->
    Type where
      TypecheckVacuous : TypecheckSuccesses rl context []
      TypecheckSuccessCons : TypecheckSuccess rl context type x ->
        TypecheckSuccesses rl context l ->
        TypecheckSuccesses rl context ((type, x) :: l)

  -- | The result of a failed typecheck of @x, which contains one or more
  -- | @TypecheckError terms.  It may also contain successful typechecks
  -- | of sub-expressions of the failed original expression.
  data TypecheckFailure : (rl : RefinementLanguage) ->
    (context : rl.rlContext) -> (x : RLExp rl) -> Type where
      TypecheckSubExpressionFailed : (rl : RefinementLanguage) ->
        (context : rl.rlContext) -> (l : RLList rl) ->
        TypecheckSomeFailure rl context l ->
        TypecheckFailure rl context ($| l)

  -- | The result of a failed typecheck of at least one member of @l.
  public export
  data TypecheckSomeFailure : (rl : RefinementLanguage) ->
    (context : rl.rlContext) -> RLList rl -> Type where
      TypecheckHeadFailed : (rl : RefinementLanguage) ->
        (context : rl.rlContext) -> (x : RLExp rl) -> (l : RLList rl) ->
        TypecheckFailure rl context x ->
        TypecheckResults rl context l ->
        TypecheckSomeFailure rl context (x :: l)
      TypecheckFailureCons : TypecheckResult rl context x ->
        TypecheckSomeFailure rl context l ->
        TypecheckSomeFailure rl context (x :: l)

  -- | The result of attempting to typecheck an S-expression as a word
  -- | of a particular refined S-expression language.
  public export
  data TypecheckResult : (rl : RefinementLanguage) ->
    (context : rl.rlContext) -> (x : RLExp rl) -> Type where
      TypecheckSucceeded : (rl : RefinementLanguage) ->
        (context : rl.rlContext) -> (type : RLExp rl) -> (x : RLExp rl) ->
        TypecheckSuccess rl context type x -> TypecheckResult rl context x
      TypecheckFailed : (rl : RefinementLanguage) ->
        (context : rl.rlContext) -> (x : RLExp rl) ->
        TypecheckFailure rl context x -> TypecheckResult rl context x

  -- | The results of attempting to typecheck each of a list of S-expressions
  -- | of a particular refined S-expression language.
  public export
  data TypecheckResults : (rl : RefinementLanguage) ->
    (context : rl.rlContext) -> (l : RLList rl) -> Type where
      TypecheckNil : (rl : RefinementLanguage) ->
        (context : rl.rlContext) -> TypecheckResults rl context []
      TypecheckCons : (rl : RefinementLanguage) ->
        (context : rl.rlContext) -> (x : RLExp rl) -> (l : RLList rl) ->
        TypecheckResult rl context x -> TypecheckResults rl context l ->
        TypecheckResults rl context (x :: l)

  -- | A witness that a typecheck result is a success.
  public export
  data IsTypecheckSuccess : {rl : RefinementLanguage} ->
    {context : rl.rlContext} -> {x : RLExp rl} ->
    TypecheckResult rl context x -> Type where
      ResultIsSuccessful :
        (success : TypecheckSuccess rl context type x) ->
        IsTypecheckSuccess (TypecheckSucceeded rl context type x success)

  -- | A witness that all typecheck results in a list are successes.
  public export
  data AreTypecheckSuccesses : {rl : RefinementLanguage} ->
    {context : rl.rlContext} -> {l : RLList rl} ->
    TypecheckResults rl context l -> Type where
      ResultsAreVacuous : AreTypecheckSuccesses (TypecheckNil rl context)
      ResultsAreSuccessful : {rl : RefinementLanguage} ->
        {context : rl.rlContext} ->
        {x : RLExp rl} -> {l : RLList rl} ->
        {result : TypecheckResult rl context x} ->
        {results : TypecheckResults rl context l} ->
        (success : IsTypecheckSuccess result) ->
        (successes : AreTypecheckSuccesses results) ->
        AreTypecheckSuccesses (TypecheckCons rl context x l result results)

{-
mutual
  -- | Check whether a term is a word of a particular refined S-expression
  -- | language.
  public export
  typecheck : (rl : RefinementLanguage) -> (context : rl.rlContext) ->
    (x : RLExp rl) -> rl.rlApplicative (TypecheckResult rl context x)
  typecheck rl context x = typecheck_hole

  -- | Check whether each of a list of terms is a word of a particular
  -- | refined S-expression language.
  public export
  typecheckList : (rl : RefinementLanguage) -> (context : rl.rlContext) ->
    (l : RLList rl) -> rl.rlApplicative (TypecheckResults rl context l)
  typecheckList rl context x = typecheckList_hole
  -}
-}
