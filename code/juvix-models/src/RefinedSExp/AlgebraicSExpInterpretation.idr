module RefinedSExp.AlgebraicSExpInterpretation

import public RefinedSExp.AlgebraicSExp
import Data.Maybe
import Library.List

%default total

----------------------------------------------------------------------
---- Computable functions as (Idris-2) functions on S-expressions ----
----------------------------------------------------------------------

-- | A computable function takes an argument and either returns a result or
-- | fails.
public export
GeneralComputableFunction : Type
GeneralComputableFunction = RefinedSExp -> Maybe RefinedSExp

-- | When composing computable functions, any failure of the computation
-- | of any argument of the first function application must produce a
-- | failure in the computation of the second function application.
infixl 1 #.
public export
(#.) : GeneralComputableFunction -> GeneralComputableFunction ->
  GeneralComputableFunction
(#.) = flip (>=>)

-- | A total computable function returns some input for every output
-- | (its domain is all S-expressions and it terminates on all inputs).
public export
IsTotal : GeneralComputableFunction -> Type
IsTotal f = (x : RefinedSExp) -> IsJust $ f x

public export
TotalComputableFunction : Type
TotalComputableFunction = RefinedSExp -> RefinedSExp

public export
toTotal :
  {f : GeneralComputableFunction} -> IsTotal f -> TotalComputableFunction
toTotal isTotal x = IsJustElim $ isTotal x

-- | Extensional equality on computable functions.
infixl 1 #~~
public export
(#~~) : GeneralComputableFunction -> GeneralComputableFunction -> Type
f #~~ g = ((x : RefinedSExp) -> f x = g x)

--------------------------------
---- Computable refinements ----
--------------------------------

-- | A refinement is a characteristic function on S-expressions.  A
-- | refinement selects a decidable subset of S-expressions.
public export
Refinement : Type
Refinement = RefinedSExp -> Bool

public export
ListRefinement : Type
ListRefinement = RefinedSList -> Bool

-- | A refinement on S-expressions such that a given function succeeds
-- | on all expressions selected by the refinement.
public export
RefinesDomain : GeneralComputableFunction -> Refinement -> Type
RefinesDomain f r = (x : RefinedSExp) -> IsTrue (r x) -> IsJust (f x)

-- | A refinement on S-expressions such that any expression on which
-- | a given function succeeds is selected by the refinement.
public export
IncludesDomain : GeneralComputableFunction -> Refinement -> Type
IncludesDomain f r = (x : RefinedSExp) -> IsJust (f x) -> IsTrue (r x)

-- | A refinement on S-expressions which selects exactly those expressions
-- | for which a given function succeeds.
public export
CharacterizesDomain : GeneralComputableFunction -> Refinement -> Type
CharacterizesDomain f r = (RefinesDomain f r, IncludesDomain f r)

-- | A refinement on S-expressions such that any expression selected
-- | by the refinement is the output of a given function for some input.
public export
RefinesRange : GeneralComputableFunction -> Refinement -> Type
RefinesRange f r = (x : RefinedSExp) ->
  IsTrue (r x) -> (preX : RefinedSExp ** f preX = Just x)

-- | A refinement on S-expressions such that any successful output of the
-- | given function is selected by the refinement.
public export
IncludesRange : GeneralComputableFunction -> Refinement -> Type
IncludesRange f r = (x : RefinedSExp) ->
  (success : IsJust (f x)) -> IsTrue $ r $ IsJustElim success

-- | A refinement on S-expressions which selects exactly those expressions
-- | which are the outputs of a given function for some input.
public export
CharacterizesRange : GeneralComputableFunction -> Refinement -> Type
CharacterizesRange f r = (RefinesRange f r, IncludesRange f r)

-- | A refinement which may be treated as a predicate on the input-output
-- | behavior of an arbitrary general computable function.  This might be viewed
-- | as an unbundled dependent type.
public export
InputOutputRefinement : Type
InputOutputRefinement =
  (RefinedSExp -> Bool, -- The domain of the refinement (when it applies)
   Maybe RefinedSExp -> Bool, -- the possible return values
   RefinedSExp -> Maybe RefinedSExp -> Bool) -- How input and output relate

-- | The type of proofs that a given function's input-output behavior satisfies
-- | a given dependent refinement.
public export
HasInputOutputBehavior :
  InputOutputRefinement -> GeneralComputableFunction -> Type
HasInputOutputBehavior (domain, codomain, relation) f =
  (x : RefinedSExp) -> IsTrue (domain x) ->
    (IsTrue $ codomain (f x), IsTrue $ relation x (f x))

public export
IsRefinedBy : InputOutputRefinement -> Type
IsRefinedBy r = (f : GeneralComputableFunction) -> HasInputOutputBehavior r f

{-
-- | Compose two input/output refinements.
public export
composeInputOutputRefinements :
  (g, f : GeneralComputableFunction) ->
  (rg, rf : InputOutputRefinement) ->
  InputOutputRefinement
composeInputOutputRefinements g f rg rf = composeInputOutputRefinements_hole

public export
composeInputOutputRefinementProofs :
  {g, f : GeneralComputableFunction} ->
  {rg, rf : InputOutputRefinement} ->
  HasInputOutputBehavior rg g ->
  HasInputOutputBehavior rf f ->
  HasInputOutputBehavior (composeInputOutputRefinements g f rg rf) $ g #. f
composeInputOutputRefinementProofs {g} {f} {rg} {rf} rgp rgf =
  composeInputOutputRefinementProofs_hole
  -}

---------------------------------------------------------------------------
---- Definition of RefinedSExp language by interpretation into Idris-2 ----
---------------------------------------------------------------------------

public export
alwaysFail : GeneralComputableFunction
alwaysFail = \_ => Nothing

public export
NameInterpretation : Type
NameInterpretation = RefinedName -> GeneralComputableFunction

public export
InitialInterpretation : NameInterpretation
InitialInterpretation _ = alwaysFail

mutual
  -- | Interpret a refined S-expression as a general computatable function.
  -- | Note that this signature implies that we can _always_ do such an
  -- | interpretation.  That is true, even though a given random S-expression
  -- | would almost certainly be nonsense if interpreted as a function --
  -- | but we would still interpret it, simply as a function which failed
  -- | on all (or perhaps nearly all) inputs.
  public export
  interpretRSExp :
    NameInterpretation -> RefinedSExp -> GeneralComputableFunction

  -- The identity function always succeeds and returns its argument.
  interpretRSExp _ (RAKeyword RKIdentity $* []) = Just

  -- The identity atom should not have any arguments.
  interpretRSExp _ (RAKeyword RKIdentity $* _ :: _) = alwaysFail

  -- Composing a list folds the list with composition operator, using the
  -- identity function as the initial value.
  interpretRSExp interpretName (RAKeyword RKCompose $* l) =
    interpretAndComposeRSList interpretName l

  -- Void is a type, not a function; interpreted as a function, therefore,
  -- it always fails.
  interpretRSExp _ (RAKeyword RKVoid $* _) = alwaysFail

  -- FromVoid is ex falso -- a legitimate way of reasoning.  However,
  -- it is, and should be, impossible to _interpret_ -- because it can
  -- only be called on a paramater which can never be constructed (if the
  -- logic is consistent).  Therefore, an attempt to interpret it always
  -- fails (and there is no sensible interpretation that we could give it).
  interpretRSExp _ (RAKeyword RKFromVoid $* _) = alwaysFail

  -- UnitType is a type, not a function; interpreted as a function, therefore,
  -- it always fails.
  interpretRSExp _ (RAKeyword RKUnitType $* _) = alwaysFail

  -- UnitTerm is a term, not a function; interpreted as a function, therefore,
  -- it always fails.
  interpretRSExp _ (RAKeyword RKUnitTerm $* _) = alwaysFail

  -- The to-unit function is a constant function which returns the
  -- single term of unit type.
  interpretRSExp _ (RAKeyword RKToUnit $* []) = \_ => Just RSUnitTerm

  -- The to-unit function should not have any arguments.
  interpretRSExp _ (RAKeyword RKToUnit $* _ :: _) = alwaysFail

  -- A failed S-expression represents a function that fails on all inputs.
  interpretRSExp _ (RAKeyword RKFailed $* _) = alwaysFail

  -- A name is, perhaps not surprisingly, the one type of S-expression whose
  -- interpretation depends directly on the given name interpretation.
  -- (Composition depends indirectly on it.)
  interpretRSExp interpretName (RAName name $* []) = interpretName name

  -- A name takes no arguments; it is nothing but an atom with a
  -- decidable equality.
  interpretRSExp interpretName (RAName _ $* (_ :: _)) = alwaysFail

  -- Not implemented yet.
  interpretRSExp interpretName
    (RAKeyword RKWithName $* [RAName name $* [], interpretation]) =
      alwaysFail

  -- "withName" should take precisely two arguments, a name and its
  -- interpretation, and the name must be a name atom.  Any other
  -- form is illegal.
  interpretRSExp interpretName (RAKeyword RKWithName $* _) = alwaysFail

  public export
  interpretAndComposeRSList :
    NameInterpretation -> RefinedSList -> GeneralComputableFunction
  interpretAndComposeRSList _ [] = Just
  interpretAndComposeRSList interpretName (x :: xs) =
    interpretRSExp interpretName x #. interpretAndComposeRSList interpretName xs

-- | Confirm that we correctly interpreted composition of an empty list
-- | as the identity.
ComposeNilIsIdentity : (interpretName : NameInterpretation) ->
  interpretAndComposeRSList interpretName [] =
    interpretRSExp interpretName RSIdentity
ComposeNilIsIdentity _ = Refl

public export
interpretClosedRSExp : RefinedSExp -> GeneralComputableFunction
interpretClosedRSExp = interpretRSExp InitialInterpretation

public export
interpretAndComposeClosedRSList : RefinedSList -> GeneralComputableFunction
interpretAndComposeClosedRSList =
  interpretAndComposeRSList InitialInterpretation

-------------------------------------------
---- Interpretation of primitive types ----
-------------------------------------------

public export
isNatAtom : Refinement
isNatAtom (a $* []) = atomIsNat a
isNatAtom _ = False

public export
isStringAtom : Refinement
isStringAtom (a $* []) = atomIsString a
isStringAtom _ = False

public export
isGivenNat : Nat -> Refinement
isGivenNat n ((RAName (RNNat a)) $* []) = n == a
isGivenNat _ _ = False

public export
isGivenString : String -> Refinement
isGivenString s ((RAName (RNString a)) $* []) = s == a
isGivenString _ _ = False

-----------------------------------------------
---- Extensions to admit error propagation ----
-----------------------------------------------

-- | Extend the notion of computable functions to include error propagation,
-- | to allow arbitrary descriptions of the forms of failures in earlier
-- | steps of chains of composed functions.

public export
Annotation : GeneralComputableFunction -> Type
Annotation f = (x : RefinedSExp) -> IsNothing (f x) -> RefinedSExp

public export
AnnotatedComputableFunction : Type
AnnotatedComputableFunction = DPair GeneralComputableFunction Annotation

public export
AnnotatedIsTotal : AnnotatedComputableFunction -> Type
AnnotatedIsTotal = IsTotal . fst

public export
FailurePropagator : Type
FailurePropagator = Endofunction RefinedSExp

public export
ExtendedComputableFunction : Type
ExtendedComputableFunction = (AnnotatedComputableFunction, FailurePropagator)

public export
ExtendedIsTotal : ExtendedComputableFunction -> Type
ExtendedIsTotal = AnnotatedIsTotal . fst

public export
composeUnannotated :
  ExtendedComputableFunction -> AnnotatedComputableFunction ->
  GeneralComputableFunction
composeUnannotated ((g ** _), _) (f ** _) = g #. f

public export
composedAnnotation :
  (g : ExtendedComputableFunction) -> (f : AnnotatedComputableFunction) ->
  Annotation (composeUnannotated g f)
composedAnnotation ((g ** gAnn), gFail) (f ** fAnn) x failure
  with (f x) proof fxeq
    composedAnnotation ((g ** gAnn), gFail) (f ** fAnn) x failure | Just fx =
      gAnn fx failure
    composedAnnotation ((g ** _), gFail) (f ** fAnn) x failure | Nothing =
      let
        rewriteAnn = replace {p=(\fx' => IsNothing (fx') -> RefinedSExp)} fxeq
      in
      gFail $ rewriteAnn (fAnn x) failure

-- | Compose an extended computable function with an annotated computable
-- | function.  (See "railway-oriented programming"!)
infixl 1 ~.
public export
extendedAfterAnnotated :
  ExtendedComputableFunction -> AnnotatedComputableFunction ->
  AnnotatedComputableFunction
extendedAfterAnnotated g f = (composeUnannotated g f ** composedAnnotation g f)

-- | Composition of extended computable functions according to the rules
-- | described above.  (See "railway-oriented programming" again!)
infixl 1 ##.
public export
(##.) : ExtendedComputableFunction -> ExtendedComputableFunction ->
  ExtendedComputableFunction
g ##. (f, fFail) = (extendedAfterAnnotated g f, snd g . fFail)

-------------------------------------------
---- Compilers as computable functions ----
-------------------------------------------

-- | A compiler is, like any program that we can execute, a computable
-- | function.  What distinguishes a compiler from arbitrary computable
-- | functions is that its outputs are expressions specifically intended
-- | to be interpreted as computable functions -- we may _attempt_ to
-- | interpret any S-expression, but most interpretations of most S-expressions
-- | as computable functions will produce computable functions which fail on
-- | most or all inputs or which don't have any interpretation that the
-- | programmer can make sense of.  We thus define "compiler" so as to
-- | represent a function whose outputs we are interested in interpreting
-- | as computable functions.  Indeed, we interpret them as _extended_
-- | computable functions so that a compiler may add error-checking to
-- | the programs it produces.
-- |
-- | Note that this definition admits the possibility that a single
-- | computable function might be interpreted as a compiler in more than
-- | one way.
public export
Compiler : ExtendedComputableFunction -> Type
Compiler f =
  (x : RefinedSExp) -> IsJust (fst (fst f) x) -> ExtendedComputableFunction

-- | A strongly normalizing language is one whose functions all terminate.
-- | To interpret a computable function as a compiler for a strongly
-- | normalizing language therefore means interpreting all successful
-- | outputs as _total_ computable functions.  This could be treated as
-- | an expression of the notion that "well-typed programs never go wrong".
-- |
-- | Note that this definition does not require that the compiler _itself_
-- | be a total computable function.
public export
Normalizing : {c : ExtendedComputableFunction} -> Compiler c -> Type
Normalizing {c} interpret =
  (x : RefinedSExp) -> (checked : IsJust (fst (fst c) x)) ->
  IsTotal (fst (fst (interpret x checked)))

-------------------------------------------------------------------
---- Interpretations as top-level metalanguage (Idris-2) types ----
-------------------------------------------------------------------

public export
Signature : Type
Signature = PairOf Type

-- | A typechecker in our top-level metalanguage -- in this case Idris-2 --
-- | is a function which decides whether any given expression represents
-- | a metalanguage function, and if so, of what type.
public export
MetaTypechecker : Type
MetaTypechecker = RefinedSExp -> Maybe Signature

-- | An interpreter in our top-level metalanguage -- in this case Idris-2 --
-- | is a function which, given a typechecker, interprets those expressions
-- | which typecheck as functions of the types that the typechecker returns.
public export
MetaInterpreter : MetaTypechecker -> Type
MetaInterpreter typechecker =
  (x : RefinedSExp) -> (signature : IsJust $ typechecker x) ->
  (fst $ IsJustElim signature) -> (snd $ IsJustElim signature)

public export
TypeFamily : Type
TypeFamily = (indexType : Type ** indexType -> Type)
