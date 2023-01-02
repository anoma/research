module RefinedSExp.Computation

import public Library.FunctionsAndRelations
import public Library.Decidability
import public Library.List
import public Category.ComputableCategories
import public RefinedSExp.SExp
import public RefinedSExp.Data

%default total

-- | Atoms representing the built-in morphisms of the Geb language, which is:
-- |
-- |  - Named as an homage to Hofstadter's _Gödel, Escher, Bach_
-- |  - A Lisp variant, in that it includes what Lisp calls `quote` and `eval`
-- |    as primitives
-- |  - Point-free, like Backus's FP, to avoid having to define how names and
-- |    contexts should be implemented, most importantly in the context of
-- |    metaprogramming (its built-in constructs are all combinators, not
-- |    lambdas, although names, contexts, and lambdas could all be defined in
-- |    terms of its primitive combinators, each in many different ways suitable
-- |    to different programming languages)
-- |  - Category-theoretical; its semantics are defined operationally by
-- |    small-step interpretation of its S-expressions as general (i.e.
-- |    potentially partial, potentially non-terminating) computable functions
-- |    from S-expressions to S-expressions.  Its atoms therefore
-- |    include both atoms representing morphisms in the one-object category of
-- |    general computable functions, and atoms representing elements of the
-- |    set of all S-expressions, using which its semantics may be defined.
-- |    The interpretation of an S-expression which itself represents an
-- |    interpretation, i.e., an element of the set of all expressions as
-- |    opposed to a morphism on computable functions on S-expressions, is a
-- |    computable function which fails on all inputs.  (In programming terms,
-- |    interpreting an S-expression that does not represent a morphism is an
-- |    attempt to execute something which is not a function.)
-- |  - A Turing machine, when the Turing operator (which is what Geb calls
-- |    its equivalent of Lisp's `eval`) is used without restrictions, or
-- |    with some restrictions but not enough to prevent the construction of
-- |    all general computable functions (including the partial and
-- |    non-terminating ones)
-- |  - A minimal metalogic -- just enough to be subject to Gödel's
-- |    incompleteness theorems -- when the Turing operator is not used at all.
-- |    It is possible, although unproven, that in this form it is equivalent
-- |    to Robinson arithmetic.
-- |  - A "potentially consistent metalogic" -- we can never refer to a
-- |    as absolutely consistent, in light of Gödel's results -- when the Turing
-- |    operator may be used, but only with restrictions which prevent any
-- |    S-expressions from being interpreted as non-total computable functions
-- |    (if the metalogic really is consistent, which, again, can not be
-- |    proven absolutely -- so we should say that all of its S-expressions
-- |    are interpreted as non-total computable functions _as far as anyone
-- |    knows_).  A given restriction of the Turing operator is known as the
-- |    type system -- type-checking an S-expression is equivalent to
-- |    claiming that all well-typed S-expressions are interpreted as total
-- |    computable functions.
-- |  - In light of the previous three points, a super-category of all
-- |    metalogics and programming languages (we are referring to a logic
-- |    strong enough to be subject to Gödel's incompleteness theorems, and
-- |    therefore to reflect and check typing derivations of other logics and
-- |    languages, including itself, as a "metalogic"), although it is itself,
-- |    as a complete category, unityped, in that its only object is that of
-- |    S-expressions (as Harper points out, "unityped" and "untyped" are
-- |    equivalent; in programming we also call this "dynamically typed")
-- |  - A category-theoretically unique construction, and therefore not only _a_
-- |    super-category of all metalogics and programming languages, but the
-- |    _only_ such super-category, up to isomorphism
-- |  - In light of the previous two points, a potential universal
-- |    "intermediate representation", or "open protocol description", for
-- |    all programming languages and metalogics, with which individual
-- |    compilers (and mathematical papers) could unambiguously and universally
-- |    define type systems for both potentially consistent metalogics and
-- |    programming languages and for Turing machines (which are inconsistent
-- |    when viewed as logics), unambiguously define notions of correct
-- |    transformations within and across metalogics and programming languages,
-- |    and unambiguously share definitions of metalogics and programming
-- |    languages with other compilers (and mathematical papers), in a way
-- |    which it itself can verify (in the sense of type-checking completely
-- |    enumerated alleged typing derivations), including the definition of
-- |    Geb itself.  As an open protocol description, it could also function
-- |    as a bridge between theorem provers / proof assistants / SMT solvers and
-- |    metalogics / programming languages:  defining the semantics of a
-- |    language or logic as a functor to a sub-category of Geb would allow
-- |    different theorem provers to prove results about it without requiring
-- |    any code to connect the specific language or logic to the specific proof
-- |    assistant
-- |  - Also in light of previous points, a potential component of compiler
-- |    architecture which allows as much of the compiler code as is possible
-- |    and efficient to be written in terms of category-theoretically unique
-- |    universal constructions, and therefore to be verified independently of
-- |    the specific type theory or theories (programming languages) which the
-- |    compiler is able to typecheck and compile.
-- |  - In light of the previous point, such a compiler architecture could also
-- |    be developed into a shared library usable by _all_ compilers which
-- |    adopt that architecture, allowing new programming languages to be
-- |    defined using that library, inheriting whichever concepts, constructs,
-- |    and theorems that its author wishes it to, and requiring the author
-- |    to write new code only for the concepts which distinguish the new
-- |    language from existing languages
-- |  - In light of its potential use as an open protocol, and a shared
-- |    "intermediate representation", a potential language for a shared library
-- |    of all formalizable knowledge -- a sort of symbolic Wikipedia -- whose
-- |    code could be checked by theorem provers and compiled directly into
-- |    executable programs
-- |  - Possibly a topos, although this is unproven (if so, then its internal
-- |    logic is inconsistent -- but the sub-categories of it which contain
-- |    only total computable functions, if there are any (if not, then
-- |    even a very weak (possibly Robinson) arithmetic is inconsistent), have
-- |    consistent internal logics)
-- |  - "Production-ready" upon initial release:  its category-theoretical
-- |    universality and uniqueness, together with its being defined solely
-- |    in terms of combinators whose semantics have been well-known and
-- |    unambiguously, formally defined for over sixty years (there's no new
-- |    math here!  Just a possibly-new software representation), and together
-- |    with the provable ability of Turing machines to define all programming
-- |    languages, and of Gödel-incomplete (i.e. reflective) metalogics to
-- |    check alleged proofs in all logics, mean that there is no alternative as
-- |    to how to define it, and no possibility of needing to extend the
-- |    language in order to allow define anything further to be defined _in_
-- |    it (assuming that computers are only ever able to execute those
-- |    functions that we currently know as "computable", i.e., those executable
-- |    by Turing machines).  All further Geb development can provably _only_ be
-- |    in libraries written in Geb; the language itself is provably
-- |    unchangeable.  (Any extension would no longer be category-theoretically
-- |    unique, and any restriction would either no longer be
-- |    category-theoretically unique or would no longer be a Turing machine.)
public export
data MorphismAtom : Type where
  -- | Represents failure of a general computable function application.
  Fail : MorphismAtom

  -- | Composition of general computable functions.
  Compose : MorphismAtom

  -- | The identity general computable function (which is total).
  Identity : MorphismAtom

  -- | Product introduction for general computable functions:  form a function
  -- | which returns tuples from a tuple of functions (which must have the same
  -- | domain for this operation to make sense).
  ProductIntro : MorphismAtom

  -- | Product elimination for general computable functions:  select a
  -- | function from a tuple of functions.  Also known as projection.
  ProductElimLeft : MorphismAtom
  ProductElimRight : MorphismAtom

  -- | Coproduct introduction for general computable functions:  choose one
  -- | of one or more possible forms.  Also known as injection.
  CoproductIntroLeft : MorphismAtom
  CoproductIntroRight : MorphismAtom

  -- | Coproduct elimination for general computable functions:  form a function
  -- | which accepts a coproduct and returns a case depending on which of the
  -- | coproduct's injections is passed in.  Can be viewed as a case statement.
  CoproductElim : MorphismAtom

  -- | A const-atom-valued function.  This is atom introduction.
  AtomConst : MorphismAtom

  -- | Decidable equality on atoms.
  -- | This combinator can be viewed as atom elimination.
  AtomTest : MorphismAtom

  -- | Reflection: introduce an S-expression-valued-function from an
  -- | atom-valued function and a product-of-S-expressions-valued function.
  -- |
  -- | This can be viewed as metaprogramming introduction.  It can be viewed as
  -- | a combinator form of the "quote" of Lisp.
  Gödel : MorphismAtom

  -- | The combinator which gives us unconstrained general recursion:
  -- | we name it after Turing; it is the "eval" of Lisp, but we wish
  -- | to avoid confusion with the "eval" of the category theory of
  -- | exponential objects.
  -- |
  -- | This combinator can be viewed as metaprogramming elimination.
  Turing : MorphismAtom

public export
morphismToString : MorphismAtom -> String
morphismToString Fail = "Fail"
morphismToString Compose = "Compose"
morphismToString Identity = "Identity"
morphismToString ProductIntro = "ProductIntro"
morphismToString ProductElimLeft = "ProductElimLeft"
morphismToString ProductElimRight = "ProductElimRight"
morphismToString CoproductIntroLeft = "CoproductIntroLeft"
morphismToString CoproductIntroRight = "CoproductIntroRight"
morphismToString CoproductElim = "CoproductElim"
morphismToString AtomConst = "AtomConst"
morphismToString AtomTest = "AtomTest"
morphismToString Gödel = "Gödel"
morphismToString Turing = "Turing"

public export
Show MorphismAtom where
  show m = ":" ++ morphismToString m

public export
mEncode : MorphismAtom -> Nat
mEncode Fail = 0
mEncode Compose = 1
mEncode Identity = 2
mEncode ProductIntro = 3
mEncode ProductElimLeft = 4
mEncode ProductElimRight = 5
mEncode CoproductIntroLeft = 6
mEncode CoproductIntroRight = 7
mEncode CoproductElim = 8
mEncode AtomConst = 9
mEncode AtomTest = 10
mEncode Gödel = 11
mEncode Turing = 12

public export
mDecode : Nat -> MorphismAtom
mDecode 0 = Fail
mDecode 1 = Compose
mDecode 2 = Identity
mDecode 3 = ProductIntro
mDecode 4 = ProductElimLeft
mDecode 5 = ProductElimRight
mDecode 6 = CoproductIntroLeft
mDecode 7 = CoproductIntroRight
mDecode 8 = CoproductElim
mDecode 9 = AtomConst
mDecode 10 = AtomTest
mDecode 11 = Gödel
mDecode 12 = Turing
mDecode _ = Fail

export
mDecodeIsLeftInverse :
  IsLeftInverseOf Computation.mEncode Computation.mDecode
mDecodeIsLeftInverse Fail = Refl
mDecodeIsLeftInverse Compose = Refl
mDecodeIsLeftInverse Identity = Refl
mDecodeIsLeftInverse ProductIntro = Refl
mDecodeIsLeftInverse ProductElimLeft = Refl
mDecodeIsLeftInverse ProductElimRight = Refl
mDecodeIsLeftInverse CoproductIntroLeft = Refl
mDecodeIsLeftInverse CoproductIntroRight = Refl
mDecodeIsLeftInverse CoproductElim = Refl
mDecodeIsLeftInverse AtomConst = Refl
mDecodeIsLeftInverse AtomTest = Refl
mDecodeIsLeftInverse Gödel = Refl
mDecodeIsLeftInverse Turing = Refl

export
mEncodeIsInjective : IsInjective Computation.mEncode
mEncodeIsInjective =
  leftInverseImpliesInjective mEncode {g=mDecode} mDecodeIsLeftInverse

public export
MInjection : Injection MorphismAtom Nat
MInjection = (mEncode ** mEncodeIsInjective)

public export
MCountable : Countable
MCountable = (MorphismAtom ** MInjection)

public export
mDecEq : DecEqPred MorphismAtom
mDecEq = countableEq MCountable

public export
DecEq MorphismAtom where
  decEq = mDecEq

public export
Eq MorphismAtom using decEqToEq where
  (==) = (==)

public export
Ord MorphismAtom where
  m < m' = mEncode m < mEncode m'

public export
MExp : Type
MExp = SExp MorphismAtom

public export
MList : Type
MList = SList MorphismAtom

public export
Show MExp where
  show = fst (sexpShows show)

public export
Show MList where
  show l = "(" ++ snd (sexpShows show) l ++ ")"

public export
msDecEq : DecEqPred MExp
msDecEq = sexpDecEq mDecEq

public export
mslDecEq : DecEqPred MList
mslDecEq = slistDecEq mDecEq

public export
DecEq MExp where
  decEq = msDecEq

public export
DecEq MList where
  decEq = mslDecEq

public export
Eq MExp using decEqToEq where
  (==) = (==)

-- | Atoms from which are constructed the elements of the set of S-expressions
-- | which we interpret as the domain and the codomain of general computable
-- | functions when defining Geb's semantics by interpretation.
public export
data InterpretationAtom : Type where
  -- | The interpretation of the failure of the application of a partial
  -- | computable function to an S-expression outside of its domain.
  Failure : InterpretationAtom

  -- | Apply a function to an argument.
  Apply : InterpretationAtom

  -- | The interpretation of a product.
  Pair : InterpretationAtom

  -- | The interpretation of a coproduct.
  ILeft : InterpretationAtom
  IRight : InterpretationAtom

  -- | The interpretation of an S-expression.
  ReflectedSExp : InterpretationAtom

public export
interpretationToString : InterpretationAtom -> String
interpretationToString Failure = "Failure"
interpretationToString Apply = "Apply"
interpretationToString Pair = "Pair"
interpretationToString ILeft = "ILeft"
interpretationToString IRight = "IRight"
interpretationToString ReflectedSExp = "ReflectedSExp"

public export
Show InterpretationAtom where
  show i = "*" ++ interpretationToString i

public export
iEncode : InterpretationAtom -> Nat
iEncode Failure = 0
iEncode Apply = 1
iEncode Pair = 2
iEncode ILeft = 3
iEncode IRight = 4
iEncode ReflectedSExp = 5

public export
iDecode : Nat -> InterpretationAtom
iDecode 0 = Failure
iDecode 1 = Apply
iDecode 2 = Pair
iDecode 3 = ILeft
iDecode 4 = IRight
iDecode 5 = ReflectedSExp
iDecode _ = Failure

export
iDecodeIsLeftInverse :
  IsLeftInverseOf Computation.iEncode Computation.iDecode
iDecodeIsLeftInverse Failure = Refl
iDecodeIsLeftInverse Apply = Refl
iDecodeIsLeftInverse Pair = Refl
iDecodeIsLeftInverse ILeft = Refl
iDecodeIsLeftInverse IRight = Refl
iDecodeIsLeftInverse ReflectedSExp = Refl

export
iEncodeIsInjective : IsInjective Computation.iEncode
iEncodeIsInjective =
  leftInverseImpliesInjective iEncode {g=iDecode} iDecodeIsLeftInverse

public export
IInjection : Injection InterpretationAtom Nat
IInjection = (iEncode ** iEncodeIsInjective)

public export
ICountable : Countable
ICountable = (InterpretationAtom ** IInjection)

public export
iDecEq : DecEqPred InterpretationAtom
iDecEq = countableEq ICountable

public export
DecEq InterpretationAtom where
  decEq = iDecEq

public export
Eq InterpretationAtom using decEqToEq where
  (==) = (==)

public export
Ord InterpretationAtom where
  i < i' = iEncode i < iEncode i'

public export
data ExtendedAtom : Type where
  EAMorphism : MorphismAtom -> ExtendedAtom
  EAInterpretation : InterpretationAtom -> ExtendedAtom
  EAData : Data -> ExtendedAtom

public export
Show ExtendedAtom where
  show (EAMorphism m) = show m
  show (EAInterpretation i) = show i
  show (EAData d) = show d

public export
eaShow : ExtendedAtom -> String
eaShow = show

public export
eaDecEq : DecEqPred ExtendedAtom
eaDecEq (EAMorphism m) (EAMorphism m') =
  case decEq m m' of
    Yes Refl => Yes Refl
    No neq => No $ \eq => case eq of Refl => neq Refl
eaDecEq (EAMorphism _) (EAInterpretation _) =
  No $ \eq => case eq of Refl impossible
eaDecEq (EAMorphism _) (EAData _) =
  No $ \eq => case eq of Refl impossible
eaDecEq (EAInterpretation _) (EAMorphism _) =
  No $ \eq => case eq of Refl impossible
eaDecEq (EAInterpretation i) (EAInterpretation i') = case decEq i i' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl
eaDecEq (EAInterpretation _) (EAData _) =
  No $ \eq => case eq of Refl impossible
eaDecEq (EAData _) (EAMorphism _) =
  No $ \eq => case eq of Refl impossible
eaDecEq (EAData _) (EAInterpretation _) =
  No $ \eq => case eq of Refl impossible
eaDecEq (EAData d) (EAData d') = case decEq d d' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl

public export
DecEq ExtendedAtom where
  decEq = eaDecEq

public export
Eq ExtendedAtom using decEqToEq where
  (==) = (==)

public export
Ord ExtendedAtom where
  EAMorphism m < EAMorphism m' = m < m'
  EAMorphism _ < EAInterpretation _ = True
  EAMorphism _ < EAData _ = True
  EAInterpretation _ < EAMorphism _ = False
  EAInterpretation i < EAInterpretation i' = i < i'
  EAInterpretation _ < EAData _ = True
  EAData _ < EAMorphism _ = False
  EAData _ < EAInterpretation _ = False
  EAData d < EAData d' = d < d'

public export
EAFail : ExtendedAtom
EAFail = EAMorphism Fail

public export
EAFailure : ExtendedAtom
EAFailure = EAInterpretation Failure

public export
EANat : Nat -> ExtendedAtom
EANat = EAData . DNat

public export
EAString : String -> ExtendedAtom
EAString = EAData . DString

public export
EExp : Type
EExp = SExp ExtendedAtom

public export
EList : Type
EList = SList ExtendedAtom

public export
Show EExp where
  show = fst (sexpShows show)

public export
Show EList where
  show l = "(" ++ snd (sexpShows show) l ++ ")"

public export
esDecEq : DecEqPred EExp
esDecEq = sexpDecEq eaDecEq

public export
eslDecEq : DecEqPred EList
eslDecEq = slistDecEq eaDecEq

public export
DecEq EExp where
  decEq = esDecEq

public export
DecEq EList where
  decEq = eslDecEq

public export
Eq EExp using decEqToEq where
  (==) = (==)

mutual
  public export
  MExpToEExp : MExp -> EExp
  MExpToEExp (a $* l) = EAMorphism a $* MListToEList l

  public export
  MListToEList : MList -> EList
  MListToEList [] = []
  MListToEList (x :: xs) = MExpToEExp x :: MListToEList xs

public export
ESFail : EExp
ESFail = $^ EAFail

public export
ESFailure : EExp
ESFailure = $^ EAFailure

public export
ESApply : EExp -> EExp -> EExp
ESApply f x = EAInterpretation Apply $* [f, x]

public export
ESPair : EExp -> EExp -> EExp
ESPair x y = EAInterpretation Pair $* [x, y]

public export
ESReflected : EExp -> EExp
ESReflected x = EAInterpretation ReflectedSExp $* [x]

public export
ESNat : Nat -> EExp
ESNat = ($^) . EANat

public export
ESString : String -> EExp
ESString = ($^) . EAString
