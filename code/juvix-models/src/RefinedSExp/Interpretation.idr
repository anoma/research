module RefinedSExp.Interpretation

import public Library.FunctionsAndRelations
import public Library.Decidability
import public Library.List
import public RefinedSExp.Computation

%default total

-- | A single function application, on two fully-evaluated terms (that
-- | full sub-evaluation is the caller's responsibility to guarantee).
mutual
  public export
  eexpApplyOneMorphism : MorphismAtom -> EList -> EExp -> EExp
  eexpApplyOneMorphism Fail _ _ = ESFailure
  eexpApplyOneMorphism Compose [g, f] x = ESApply g (ESApply f x)
  eexpApplyOneMorphism Compose _ _ = ESFailure
  eexpApplyOneMorphism Identity [] x = x
  eexpApplyOneMorphism Identity _ _ = ESFailure
  eexpApplyOneMorphism ProductIntro [f, g] x =
    ESPair (ESApply f x) (ESApply g x)
  eexpApplyOneMorphism ProductIntro _ _ = ESFailure
  eexpApplyOneMorphism ProductElimLeft [] (EAInterpretation Pair $* [x, _]) = x
  eexpApplyOneMorphism ProductElimLeft _ _ = ESFailure
  eexpApplyOneMorphism ProductElimRight [] (EAInterpretation Pair $* [_, y]) = y
  eexpApplyOneMorphism ProductElimRight _ _ = ESFailure
  eexpApplyOneMorphism CoproductIntroLeft [] x = EAInterpretation ILeft $* [x]
  eexpApplyOneMorphism CoproductIntroLeft _ _ = ESFailure
  eexpApplyOneMorphism CoproductIntroRight [] x = EAInterpretation IRight $* [x]
  eexpApplyOneMorphism CoproductIntroRight _ _ = ESFailure
  eexpApplyOneMorphism CoproductElim [l, _]
    (EAInterpretation ILeft $* [x]) = ESApply l x
  eexpApplyOneMorphism CoproductElim [_, r]
    (EAInterpretation IRight $* [x]) = ESApply r x
  eexpApplyOneMorphism CoproductElim _ _ = ESFailure
  eexpApplyOneMorphism AtomConst [a $* []] _ = ESReflected ($^ a)
  eexpApplyOneMorphism AtomConst _ _ = ESFailure
  eexpApplyOneMorphism AtomTest [(a $* []), (a' $* []), eq, neq] x =
    if a == a' then ESApply eq x else ESApply neq x
  eexpApplyOneMorphism AtomTest _ _ = ESFailure
  eexpApplyOneMorphism
    Gödel ((EAInterpretation ReflectedSExp $* [a $* []]) :: l) x =
      ESReflected (a $* applyList l x)
  eexpApplyOneMorphism Gödel _ _ = ESFailure
  eexpApplyOneMorphism Turing [EAInterpretation ReflectedSExp $* [f]] x =
    ESApply f x
  eexpApplyOneMorphism Turing _ _ = ESFailure

  public export
  applyList : EList -> EExp -> EList
  applyList [] _ = []
  applyList (g :: gs) x = ESApply g x :: applyList gs x

  public export
  eexpApplyOne : EExp -> EExp -> EExp
  eexpApplyOne (EAMorphism m $* margs) x = eexpApplyOneMorphism m margs x
  eexpApplyOne (EAInterpretation _ $* _) _ = ESFailure
  eexpApplyOne (EAData _ $* _) _ = ESFailure

  public export
  eexpReduceOne : ExtendedAtom -> EList -> Maybe EExp
  eexpReduceOne (EAInterpretation Apply) [m, x] = Just $ eexpApplyOne m x
  eexpReduceOne (EAInterpretation Apply) _ = Just ESFailure
  eexpReduceOne (EAInterpretation Failure) (_ :: _) = Just ESFailure
  eexpReduceOne _ _ = Nothing

  public export
  eexpInterpretStep : EExp -> Maybe EExp
  eexpInterpretStep (a $* l) = case elistInterpretStep l of
    Just l' => Just (a $* l')
    Nothing => eexpReduceOne a l

  public export
  elistInterpretStep : EList -> Maybe EList
  elistInterpretStep [] = Nothing
  elistInterpretStep (x :: l) = case eexpInterpretStep x of
    Just x' => Just (x' :: l)
    Nothing => case elistInterpretStep l of
      Just l' => Just (x :: l')
      Nothing => Nothing

public export
eexpInterpretSteps : Nat -> EExp -> EExp
eexpInterpretSteps Z x = x
eexpInterpretSteps (S n) x = case eexpInterpretStep x of
  Just x' => eexpInterpretSteps n x'
  Nothing => x

-- | A computable function whose termination Idris-2 can prove.
-- | It still returns "maybe" because it might be partial (its
-- | domain might not include all of EExp).
public export
TerminatingComputableFunction : Type
TerminatingComputableFunction = EExp -> Maybe EExp

-- | When composing computable functions, any failure of the computation
-- | of any argument of the first function application must produce a
-- | failure in the computation of the second function application.
infixl 1 #.
public export
(#.) : TerminatingComputableFunction -> TerminatingComputableFunction ->
  TerminatingComputableFunction
(#.) = flip (>=>)

-- | A total computable function returns some input for every output
-- | (its domain is all S-expressions and it terminates on all inputs).
public export
IsTotal : TerminatingComputableFunction -> Type
IsTotal f = (x : EExp) -> IsJust $ f x

public export
TotalComputableFunction : Type
TotalComputableFunction = EExp -> EExp

public export
toTotal :
  {f : TerminatingComputableFunction} -> IsTotal f -> TotalComputableFunction
toTotal isTotal x = IsJustElim $ isTotal x

-- | Extensional equality on computable functions.
infixl 1 #~~
public export
(#~~) : TerminatingComputableFunction -> TerminatingComputableFunction -> Type
f #~~ g = ((x : EExp) -> f x = g x)
