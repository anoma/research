module Category.SumsAndProducts

import public Category.Category
import public Category.Isomorphism
import public Category.Universality

%default total

TypeOperator : Category -> Type
TypeOperator cat = Object cat -> Object cat -> Object cat

IsUnitOf : {cat : Category} -> TypeOperator cat -> Object cat -> Type
IsUnitOf {cat} op u = (a : Object cat) ->
    (Isomorphic (op u a) a, Isomorphic (op a u) a)

TypeOperatorIsAssociative : {cat : Category} -> (op : TypeOperator cat) -> Type
TypeOperatorIsAssociative {cat} op = (a, b, c : Object cat) ->
    Isomorphic (op a (op b c)) (op (op a b) c)

IsMonoid : {cat : Category} -> TypeOperator cat -> Object cat -> Type
IsMonoid op u = (TypeOperatorIsAssociative op, IsUnitOf op u)

public export
ProjectionsFrom : {cat : Category} -> (source, target, target' : Object cat) ->
  Type
ProjectionsFrom {cat} source target target' =
  (Morphism cat source target, Morphism cat source target')

public export
InjectionsTo : {cat : Category} -> (target, source, source' : Object cat) ->
  Type
InjectionsTo {cat} target source source' =
  (Morphism cat source target, Morphism cat source' target)

public export
CandidateProduct : {cat : Category} -> (a, b : Object cat) -> Type
CandidateProduct {cat} a b =
    (c : Object cat ** SumsAndProducts.ProjectionsFrom c a b)

public export
CandidateCoproduct : {cat : Category} -> (a, b : Object cat) -> Type
CandidateCoproduct {cat} a b =
    (c : Object cat ** SumsAndProducts.InjectionsTo c a b)

public export
IsProduct : {cat : Category} -> (a, b : Object cat) ->
  SumsAndProducts.CandidateProduct {cat} a b -> Type
IsProduct {cat} a b c =
  (c' : SumsAndProducts.CandidateProduct a b) ->
    (m : Morphism cat (DPair.fst c') (DPair.fst c) **
     Universality.IsUniqueMorphismWithProperty
       (\m' =>
         ((Builtin.fst (DPair.snd c)) .* m = (Builtin.fst (DPair.snd c')),
          (Builtin.snd (DPair.snd c)) .* m = (Builtin.snd (DPair.snd c')))) m)

public export
IsCoproduct : {cat : Category} -> (a, b : Object cat) ->
  SumsAndProducts.CandidateCoproduct {cat} a b -> Type
IsCoproduct {cat} a b c =
  (c' : SumsAndProducts.CandidateCoproduct a b) ->
    (m : Morphism cat (fst c) (fst c') **
     Universality.IsUniqueMorphismWithProperty
       (\m' =>
         (m .* (fst (snd c)) = (fst (snd c')),
          m .* (snd (snd c)) = (snd (snd c')))) m)

public export
Product : {cat : Category} -> (a, b : Object cat) -> Type
Product a b =
    DPair (SumsAndProducts.CandidateProduct a b) (SumsAndProducts.IsProduct a b)

public export
candidateProduct : {cat : Category} -> {a, b : Object cat} ->
  SumsAndProducts.Product {cat} a b ->
  SumsAndProducts.CandidateProduct {cat} a b
candidateProduct {cat} prod = fst prod

public export
productObject : {cat : Category} -> {a, b : Object cat} ->
  SumsAndProducts.Product {cat} a b -> Object cat
productObject {cat} prod = fst (SumsAndProducts.candidateProduct prod)

public export
productProjections : {cat : Category} -> {a, b : Object cat} ->
  (prod : SumsAndProducts.Product {cat} a b) ->
  SumsAndProducts.ProjectionsFrom {cat}
    (SumsAndProducts.productObject {cat} {a} {b} prod) a b
productProjections {cat} {a} {b} prod =
  snd (SumsAndProducts.candidateProduct {a} {b} prod)

public export
productProperty : {cat : Category} -> {a, b : Object cat} ->
  (prod : SumsAndProducts.Product {cat} a b) ->
  SumsAndProducts.IsProduct {cat} a b
    (SumsAndProducts.candidateProduct {cat} {a} {b} prod)
productProperty {cat} prod = snd prod

public export
Coproduct : {cat : Category} -> (a, b : Object cat) -> Type
Coproduct a b =
  DPair (SumsAndProducts.CandidateCoproduct a b)
    (SumsAndProducts.IsCoproduct a b)

public export
candidateCoproduct : {cat : Category} -> {a, b : Object cat} ->
  SumsAndProducts.Coproduct {cat} a b ->
  SumsAndProducts.CandidateCoproduct {cat} a b
candidateCoproduct {cat} prod = fst prod

public export
coproductObject : {cat : Category} -> {a, b : Object cat} ->
  SumsAndProducts.Coproduct {cat} a b -> Object cat
coproductObject {cat} coprod = fst (SumsAndProducts.candidateCoproduct coprod)

public export
coproductProperty : {cat : Category} -> {a, b : Object cat} ->
  (coprod : SumsAndProducts.Coproduct {cat} a b) ->
  SumsAndProducts.IsCoproduct {cat} a b
    (SumsAndProducts.candidateCoproduct {cat} {a} {b} coprod)
coproductProperty {cat} coprod = snd coprod

public export
coproductInjections : {cat : Category} -> {a, b : Object cat} ->
  (coprod : SumsAndProducts.Coproduct {cat} a b) ->
  SumsAndProducts.InjectionsTo {cat}
    (SumsAndProducts.coproductObject {cat} {a} {b} coprod) a b
coproductInjections {cat} {a} {b} coprod =
  snd (SumsAndProducts.candidateCoproduct {a} {b} coprod)

public export
HasAllProducts : Category -> Type
HasAllProducts cat = (a, b : Object cat) -> SumsAndProducts.Product a b

public export
HasAllCoproducts : Category -> Type
HasAllCoproducts cat = (a, b : Object cat) -> SumsAndProducts.Coproduct a b

public export
morphismProduct : {c : Category} ->
  {a, b, b' : Object c} ->
  (prodb : SumsAndProducts.Product {cat=c} b b') ->
  (m : Morphism c a b) -> (m' : Morphism c a b') ->
  Morphism c a (SumsAndProducts.productObject {cat=c} {a=b} {b=b'} prodb)
morphismProduct prodb {a} {b} m m' =
  fst (SumsAndProducts.productProperty prodb (a ** (m, m')))

public export
morphismCoproduct : {c : Category} ->
  {a, a', b : Object c} ->
  (coproda : SumsAndProducts.Coproduct {cat=c} a a') ->
  (m : Morphism c a b) -> (m' : Morphism c a' b) ->
  Morphism c (SumsAndProducts.coproductObject {cat=c} {a=a} {b=a'} coproda) b
morphismCoproduct coproda {a} {b} m m' =
  fst (SumsAndProducts.coproductProperty coproda (b ** (m, m')))

parallelMorphismProduct : {c : Category} ->
  {a, a', b, b' : Object c} ->
  (proda : SumsAndProducts.Product {cat=c} a a') ->
  (prodb : SumsAndProducts.Product {cat=c} b b') ->
  (m : Morphism c a b) -> (m' : Morphism c a' b') ->
  Morphism c
    (SumsAndProducts.productObject {cat=c} {a=a} {b=a'} proda)
    (SumsAndProducts.productObject {cat=c} {a=b} {b=b'} prodb)
parallelMorphismProduct {c} proda prodb m m' =
  let
    projFromA = SumsAndProducts.productProjections proda
    leftProj = m .* (fst projFromA)
    rightProj = m' .* (snd projFromA)
  in
  SumsAndProducts.morphismProduct prodb leftProj rightProj

parallelMorphismCoproduct : {c : Category} ->
  {a, a', b, b' : Object c} ->
  (coproda : SumsAndProducts.Coproduct {cat=c} a a') ->
  (coprodb : SumsAndProducts.Coproduct {cat=c} b b') ->
  (m : Morphism c a b) -> (m' : Morphism c a' b') ->
  Morphism c
    (SumsAndProducts.coproductObject {cat=c} {a=a} {b=a'} coproda)
    (SumsAndProducts.coproductObject {cat=c} {a=b} {b=b'} coprodb)
parallelMorphismCoproduct {c} coproda coprodb m m' =
  let
    injToB = SumsAndProducts.coproductInjections coprodb
    leftInj = (fst injToB) .* m
    rightInj = (snd injToB) .* m'
  in
  SumsAndProducts.morphismCoproduct coproda leftInj rightInj

public export
record CartesianClosedCategory where
  CCC_cat : Category
  CCC_initial : Object CCC_cat
  CC_is_initial : IsInitial {cat=CCC_cat} CCC_initial
  CCC_terminal : Object CCC_cat
  CCC_is_terminal : Universality.IsTerminal {cat=CCC_cat} CCC_terminal
  CCC_has_all_products : SumsAndProducts.HasAllProducts CCC_cat
  CCC_has_all_sums : SumsAndProducts.HasAllCoproducts CCC_cat

public export
CCC_object : (ccc : CartesianClosedCategory) -> Type
CCC_object ccc = Object (CCC_cat ccc)

public export
CCC_morphism : {ccc : CartesianClosedCategory} ->
  CCC_object ccc -> CCC_object ccc -> Type
CCC_morphism {ccc} a b = Morphism (CCC_cat ccc) a b

public export
CCC_id : {ccc : CartesianClosedCategory} -> (a : CCC_object ccc) ->
  CCC_morphism {ccc} a a
CCC_id {ccc} a = Identity (CCC_cat ccc) a

public export
CCC_product : {ccc : CartesianClosedCategory} -> (a, b : CCC_object ccc) ->
  CCC_object ccc
CCC_product {ccc} a b = fst (fst (CCC_has_all_products ccc a b))

public export
CCC_sum : {ccc : CartesianClosedCategory} -> (a, b : CCC_object ccc) ->
  CCC_object ccc
CCC_sum {ccc} a b = fst (fst (CCC_has_all_sums ccc a b))

public export
CCC_morphism_product : {ccc : CartesianClosedCategory} ->
  {a, b, b' : CCC_object ccc} ->
  CCC_morphism {ccc} a b -> CCC_morphism {ccc} a b' ->
  CCC_morphism {ccc} a (CCC_product {ccc} b b')
CCC_morphism_product {ccc} {b} {b'} m m' =
  SumsAndProducts.morphismProduct (CCC_has_all_products ccc b b') m m'

public export
CCC_morphism_sum : {ccc : CartesianClosedCategory} ->
  {a, a', b : CCC_object ccc} ->
  CCC_morphism {ccc} a b -> CCC_morphism {ccc} a' b ->
  CCC_morphism {ccc} (CCC_sum {ccc} a a') b
CCC_morphism_sum {ccc} {a} {a'} m m' =
  SumsAndProducts.morphismCoproduct (CCC_has_all_sums ccc a a') m m'

public export
CCC_first : {ccc : CartesianClosedCategory} -> (a, b : CCC_object ccc) ->
  CCC_morphism {ccc} (CCC_product {ccc} a b) a
CCC_first a b =
  fst (SumsAndProducts.productProjections (CCC_has_all_products ccc a b))

public export
CCC_second : {ccc : CartesianClosedCategory} -> (a, b : CCC_object ccc) ->
  CCC_morphism {ccc} (CCC_product {ccc} a b) b
CCC_second a b =
  snd (SumsAndProducts.productProjections (CCC_has_all_products ccc a b))

public export
CCC_left : {ccc : CartesianClosedCategory} -> (a, b : CCC_object ccc) ->
  CCC_morphism {ccc} a (CCC_sum {ccc} a b)
CCC_left a b =
  fst (SumsAndProducts.coproductInjections (CCC_has_all_sums ccc a b))

public export
CCC_right : {ccc : CartesianClosedCategory} -> (a, b : CCC_object ccc) ->
  CCC_morphism {ccc} b (CCC_sum {ccc} a b)
CCC_right a b =
  snd (SumsAndProducts.coproductInjections (CCC_has_all_sums ccc a b))

public export
CCC_parallel_morphism_product : {ccc : CartesianClosedCategory} ->
  {a, a', b, b' : CCC_object ccc} ->
  CCC_morphism {ccc} a b -> CCC_morphism {ccc} a' b' ->
  CCC_morphism {ccc} (CCC_product {ccc} a a') (CCC_product {ccc} b b')
CCC_parallel_morphism_product {ccc} {a} {a'} {b} {b'} m m' =
  Category.SumsAndProducts.parallelMorphismProduct
    (CCC_has_all_products ccc a a') (CCC_has_all_products ccc b b') m m'

public export
CCC_parallel_morphism_sum : {ccc : CartesianClosedCategory} ->
  {a, a', b, b' : CCC_object ccc} ->
  CCC_morphism {ccc} a b -> CCC_morphism {ccc} a' b' ->
  CCC_morphism {ccc} (CCC_sum {ccc} a a') (CCC_sum {ccc} b b')
CCC_parallel_morphism_sum {ccc} {a} {a'} {b} {b'} m m' =
  Category.SumsAndProducts.parallelMorphismCoproduct
    (CCC_has_all_sums ccc a a') (CCC_has_all_sums ccc b b') m m'
