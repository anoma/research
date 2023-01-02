module Theories.SimplyTypedLambdaCalculus

import Data.List

%default total

namespace STLC

data
STLC_Type : Type where
    Boolean : STLC_Type
    Nat : STLC_Type
    Function : STLC_Type -> STLC_Type -> STLC_Type

CurriedFunction : List STLC_Type -> STLC_Type -> STLC_Type
CurriedFunction [] return_type = return_type
CurriedFunction (first_arg :: later_args) return_type =
    Function first_arg (CurriedFunction later_args return_type)

STLC_Context : Type
STLC_Context = List STLC_Type

data
STLC_Expression : STLC_Context -> STLC_Type -> Type where
    True : STLC_Expression context Boolean
    False  : STLC_Expression context Boolean
    If : STLC_Expression context (CurriedFunction [Boolean, type, type] type)
    Zero : STLC_Expression context Nat
    Successor : STLC_Expression context (Function Nat Nat)
    Recurse : STLC_Expression context
        (CurriedFunction [Nat, type, (CurriedFunction [Nat, type] type) ] type)
    Variable : (member : InBounds idx context) ->
        STLC_Expression context (List.index _ _ {ok=member})
    Lambda : {var_type, expr_type : STLC_Type} -> {context : STLC_Context} ->
        STLC_Expression (var_type :: context) expr_type ->
        STLC_Expression context (Function var_type expr_type)
    Intro : {var_type, expr_type : STLC_Type} -> {context : STLC_Context} ->
        STLC_Expression context expr_type ->
        STLC_Expression (var_type :: context) expr_type
    Apply : {domain, codomain : STLC_Type} ->
        STLC_Expression context (Function domain codomain) ->
        STLC_Expression context domain ->
        STLC_Expression context codomain

Var0 : {var_type : STLC_Type} -> {context : STLC_Context} ->
    STLC_Expression (var_type :: context) var_type
Var0 = Variable InFirst

Var1 : {preceding_type, var_type : STLC_Type} -> {context : STLC_Context} ->
    STLC_Expression (preceding_type :: var_type :: context) var_type
Var1 = Variable (InLater InFirst)

compose :
    {context : STLC_Context} ->
    {a, b, c : STLC_Type} ->
    STLC_Expression context (Function b c) ->
    STLC_Expression context (Function a b) ->
    STLC_Expression context (Function a c)
compose g f = Lambda (Apply (Intro g) (Apply (Intro f) Var0))

interpret_type : STLC_Type -> Type
interpret_type Boolean = Bool
interpret_type Nat = Nat
interpret_type (Function a b) = interpret_type a -> interpret_type b

data
MetaLanguageContext : STLC_Context -> Type where
    EmptyContext : MetaLanguageContext []
    ConsContext : {type : STLC_Type} -> {context : STLC_Context} ->
        interpret_type type -> MetaLanguageContext context ->
        MetaLanguageContext (type :: context)

context_get :
    {context : STLC_Context} ->
    (metaContext : MetaLanguageContext stlc_context) ->
    (member : InBounds idx stlc_context) ->
    interpret_type (List.index _ stlc_context {ok=member})
context_get EmptyContext _ impossible
context_get (ConsContext var_value context_value) InFirst = var_value
context_get (ConsContext {context=(_ :: context')}
    var_value context_value) (InLater inBounds) =
        context_get {context=context'} context_value inBounds

recurse : (n : Nat) -> (base_case : type) ->
    (inductive_case : Nat -> type -> type) -> type
recurse Z base_case _ = base_case
recurse (S n) base_case inductive_case =
    inductive_case n (recurse n base_case inductive_case)

interpret_expression :
    {context : STLC_Context} ->
    MetaLanguageContext context ->
    STLC_Expression context type ->
    interpret_type type
interpret_expression _ True = True
interpret_expression _ False = False
interpret_expression metaContext If = \bool_exp, if_case, else_case =>
    if bool_exp then
        if_case
    else
        else_case
interpret_expression _ Zero = Z
interpret_expression metaContext Successor = S
interpret_expression metaContext Recurse = recurse
interpret_expression {context} metaContext (Variable member) =
    context_get {context} metaContext member
interpret_expression metaContext (Lambda expression) =
    \interpret_var =>
        interpret_expression (ConsContext interpret_var metaContext) expression
interpret_expression EmptyContext (Intro expression) impossible
interpret_expression (ConsContext _ metaContext) (Intro expression) =
    interpret_expression metaContext expression
interpret_expression metaContext (Apply function expression) =
    (interpret_expression metaContext function)
        (interpret_expression metaContext expression)

nat_expr : Nat -> STLC_Expression context Nat
nat_expr Z = Zero
nat_expr (S n) = Apply Successor (nat_expr n)

const : {context : STLC_Context} -> {domain, codomain : STLC_Type} ->
    STLC_Expression context codomain ->
    STLC_Expression context (Function domain codomain)
const expr = Lambda (Intro expr)

recursive_def : {context : STLC_Context} -> {type : STLC_Type} ->
    STLC_Expression context (CurriedFunction [Nat, type] type) ->
    STLC_Expression context (CurriedFunction [Nat, type] type)
recursive_def inductive_case =
    Lambda (Lambda (Apply
        (Apply (Apply Recurse Var1) Var0) (Intro (Intro inductive_case))))

reverse_first_two_args : {context : STLC_Context} -> {arg1, arg2 : STLC_Type} ->
    {remaining_args : List STLC_Type} -> {return_type : STLC_Type} ->
    STLC_Expression context
        (CurriedFunction (arg1 :: arg2 :: remaining_args) return_type) ->
    STLC_Expression context
        (CurriedFunction (arg2 :: arg1 :: remaining_args) return_type)
reverse_first_two_args f =
    Lambda (Lambda (Apply (Apply (Intro (Intro f)) Var0) Var1))

repeat_unaryOp :
    {context : STLC_Context} -> {type : STLC_Type} ->
    STLC_Expression context (Function type type) ->
    STLC_Expression context (CurriedFunction [Nat, type] type)
repeat_unaryOp = recursive_def . const

repeat_applied_binOp :
    {context : STLC_Context} -> {type : STLC_Type} ->
    STLC_Expression context (CurriedFunction [type, type] type) ->
    STLC_Expression context (CurriedFunction [type, Nat, type] type)
repeat_applied_binOp binOp = Lambda (repeat_unaryOp (Apply (Intro binOp) Var0))

const_S : {context : STLC_Context} ->
    STLC_Expression context (CurriedFunction [Nat, Nat] Nat)
const_S = const Successor

add : {context : STLC_Context} ->
    STLC_Expression context (CurriedFunction [Nat, Nat] Nat)
add = recursive_def const_S

repeated_binOp : {context : STLC_Context} ->
    STLC_Expression context (CurriedFunction [Nat, Nat] Nat) ->
    STLC_Expression context (CurriedFunction [Nat, Nat, Nat] Nat)
repeated_binOp binOp =
    reverse_first_two_args {remaining_args=[Nat]}
        (Lambda (reverse_first_two_args {remaining_args=[]}
            (Apply (repeat_applied_binOp (Intro binOp)) Var0)))

multiply : {context : STLC_Context} ->
    STLC_Expression context (CurriedFunction [Nat, Nat] Nat)
multiply = Apply (repeated_binOp add) Zero

pred : {context : STLC_Context} -> STLC_Expression context (Function Nat Nat)
pred = Lambda (Apply (Apply (Apply Recurse Var0) Zero) (Lambda (Lambda (Var1))))

one : Nat
one = interpret_expression EmptyContext (Apply Successor Zero)

one_equals_one : SimplyTypedLambdaCalculus.one = (S Z)
one_equals_one = Refl

one_plus_two : Nat
one_plus_two = interpret_expression EmptyContext
    (Apply (Apply add (nat_expr 1)) (nat_expr 2))

one_plus_two_equals_three : SimplyTypedLambdaCalculus.one_plus_two = 3
one_plus_two_equals_three = Refl

two_by_four : Nat
two_by_four = interpret_expression EmptyContext
    (Apply (Apply multiply (nat_expr 2)) (nat_expr 4))

two_by_four_equals_eight : SimplyTypedLambdaCalculus.two_by_four = 8
two_by_four_equals_eight = Refl

eight_minus_one : Nat
eight_minus_one = interpret_expression EmptyContext (Apply pred (nat_expr 8))

eight_minus_one_equals_seven : SimplyTypedLambdaCalculus.eight_minus_one = 7
eight_minus_one_equals_seven = Refl
