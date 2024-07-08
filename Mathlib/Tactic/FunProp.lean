/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Mathlib.Tactic.FunProp.Attr
import Mathlib.Tactic.FunProp.Core
import Mathlib.Tactic.FunProp.Decl
import Mathlib.Tactic.FunProp.Elab
import Mathlib.Tactic.FunProp.FunctionData
import Mathlib.Tactic.FunProp.Mor
import Mathlib.Tactic.FunProp.RefinedDiscrTree
import Mathlib.Tactic.FunProp.StateList
import Mathlib.Tactic.FunProp.Theorems
import Mathlib.Tactic.FunProp.ToBatteries
import Mathlib.Tactic.FunProp.Types

/-!
# Tactic `fun_prop` for proving function properties like `Continuous f`, `Differentiable ℝ f`, ...

**Basic use:**
Using `fun_prop` tactic should be as simple as
```lean
example : Continuous (fun x : ℝ => x * sin x) := by fun_prop
```
Mathlib sets up `fun_prop` for many different properties like `Continuous`, `Measurable`,
`Differentiable`, `ContDiff`, etc. so `fun_prop` should work for such goals. How the `fun_prop`
tactic works is that it decomposes the function in question into a composition of elementary
functions and then looks up if every single elementary function is e.g. `Continuous`.

For `ContinuousAt/On/Within` variants one has to specify a tactic to solve potential side goals
with `disch:=<tactic>`. For example
```lean
example (y : ℝ) (hy : y ≠ 0) : ContinuousAt (fun x : ℝ => 1/x) y := by fun_prop (disch:=assumption)
```

**Basic debugging:**
The most common issue is that a function is missing the appropriate theorem. For example
```lean
import Mathlib.Data.Complex.Exponential
example : Continuous (fun x : ℝ => x * Real.sin x) := by fun_prop
```
Fails with the error
```lean
`fun_prop` was unable to prove `Continuous fun x => x * x.sin`

Issues:
  No theorems found for `Real.sin` in order to prove `Continuous fun x => x.sin`
```
this can be easily fixed by importing `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`
where the theorem `Real.continuous_sin` is marked with the `fun_prop` attribute.

When the issue is not simply a few missing theorems then you can turn on the option
```lean
set_option trace.Meta.Tactic.fun_prop true
```
and the trace of how `fun_prop` steps through the whole expression is displayed.


**Basic setup for new function property:**

To set up `fun_prop` for a new function property you have to:

1. Mark the function property with `fun_prop` attribute when defining it
```lean
@[fun_prop]
def Continuous (f : X → Y) := ...
```
or later on with
```lean
attribute [fun_prop] Continuous
```

2. Mark basic lambda calclus theorems. The bare mininum is the identity, constant and composition
theorems
```lean
@[fun_prop]
theorems continuous_id : Continuous (fun x => x) := ...

@[fun_prop]
theorems continuous_const (y : Y) : Continuous (fun x => y) := ...

@[fun_prop]
theorems continuous_comp (f : Y → Z) (g : X → Y) (hf : Continuous f) (hg : Continuous g) :
  Continuous (fun x => f (g x)) := ...
```
The constant theorem is not absolutely necessary as for example `IsLinearMap ℝ (fun x => y)` does
not hold but we almost certainly want to mark it if it is available.

You shold also provide theorems for `Prod.mk`, `Prod.fst` and `Prod.snd`.
```
theorems continuous_fst (f : X → Y×Z) (hf : Continuous) : Continuous (fun x => (f x).fst) := ...
theorems continuous_snd (f : X → Y×Z) (hf : Continuous) : Continuous (fun x => (f x).snd) := ...
theorem continuous_prod_mk (f : X → Y) (g : X → Z)
   (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => Prod.mk (f x) (g x)) := ...
```


3. Mark concrete function theorems. They can be stated simply as
```lean
@[fun_prop]
theorem continuous_neg : Continuous (fun x => - x) := ...

@[fun_prop]
theorem continuous_add : Continuous (fun x : X×X => x.1 + x.2) := ...
```
where function of multiple arguments have to be appropriately uncurried. Alternatively, they can
be stated in compositional form as
```lean
@[fun_prop]
theorem continuous_neg (f : X → Y) (hf : Continuous f) : Continuous (fun x => - f x) := ...

@[fun_prop]
theorem continuous_add (f g : X → Y) (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x + g x) := ...
```
It is enough to provide function theorems in either form. It is mainly a matter of convenience.

With such a basic set up you should be able to prove continuity of basic algebraic expressions.

When marking theorems it is a good idea to check that a theorem has been registered correctly.
You can do this by turning on the `Meta.Tactic.fun_prop.attr` option. For example
(note that the notation `f x + g x` is just a syntactic sugar for `@HAdd.hAdd X Y Y _ (f x) (g x))
```
set_option trace.Meta.Tactic.fun_prop.attr true
@[fun_prop]
theorem continuous_add (f g : X → Y) (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => @HAdd.hAdd X Y Y _ (f x) (g x)) := sorry
```
displays
```lean
[Meta.Tactic.fun_prop.attr] function theorem: continuous_add
    function property: Continuous
    function name: HAdd.hAdd
    main arguments: [4, 5]
    applied arguments: 6
    form: .comp
```
Which exactly says that the theorem `continuous_add` states continuity of `HAdd.hAdd` in
4th and 5th arguments and the theorem is in compositional form.


### Advanced

### Type of theorems

There are four types of theorems that are treated a little bit differently.

  - Lambda theorems:
    These theorems about basic lambda calculus terms like identity, constant or composition etc.
    They are use when a bigger expression is decomposed into a sequence of function composition.
    They are also used when we for example know that function is continuous in `x` and `y` variable
    but we want continuity only in `x`.
    There is 5 of them and they should be formulated in the following way:
    - Identity theorem
    ```
    @[fun_prop]
    theorem continuous_id : Continuous (fun (x : X) => x) := ..
    ```
    - Constant theorem
    ```
    @[fun_prop]
    theorem continuous_const (y : Y) : Continuous (fun (x : X) => y) := ..
    ```
    - Composition theorem
    ```
    @[fun_prop]
    theorem continuous_comp
      (f : Y → Z) (g : X → Y)
      (hf : Continuous f) (hg : Continuous g) :
      Continuous (fun (x : X) => f (g x)) := ..
    ```
    - Apply theorem
    It can be either non-dependent version
    ```
    @[fun_prop]
    theorem continuous_apply (a : α) : Continuous (fun f : (α → X) => f a) := ..
    ```
    or dependent version
    ```
    @[fun_prop]
    theorem continuous_apply (a : α) : Continuous (fun f : ((a' : α) → E a') => f a) := ..
    ```
    - Pi theorem
    ```
    @[fun_prop]
    theorem continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x a)) :
       Continuous (fun x a => f x a) := ..
    ```

    Not all of these theorems have to be provided, but at least the identity and composition theorem
    should be.

    Use should also add theorems for `Prod.mk`, `Prod.fst` and `Prod.snd`. Technically speaking
    they fall under the *function theorems* category but without them `fun_prop` can't function
    properly. We are mentioning them as they are used together with *lambda theorems* to break
    compicated expressions into a composition of simpler functions.
    ```
    theorems continuous_fst (f : X → Y×Z) (hf : Continuous) : Continuous (fun x => (f x).fst) := ...
    theorems continuous_snd (f : X → Y×Z) (hf : Continuous) : Continuous (fun x => (f x).snd) := ...
    theorem continuous_prod_mk (f : X → Y) (g : X → Z) (hf : Continuous f) (hg : Continuous g) :
        Continuous (fun x => (f x, g x)) := ...
    ```

  - Function theorems
    Theorems about define functions. The main idea behind `fun_prop` tactic is that
    it decomposes an expression using *lambda theorem* into a composition of elementary functions
    and then uses `*function theorems* to prove that all of the elementary functions are e.g.
    continuous.

    The function theorem for `Neg.neg` and `Continuous` can be stated as
    ```
    @[fun_prop]
    theorem continuous_neg : Continuous (fun x => Neg.neg x) := ...
    ```
    or as
    ```
    @[fun_prop]
    theorem continuous_neg (f : X → Y) (hf : Continuous f) : Continuous (fun x => Neg.neg f x) := ...
    ```
    The first form is called *uncurried form* and the sencond for is called *compositional form*.
    You can provide either form, it is mainly a matter of convenience. You can check if the form of
    a theorem has been correctly detected by turning on the option
    `set_option Meta.Tactic.fun_prop.attr true`
    If you really care that the resulting proof term is as short as possible it is a good idea to
    provide both versions.

    One exception to this rule is the theorem for `Prod.mk` which has to be stated in compositional
    form.

    The reason the first form is called *uncurried* is because if we have a function of multiple
    arguments we have to uncurry the function
    ```
    @[fun_prop]
    theorem continuous_add : Continuous (fun (x : X×X) => HAdd.hAdd x.1 x.2) := ...
    ```
    and the *compositional form* of this this theorems is
    ```
    @[fun_prop]
    theorem continuous_add (f g : X → Y) (hf : Continuous f) (hg : Continous g) :
        Continuous (fun x => HAdd.hAdd (f x) (g x)) := ...
    ```

    When dealing with functions with multiple arguments, you need to state e.g. continuity only
    in the maximal set of argument .i.e. once we state that addition is jointly continuous in both
    arguments we do not need to add new theorems that addition is also continuous only in the
    first or only in the second argument. This is automatically infered using lambda theorems.

    Internally, when `fun_prop` tries to prove a function property of some function it looks at the
    head of the function body e.g. for fuction `fun x => HAdd.hAdd (Neg.neg x) (HMul.hMul x x)`
    the head is `HAdd.hAdd` and if the head function has registered *function theorem* it applies it.


  - Morphism theorems
    The `fun_prop` tactic can also deal bundled morphisms. For example we can state that every
    continuous linear function is indeed continuous
    ```
    theorem continuous_clm_eval (f : X →L[𝕜] Y) : Continuous 𝕜 (fun x => f x) := ...
    ```
    The head of the function body `f x` in this case is `DFunLike.coe` and this function is treated
    differently and its theorems are tracked separaterly.

    `DFunLike.coe` has two arguments the morphism `f` and the argument `x`. One differences is
    that theorems talking about the argument `f` have to be stated in the compositional form
    ```
    theorem continuous_clm_apply (f : X → Y →L[𝕜] Z) (hf : Continuous f) (y : Y) :
       Continuous 𝕜 (fun x => f x y) := ...
    ```
    note that without notation and coercion the function looks like `fun x => DFunLike.coe (f x) y`.

    In fact, not only `DFunLike.coe` but any function coercion is treated this way. Such function
    coercion has to be registered with `Lean.Meta.registerCoercion` with coerction type `.coeFun`.
    ```
    #eval Lean.Elab.Command.liftTermElabM do
      Lean.Meta.registerCoercion <morphism_to_fun_coerction_name>
        (some { numArgs := _, coercee := _, type := .coeFun })
    ```
    This is useful when you define your own bundled morphism and do not want to use mathlib's
    `FunLike` class.

  - Transition theorems
    Transition theorems allow `fun_prop` to infer one function property from another. For exmaple,
    theorem like
    ```
    @[fun_prop]
    theorem differentiable_continuous (f : X → Y) (hf : Differentiable 𝕜 f) :
        Continuous f := ...
    ```
    There are two features of these theorems, they mix different function properties and the
    conclusion is about a free variable `f`.

    Transition theorem are the most dangerous theorems as they considerably increase the search space
    as they do not simplify the function in question. For this reason `fun_prop` only applies
    transition theorems only on functions that can't be written as non-trivial composition of
    two functions. (`f = f ∘ id`, `f = id ∘ f` is considered to be trivial composition)

    For this reason, it is recomended to state *function theorems* for every property. For example,
    if you have a theorem
    ```
    @[fun_prop]
    theorem differentiable_neg : Differentiable ℝ (fun x => - x) := ...
    ```
    you shold also state continuous theorem
    ```
    @[fun_prop]
    theorem continuous_neg : Continuous ℝ (fun x => - x) := ...
    ```
    eventhough `fun_prop` can already prove `continuous_neg` from `differentiable_continuous` and
    `differentiable_neg`. Doing this will have considerable implact on `fun_prop` speed.

    Furthermore, one has to be careful when writing these theorem to not to introduce loops which
    are not supported. For example
    ```
    theorem clm_is_linear (f : X → Y) (hf : IsContinousLinearMap 𝕜 f) :
        IsLinearMap 𝕜 f := ...

    theorem clm_is_continuous (f : X → Y) (hf : IsContinousLinearMap 𝕜 f) :
        IsLinearMap 𝕜 f := ...

    theorem lin_cont_is_clm (f : X → Y) (hf : IsLinearMap 𝕜 f) (hf : Continuous 𝕜 f) :
        IsContinuousLinearMap 𝕜 f := ...
    ```
    would introduce a loop. It is prefered to have theorems only from more specialized property
    to a less specific i.e. `clm_is_linear` and `clm_is_continuous` are considered okay but
    `lin_cont_is_clm` is not.

    Transition theorems do not have to be between two compltely different properties. They can be
    between the same property differing by a parameter. Consider this example
    ```
    example (f : X → Y) (hf : ContDiff ℝ ∞ f) : ContDiff ℝ 2 (fun x => f x + f x) := by
      fun_prop (disch:=aesop)
    ```
    Which is first reduced to `ContDiff ℝ 2 f` using lambda theorems and then the transition theorem
    ```
    @[fun_prop]
    theorem contdiff_le (f : ContDiff 𝕜 n f) (h : m ≤ n) : ContDiff 𝕜 m f := ...
    ```
    is used together with `aesop` to discharge `2 ≤ ∞` subgoal.

-/
