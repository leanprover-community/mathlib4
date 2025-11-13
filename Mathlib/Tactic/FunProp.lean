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
import Mathlib.Tactic.FunProp.Theorems
import Mathlib.Tactic.FunProp.ToBatteries
import Mathlib.Tactic.FunProp.Types

/-!
# Tactic `fun_prop` for proving function properties like `Continuous f`, `Differentiable ℝ f`, ...

**Basic use:**
Using the `fun_prop` tactic should be as simple as:
```lean
example : Continuous (fun x : ℝ => x * sin x) := by fun_prop
```
Mathlib sets up `fun_prop` for many different properties like `Continuous`, `Measurable`,
`Differentiable`, `ContDiff`, etc., so `fun_prop` should work for such goals. The basic idea behind
`fun_prop` is that it decomposes the function into a composition of elementary functions and then
checks if every single elementary function is, e.g., `Continuous`.

For `ContinuousAt/On/Within` variants, one has to specify a tactic to solve potential side goals
with `disch:=<tactic>`. For example:
```lean
example (y : ℝ) (hy : y ≠ 0) : ContinuousAt (fun x : ℝ => 1/x) y := by fun_prop (disch:=assumption)
```

**Basic debugging:**
The most common issue is that a function is missing the appropriate theorem. For example:
```lean
import Mathlib.Analysis.Complex.Trigonometric
example : Continuous (fun x : ℝ => x * Real.sin x) := by fun_prop
```
Fails with the error:
```lean
`fun_prop` was unable to prove `Continuous fun x => x * x.sin`

Issues:
  No theorems found for `Real.sin` in order to prove `Continuous fun x => x.sin`
```
This can be easily fixed by importing `Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean`
where the theorem `Real.continuous_sin` is marked with the `fun_prop` attribute.

When the issue is not simply a few missing theorems, you can turn on the option:
```lean
set_option trace.Meta.Tactic.fun_prop true
```
This will display the trace of how `fun_prop` steps through the whole expression.

**Basic setup for a new function property:**

To set up `fun_prop` for a new function property, you have to:

1. Mark the function property with the `fun_prop` attribute when defining it:
```lean
@[fun_prop]
def Continuous (f : X → Y) := ...
```
or later on with:
```lean
attribute [fun_prop] Continuous
```

2. Mark basic lambda calculus theorems. The bare minimum is the identity, constant, and composition
theorems:
```lean
@[fun_prop]
theorem continuous_id : Continuous (fun x => x) := ...

@[fun_prop]
theorem continuous_const (y : Y) : Continuous (fun x => y) := ...

@[fun_prop]
theorem continuous_comp (f : Y → Z) (g : X → Y) (hf : Continuous f) (hg : Continuous g) :
  Continuous (fun x => f (g x)) := ...
```
The constant theorem is not absolutely necessary as, for example, `IsLinearMap ℝ (fun x => y)` does
not hold, but we almost certainly want to mark it if it is available.

You should also provide theorems for `Prod.mk`, `Prod.fst`, and `Prod.snd`:
```lean
@[fun_prop]
theorem continuous_fst (f : X → Y × Z) (hf : Continuous f) : Continuous (fun x => (f x).fst) := ...
@[fun_prop]
theorem continuous_snd (f : X → Y × Z) (hf : Continuous f) : Continuous (fun x => (f x).snd) := ...
@[fun_prop]
theorem continuous_prod_mk (f : X → Y) (g : X → Z) (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => Prod.mk (f x) (g x)) := ...
```

3. Mark function theorems. They can be stated simply as:
```lean
@[fun_prop]
theorem continuous_neg : Continuous (fun x => - x) := ...

@[fun_prop]
theorem continuous_add : Continuous (fun x : X × X => x.1 + x.2) := ...
```
where functions of multiple arguments have to be appropriately uncurried. Alternatively, they can
be stated in compositional form as:
```lean
@[fun_prop]
theorem continuous_neg (f : X → Y) (hf : Continuous f) : Continuous (fun x => - f x) := ...

@[fun_prop]
theorem continuous_add (f g : X → Y) (hf : Continuous f) (hg : Continuous g) :
  Continuous (fun x => f x + g x) := ...
```
It is enough to provide function theorems in either form. It is mainly a matter of convenience.

With such a basic setup, you should be able to prove the continuity of basic algebraic expressions.

When marking theorems, it is a good idea to check that a theorem has been registered correctly.
You can do this by turning on the `Meta.Tactic.fun_prop.attr` option. For example:
(note that the notation `f x + g x` is just syntactic sugar for `@HAdd.hAdd X Y Y _ (f x) (g x)`)
```lean
set_option trace.Meta.Tactic.fun_prop.attr true
@[fun_prop]
theorem continuous_add (f g : X → Y) (hf : Continuous f) (hg : Continuous g) :
  Continuous (fun x => @HAdd.hAdd X Y Y _ (f x) (g x)) := ...
```
displays:
```lean
[Meta.Tactic.fun_prop.attr] function theorem: continuous_add
    function property: Continuous
    function name: HAdd.hAdd
    main arguments: [4, 5]
    applied arguments: 6
    form: compositional form
```
This indicates that the theorem `continuous_add` states the continuity of `HAdd.hAdd` in the 4th and
5th arguments and the theorem is in compositional form.

### Advanced

### Type of Theorems

There are four types of theorems that are used a bit differently.

- Lambda Theorems:
    These theorems are about basic lambda calculus terms like identity, constant, composition, etc.
    They are used when a bigger expression is decomposed into a sequence of function compositions.
    They are also used when, for example, we know that a function is continuous in the `x` and `y`
    variables, but we want continuity only in `x`.

    There are five of them, and they should be formulated in the following way:

    - Identity Theorem
    ```lean
    @[fun_prop]
    theorem continuous_id : Continuous (fun (x : X) => x) := ..
    ```

    - Constant Theorem
    ```lean
    @[fun_prop]
    theorem continuous_const (y : Y) : Continuous (fun (x : X) => y) := ..
    ```

    - Composition Theorem
    ```lean
    @[fun_prop]
    theorem continuous_comp (f : Y → Z) (g : X → Y) (hf : Continuous f) (hg : Continuous g) :
      Continuous (fun (x : X) => f (g x)) := ..
    ```

    - Apply Theorem
      It can be either non-dependent version
    ```lean
    @[fun_prop]
    theorem continuous_apply (a : α) : Continuous (fun f : (α → X) => f a) := ..
    ```
      or dependent version
    ```lean
    @[fun_prop]
    theorem continuous_apply (a : α) : Continuous (fun f : ((a' : α) → E a') => f a) := ..
    ```

    - Pi Theorem
    ```lean
    @[fun_prop]
    theorem continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x a)) :
       Continuous (fun x a => f x a) := ..
    ```

    Not all of these theorems have to be provided, but at least the identity and composition
    theorems should be.

    You should also add theorems for `Prod.mk`, `Prod.fst`, and `Prod.snd`. Technically speaking,
    they fall under the *function theorems* category, but without them, `fun_prop` can't function
    properly. We are mentioning them as they are used together with *lambda theorems* to break
    complicated expressions into a composition of simpler functions.
    ```lean
    @[fun_prop]
    theorem continuous_fst (f : X → Y × Z) (hf : Continuous f) :
        Continuous (fun x => (f x).fst) := ...
    @[fun_prop]
    theorem continuous_snd (f : X → Y × Z) (hf : Continuous f) :
        Continuous (fun x => (f x).snd) := ...
    @[fun_prop]
    theorem continuous_prod_mk (f : X → Y) (g : X → Z) (hf : Continuous f) (hg : Continuous g) :
        Continuous (fun x => (f x, g x)) := ...
    ```

- Function Theorems:
    When `fun_prop` breaks complicated expression apart using *lambda theorems* it then uses
    *function theorems* to prove that each piece is, for example, continuous.

    The function theorem for `Neg.neg` and `Continuous` can be stated as:
    ```lean
    @[fun_prop]
    theorem continuous_neg : Continuous (fun x => - x) := ...
    ```
    or as:
    ```lean
    @[fun_prop]
    theorem continuous_neg (f : X → Y) (hf : Continuous f) : Continuous (fun x => - f x) := ...
    ```
    The first form is called *uncurried form* and the second form is called *compositional form*.
    You can provide either form; it is mainly a matter of convenience. You can check if the form of
    a theorem has been correctly detected by turning on the option:
    ```lean
    set_option Meta.Tactic.fun_prop.attr true
    ```
    If you really care that the resulting proof term is as short as possible, it is a good idea to
    provide both versions.

    One exception to this rule is the theorem for `Prod.mk`, which has to be stated in compositional
    form. This because this theorem together with *lambda theorems* is used to break expression to
    smaller pieces and `fun_prop`  assumes it is written in compositional form.

    The reason the first form is called *uncurried* is because if we have a function of multiple
    arguments, we have to uncurry the function:
    ```lean
    @[fun_prop]
    theorem continuous_add : Continuous (fun (x : X × X) => x.1 + x.2) := ...
    ```
    and the *compositional form* of this theorem is:
    ```lean
    @[fun_prop]
    theorem continuous_add (f g : X → Y) (hf : Continuous f) (hg : Continuous g) :
        Continuous (fun x => f x + g x) := ...
    ```

    When dealing with functions with multiple arguments, you need to state, e.g., continuity only
    in the maximal set of arguments. Once we state that addition is jointly continuous in both
    arguments, we do not need to add new theorems that addition is also continuous only in the first
    or only in the second argument. This is automatically inferred using lambda theorems.


- Morphism Theorems:
    The `fun_prop` tactic can also deal with bundled morphisms. For example, we can state that every
    continuous linear function is indeed continuous:
    ```lean
    @[fun_prop]
    theorem continuous_clm_eval (f : X →L[𝕜] Y) : Continuous 𝕜 (fun x => f x) := ...
    ```
    In this case, the head of the function body `f x` is `DFunLike.coe`. This function is
    treated differently and its theorems are tracked separately.

    `DFunLike.coe` has two arguments: the morphism `f` and the argument `x`. One difference is that
    theorems talking about the argument `f` have to be stated in the compositional form:
    ```lean
    @[fun_prop]
    theorem continuous_clm_apply (f : X → Y →L[𝕜] Z) (hf : Continuous f) (y : Y) :
       Continuous 𝕜 (fun x => f x y) := ...
    ```
    Note that without notation and coercion, the function looks like
    `fun x => DFunLike.coe (f x) y`.

    In fact, not only `DFunLike.coe` but any function coercion is treated this way. Such function
    coercion has to be registered with `Lean.Meta.registerCoercion` with coercion type `.coeFun`.
    Here is an example of custom structure `MyFunLike` that should be considered as bundled
    morphism by `fun_prop`:
    ```lean
    structure MyFunLike (α β : Type) where
      toFun : α → β

    instance {α β} : CoeFun (MyFunLike α β) (fun _ => α → β) := ⟨MyFunLike.toFun⟩

    #eval Lean.Elab.Command.liftTermElabM do
      Lean.Meta.registerCoercion ``MyFunLike.toFun
        (.some { numArgs := 3, coercee := 2, type := .coeFun })
    ```

- Transition Theorems:
    Transition theorems allow `fun_prop` to infer one function property from another.
    For example, a theorem like:
    ```lean
    @[fun_prop]
    theorem differentiable_continuous (f : X → Y) (hf : Differentiable 𝕜 f) :
        Continuous f := ...
    ```
    There are two features of these theorems: they mix different function properties and the
    conclusion is about a free variable `f`.

    Transition theorems are the most dangerous theorems as they considerably increase the search
    space since they do not simplify the function in question. For this reason, `fun_prop` only
    applies transition theorems to functions that can't be written as a non-trivial composition of
    two functions (`f = f ∘ id`, `f = id ∘ f` is considered to be a trivial composition).

    For this reason, it is recommended to state *function theorems* for every property. For example,
    if you have a theorem:
    ```lean
    @[fun_prop]
    theorem differentiable_neg : Differentiable ℝ (fun x => -x) := ...
    ```
    you should also state the continuous theorem:
    ```lean
    @[fun_prop]
    theorem continuous_neg : Continuous ℝ (fun x => -x) := ...
    ```
    even though `fun_prop` can already prove `continuous_neg` from `differentiable_continuous` and
    `differentiable_neg`. Doing this will have a considerable impact on `fun_prop` speed.

    By default, `fun_prop` will not apply more then one transitions theorems consecutivelly. For
    example, it won't prove `AEMeasurable f` from `Continuous f` by using transition theorems
    `Measurable.aemeasurable` and `Continuous.measurable`. You can enable this by running
    `fun_prop (maxTransitionDepth :=2)`.
    Ideally `fun_prop` theorems should be transitivelly closed i.e. if `Measurable.aemeasurable` and
    `Continuous.measurable` are `fun_prop` theorems then `Continuous.aemeasurable` should be too.

    Transition theorems do not have to be between two completely different properties. They can be
    between the same property differing by a parameter. Consider this example:
    ```lean
    example (f : X → Y) (hf : ContDiff ℝ ∞ f) : ContDiff ℝ 2 (fun x => f x + f x) := by
      fun_prop (disch := aesop)
    ```
    which is first reduced to `ContDiff ℝ 2 f` using lambda theorems and then the transition
    theorem:
    ```lean
    @[fun_prop]
    theorem contdiff_le (f : ContDiff 𝕜 n f) (h : m ≤ n) : ContDiff 𝕜 m f := ...
    ```
    is used together with `aesop` to discharge the `2 ≤ ∞` subgoal.

-/
