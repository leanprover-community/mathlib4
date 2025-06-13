/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Constructions

import Mathlib.Tactic.FunProp


open Mathlib


/-!
The first step in using `fun_prop` is to mark desired function property with `fun_prop` attribute.
In this example we work with `Measurable`.
-/
attribute [fun_prop] Measurable


/-!
Now we can start marking theorems about `Measurable` with the attribute `@[fun_prop]`.
It is best to start with the basic lambda calculus rules. There are five of these rules in total

  - identity rule    `Measurable fun x => x`
  - constant rule    `Measurable fun x => y`
  - composition rule `Measurable f → Measurable g → Measurable fun x => f (g x)`
  - apply rule       `Measurable fun f => f x`
  - pi rule          `∀ i, Measurable (f · i) → Measurable fun x i => f x i`

You do not have to provide them all. For example `IsLinearMap` does not have the constant rule.
However, to have any hope at using `fun_prop` successfully you need to at least provide identity
and composition rule.
-/

attribute [fun_prop]
  measurable_id'
  measurable_const
  Measurable.comp'
  measurable_pi_apply
  measurable_pi_lambda

/-!
Measurability also behaves nicely with respect to taking products.
Let's mark the product constructor.
-/

attribute [fun_prop]
  Measurable.prodMk -- Measurable f → Measurable g → Measurable fun x => (f x, g x)

/-!
When it comes to product projection, their properties are usually stated in two different ways
```
measurable_fst : Measurable fun x => Prod.fst x
```
or
```
Measurable.fst : Measurable f → Measurable fun x => Prod.fst (f x)
```
The tactic `fun_prop` can work with both versions;
it should be sufficient to provide just one of them.
It does not hurt to provide both of them though.
-/

attribute [fun_prop]
  measurable_fst
  Measurable.fst
  measurable_snd
  Measurable.snd

/-!
A silly example on which `measurability` fails and `fun_prop` succeeds. Let's turn on tracing
to see what is going on
set_option trace.Meta.Tactic.fun_prop true in
-/
example {α} [MeasurableSpace α] (f : α → α → α) (hf : Measurable fun (x, y) ↦ f x y) (a : α) :
    Measurable (fun x => (f x a, f (f x x) (f (f x x) x))) := by
  -- This now takes longer than 200,000 heartbeats to fail, so I've commented it out.
  -- fail_if_success measurability
  fun_prop

/-!
To give more complicated examples we mark theorems about arithmetic operations with `@[fun_prop]`

Again we mark both versions of theorems. Internally `fun_prop` says that theorems like
`measurable_add` are in "uncurried form" and theorems like `Measurable.add` are in compositional
form.
-/

attribute [fun_prop]
  measurable_add
  measurable_sub
  measurable_mul
  measurable_neg
  measurable_div
  measurable_smul

  Measurable.add
  Measurable.sub
  Measurable.mul
  Measurable.neg
  Measurable.div
  Measurable.smul


/-!
An example of measurability of some arithmetic function
-/
example : Measurable fun x : ℝ => (x * x - 1) / x + (x - x*x) := by fun_prop



/-!
So far we talked about two types of theorems:
1. theorems about basic lambda calculus terms
2. theorems about defined functions

There are two other kinds of theorems `fun_prop` can work with:
3. transition theorems - theorems that imply e.g. measurability from continuity
4. morphism theorems - theorems talking about bundles

When you mark a theorem with `@[fun_prop]` attribute you can check the type of the
theorem by turning on the option `trace.Meta.Tactic.fun_prop.attr`.
-/

/-!
Transition theorems prove one function property from another. We already mentioned
that continuity implies measurability but there are many more. For example differentiability
implies continuity, linear map between finitely dimensional spaces is continuous etc.

The theorem proving measurability from continuity is `Continuous.measurable` so let's
mark it with `@[fun_prop]`
-/

attribute [fun_prop]
  Continuous.measurable -- Continuous f → Measurable f

/-!
For this theorem to be used properly we also need to set up `Continuous` with `fun_prop`.
The bare bones setup is
-/

attribute [fun_prop]

  Continuous
  continuous_id'
  continuous_const
  Continuous.comp'
  continuous_pi
  continuous_apply
  Continuous.prodMk
  Continuous.fst
  Continuous.snd


/-!
Now we can prove one of the earlier examples assuming the function is continuous instead of
measurable.
-/

example (f : ℝ → ℝ → ℝ) (hf : Continuous fun (x, y) ↦ f x y) (a : ℝ) :
    Measurable (fun x => (f x a, f (f x x) (f (f x x) x))) := by fun_prop


/-!
To keep `fun_prop` performant it is important to keep these "transition theorems" in the form
`P f → Q f` i.e. the conclusion has to talk about a single free variable `f`. Furthermore,
the "transition theorems" should **not** form a cycle.
-/


/-!
Lastly there are "morphism theorems". These are really just theorems about the properties of
`DFunLike.coe` and are treated somewhat specially.

Let's make continuous linear maps work with measurability. The function `DFunLike.coe` is
a function of two arguments `f : E →L[K] F` and `x : E`. Mathlib currently states
measurability of `DFunLike.coe` in `f` and `x` separately.

The theorem `ContinuousLinearMap.measurable` states measurability in `x` in uncurried form.
The theorem `ContinuousLinearMap.measurable_comp` states measurability in `x` in compositional form.
The theorem `ContinuousLinearMap.measurable_apply` states measurability in `f` in uncurried form.
The theorem `Measurable.apply_continuousLinearMap` states measurability in `f` in compositional
form.
-/

set_option linter.style.longLine false in
attribute [fun_prop]
  ContinuousLinearMap.measurable       -- Measurable fun (x : E) => DFunLike.coe L x
  ContinuousLinearMap.measurable_comp  -- Measurable φ → Measurable fun (x : E) => DFunLike.coe L (φ x)
  ContinuousLinearMap.measurable_apply -- Measurable fun (f : E →L[K] F) => DFunLike.coe f x
  Measurable.apply_continuousLinearMap -- Measurable L → Measurable fun (x : α) => DFunLike.coe (L x) v


/-!
A silly example that everything together works as expected
-/

example (f : ℝ → ℝ → (ℝ →L[ℝ] ℝ)) (hf : Continuous (fun (x, y) ↦ f x y)) :
    Measurable fun x => (f (x / x) (x * x) 1 + x) := by fun_prop

set_option linter.style.longLine false in
/-!
In the current state of `fun_prop`, morphism theorems **have to** be stated in compositional form.
Sometimes they might work in uncurried form but `fun_prop` is not designed that way right now.


In other cases the function property of `DFunLike.coe` can be stated jointly in `f` and `x`.
This is the case of `ContDiff n` and continuous linear maps. The theorem is `ContDiff.clm_apply`.


#check ContDiff.clm_apply -- {f : E → F →L[K] G} → {g : E → F} →  ContDiff K n f → ContDiff K n g → ContDiff K n fun x => DFunLike.coe (f x) (g x)

If possible, `fun_prop` theorem about `DFunLike.coe` should be state in this way.


That should be all about `fun_prop`, I hope you will enjoy using it :)
-/
