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
`Differentiable`, `ContDiff`, etc. so `fun_prop` should work for such goals

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

basic setup and using the tactic

### Type of theorems

  - lambda theorems
  - function theorems - compositional form vs simple
  - morphism theorems
  - transition theorems

- checking theorems are correctly recognized

### Dischargning subgoals and `ContinuousAt/On` variants

### Local hypothesis

### Bundled Morphisms

#### Transition theorems

-- the need for transition theorems and how they are used
-- between different properties
-- between different data

### Debugging


### Tactic design
-/
