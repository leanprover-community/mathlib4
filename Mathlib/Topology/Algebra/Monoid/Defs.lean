/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Algebra.Group.Basic

/-!
# Topological monoids - definitions

In this file we define three mixin typeclasses:

- `ContinuousMul M` says that the multiplication on `M` is continuous as a function on `M × M`;
- `ContinuousAdd M` says that the addition on `M` is continuous as a function on `M × M`.
- `SeparatelyContinuousMul M` says that the multiplication on `M` is continuous in each argument
  separately. This is strictly weaker than `ContinuousMul M`, but arises frequently in practice in
  functional analysis where one often considers topologies weaker than the norm topology. In these
  topologies it is frequently the case that the multiplication is not jointly continuous, but is
  continuous in each argument separately.

These classes are `Prop`-valued mixins,
i.e., they take data (`TopologicalSpace`, `Mul`/`Add`) as arguments
instead of extending typeclasses with these fields.

We also provide convenience dot notation lemmas like `Filter.Tendsto.mul` and `ContinuousAt.add`.
-/

@[expose] public section

open scoped Topology

/-- Basic hypothesis to talk about a topological additive monoid or a topological additive
semigroup. A topological additive monoid over `M`, for example, is obtained by requiring both the
instances `AddMonoid M` and `ContinuousAdd M`.

Continuity in each argument separately can be stated using `SeparatelyContinuousAdd α`. If one wants
only continuity in either the left or right argument, but not both one can use
`ContinuousConstVAdd α α`/`ContinuousConstVAdd αᵐᵒᵖ α`. -/
class ContinuousAdd (M : Type*) [TopologicalSpace M] [Add M] : Prop where
  continuous_add : Continuous fun p : M × M => p.1 + p.2

/-- Basic hypothesis to talk about a topological monoid or a topological semigroup.
A topological monoid over `M`, for example, is obtained by requiring both the instances `Monoid M`
and `ContinuousMul M`.

Continuity in each argument separately can be stated using `SeparatelyContinuousMul α`. If one wants
only continuity in either the left or right argument, but not both one can use
`ContinuousConstSMul α α`/`ContinuousConstSMul αᵐᵒᵖ α`. -/
@[to_additive]
class ContinuousMul (M : Type*) [TopologicalSpace M] [Mul M] : Prop where
  continuous_mul : Continuous fun p : M × M => p.1 * p.2

/-- A type class encoding that addition is continuous in each argument. This is weaker than
`ContinuousAdd`. -/
class SeparatelyContinuousAdd (M : Type*) [TopologicalSpace M] [Add M] : Prop where
  continuous_const_add {a : M} : Continuous (a + ·)
  continuous_add_const {a : M} : Continuous (· + a)

/-- A type class encoding that addition is continuous in each argument. This is weaker than
`ContinuousMul`. -/
@[to_additive]
class SeparatelyContinuousMul (M : Type*) [TopologicalSpace M] [Mul M] : Prop where
  continuous_const_mul {a : M} : Continuous (a * ·)
  continuous_mul_const {a : M} : Continuous (· * a)

section ContinuousMul

variable {M : Type*} [TopologicalSpace M] [Mul M] [ContinuousMul M]

@[to_additive (attr := continuity, fun_prop)]
theorem continuous_mul : Continuous fun p : M × M => p.1 * p.2 :=
  ContinuousMul.continuous_mul

@[to_additive]
theorem Filter.Tendsto.mul {α : Type*} {f g : α → M} {x : Filter α} {a b : M}
    (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (fun x ↦ f x * g x) x (𝓝 (a * b)) :=
  (continuous_mul.tendsto _).comp (hf.prodMk_nhds hg)

@[to_additive]
lemma Filter.tendsto_of_div_tendsto_one {α E : Type*} [CommGroup E] [TopologicalSpace E]
    [ContinuousMul E] {f g : α → E} (m : E) {x : Filter α} (hf : Tendsto f x (𝓝 m))
    (hfg : Tendsto (g / f) x (𝓝 1)) : Tendsto g x (𝓝 m) := by
  simpa using Tendsto.mul hf hfg

variable {X : Type*} [TopologicalSpace X] {f g : X → M} {s : Set X} {x : X}

@[to_fun (attr := to_additive (attr := continuity, fun_prop))]
theorem Continuous.mul (hf : Continuous f) (hg : Continuous g) :
    Continuous (f * g) :=
  continuous_mul.comp₂ hf hg

@[to_fun (attr := to_additive (attr := fun_prop))]
theorem ContinuousWithinAt.mul (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (f * g) s x :=
  Filter.Tendsto.mul hf hg

@[to_fun (attr := to_additive (attr := fun_prop))]
theorem ContinuousAt.mul (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (f * g) x :=
  Filter.Tendsto.mul hf hg

@[to_fun (attr := to_additive (attr := fun_prop))]
theorem ContinuousOn.mul (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (f * g) s := fun x hx ↦
  (hf x hx).mul (hg x hx)

end ContinuousMul

section

variable {M : Type*} [TopologicalSpace M] [Mul M]

@[to_additive]
instance [ContinuousMul M] : SeparatelyContinuousMul M where
  continuous_const_mul := continuous_const.mul continuous_id
  continuous_mul_const := continuous_id.mul continuous_const

variable [SeparatelyContinuousMul M]

@[to_additive (attr := continuity, fun_prop)]
theorem continuous_const_mul (m : M) : Continuous (m * ·) :=
  SeparatelyContinuousMul.continuous_const_mul

@[to_additive (attr := continuity, fun_prop)]
theorem continuous_mul_const (m : M) : Continuous (· * m) :=
  SeparatelyContinuousMul.continuous_mul_const

@[to_additive]
theorem Filter.Tendsto.const_mul {α : Type*} {f : α → M} {x : Filter α} {a : M}
    (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (b * f ·) x (𝓝 (b * a)) :=
  continuous_const_mul  b |>.tendsto _ |>.comp hf

@[to_additive]
theorem Filter.Tendsto.mul_const {α : Type*} {f : α → M} {x : Filter α} {a : M}
    (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (f · * b) x (𝓝 (a * b)) :=
  continuous_mul_const b |>.tendsto _ |>.comp hf

variable {X : Type*} [TopologicalSpace X] {f g : X → M} {s : Set X} {x : X}

@[to_additive (attr := continuity, fun_prop)]
theorem Continuous.mul_const (hf : Continuous f) (b : M) : Continuous (f · * b) :=
  continuous_mul_const b |>.comp hf

@[to_additive (attr := continuity, fun_prop)]
theorem Continuous.const_mul (hf : Continuous f) (b : M) : Continuous (b * f ·) :=
  continuous_const_mul b |>.comp hf

@[to_additive (attr := fun_prop)]
theorem ContinuousWithinAt.mul_const (hf : ContinuousWithinAt f s x) (b : M) :
    ContinuousWithinAt (f · * b) s x :=
  Filter.Tendsto.mul_const b hf

@[to_additive (attr := fun_prop)]
theorem ContinuousWithinAt.const_mul (hf : ContinuousWithinAt f s x) (b : M) :
    ContinuousWithinAt (b * f ·) s x :=
  Filter.Tendsto.const_mul b hf

@[to_additive (attr := fun_prop)]
theorem ContinuousAt.mul_const (hf : ContinuousAt f x) (b : M) :
    ContinuousAt (f · * b) x :=
  Filter.Tendsto.mul_const b hf

@[to_additive (attr := fun_prop)]
theorem ContinuousAt.const_mul (hf : ContinuousAt f x) (b : M) :
    ContinuousAt (b * f ·) x :=
  Filter.Tendsto.const_mul b hf

@[to_additive (attr := fun_prop)]
theorem ContinuousOn.mul_const (hf : ContinuousOn f s) (b : M) :
    ContinuousOn (f · * b) s :=
  fun x hx ↦ (hf x hx).mul_const b

@[to_additive (attr := fun_prop)]
theorem ContinuousOn.const_mul (hf : ContinuousOn f s) (b : M) :
    ContinuousOn (b * f ·) s :=
  fun x hx ↦ (hf x hx).const_mul b
