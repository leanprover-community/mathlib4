/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Topology.Constructions.SumProd

/-!
# Topological monoids - definitions

In this file we define two mixin typeclasses:

- `ContinuousMul M` says that the multiplication on `M` is continuous as a function on `M × M`;
- `ContinuousAdd M` says that the addition on `M` is continuous as a function on `M × M`.

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

Continuity in only the left/right argument can be stated using
`ContinuousConstVAdd α α`/`ContinuousConstVAdd αᵐᵒᵖ α`. -/
class ContinuousAdd (M : Type*) [TopologicalSpace M] [Add M] : Prop where
  continuous_add : Continuous fun p : M × M => p.1 + p.2

/-- Basic hypothesis to talk about a topological monoid or a topological semigroup.
A topological monoid over `M`, for example, is obtained by requiring both the instances `Monoid M`
and `ContinuousMul M`.

Continuity in only the left/right argument can be stated using
`ContinuousConstSMul α α`/`ContinuousConstSMul αᵐᵒᵖ α`. -/
@[to_additive]
class ContinuousMul (M : Type*) [TopologicalSpace M] [Mul M] : Prop where
  continuous_mul : Continuous fun p : M × M => p.1 * p.2

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

@[to_additive (attr := continuity, fun_prop)]
theorem Continuous.mul (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => f x * g x :=
  continuous_mul.comp₂ hf hg

@[to_additive]
theorem ContinuousWithinAt.mul (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun x => f x * g x) s x :=
  Filter.Tendsto.mul hf hg

@[to_additive (attr := fun_prop)]
theorem ContinuousAt.mul (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun x => f x * g x) x :=
  Filter.Tendsto.mul hf hg

@[to_additive (attr := fun_prop)]
theorem ContinuousOn.mul (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => f x * g x) s := fun x hx ↦
  (hf x hx).mul (hg x hx)

end ContinuousMul
