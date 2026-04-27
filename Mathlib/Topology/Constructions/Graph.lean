/-
Copyright (c) 2026 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee
-/
module
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Data.Set.Prod

/-!
# Graphs of Continuous Functions as Topological Spaces

This file proves that the graph of a continuous function is homeomorphic to its domain.

## Main Results

* `Set.graphOn.homeomorph`: The graph of a continuous function `f : E → E'` restricted to `s`,
  with the subspace topology, is homeomorphic to `s`.
* `Set.graphOn.homeomorphUniv`: Special case for globally continuous functions, proving
  `univ.graphOn f ≃ₜ E`.

## Implementation Notes

The key insight is that the projection `(x, f(x)) ↦ x` is a homeomorphism from the graph to the
domain.
-/

@[expose] public section

open Set Topology

namespace Set.graphOn

variable {E E' : Type*} [TopologicalSpace E] [TopologicalSpace E']

/--
The graph of a continuous function `f : s → E'`, viewed as a subtype of `E × E'`,
is homeomorphic to `s` via the projection onto the first factor.
-/
def homeomorph {s : Set E} {f : E → E'} (hf : ContinuousOn f s) : s.graphOn f ≃ₜ s where
  toFun := fun ⟨⟨x, _⟩, hx⟩ ↦ ⟨x, (mem_graphOn.mp hx).1⟩
  invFun := fun ⟨x, hx⟩ ↦ ⟨(x, f x), mem_graphOn.mpr ⟨hx, rfl⟩⟩
  left_inv := fun ⟨⟨x, y⟩, hxy⟩ ↦ by
    simp only [Subtype.mk.injEq, Prod.mk.injEq, true_and]
    exact (mem_graphOn.mp hxy).2
  right_inv := fun _ ↦ rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact Continuous.prodMk continuous_subtype_val
      (hf.comp_continuous continuous_subtype_val fun x ↦ x.2)

@[simp]
theorem homeomorph_apply {s : Set E} {f : E → E'} (hf : ContinuousOn f s) (x : s.graphOn f) :
    homeomorph hf x = ⟨x.1.1, (mem_graphOn.mp x.2).1⟩ := rfl

@[simp]
theorem homeomorph_symm_apply {s : Set E} {f : E → E'} (hf : ContinuousOn f s) (x : s) :
    (homeomorph hf).symm x = ⟨(x, f x), mem_graphOn.mpr ⟨x.2, rfl⟩⟩ := rfl

/--
The graph of a globally continuous function `f : E → E'` is homeomorphic to `E`.
Special case of `graphOn.homeomorph` when the domain is the whole space.
-/
def homeomorphUniv {f : E → E'} (hf : Continuous f) : (Set.univ.graphOn f) ≃ₜ E :=
  (homeomorph hf.continuousOn).trans (Homeomorph.Set.univ E)

@[simp]
theorem homeomorphUniv_apply {f : E → E'} (hf : Continuous f) (x : Set.univ.graphOn f) :
    homeomorphUniv hf x = x.1.1 := by simp [homeomorphUniv]

@[simp]
theorem homeomorphUniv_symm_apply {f : E → E'} (hf : Continuous f) (x : E) :
    (homeomorphUniv hf).symm x = ⟨(x, f x), mem_graphOn.mpr ⟨by simp, rfl⟩⟩ := by
  simp [homeomorphUniv]

end Set.graphOn
