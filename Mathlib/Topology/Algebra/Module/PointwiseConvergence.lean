/-
Copyright (c) 2024 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Topology.Algebra.Module.StrongTopology
import Mathlib.Topology.Algebra.Module.WeakDual

/-!
# PointwiseConvergence

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

namespace PointwiseConvergenceCLM

variable {α 𝕜 E F : Type*} [TopologicalSpace α]
variable [NormedField 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [TopologicalAddGroup F]
  [ContinuousConstSMul 𝕜 F]

variable (𝕜 E F) in
/-- Coercion from `E →Lₛ[𝕜] F` to `E →ₗ[𝕜] F` as a `𝕜`-linear map. -/
def coeLM : (E →Lₛ[𝕜] F) →ₗ[𝕜] E →ₗ[𝕜] F where
  toFun := ContinuousLinearMap.toLinearMap
  map_add' := ContinuousLinearMap.coe_add
  map_smul' := ContinuousLinearMap.coe_smul

variable (𝕜 F) in
/-- The evaluation map `(f : E →Lₛ[𝕜] F) ↦ f a` for `a : E` as a continuous linear map. -/
def evalCLM (a : E) : (E →Lₛ[𝕜] F) →L[𝕜] F where
  toLinearMap := (coeLM 𝕜 E F).flip a
  cont := by
    change Continuous ((coeLM 𝕜 E F).flip a)
    apply continuous_of_continuousAt_zero
    unfold ContinuousAt
    simp only [map_zero]
    rw [PointwiseConvergenceCLM.hasBasis_nhds_zero.tendsto_left_iff]
    intro s hs
    use ({a}, s)
    simp only [hs, and_true, Set.mem_singleton_iff, forall_eq]
    exact ⟨Set.finite_singleton _, fun _ hy ↦ by rwa [Set.mem_setOf_eq] at hy⟩

theorem continuous_of_continuous_eval {g : α → E →Lₛ[𝕜] F}
    (h : ∀ y, Continuous fun a ↦ (g a) y) : Continuous g := by
  rw [continuous_iff_continuousAt]
  intro f
  unfold ContinuousAt
  rw [tendsto_iff_forall_tendsto]
  intro x
  exact (h x).continuousAt

variable (𝕜 E) in
/-- The topology of pointwise convergence on `E →Lₛ[𝕜] 𝕜` coincides with the weak-* topology. -/
def equivWeakDual : (E →Lₛ[𝕜] 𝕜) ≃L[𝕜] WeakDual 𝕜 E where
  toLinearEquiv := LinearEquiv.refl 𝕜 (E →L[𝕜] 𝕜)
  continuous_toFun := by
    apply WeakDual.continuous_of_continuous_eval
    intro y
    apply (evalCLM 𝕜 𝕜 y).continuous
  continuous_invFun := by
    apply continuous_of_continuous_eval
    intro y
    apply WeakBilin.eval_continuous

end PointwiseConvergenceCLM
