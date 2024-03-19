/-
Copyright (c) 2024 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Topology.Algebra.Module.StrongTopology
import Mathlib.Topology.Algebra.Module.WeakDual

/-!
# Topology of pointwise convergence on continous linear maps

## Main definitions

* `PointwiseConvergenceCLM`: Type synonym of `E →SL[σ] F` equipped with the uniform convergence
topology on finite sets.

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

/-! ### Topology of pointwise convergence -/

variable {α ι : Type*} [TopologicalSpace α]
variable {𝕜 𝕜₁ 𝕜₂ : Type*} [NormedField 𝕜] [NormedField 𝕜₁] [NormedField 𝕜₂]
variable {σ : 𝕜₁ →+* 𝕜₂}
variable {E F : Type*} [AddCommGroup E] [TopologicalSpace E]
  [AddCommGroup F] [TopologicalSpace F] [TopologicalAddGroup F]
  [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜₁ E] [Module 𝕜₂ F]

open Topology

variable (σ E F) in
/-- The space of continuous linear maps equipped with the topology of pointwise/simple convergence,
sometimes also called the strong operator topology.

This topology is also known as the weak*-topology in the case that `σ = RingHom.id 𝕜` and `F = 𝕜` -/
@[reducible]
def PointwiseConvergenceCLM :=
    UniformConvergenceCLM σ F {s : Set E | Finite s}

@[inherit_doc]
notation:25 E " →SLₛ[" σ "] " F => PointwiseConvergenceCLM σ E F

@[inherit_doc]
notation:25 E " →Lₛ[" R "] " F => PointwiseConvergenceCLM (RingHom.id R) E F

namespace PointwiseConvergenceCLM

protected theorem hasBasis_nhds_zero_of_basis
    {ι : Type*} {p : ι → Prop} {b : ι → Set F} (h : (𝓝 0 : Filter F).HasBasis p b) :
    (𝓝 (0 : E →SLₛ[σ] F)).HasBasis (fun Si : Set E × ι => Finite Si.1 ∧ p Si.2)
      fun Si => { f : E →SLₛ[σ] F | ∀ x ∈ Si.1, f x ∈ b Si.2 } :=
  UniformConvergenceCLM.hasBasis_nhds_zero_of_basis σ F { S | Finite S }
    ⟨∅, Set.finite_empty⟩ (directedOn_of_sup_mem fun _ _ => Set.Finite.union) h

protected theorem hasBasis_nhds_zero [TopologicalSpace F] [TopologicalAddGroup F] :
    (𝓝 (0 : E →SLₛ[σ] F)).HasBasis
      (fun SV : Set E × Set F => Finite SV.1 ∧ SV.2 ∈ (𝓝 0 : Filter F))
      fun SV => { f : E →SLₛ[σ] F | ∀ x ∈ SV.1, f x ∈ SV.2 } :=
  PointwiseConvergenceCLM.hasBasis_nhds_zero_of_basis (𝓝 0).basis_sets

/-- In the topology of pointwise convergence, `a` converges to `a₀` iff for every `x : E`
`a · x` converges to `a₀ x`. -/
theorem tendsto_iff_forall_tendsto {p : Filter ι} {a : ι → E →SLₛ[σ] F} {a₀ : E →SLₛ[σ] F} :
    Filter.Tendsto a p (𝓝 a₀) ↔ ∀ x : E, Filter.Tendsto (a · x) p (𝓝 (a₀ x)) := by
  let _ := TopologicalAddGroup.toUniformSpace F
  have _ : UniformAddGroup F := comm_topologicalAddGroup_is_uniform
  suffices h : Filter.Tendsto a p (𝓝 a₀) ↔ ∀ x, TendstoUniformlyOn (a · ·) a₀ p {x} by
    rw [h, forall_congr]
    intro
    rw [tendstoUniformlyOn_singleton_iff_tendsto]
  rw [UniformConvergenceCLM.tendsto_iff_tendstoUniformlyOn]
  unfold TendstoUniformlyOn
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h x u hu
    simpa using h {x} (Set.finite_singleton _) u hu
  · intro h s hs u hu
    rw [Filter.eventually_all_finite hs]
    intro x _hx
    exact h x u hu

variable [ContinuousConstSMul 𝕜₂ F]

variable (σ E F) in
/-- Coercion from `E →Lₛ[𝕜] F` to `E →ₗ[𝕜] F` as a `𝕜`-linear map. -/
def coeLM : (E →SLₛ[σ] F) →ₗ[𝕜₂] E →ₛₗ[σ] F where
  toFun := ContinuousLinearMap.toLinearMap
  map_add' := ContinuousLinearMap.coe_add
  map_smul' := ContinuousLinearMap.coe_smul

variable (σ F) in
/-- The evaluation map `(f : E →Lₛ[𝕜] F) ↦ f a` for `a : E` as a continuous linear map. -/
def evalCLM (a : E) : (E →SLₛ[σ] F) →L[𝕜₂] F where
  toLinearMap := (coeLM σ E F).flip a
  cont := by
    change Continuous ((coeLM σ E F).flip a)
    apply continuous_of_continuousAt_zero
    unfold ContinuousAt
    simp only [map_zero]
    rw [PointwiseConvergenceCLM.hasBasis_nhds_zero.tendsto_left_iff]
    intro s hs
    use ({a}, s)
    simp only [hs, and_true, Set.mem_singleton_iff, forall_eq]
    exact ⟨Set.finite_singleton _, fun _ hy ↦ by rwa [Set.mem_setOf_eq] at hy⟩

theorem continuous_of_continuous_eval {g : α → E →SLₛ[σ] F}
    (h : ∀ y, Continuous fun a ↦ (g a) y) : Continuous g := by
  rw [continuous_iff_continuousAt]
  intro f
  unfold ContinuousAt
  rw [tendsto_iff_forall_tendsto]
  intro x
  exact (h x).continuousAt

def _root_.ContinousLinearMap.toPointwiseConvergenceCLM : (E →SL[σ] F) →L[𝕜₂] (E →SLₛ[σ] F) where
  toLinearMap := LinearMap.id
  cont := by
    apply continuous_of_continuous_eval
    intro x
    change (Continuous (· x))
    --exact ContinuousLinearMap.continuous
    sorry

variable (𝕜 E) in
/-- The topology of pointwise convergence on `E →Lₛ[𝕜] 𝕜` coincides with the weak-* topology. -/
def equivWeakDual : (E →Lₛ[𝕜] 𝕜) ≃L[𝕜] WeakDual 𝕜 E where
  toLinearEquiv := LinearEquiv.refl 𝕜 (E →L[𝕜] 𝕜)
  continuous_toFun := by
    apply WeakDual.continuous_of_continuous_eval
    intro y
    apply (evalCLM (RingHom.id 𝕜) 𝕜 y).continuous
  continuous_invFun := by
    apply continuous_of_continuous_eval
    intro y
    apply WeakBilin.eval_continuous

end PointwiseConvergenceCLM
