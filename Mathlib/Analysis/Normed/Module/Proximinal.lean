/-
Copyright (c) 2026 E. S. Markov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E. S. Markov
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.RCLike.Basic

/-!
# Proximinal Subspaces and Multivalued Metric Projections

This file introduces the set-valued metric projection onto subspaces of normed spaces,
defines proximinal subspaces and the null layer of a metric projection, and establishes
fundamental proximinality criteria.

## Main definitions

* `Submodule.metricProjection`: the set-valued metric projection `P_V(x)` of an element `x` onto a
  submodule `V`, consisting of all `v ∈ V` minimizing `‖x - v‖`.
* `Submodule.IsProximinal`: predicate asserting that `P_V(x)` is nonempty for every `x : X`.
* `Submodule.metricProjectionZeroLayer`: the null layer `P_V⁻¹(0) = {x : X | 0 ∈ P_V(x)}`.

## Main results

* `Submodule.isProximinal_of_finiteDimensional`: every finite-dimensional submodule of a normed
  space over a locally compact normed field is proximinal.
* `Submodule.isProximinal_ker_of_attains_norm`: a closed hyperplane `V = ker f` is proximinal if
  `f` attains its operator norm on the unit sphere.
* `Submodule.attains_norm_of_isProximinal_ker`: conversely, if `V = ker f` is proximinal and
  achieves the distance `‖f x‖ / ‖f‖`, then `f` attains its operator norm on the unit sphere.

## References

* E. S. Markov, *On Linear Metric Projections in Non-Reflexive Banach Spaces: Proximinal Lattices,
  Multivalued Boundaries and Linear Selections*, Zenodo (2026),
  [DOI: 10.5281/zenodo.24318041](https://doi.org).
* I. Singer, *Best Approximation in Normed Linear Spaces by Elements of Linear Subspaces*,
  Springer-Verlag, 1970.
-/

open Set Topology

namespace Submodule

section Basic

variable {𝕜 : Type*} [Semiring 𝕜] {X : Type*} [NormedAddCommGroup X] [Module 𝕜 X]

/-- The set-valued metric projection `P_V(x)` of `x : X` onto a submodule `V`, consisting of all
elements of best approximation to `x` in `V`. -/
def metricProjection (V : Submodule 𝕜 X) (x : X) : Set X :=
  {v ∈ V | ∀ w ∈ V, ‖x - v‖ ≤ ‖x - w‖}

/-- A submodule `V` of a normed space `X` is *proximinal* if every element `x : X` admits at least
one best approximation in `V`. -/
def IsProximinal (V : Submodule 𝕜 X) : Prop :=
  ∀ x : X, (V.metricProjection x).Nonempty

/-- The null layer `P_V⁻¹(0)` of the metric projection onto `V`, consisting of all elements in `X`
for which `0` is an element of best approximation in `V`. -/
def metricProjectionZeroLayer (V : Submodule 𝕜 X) : Set X :=
  {x : X | (0 : X) ∈ V.metricProjection x}

@[simp]
lemma mem_metricProjection_iff {V : Submodule 𝕜 X} {x v : X} :
    v ∈ V.metricProjection x ↔ v ∈ V ∧ ∀ w ∈ V, ‖x - v‖ ≤ ‖x - w‖ :=
  Iff.rfl

@[simp]
lemma mem_metricProjectionZeroLayer_iff {V : Submodule 𝕜 X} {x : X} :
    x ∈ V.metricProjectionZeroLayer ↔ ∀ w ∈ V, ‖x‖ ≤ ‖x - w‖ := by
  simp [metricProjectionZeroLayer, metricProjection]

lemma self_mem_metricProjection {V : Submodule 𝕜 X} {v : X} (hv : v ∈ V) :
    v ∈ V.metricProjection v := by
  refine ⟨hv, fun w _ => ?_⟩
  rw [sub_self, norm_zero]
  exact norm_nonneg _

lemma metricProjection_eq_singleton_of_mem {V : Submodule 𝕜 X} {v : X} (hv : v ∈ V) :
    V.metricProjection v = {v} := by
  ext u
  simp only [mem_metricProjection_iff, mem_singleton_iff]
  refine ⟨fun ⟨_, hmin⟩ => ?_, ?_⟩
  · have h0 : ‖v - u‖ ≤ 0 := by simpa using hmin v hv
    have h_eq : v - u = 0 := norm_le_zero_iff.mp h0
    exact (sub_eq_zero.mp h_eq).symm
  · rintro rfl
    exact ⟨hv, fun w _ => by simp⟩

end Basic

section FiniteDimensional

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Every finite-dimensional submodule of a normed space over a locally compact normed field
is proximinal. -/
theorem isProximinal_of_finiteDimensional (V : Submodule 𝕜 X) [FiniteDimensional 𝕜 V] :
    V.IsProximinal := by
  intro x
  have : ProperSpace V := FiniteDimensional.proper 𝕜 V
  let B : Set V := Metric.closedBall (0 : V) (2 * ‖x‖)
  have hB_comp : IsCompact B := isCompact_closedBall (0 : V) (2 * ‖x‖)
  have hB_ne : B.Nonempty := ⟨0, Metric.mem_closedBall_self (by positivity)⟩
  have h_cont : Continuous (fun v : V => ‖x - (v : X)‖) :=
    continuous_norm.comp (continuous_const.sub continuous_subtype_val)
  rcases hB_comp.exists_isMinOn hB_ne h_cont.continuousOn with ⟨v₀, _, hv₀_min⟩
  refine ⟨v₀, v₀.2, fun w hw => ?_⟩
  by_cases hw_ball : (⟨w, hw⟩ : V) ∈ B
  · exact hv₀_min hw_ball
  · have h_gt : 2 * ‖x‖ < ‖(⟨w, hw⟩ : V)‖ := by
      simpa [B, Metric.mem_closedBall, dist_zero_right] using hw_ball
    have h0_mem : (0 : V) ∈ B := Metric.mem_closedBall_self (by positivity)
    have h1 : ‖x - (v₀ : X)‖ ≤ ‖x‖ := by
      have := hv₀_min h0_mem
      simpa using this
    have h2 : ‖x‖ ≤ ‖x - w‖ := by
      have h_tri : ‖w‖ ≤ ‖x‖ + ‖x - w‖ := by
        calc ‖w‖ = ‖x - (x - w)‖ := by rw [sub_sub_cancel]
          _ ≤ ‖x‖ + ‖x - w‖ := norm_sub_le x (x - w)
      change 2 * ‖x‖ < ‖w‖ at h_gt
      linarith
    exact h1.trans h2

end FiniteDimensional

section Hyperplane

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- If a nonzero continuous linear functional `f : X →L[𝕜] 𝕜` attains its operator norm on the
unit sphere, then its kernel `ker f` is a proximinal hyperplane. -/
theorem isProximinal_ker_of_attains_norm (f : X →L[𝕜] 𝕜) (hf : f ≠ 0)
    (u : X) (hu_norm : ‖u‖ = 1) (hu_att : ‖f u‖ = ‖f‖) :
    (LinearMap.ker (f : X →ₗ[𝕜] 𝕜)).IsProximinal := by
  intro x
  have hf_pos : 0 < ‖f‖ := norm_pos_iff.mpr hf
  let α : 𝕜 := f x / f u
  let v₀ : X := x - α • u
  have hfu_ne : f u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hu_att
    linarith
  refine ⟨v₀, ?_, ?_⟩
  · rw [LinearMap.mem_ker]
    change f (x - α • u) = 0
    rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hfu_ne, sub_self]
  · intro w hw
    rw [LinearMap.mem_ker] at hw
    change f w = 0 at hw
    have h_diff : x - v₀ = α • u := sub_sub_cancel x _
    rw [h_diff, norm_smul, norm_div, hu_att, hu_norm, mul_one]
    have h_fx : ‖f x‖ = ‖f (x - w)‖ := by rw [map_sub, hw, sub_zero]
    rw [h_fx, div_le_iff₀ hf_pos, mul_comm]
    exact f.le_opNorm (x - w)

/-- Conversely, if a hyperplane `ker f` admits an element `v₀` achieving the Ascoli distance
`‖f x‖ / ‖f‖` for some `x ∉ ker f`, then `f` attains its operator norm on the unit sphere. -/
theorem attains_norm_of_isProximinal_ker (f : X →L[𝕜] 𝕜) (hf : f ≠ 0)
    (x : X) (hx : f x ≠ 0) (v₀ : X) (hv₀_ker : f v₀ = 0)
    (hv₀_dist : ‖x - v₀‖ = ‖f x‖ / ‖f‖) :
    ∃ u : X, ‖u‖ = 1 ∧ ‖f u‖ = ‖f‖ := by
  have hf_pos : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hfx_pos : 0 < ‖f x‖ := norm_pos_iff.mpr hx
  have h_diff_pos : 0 < ‖x - v₀‖ := by
    rw [hv₀_dist]
    exact div_pos hfx_pos hf_pos
  let c : 𝕜 := (‖x - v₀‖ : 𝕜)⁻¹
  refine ⟨c • (x - v₀), ?_, ?_⟩
  · rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm, inv_mul_cancel₀ h_diff_pos.ne']
  · rw [map_smul, norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm, map_sub, hv₀_ker, sub_zero,
      hv₀_dist, inv_div, div_mul_cancel₀ _ hfx_pos.ne']

end Hyperplane

end Submodule
