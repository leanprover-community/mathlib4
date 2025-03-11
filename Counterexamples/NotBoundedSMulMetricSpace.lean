/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.Topology.MetricSpace.PiNat.Normed

/-! # Metric spaces are not necessarily induced by a norm.

In a normed space, the distance must be translation invariant and
homogeneous (scaled by scalar multiplication).

There are examples of metric spaces where distances do not satisfy these properties,
and thus cannot even have `BoundedSMul` instances.

-/

namespace Counterexample

section NormInduced

variable {𝕜 E : Type*} [NormedAddCommGroup E] [NormedField 𝕜] [NormedSpace 𝕜 E]

/-- A distance induced by a normed space must be translation invariant. -/
lemma dist_translation_invariant (x y c : E) :
    dist (x + c) (y + c) = dist x y := by
  simp

/-- A distance induced by a normed space must be homogeneous, which means that it is scaled
by scalar multiplication. -/
lemma dist_homogeneous (c : 𝕜) (x : E) :
    dist (c • x) 0 = ‖c‖ * dist x 0 := by
  simp [norm_smul]

end NormInduced

open PiCountable

variable {ι : Type*} [Encodable ι] {F : ι → Type*}

open Encodable

attribute [local instance] PiCountable.normedAddCommGroup

lemma PiCountable.not_dist_homogeneous' [DecidableEq ι]
    [∀ i, NormedLinearOrderedField (F i)] [∀ i, NormedSpace ℝ (F i)] [∀ i, BoundedSMul ℝ (F i)]
     (i : ι) (hi : 0 < encode i) :
    ¬ ∀ (x y : Π i, F i) (r : ℝ),
    dist (r • x) (r • y) ≤ ‖r‖ * dist x y := by
  intro H
  specialize H (Pi.single i 1) 0 2⁻¹
  refine H.not_lt ?_
  clear H
  have : (2 ^ encode i : ℝ)⁻¹ < 1 := by
    rw [inv_lt_comm₀ (by simp) (by simp), inv_one]
    simpa using pow_lt_pow_right₀ one_lt_two hi
  simp only [norm_inv, RCLike.norm_ofNat, dist_eq_norm, sub_zero, norm_single, norm_one,
    min_eq_left this.le, ← Pi.single_smul, smul_zero, norm_smul, lt_inf_iff, inv_pos, Nat.ofNat_pos,
    pow_pos, mul_lt_iff_lt_one_left, two_inv_lt_one, true_and, gt_iff_lt]
  norm_num
  exact this

open PiCountable

/-- Not all distances on a metric space are induced by a norm. Phrased by remarking that
one can have a `MetricSpace` and even `NormedAddCommGroup` without `BoundedSMul`, which is
a prerequisite for `NormedSpace`. -/
theorem not_all_dist_induced_by_norm : ¬ ∀ (𝕜 E : Type) [MetricSpace 𝕜] [MetricSpace E]
    [Zero 𝕜] [Zero E] [SMul 𝕜 E], BoundedSMul 𝕜 E := by
  intro H
  obtain ⟨H, -⟩ := H ℝ (ℕ → ℝ)
  classical
  apply PiCountable.not_dist_homogeneous' (ι := ℕ) (F := fun _ ↦ ℝ) 1 (by simp)
  intro f g r
  simpa using H r f g

end Counterexample
