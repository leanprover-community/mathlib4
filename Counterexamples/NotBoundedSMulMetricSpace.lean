/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.Topology.MetricSpace.PiNat

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

noncomputable local instance : MetricSpace (ℕ → ℕ) := PiNat.metricSpace
noncomputable local instance : MetricSpace (ℕ → ℝ) := PiCountable.metricSpace

@[simp]
lemma PiCountable.dist_translation_invariant (x y c : ℕ → ℝ) :
    dist (x + c) (y + c) = dist x y := by
  simp [dist_eq_tsum]

noncomputable instance : NormedAddCommGroup (ℕ → ℝ) where
  __ := PiCountable.metricSpace
  norm x := dist x 0
  dist_eq x y := by
    simpa [← sub_eq_add_neg] using
      (PiCountable.dist_translation_invariant x y (-y)).symm

lemma PiCountable.norm_single (i : ℕ) (r : ℝ) :
    ‖(Pi.single i r : ℕ → ℝ)‖ = (2 ^ i)⁻¹ ⊓ |r| := by
  rw [← sub_zero (Pi.single _ _), ← dist_eq_norm, dist_eq_tsum, tsum_eq_single i]
  · simp
  · simp +contextual [Pi.single_apply]

lemma PiCountable.not_dist_homogeneous' : ¬ ∀ (x y : ℕ → ℝ) (r : ℝ),
    dist (r • x) (r • y) ≤ |r| * dist x y := by
  intro H
  specialize H (Pi.single 4 1) 0 2⁻¹
  refine H.not_lt ?_
  clear H
  have : (2 ^ 4 : ℝ)⁻¹ < 1 := by norm_num
  rw [dist_eq_norm]
  simp only [sub_zero, ← Pi.single_smul, smul_eq_mul, smul_zero, dist_zero_right,
    norm_single, abs_one, mul_one, lt_inf_iff, abs_pos, ne_eq, inv_eq_zero,
    OfNat.ofNat_ne_zero, not_false_eq_true, mul_lt_iff_lt_one_right, inf_lt_right, not_le,
    min_eq_left this.le, inv_pos, Nat.ofNat_pos, pow_pos, mul_lt_iff_lt_one_left, this,
    and_true, gt_iff_lt, abs_inv]
  norm_num

open PiCountable

/-- Not all distances on a metric space are induced by a norm. Phrased by remarking that
one can have a `MetricSpace` and even `NormedAddCommGroup` without `BoundedSMul`, which is
a prerequisite for `NormedSpace`. -/
theorem not_all_dist_induced_by_norm : ∃ (𝕜 E : Type) (_ : MetricSpace 𝕜) (_ : MetricSpace E)
    (_ : Zero 𝕜) (_ : Zero E) (_: SMul 𝕜 E),
    ¬ BoundedSMul 𝕜 E := by
  refine ⟨ℝ, ℕ → ℝ, inferInstance, PiCountable.metricSpace, inferInstance, inferInstance,
    inferInstance, ?_⟩
  rintro ⟨H, H'⟩
  apply PiCountable.not_dist_homogeneous'
  intro f g r
  simpa using H r f g

end Counterexample
