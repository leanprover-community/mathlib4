/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.FactorizedRational

/-!
# Canonical Decomposition

If a function `f` is meromorphic on a compact set `U`, then it has only finitely many zeros and
poles on the disk, and the theorem `MeromorphicOn.extract_zeros_poles` can be used to re-write `f`
as `(∏ᶠ u, (· - u) ^ divisor f U u) • g`, where `g` is analytic without zeros on `U`. In case where
`U` is a disk, one consider a similar decomposition, called *Canonical Decomposition* or *Blaschke
Product* that replaces the factors `(· - u)` by canonical factors that take only values of norm
one on the boundary of the circle. This file introduces the canonical factors.

See Page 160f of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] for a detailed
discussion.

TODO: Formulate the canonical decomposition.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace Complex

open ComplexConjugate Metric Real

variable {R : ℝ} {w : ℂ}

/-!
## Canonical Factors

Given `R : ℝ` and `w : ℂ`, the Blaschke factor `Blaschke R w : ℂ → ℂ` is meromorphic in normal form,
has a single pole at `w`, no zeros, and takes values of norm one on the circle of radius `R`.
-/

/--
Given `R : ℝ` and `w : ℂ`, the canonical factor is the function
`fun z ↦ (R ^ 2 - (conj w) * z) / (R * (z - w))`. In applications, one will typically consider a
setting where `w ∈ ball 0 R`.
-/
noncomputable def canonicalFactor (R : ℝ) (w : ℂ) : ℂ → ℂ :=
  fun z ↦ (R ^ 2 - (conj w) * z) / (R * (z - w))

lemma canonicalFactor_def (R : ℝ) (w : ℂ) :
    canonicalFactor R w = fun z ↦ (R ^ 2 - (conj w) * z) / (R * (z - w)) :=
  rfl

lemma canonicalFactor_apply (R : ℝ) (w z : ℂ) :
    canonicalFactor R w z = (R ^ 2 - (conj w) * z) / (R * (z - w)) :=
  rfl

@[simp]
lemma canonicalFactor_apply_self (R : ℝ) (w : ℂ) :
    canonicalFactor R w w = 0 := by
  simp [canonicalFactor_apply]

/-!
### Regularity properties
-/

variable (R w) in
/--
Canonical factors are meromorphic.
-/
theorem meromorphicOn_canonicalFactor : MeromorphicOn (canonicalFactor R w) Set.univ := by
  intro x hx
  unfold canonicalFactor
  fun_prop

open scoped ComplexOrder in
variable (R w) in
/--
The canonical factor `CanonicalFactor R w` is analytic on the complement of `w`.
-/
theorem analyticOnNhd_canonicalFactor : AnalyticOnNhd ℂ (canonicalFactor R w) {w}ᶜ := by
  intro x hx
  rw [canonicalFactor_def]
  obtain (rfl | h) := eq_or_ne R 0
  · simpa using analyticAt_const
  have : x - w ≠ 0 := by grind
  fun_prop (disch := positivity)

/--
The canonical factor `CanonicalFactor R w` has a simple pole at `z = w`.
-/
theorem meromorphicOrderAt_canonicalFactor (h : w ∈ ball 0 R) :
    meromorphicOrderAt (canonicalFactor R w) w = -1 := by
  unfold canonicalFactor
  rw [fun_meromorphicOrderAt_div (by fun_prop) (by fun_prop),
    fun_meromorphicOrderAt_mul (by fun_prop) (by fun_prop)]
  have : meromorphicOrderAt (fun z ↦ ↑R ^ 2 - (starRingEnd ℂ) w * z) w = 0 := by
    refine (MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff ?_).2 ?_
    · apply AnalyticAt.meromorphicNFAt
      fun_prop
    · rw [← normSq_eq_conj_mul_self, normSq_eq_norm_sq w, sub_ne_zero, ne_eq, ← ofReal_pow,
        ofReal_inj, sq_eq_sq₀ (pos_of_mem_ball h).le (norm_nonneg w)]
      rw [mem_ball_iff_norm, sub_zero] at h
      grind
  simp [this, meromorphicOrderAt_const, (pos_of_mem_ball h).ne',
    meromorphicOrderAt_id_sub_const]

/--
Canonical factors are meromorphic in normal form.
-/
theorem meromorphicNFOn_canonicalFactor (h : w ∈ ball 0 R) :
    MeromorphicNFOn (canonicalFactor R w) Set.univ := by
  intro z hz
  obtain (rfl | h₁) := eq_or_ne z w
  · rw [meromorphicNFAt_iff_analyticAt_or]
    right
    refine ⟨meromorphicOn_canonicalFactor R z z (Set.mem_univ z), ?_, by simp⟩
    simpa [meromorphicOrderAt_canonicalFactor h] using WithTop.coe_lt_zero.mpr (by lia : -1 < 0)
  apply (analyticOnNhd_canonicalFactor R w z h₁).meromorphicNFAt

/-!
### Values of Canonical Factors
-/

open scoped ComplexOrder in
/--
The canonical factor `CanonicalFactor R w` has no zeros inside the ball of radius `R`.
-/
theorem canonicalFactor_ne_zero {z : ℂ} (hw : w ∈ ball 0 R) (h₁z : z ∈ closedBall 0 R)
    (h₂z : z ≠ w) :
    canonicalFactor R w z ≠ 0 := by
  obtain ⟨hR, hzw⟩ : 0 < R ∧ z - w ≠ 0 := by grind [mem_ball_zero_iff, norm_nonneg]
  simp only [mem_ball, dist_zero_right, mem_closedBall] at hw h₁z
  have h_num_ne_zero : R ^ 2 - conj w * z ≠ 0 := by
    suffices ‖conj w * z‖ < ‖(R : ℂ) ^ 2‖ by grind
    suffices ‖w‖ * ‖z‖ < R * R by simpa [sq]
    grw [h₁z]
    gcongr
  rw [canonicalFactor_apply]
  positivity

open scoped ComplexOrder in
/--
The canonical factor `CanonicalFactor R w` takes values of norm one on `sphere 0 R`.
-/
theorem norm_canonicalFactor_eval_circle_eq_one {z : ℂ} (hw : w ∈ ball 0 R) (hz : z ∈ sphere 0 R) :
    ‖canonicalFactor R w z‖ = 1 := by
  obtain ⟨hR, hzw⟩ : 0 < R ∧ z - w ≠ 0 := by
    grind [mem_ball_zero_iff, norm_nonneg, mem_sphere_zero_iff_norm]
  rw [canonicalFactor, norm_div, div_eq_iff (by rw [ne_eq, norm_eq_zero]; positivity), one_mul]
  obtain rfl := by simpa [mem_sphere_zero_iff_norm] using hz
  rw [← ofReal_pow, ← normSq_eq_norm_sq, normSq_eq_conj_mul_self, ← sub_mul, mul_comm _ z]
  simp [← map_sub]

end Complex
