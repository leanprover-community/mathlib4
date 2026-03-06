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
`U` is a disk, one consider a similar decomposition, called "Canonical Decomposition" or "Blaschke
Product" that replaces the factors `(· - u)` by "canonical factors" that take only values of norm
one on the boundary of the circle. This file introduces the canonical factors.

See Page 160f of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] for a detailed
discussion.

TODO: Formulate the canonical decomposition.
-/

@[expose] public section

open Complex ComplexConjugate Metric Real

variable {R : ℝ} {w : ℂ}

theorem nonneg_radius_of_mem_sphere {c : ℂ} (hw : w ∈ sphere c R) :
    0 ≤ R := by
  rw [mem_sphere_iff_norm] at hw
  rw [← hw]
  apply norm_nonneg

/-!
## Canonical Factors

Given `R : ℝ` and `w : ℂ`, the Blaschke factor `Blaschke R w : ℂ → ℂ` is meromorphic in normal form,
has a single pole at `w`, no zeros, and takes values of norm one on the circle of radius `R`.
-/

/--
Given `R : ℝ` and `w : ℂ`, the canonical factor is the function
`fun z ↦ (R ^ 2 - (conj w) * z) / (R * (z - w))`. In applications, on will typically consider a
setting where `w ∈ ball 0 R`.
-/
noncomputable def CanonicalFactor (R : ℝ) (w : ℂ) : ℂ → ℂ :=
  fun z ↦ (R ^ 2 - (conj w) * z) / (R * (z - w))

/-!
### Regularity properties
-/

variable (R w) in
/--
Canonical factors are meromorphic.
-/
theorem meromorphicOn_canonicalFactor : MeromorphicOn (CanonicalFactor R w) Set.univ := by
  intro x hx
  unfold CanonicalFactor
  fun_prop

variable (R w) in
/--
The canonical factor `CanonicalFactor R w` is analytic on the complement of `w`.
-/
theorem analyticOnNhd_canonicalFactor : AnalyticOnNhd ℂ (CanonicalFactor R w) {w}ᶜ := by
  intro x hx
  by_cases h : R = 0
  · subst h
    unfold CanonicalFactor
    simp only [ofReal_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_sub,
      zero_mul, div_zero]
    fun_prop
  have : R * (x - w) ≠ 0 := mul_ne_zero (ofReal_ne_zero.2 h) (sub_ne_zero_of_ne hx)
  unfold CanonicalFactor
  fun_prop (disch := aesop)

/--
The canonical factor `CanonicalFactor R w` has a simple pole at `z = w`.
-/
theorem meromorphicOrderAt_canonicalFactor (h : w ∈ ball 0 R) :
    meromorphicOrderAt (CanonicalFactor R w) w = -1 := by
  unfold CanonicalFactor
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
    MeromorphicNFOn (CanonicalFactor R w) Set.univ := by
  intro z hz
  by_cases h₁ : z = w
  · rw [meromorphicNFAt_iff_analyticAt_or]
    right
    use (meromorphicOn_canonicalFactor R w z (Set.mem_univ z))
    constructor
    · simp_all only [Set.mem_univ, meromorphicOrderAt_canonicalFactor h]
      exact sign_eq_neg_one_iff.1 rfl
    simp_all [CanonicalFactor]
  apply (analyticOnNhd_canonicalFactor R w z h₁).meromorphicNFAt

/-!
### Values of Canonical Factors
-/

/--
The canonical factor `CanonicalFactor R w` has no zeros inside the ball of radius `R`.
-/
theorem nonzero_canonicalFactor {z : ℂ} (hw : w ∈ ball 0 R) (h₁z : z ∈ ball 0 R) (h₂z : z ≠ w) :
    CanonicalFactor R w z ≠ 0 := by
  have h_denom_ne_zero : R * (z - w) ≠ 0 := by
    apply mul_ne_zero _ (sub_ne_zero.2 h₂z)
    rw [ne_eq, ofReal_eq_zero]
    by_contra hCon
    subst hCon
    simp_all
  have h_num_ne_zero : R^2 - (conj w) * z ≠ 0 := by
    by_contra h
    rw [sub_eq_zero] at h
    have : ‖(starRingEnd ℂ) w * z‖ < R ^ 2 := by
      simpa [Complex.norm_mul, RCLike.norm_conj, pow_two] using
        mul_lt_mul' (mem_ball_zero_iff.mp hw).le h₁z dist_nonneg (pos_of_mem_ball hw)
    simp [← h] at this
  exact div_ne_zero h_num_ne_zero h_denom_ne_zero

/--
The canonical factor `CanonicalFactor R w` evalues to zero at `z = w`.
-/
@[simp]
theorem canonicalFactor_eval_center (R : ℝ) (w : ℂ) : CanonicalFactor R w w = 0 := by
  simp [CanonicalFactor]

/--
The canonical factor `CanonicalFactor R w` takes values of norm one on `sphere 0 R`.
-/
theorem norm_canonicalFactor_eval_circle_eq_one {z : ℂ} (hw : w ∈ ball 0 R) (hz : z ∈ sphere 0 R) :
    ‖CanonicalFactor R w z‖ = 1 := by
  rw [CanonicalFactor, norm_div, div_eq_iff, one_mul]
  · rw [mem_sphere_zero_iff_norm] at hz
    have : (starRingEnd ℂ) z * z = R ^ 2 := by
      rw [← hz]
      exact conj_mul' z
    rw [← this, ← mul_sub_right_distrib, norm_mul, norm_mul, hz, ← (starRingEnd ℂ).map_sub,
      RCLike.norm_conj, mul_comm]
    congr
    simp [abs_of_pos (pos_of_mem_ball hw)]
  · simp only [Complex.norm_mul, norm_real, norm_eq_abs, ne_eq, mul_eq_zero, abs_eq_zero,
      norm_eq_zero, not_or]
    constructor
    · linarith [pos_of_mem_ball hw]
    · by_contra hCon
      rw [sub_eq_zero] at hCon
      simp_all
