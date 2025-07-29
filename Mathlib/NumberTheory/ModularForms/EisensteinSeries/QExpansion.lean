/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.Complex.SummableUniformlyOn


/-!
# Einstein series Q-expansions

We give some identities for Q-expansions of Eisenstein series that will be used in describing their
Q-expansions.

-/

open Set Metric TopologicalSpace Function Filter Complex UpperHalfPlane

open scoped Topology Real Nat Complex Pointwise

local notation "ℍₒ" => complexUpperHalfPlane

lemma iteratedDerivWithin_cexp_mul_const (k m : ℕ) (c : ℂ) (p : ℝ) {S : Set ℂ} (hs : IsOpen S) :
    EqOn (iteratedDerivWithin k (fun s : ℂ => c * cexp (2 * ↑π * Complex.I * m * s / p)) S)
    (fun s => c * (2 * ↑π * Complex.I * m / p) ^ k * cexp (2 * ↑π * Complex.I * m * s / p)) S := by
  apply (iteratedDerivWithin_of_isOpen hs).trans
  intro x hx
  rw [iteratedDeriv_const_mul (by fun_prop)]
  have : (fun s ↦ cexp (2 * ↑π * Complex.I * ↑m * s / ↑p)) =
      (fun s ↦ cexp (((2 * ↑π * Complex.I * ↑m) / p) * s)) := by
      ext z; ring_nf
  simp only [this, iteratedDeriv_cexp_const_mul]
  ring_nf

private lemma aux_IsBigO_mul (k : ℕ) (p : ℝ) {f : ℕ → ℂ}
    (hf : f =O[atTop] (fun n => (↑(n ^ k) : ℝ))) :
    (fun n => f n * (2 * ↑π * Complex.I * ↑n / p) ^ k) =O[atTop]
    (fun n => (↑(n ^ (2 * k)) : ℝ)) := by
  have h0 : (fun n : ℕ => (2 * ↑π * Complex.I * ↑n / p) ^ k) =O[atTop]
    (fun n => (↑(n ^ (k)) : ℝ)) := by
    have h1 : (fun n : ℕ => (2 * ↑π * Complex.I * ↑n / p) ^ k) =
      (fun n : ℕ => ((2 * ↑π * Complex.I / p) ^ k) * ↑n ^ k) := by
      ext z; ring
    simpa [h1] using (Complex.isBigO_ofReal_right.mp (Asymptotics.isBigO_const_mul_self
      ((2 * ↑π * Complex.I / p) ^ k) (fun (n : ℕ) ↦ (↑(n ^ k) : ℝ)) atTop))
  simp only [Nat.cast_pow] at *
  convert hf.mul h0
  ring

open BoundedContinuousFunction in
theorem summableLocallyUniformlyOn_iteratedDerivWithin_qExpansion (k : ℕ) {f : ℕ → ℂ} {p : ℝ}
    (hp : 0 < p) (hf : f =O[atTop] (fun n => (↑(n ^ k) : ℝ))) :
    SummableLocallyUniformlyOn (fun n ↦ iteratedDerivWithin k
    (fun z ↦ f n * cexp (2 * ↑π * Complex.I * z / p) ^ n) ℍₒ) ℍₒ := by
  apply SummableLocallyUniformlyOn_of_locally_bounded complexUpperHalPlane_isOpen
  intro K hK hKc
  haveI : CompactSpace K := isCompact_univ_iff.mp (isCompact_iff_isCompact_univ.mp hKc)
  let c : ContinuousMap K ℂ := ⟨fun r : K => cexp (2 * ↑π * Complex.I * r / p), by fun_prop⟩
  let r : ℝ := ‖mkOfCompact c‖
  have hr : ‖r‖ < 1 := by
    simp only [norm_norm, r, norm_lt_iff_of_compact Real.zero_lt_one, mkOfCompact_apply,
      ContinuousMap.coe_mk, c]
    intro x
    have h1 : cexp (2 * ↑π * Complex.I * (↑x / ↑p)) = cexp (2 * ↑π * Complex.I * ↑x / ↑p) := by
      congr 1
      ring
    simpa using h1 ▸ UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨((x : ℂ) / p) , by aesop⟩
  refine ⟨_, by simpa using (summable_norm_mul_geometric_of_norm_lt_one' hr
    (Asymptotics.isBigO_norm_left.mpr (aux_IsBigO_mul k p hf))), ?_⟩
  intro n z hz
  have h0 := pow_le_pow_left₀ (by apply norm_nonneg _) (norm_coe_le_norm (mkOfCompact c) ⟨z, hz⟩) n
  simp only [Nat.cast_pow, norm_mkOfCompact, mkOfCompact_apply, ContinuousMap.coe_mk, ←
    exp_nsmul', iteratedDerivWithin_cexp_mul_const k n (f n) p complexUpperHalPlane_isOpen (hK hz),
    Complex.norm_mul, norm_pow, Complex.norm_div, norm_ofNat, norm_real, Real.norm_eq_abs, norm_I,
    mul_one, norm_natCast, abs_norm, ge_iff_le, r, c] at *
  gcongr
  convert h0
  rw [← norm_pow, ← exp_nsmul']

/-- This is a version of `summableLocallyUniformlyOn_iteratedDerivWithin_qExpansion` for level one
and q-expansion coefficients all `1`. -/
theorem summableLocallyUniformlyOn_iteratedDerivWithin_qExpansion' (k : ℕ) :
    SummableLocallyUniformlyOn (fun n ↦ iteratedDerivWithin k
    (fun z ↦ cexp (2 * ↑π * Complex.I * z) ^ n) ℍₒ) ℍₒ := by
  have h0 : (fun n : ℕ => (1 : ℂ)) =O[atTop] (fun n => (↑(n ^ k) : ℝ)) := by
    simp only [Nat.cast_pow, Asymptotics.isBigO_iff, norm_one, norm_pow, Real.norm_natCast,
      eventually_atTop, ge_iff_le]
    refine ⟨1, 1, fun b hb => by norm_cast; simp [Nat.one_le_pow k b hb]⟩
  simpa using summableLocallyUniformlyOn_iteratedDerivWithin_qExpansion k (p := 1) (by norm_num) h0

theorem differnetiableAt_iteratedDerivWithin_cexp (n a : ℕ) {s : Set ℂ} (hs : IsOpen s) {r : ℂ}
    (hr : r ∈ s) :
    DifferentiableAt ℂ (iteratedDerivWithin a (fun z ↦ cexp (2 * ↑π * Complex.I * z) ^ n) s) r := by
  apply DifferentiableOn.differentiableAt _ (hs.mem_nhds hr)
  suffices DifferentiableOn ℂ (iteratedDeriv a (fun z ↦ cexp (2 * ↑π * Complex.I * z) ^ n)) s by
    apply this.congr (iteratedDerivWithin_of_isOpen hs)
  fun_prop

lemma iteratedDerivWithin_tsum_exp_eq (k : ℕ) (z : ℍ) : iteratedDerivWithin k (fun z =>
    ∑' n : ℕ, cexp (2 * π * Complex.I * z) ^ n) ℍₒ z =
    ∑' n : ℕ, iteratedDerivWithin k (fun s : ℂ ↦ cexp (2 * ↑π * Complex.I * s) ^ n) ℍₒ z := by
  rw [iteratedDerivWithin_tsum k complexUpperHalPlane_isOpen (by simpa using z.2)]
  · exact fun x hx => summable_geometric_iff_norm_lt_one.mpr
      (UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨x, hx⟩)
  · exact fun n _ _ => summableLocallyUniformlyOn_iteratedDerivWithin_qExpansion' n
  · exact fun n l z hl hz => differnetiableAt_iteratedDerivWithin_cexp n l
      complexUpperHalPlane_isOpen hz

theorem contDiffOn_tsum_cexp (k : ℕ∞) :
    ContDiffOn ℂ k (fun z : ℂ => ∑' n : ℕ, cexp (2 * ↑π * Complex.I * z) ^ n) ℍₒ :=
  contDiffOn_of_differentiableOn_deriv fun m _ z hz ↦
  ((summableUniformlyOn_differentiableOn complexUpperHalPlane_isOpen
  (summableLocallyUniformlyOn_iteratedDerivWithin_qExpansion' m)
  (fun n _ hz => differnetiableAt_iteratedDerivWithin_cexp n m
    complexUpperHalPlane_isOpen hz)) z hz).congr (fun z hz ↦
    iteratedDerivWithin_tsum_exp_eq m ⟨z, hz⟩) (iteratedDerivWithin_tsum_exp_eq m ⟨z, hz⟩)

private lemma iteratedDerivWithin_tsum_exp_eq' {k : ℕ} (hk : 1 ≤ k) (z : ℍ) :
    iteratedDerivWithin k (fun z => (((π : ℂ) * Complex.I) -
    (2 * π * Complex.I) * ∑' n : ℕ, cexp (2 * π * Complex.I * z) ^ n)) ℍₒ z =
    -(2 * π * Complex.I) ^ (k + 1) * ∑' n : ℕ, n ^ k * cexp (2 * ↑π * Complex.I * z) ^ n := by
  suffices
    iteratedDerivWithin k (fun z ↦ ((↑π * Complex.I) -
    (2 * π * Complex.I) * ∑' n : ℕ, cexp (2 * π * Complex.I * z) ^ n)) ℍₒ z =
    -(2 * π * Complex.I) * ∑' n : ℕ, iteratedDerivWithin k
    (fun s : ℂ => cexp (2 * ↑π * Complex.I * s) ^ n) ℍₒ z by
    have h : -(2 * ↑π * Complex.I * (2 * ↑π * Complex.I) ^ k) *
      ∑' (n : ℕ), ↑n ^ k * cexp (2 * ↑π * Complex.I * ↑z) ^ n = -(2 * π * Complex.I) *
      ∑' n : ℕ, (2 * ↑π * Complex.I * n) ^ k * cexp (2 * ↑π * Complex.I * z) ^ n := by
      simp_rw [← tsum_mul_left]
      congr
      ext y
      ring
    simp only [h, neg_mul, show k + 1 = 1 + k by ring, pow_add, pow_one, this, neg_inj,
      mul_eq_mul_left_iff, mul_eq_zero, OfNat.ofNat_ne_zero, ofReal_eq_zero, I_ne_zero,
      or_false, Real.pi_ne_zero]
    congr
    ext n
    have := exp_nsmul' (p := 1) (a := 2 * π * Complex.I) (n := n)
    simp only [div_one] at this
    simpa [this, ofReal_one, div_one, one_mul, UpperHalfPlane.coe] using
      iteratedDerivWithin_cexp_mul_const k n 1 1 complexUpperHalPlane_isOpen z.2
  rw [iteratedDerivWithin_const_sub hk, iteratedDerivWithin_fun_neg, iteratedDerivWithin_const_mul]
  · simp only [iteratedDerivWithin_tsum_exp_eq, neg_mul]
  · simpa using z.2
  · exact complexUpperHalPlane_isOpen.uniqueDiffOn
  · exact (contDiffOn_tsum_cexp k).contDiffWithinAt (by simpa using z.2)

theorem EisensteinSeries.qExpansion_identity {k : ℕ} (hk : 1 ≤ k) (z : ℍ) :
    ∑' n : ℤ, 1 / ((z : ℂ) + n) ^ (k + 1) = ((-2 * π * Complex.I) ^ (k + 1) / (k !)) *
    ∑' n : ℕ, n ^ k * cexp (2 * ↑π * Complex.I * z) ^ n := by
  suffices (-1) ^ k * (k : ℕ)! * ∑' n : ℤ, 1 / ((z : ℂ) + n) ^ (k + 1) =
    -(2 * π * Complex.I) ^ (k + 1) * ∑' n : ℕ, n ^ k * cexp (2 * ↑π * Complex.I * z) ^ n by
    simp_rw [(eq_inv_mul_iff_mul_eq₀ (by simp [Nat.factorial_ne_zero])).mpr
      this, ← tsum_mul_left]
    congr
    ext n
    have h3 : (k ! : ℂ) ≠ 0 := by
        norm_cast
        apply Nat.factorial_ne_zero
    rw [show (-2 * ↑π * Complex.I) ^ (k + 1) = (-1)^ (k + 1) * (2 * π * Complex.I) ^ (k + 1) by
        rw [← neg_pow]; ring]
    field_simp [h3]
    ring_nf
    simp [Nat.mul_two]
  rw [← iteratedDerivWithin_tsum_exp_eq' hk z, ← iteratedDerivWithin_cot_series_rep_one_div hk z]
  apply iteratedDerivWithin_congr
  · intro x hx
    simpa using pi_mul_cot_pi_q_exp ⟨x, hx⟩
  · simpa using z.2
