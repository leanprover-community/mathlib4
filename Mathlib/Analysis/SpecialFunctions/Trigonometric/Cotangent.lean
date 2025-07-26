/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.Analysis.NormedSpace.MultipliableUniformlyOn
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable

/-!
# Cotangent

This file contains lemmas about the cotangent function, including useful series expansions.
In particular, we prove that
`π * cot (π * z) = π * I - 2 * π * I * ∑' n : ℕ, Complex.exp (2 * π * I * z) ^ n`
as well as the infinite sum representation of cotangent (also known as the Mittag-Leffler
expansion): `π * cot (π * z) = 1 / z + ∑' n : ℕ+, (1 / ((z : ℂ) - n) + 1 / (z + n))`.
-/

open Real Complex

open scoped UpperHalfPlane

lemma Complex.cot_eq_exp_ratio (z : ℂ) :
    cot z = (Complex.exp (2 * I * z) + 1) / (I * (1 - Complex.exp (2 * I * z))) := by
  rw [Complex.cot, Complex.sin, Complex.cos]
  field_simp
  have h1 : exp (z * I) + exp (-(z * I)) = exp (-(z * I)) * (exp (2 * I * z) + 1) := by
    rw [mul_add, ← Complex.exp_add]
    simp only [mul_one, add_left_inj]
    ring_nf
  have h2 : (exp (-(z * I)) - exp (z * I)) * I = exp (-(z * I)) * (I * (1 - exp (2 * I * z))) := by
    ring_nf
    rw [mul_assoc, ← Complex.exp_add]
    ring_nf
  rw [h1, h2, mul_div_mul_left _ _ (Complex.exp_ne_zero _)]

/- The version one probably wants to use more. -/
lemma Complex.cot_pi_eq_exp_ratio (z : ℂ) :
    cot (π * z) = (Complex.exp (2 * π * I * z) + 1) / (I * (1 - Complex.exp (2 * π * I * z))) := by
  rw [cot_eq_exp_ratio (π * z)]
  ring_nf

/- This is the version one probably wants, which is why the pi's are there. -/
theorem pi_mul_cot_pi_q_exp (z : ℍ) :
    π * cot (π * z) = π * I - 2 * π * I * ∑' n : ℕ, Complex.exp (2 * π * I * z) ^ n := by
  have h1 : π * ((exp (2 * π * I * z) + 1) / (I * (1 - exp (2 * π * I * z)))) =
      -π * I * ((exp (2 * π * I * z) + 1) * (1 / (1 - exp (2 * π * I * z)))) := by
    simp only [div_mul_eq_div_mul_one_div, div_I, one_div, neg_mul, mul_neg, neg_inj]
    ring
  rw [cot_pi_eq_exp_ratio, h1, one_div, (tsum_geometric_of_norm_lt_one
    (UpperHalfPlane.norm_exp_two_pi_I_lt_one z)).symm, add_comm, geom_series_mul_one_add
      (Complex.exp (2 * π * I * (z : ℂ))) (UpperHalfPlane.norm_exp_two_pi_I_lt_one _)]
  ring

section MittagLeffler

open Filter Function

open scoped Topology BigOperators Nat Complex

local notation "ℂ_ℤ" => integerComplement

variable {x : ℂ} {Z : Set ℂ}

/-- The main term in the infinite product for sine. -/
noncomputable abbrev sineTerm (x : ℂ) (n : ℕ) : ℂ := -x ^ 2 / (n + 1) ^ 2

lemma sineTerm_ne_zero {x : ℂ} (hx : x ∈ ℂ_ℤ) (n : ℕ) : 1 + sineTerm x n ≠ 0 := by
  simp only [sineTerm, ne_eq]
  rw [add_eq_zero_iff_eq_neg, neg_div', eq_div_iff]
  · have := (integerComplement_pow_two_ne_pow_two hx (n + 1 : ℤ))
    aesop
  · simp [Nat.cast_add_one_ne_zero n]

theorem tendsto_euler_sin_prod' (h0 : x ≠ 0) :
    Tendsto (fun n : ℕ ↦ ∏ i ∈ Finset.range n, (1 + sineTerm x i)) atTop
    (𝓝 (sin (π * x) / (π * x))) := by
  rw [show (sin (π * x) / (π * x)) = sin (π * x) * (1 / (π * x)) by ring]
  apply (Filter.Tendsto.mul_const (b := 1 / (π * x)) (tendsto_euler_sin_prod x)).congr
  exact fun n ↦ by field_simp [sineTerm, Real.pi_ne_zero, sub_eq_add_neg]

theorem multipliable_sineTerm (x : ℂ) : Multipliable fun i ↦ (1 + sineTerm x i) := by
  apply multipliable_one_add_of_summable
  have := summable_pow_div_add (x ^ 2) 2 1 Nat.one_lt_two
  simpa [sineTerm] using this

lemma euler_sineTerm_tprod (hx : x ∈ ℂ_ℤ) :
    ∏' i : ℕ, (1 + sineTerm x i) = Complex.sin (π * x) / (π * x) := by
  rw [← Multipliable.hasProd_iff (multipliable_sineTerm x) ,
    Multipliable.hasProd_iff_tendsto_nat (multipliable_sineTerm x)]
  exact tendsto_euler_sin_prod' (integerComplement.ne_zero hx)

private lemma sineTerm_bound_aux (hZ : IsCompact Z) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ j z, z ∈ Z → ‖sineTerm z j‖ ≤ u j := by
  have hf : ContinuousOn (fun x : ℂ => ‖-x ^ 2‖) Z := by
    fun_prop
  obtain ⟨s, hs⟩ := bddAbove_def.mp (IsCompact.bddAbove_image hZ hf)
  refine ⟨fun n : ℕ => ‖(s : ℂ) / (n + 1) ^ 2‖, ?_, ?_⟩
  · simpa using summable_pow_div_add (s : ℂ) 2 1 (Nat.one_lt_two)
  · simp only [norm_neg, norm_pow, Set.mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, sineTerm, norm_div, norm_real, norm_eq_abs] at *
    intro n x hx
    gcongr
    apply le_trans (hs x hx) (le_abs_self s)

theorem multipliableUniformlyOn_euler_sin_prod_on_compact (hZC : IsCompact Z) :
    MultipliableUniformlyOn (fun n : ℕ => fun z : ℂ => (1 + sineTerm z n)) {Z} := by
  obtain ⟨u, hu, hu2⟩ := sineTerm_bound_aux hZC
  refine Summable.multipliableUniformlyOn_nat_one_add hZC hu ?_ ?_
  · filter_upwards with n z hz using hu2 n z hz
  · fun_prop

theorem HasProdUniformlyOn_sineTerm_prod_on_compact (hZ2 : Z ⊆ ℂ_ℤ)
    (hZC : IsCompact Z) :
    HasProdUniformlyOn (fun n : ℕ => fun z : ℂ => (1 + sineTerm z n))
    (fun x => (Complex.sin (↑π * x) / (↑π * x))) {Z} := by
  apply (multipliableUniformlyOn_euler_sin_prod_on_compact hZC).hasProdUniformlyOn.congr_right
  exact fun s hs x hx => euler_sineTerm_tprod (by aesop)

theorem HasProdLocallyUniformlyOn_euler_sin_prod :
    HasProdLocallyUniformlyOn (fun n : ℕ => fun z : ℂ => (1 + sineTerm z n))
    (fun x => (Complex.sin (π * x) / (π * x))) ℂ_ℤ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_compl_range_intCast
  exact fun _ hZ hZC => HasProdUniformlyOn_sineTerm_prod_on_compact hZ hZC

theorem sin_pi_z_ne_zero (hz : x ∈ ℂ_ℤ) : Complex.sin (π * x) ≠ 0 := by
  apply Complex.sin_ne_zero_iff.2
  intro k
  nth_rw 2 [mul_comm]
  exact Injective.ne (mul_right_injective₀ (ofReal_ne_zero.mpr Real.pi_ne_zero)) (by aesop)

theorem tendsto_logDeriv_euler_sin_div (hx : x ∈ ℂ_ℤ) :
    Tendsto (fun n : ℕ ↦ logDeriv (fun z ↦ ∏ j ∈ Finset.range n, (1 + sineTerm z j)) x)
        atTop (𝓝 <| logDeriv (fun t ↦ (Complex.sin (π * t) / (π * t))) x) := by
  refine logDeriv_tendsto (isOpen_compl_range_intCast) ⟨x, hx⟩
      HasProdLocallyUniformlyOn_euler_sin_prod.tendstoLocallyUniformlyOn_finsetRange ?_ ?_
  · filter_upwards with n using by fun_prop
  · simp only [ne_eq, div_eq_zero_iff, mul_eq_zero, ofReal_eq_zero, not_or]
    exact ⟨sin_pi_z_ne_zero hx, Real.pi_ne_zero , integerComplement.ne_zero hx⟩

theorem logDeriv_sin_div_eq_cot (hz : x ∈ ℂ_ℤ) :
    logDeriv (fun t ↦ (Complex.sin (π * t) / (π * t))) x = π * cot (π * x) - 1 / x := by
  have : (fun t ↦ (Complex.sin (π * t)/ (π * t))) = fun z ↦
    (Complex.sin ∘ fun t ↦ π * t) z / (π * z) := by simp
  rw [this, logDeriv_div _ (by apply sin_pi_z_ne_zero hz) ?_
    (DifferentiableAt.comp _ (Complex.differentiableAt_sin) (by fun_prop)) (by fun_prop),
    logDeriv_comp (Complex.differentiableAt_sin) (by fun_prop), Complex.logDeriv_sin,
    deriv_const_mul _ (by fun_prop), deriv_id'', logDeriv_const_mul, logDeriv_id']
  · field_simp [mul_comm]
  · simpa using Real.pi_ne_zero
  · simp only [ne_eq, mul_eq_zero, ofReal_eq_zero, not_or]
    exact ⟨Real.pi_ne_zero, integerComplement.ne_zero hz⟩

/-- The term in the infinite sum expansion of cot. -/
noncomputable abbrev cotTerm (x : ℂ) (n : ℕ) : ℂ := 1 / (x - (n + 1)) + 1 / (x + (n + 1))

theorem logDeriv_sineTerm_eq_cotTerm (hx : x ∈ ℂ_ℤ) (i : ℕ) :
    logDeriv (fun (z : ℂ) ↦ 1 + sineTerm z i) x = cotTerm x i := by
  have h1 := integerComplement_add_ne_zero hx (i + 1)
  have h2 : ((x : ℂ) - (i + 1)) ≠ 0 := by
    simpa [sub_eq_add_neg] using integerComplement_add_ne_zero hx (-(i + 1))
  have h3 : (i+1)^2 + -x^2 ≠ 0 := by
      have := (integerComplement_pow_two_ne_pow_two hx ((i + 1) : ℤ))
      rw [← sub_eq_add_neg, sub_ne_zero]
      aesop
  simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, ne_eq, sineTerm, logDeriv_apply,
    deriv_const_add', deriv_div_const, deriv.fun_neg', differentiableAt_fun_id, deriv_fun_pow,
    Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, cotTerm, one_div] at *
  field_simp [Nat.cast_add_one_ne_zero i]
  ring

lemma logDeriv_prod_sineTerm_eq_sum_cotTerm (hx : x ∈ ℂ_ℤ) (n : ℕ) :
    logDeriv (fun (z : ℂ) ↦ ∏ j ∈ Finset.range n, (1 + sineTerm z j)) x =
    ∑ j ∈ Finset.range n, cotTerm x j := by
  rw [logDeriv_prod]
  · simp_rw [logDeriv_sineTerm_eq_cotTerm hx]
  · exact fun i _ ↦ sineTerm_ne_zero hx i
  · fun_prop

theorem tendsto_logDeriv_euler_cot_sub (hx : x ∈ ℂ_ℤ) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range n, cotTerm x j) atTop
    (𝓝 <| π * cot (π * x)- 1 / x) := by
  simp_rw [← logDeriv_sin_div_eq_cot hx, ← logDeriv_prod_sineTerm_eq_sum_cotTerm hx]
  simpa using tendsto_logDeriv_euler_sin_div hx

lemma cotTerm_identity (hz : x ∈ ℂ_ℤ) (n : ℕ) :
    cotTerm x n = 2 * x * (1 / ((x + (n + 1)) * (x - (n + 1)))) := by
  simp only [cotTerm]
  rw [one_div_add_one_div]
  · ring
  · simpa [sub_eq_add_neg] using integerComplement_add_ne_zero hz (-(n + 1) : ℤ)
  · simpa using (integerComplement_add_ne_zero hz ((n : ℤ) + 1))

theorem Summable_cotTerm (hz : x ∈ ℂ_ℤ) : Summable fun n ↦ cotTerm x n := by
  rw [funext fun n ↦ cotTerm_identity hz n]
  apply Summable.mul_left
  suffices Summable fun i : ℕ ↦ (x - (↑i : ℂ))⁻¹ * (x + (↑i : ℂ))⁻¹ by
    rw [← summable_nat_add_iff 1] at this
    simpa using this
  suffices Summable fun i : ℤ ↦ (x - (↑i : ℂ))⁻¹ * (x + (↑i : ℂ))⁻¹ by
    apply this.comp_injective CharZero.cast_injective
  apply (EisensteinSeries.summable_linear_sub_mul_linear_add x 1 1).congr
  simp [mul_comm]

theorem cot_series_rep' (hz : x ∈ ℂ_ℤ) : π * cot (π * x) - 1 / x =
    ∑' n : ℕ, (1 / (x - (n + 1)) + 1 / (x + (n + 1))) := by
  rw [HasSum.tsum_eq]
  apply (Summable.hasSum_iff_tendsto_nat (Summable_cotTerm hz)).mpr
    (tendsto_logDeriv_euler_cot_sub hz)

/-- The cotangent infinite sum representation. -/
theorem cot_series_rep (hz : x ∈ ℂ_ℤ) :
    π * cot (π * x) = 1 / x + ∑' n : ℕ+, (1 / (x - n) + 1 / (x + n)) := by
  have h0 := tsum_pnat_eq_tsum_succ fun n ↦ 1 / (x - n) + 1 / (x + n)
  have h1 := cot_series_rep' hz
  simp only [one_div, Nat.cast_add, Nat.cast_one] at *
  rw [h0, ← h1]
  ring

end MittagLeffler
