/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
public import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
public import Mathlib.Analysis.Complex.IntegerCompl
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# Cotangent

This file contains lemmas about the cotangent function, including useful series expansions.
In particular, we prove that
`π * cot (π * z) = π * I - 2 * π * I * ∑' n : ℕ, Complex.exp (2 * π * I * z) ^ n`
as well as the infinite sum representation of cotangent (also known as the Mittag-Leffler
expansion): `π * cot (π * z) = 1 / z + ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n))`.
-/

public section

open Real Complex

open scoped UpperHalfPlane

local notation "ℂ_ℤ" => integerComplement

local notation "ℍₒ" => UpperHalfPlane.upperHalfPlaneSet

lemma Complex.cot_eq_exp_ratio (z : ℂ) :
    cot z = (Complex.exp (2 * I * z) + 1) / (I * (1 - Complex.exp (2 * I * z))) := by
  rw [Complex.cot, Complex.sin, Complex.cos]
  have h1 : exp (z * I) + exp (-z * I) = exp (-(z * I)) * (exp (2 * I * z) + 1) := by
    rw [mul_add, ← Complex.exp_add]
    ring_nf
  have h2 : (exp (-z * I) - exp (z * I)) = exp (-(z * I)) * ((1 - exp (2 * I * z))) := by
    ring_nf
    rw [mul_assoc, ← Complex.exp_add]
    ring_nf
  rw [h1, h2]
  field

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

variable {x : ℂ} {Z : Set ℂ}

/-- The main term in the infinite product for sine. -/
noncomputable abbrev sineTerm (x : ℂ) (n : ℕ) : ℂ := -x ^ 2 / (n + 1) ^ 2

lemma sineTerm_ne_zero {x : ℂ} (hx : x ∈ ℂ_ℤ) (n : ℕ) : 1 + sineTerm x n ≠ 0 := by
  simp only [sineTerm, ne_eq]
  rw [add_eq_zero_iff_eq_neg, neg_div', eq_div_iff]
  · have := (integerComplement_pow_two_ne_pow_two hx (n + 1 : ℤ))
    aesop
  · simp [Nat.cast_add_one_ne_zero n]

lemma tendsto_euler_sin_prod' (h0 : x ≠ 0) :
    Tendsto (fun n : ℕ ↦ ∏ i ∈ Finset.range n, (1 + sineTerm x i)) atTop
    (𝓝 (sin (π * x) / (π * x))) := by
  rw [show (sin (π * x) / (π * x)) = sin (π * x) * (1 / (π * x)) by ring]
  apply (Filter.Tendsto.mul_const (b := 1 / (π * x)) (tendsto_euler_sin_prod x)).congr
  exact fun n ↦ by field_simp; rfl

lemma multipliable_sineTerm (x : ℂ) : Multipliable fun i ↦ (1 + sineTerm x i) := by
  apply multipliable_one_add_of_summable
  have := summable_pow_div_add (x ^ 2) 2 1 Nat.one_lt_two
  simpa [sineTerm] using this

lemma euler_sineTerm_tprod (hx : x ∈ ℂ_ℤ) :
    ∏' i : ℕ, (1 + sineTerm x i) = Complex.sin (π * x) / (π * x) := by
  rw [← Multipliable.hasProd_iff (multipliable_sineTerm x),
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

lemma multipliableUniformlyOn_euler_sin_prod_on_compact (hZC : IsCompact Z) :
    MultipliableUniformlyOn (fun n : ℕ => fun z : ℂ => (1 + sineTerm z n)) Z := by
  obtain ⟨u, hu, hu2⟩ := sineTerm_bound_aux hZC
  refine Summable.multipliableUniformlyOn_nat_one_add hZC hu ?_ ?_
  · filter_upwards with n z hz using hu2 n z hz
  · fun_prop

lemma HasProdUniformlyOn_sineTerm_prod_on_compact (hZ2 : Z ⊆ ℂ_ℤ)
    (hZC : IsCompact Z) :
    HasProdUniformlyOn (fun n : ℕ => fun z : ℂ => (1 + sineTerm z n))
    (fun x => (Complex.sin (↑π * x) / (↑π * x))) Z := by
  apply (multipliableUniformlyOn_euler_sin_prod_on_compact hZC).hasProdUniformlyOn.congr_right
  exact fun x hx => euler_sineTerm_tprod (by aesop)

lemma HasProdLocallyUniformlyOn_euler_sin_prod :
    HasProdLocallyUniformlyOn (fun n : ℕ => fun z : ℂ => (1 + sineTerm z n))
    (fun x => (Complex.sin (π * x) / (π * x))) ℂ_ℤ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_compl_range_intCast
  exact fun _ hZ hZC => HasProdUniformlyOn_sineTerm_prod_on_compact hZ hZC

/-- `sin π z` is non vanishing on the complement of the integers in `ℂ`. -/
theorem sin_pi_mul_ne_zero (hx : x ∈ ℂ_ℤ) : Complex.sin (π * x) ≠ 0 := by
  apply Complex.sin_ne_zero_iff.2
  intro k
  nth_rw 2 [mul_comm]
  exact Injective.ne (mul_right_injective₀ (ofReal_ne_zero.mpr Real.pi_ne_zero)) (by aesop)

lemma cot_pi_mul_contDiffWithinAt (k : ℕ∞) (hx : x ∈ ℂ_ℤ) :
    ContDiffWithinAt ℂ k (fun x ↦ (↑π * x).cot) ℍₒ x := by
  simp_rw [Complex.cot, Complex.cos, Complex.sin]
  exact ContDiffWithinAt.div (by fun_prop) (by fun_prop) (sin_pi_mul_ne_zero hx)

lemma tendsto_logDeriv_euler_sin_div (hx : x ∈ ℂ_ℤ) :
    Tendsto (fun n : ℕ ↦ logDeriv (fun z ↦ ∏ j ∈ Finset.range n, (1 + sineTerm z j)) x)
        atTop (𝓝 <| logDeriv (fun t ↦ (Complex.sin (π * t) / (π * t))) x) := by
  refine logDeriv_tendsto (isOpen_compl_range_intCast) hx
      HasProdLocallyUniformlyOn_euler_sin_prod.tendstoLocallyUniformlyOn_finsetRange ?_ ?_
  · filter_upwards with n using by fun_prop
  · simp only [ne_eq, div_eq_zero_iff, mul_eq_zero, ofReal_eq_zero, not_or]
    exact ⟨sin_pi_mul_ne_zero hx, Real.pi_ne_zero, integerComplement.ne_zero hx⟩

lemma logDeriv_sin_div_eq_cot (hz : x ∈ ℂ_ℤ) :
    logDeriv (fun t ↦ (Complex.sin (π * t) / (π * t))) x = π * cot (π * x) - 1 / x := by
  have : (fun t ↦ (Complex.sin (π * t) / (π * t))) = fun z ↦
    (Complex.sin ∘ fun t ↦ π * t) z / (π * z) := by simp
  rw [this, logDeriv_div _ (by apply sin_pi_mul_ne_zero hz) ?_
    (DifferentiableAt.comp _ (Complex.differentiableAt_sin) (by fun_prop)) (by fun_prop),
    logDeriv_comp (Complex.differentiableAt_sin) (by fun_prop), Complex.logDeriv_sin,
    deriv_const_mul _ (by fun_prop), deriv_id'', logDeriv_const_mul, logDeriv_id']
  · ring
  · simp
  · simp only [ne_eq, mul_eq_zero, ofReal_eq_zero, not_or]
    exact ⟨Real.pi_ne_zero, integerComplement.ne_zero hz⟩

/-- The term in the infinite sum expansion of cot. -/
noncomputable abbrev cotTerm (x : ℂ) (n : ℕ) : ℂ := 1 / (x - (n + 1)) + 1 / (x + (n + 1))

lemma logDeriv_sineTerm_eq_cotTerm (hx : x ∈ ℂ_ℤ) (i : ℕ) :
    logDeriv (fun (z : ℂ) ↦ 1 + sineTerm z i) x = cotTerm x i := by
  have h1 := integerComplement_add_ne_zero hx (i + 1)
  have h2 : ((x : ℂ) - (i + 1)) ≠ 0 := by
    simpa [sub_eq_add_neg] using integerComplement_add_ne_zero hx (-(i + 1))
  have h3 : (i + 1) ^ 2 + - x ^ 2 ≠ 0 := by
      have := (integerComplement_pow_two_ne_pow_two hx ((i + 1) : ℤ))
      rw [← sub_eq_add_neg, sub_ne_zero]
      aesop
  simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, ne_eq, sineTerm, logDeriv_apply,
    deriv_const_add', deriv_div_const, deriv.fun_neg', differentiableAt_fun_id, deriv_fun_pow,
    Nat.cast_ofNat, deriv_id'', cotTerm] at *
  field

lemma logDeriv_prod_sineTerm_eq_sum_cotTerm (hx : x ∈ ℂ_ℤ) (n : ℕ) :
    logDeriv (fun (z : ℂ) ↦ ∏ j ∈ Finset.range n, (1 + sineTerm z j)) x =
    ∑ j ∈ Finset.range n, cotTerm x j := by
  rw [logDeriv_prod]
  · simp_rw [logDeriv_sineTerm_eq_cotTerm hx]
  · exact fun i _ ↦ sineTerm_ne_zero hx i
  · fun_prop

lemma tendsto_logDeriv_euler_cot_sub (hx : x ∈ ℂ_ℤ) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range n, cotTerm x j) atTop
    (𝓝 <| π * cot (π * x) - 1 / x) := by
  simp_rw [← logDeriv_sin_div_eq_cot hx, ← logDeriv_prod_sineTerm_eq_sum_cotTerm hx]
  simpa using tendsto_logDeriv_euler_sin_div hx

lemma cotTerm_identity (hz : x ∈ ℂ_ℤ) (n : ℕ) :
    cotTerm x n = 2 * x * (1 / ((x + (n + 1)) * (x - (n + 1)))) := by
  simp only [cotTerm]
  rw [one_div_add_one_div]
  · ring
  · simpa [sub_eq_add_neg] using integerComplement_add_ne_zero hz (-(n + 1) : ℤ)
  · simpa using (integerComplement_add_ne_zero hz ((n : ℤ) + 1))

lemma summable_cotTerm (hz : x ∈ ℂ_ℤ) : Summable fun n ↦ cotTerm x n := by
  rw [funext fun n ↦ cotTerm_identity hz n]
  apply Summable.mul_left
  suffices Summable fun i : ℕ ↦ (x - (↑i : ℂ))⁻¹ * (x + (↑i : ℂ))⁻¹ by
    rw [← summable_nat_add_iff 1] at this
    simpa using this
  suffices Summable fun i : ℤ ↦ (x - (↑i : ℂ))⁻¹ * (x + (↑i : ℂ))⁻¹ by
    apply this.comp_injective CharZero.cast_injective
  apply (EisensteinSeries.summable_linear_sub_mul_linear_add x 1 1).congr
  simp [mul_comm]

@[deprecated (since := "2026-01-28")] alias Summable_cotTerm := summable_cotTerm

lemma cot_series_rep' (hz : x ∈ ℂ_ℤ) : π * cot (π * x) - 1 / x =
    ∑' n : ℕ, (1 / (x - (n + 1)) + 1 / (x + (n + 1))) := by
  rw [HasSum.tsum_eq]
  apply (Summable.hasSum_iff_tendsto_nat (summable_cotTerm hz)).mpr
    (tendsto_logDeriv_euler_cot_sub hz)

/-- The cotangent infinite sum representation. -/
theorem cot_series_rep (hz : x ∈ ℂ_ℤ) :
    π * cot (π * x) = 1 / x + ∑' n : ℕ+, (1 / (x - n) + 1 / (x + n)) := by
  have h0 := tsum_pnat_eq_tsum_succ (f := fun n ↦ 1 / (x - n) + 1 / (x + n))
  have h1 := cot_series_rep' hz
  simp only [one_div, Nat.cast_add, Nat.cast_one] at *
  rw [h0, ← h1]
  ring

end MittagLeffler

section iteratedDeriv

open Set UpperHalfPlane

open scoped Nat

variable (k : ℕ)

private lemma contDiffOn_inv_linear (d : ℤ) : ContDiffOn ℂ k (fun z : ℂ ↦ 1 / (z + d)) ℂ_ℤ := by
  simpa using ContDiffOn.inv (by fun_prop) (fun x hx ↦ integerComplement_add_ne_zero hx d)

lemma eqOn_iteratedDeriv_cotTerm (d : ℕ) :
    EqOn (iteratedDeriv k (fun z ↦ cotTerm z d))
    (fun z ↦ (-1) ^ k * k ! * ((z + (d + 1)) ^ (-1 - k : ℤ) + (z - (d + 1)) ^ (-1 - k : ℤ)))
    ℂ_ℤ := by
  intro z hz
  rw [← Pi.add_def, iteratedDeriv_add]
  · have h2 := iter_deriv_inv_linear_sub k 1 ((d + 1 : ℂ))
    have h3 := iter_deriv_inv_linear k 1 (d + 1 : ℂ)
    simp only [one_div, one_mul, one_pow, mul_one, Int.reduceNeg, iteratedDeriv_eq_iterate] at *
    rw [h2, h3]
    ring
  · simpa [sub_eq_add_neg] using (contDiffOn_inv_linear k (-(d + 1))).contDiffAt
      ((isOpen_compl_range_intCast).mem_nhds hz)
  · simpa using (contDiffOn_inv_linear k (d + 1)).contDiffAt
      ((isOpen_compl_range_intCast).mem_nhds hz)

lemma eqOn_iteratedDerivWithin_cotTerm_integerComplement (d : ℕ) :
    EqOn
      (iteratedDerivWithin k (fun z ↦ cotTerm z d) ℂ_ℤ)
      (fun z ↦ (-1) ^ k * k ! * ((z + (d + 1)) ^ (-1 - k : ℤ) + (z - (d + 1)) ^ (-1 - k : ℤ)))
      ℂ_ℤ := by
  apply Set.EqOn.trans (iteratedDerivWithin_of_isOpen isOpen_compl_range_intCast)
  exact eqOn_iteratedDeriv_cotTerm ..

lemma eqOn_iteratedDerivWithin_cotTerm_upperHalfPlaneSet (d : ℕ) :
    EqOn
      (iteratedDerivWithin k (fun z ↦ cotTerm z d) ℍₒ)
      (fun z ↦ (-1) ^ k * k ! * ((z + (d + 1)) ^ (-1 - k : ℤ) + (z - (d + 1)) ^ (-1 - k : ℤ)))
      ℍₒ := by
  apply Set.EqOn.trans (upperHalfPlane_inter_integerComplement ▸
    iteratedDerivWithin_congr_right_of_isOpen (fun z ↦ cotTerm z d) k
    isOpen_upperHalfPlaneSet (isOpen_compl_range_intCast))
  intro z hz
  simpa using eqOn_iteratedDerivWithin_cotTerm_integerComplement k d
    (coe_mem_integerComplement ⟨z, hz⟩)

open EisensteinSeries in
private noncomputable abbrev cotTermUpperBound (A B : ℝ) (hB : 0 < B) (a : ℕ) :=
  k ! * (2 * (r (⟨⟨A, B⟩, hB⟩) ^ (-1 - k : ℤ)) * ‖((a + 1) ^ (-1 - k : ℤ) : ℝ)‖)

private lemma summable_cotTermUpperBound (A B : ℝ) (hB : 0 < B) {k : ℕ} (hk : 1 ≤ k) :
    Summable fun a : ℕ ↦ cotTermUpperBound k A B hB a := by
  simp_rw [← mul_assoc]
  apply Summable.mul_left
  conv => enter [1, n]; rw [show (-1 - k : ℤ) = -(1 + k :) by lia, zpow_neg, zpow_natCast];
          enter [1, 1, 1]; norm_cast
  rw [summable_norm_iff, summable_nat_add_iff (f := fun n : ℕ ↦ ((n : ℝ) ^ (1 + k))⁻¹)]
  exact summable_nat_pow_inv.mpr <| by lia

open EisensteinSeries in
private lemma iteratedDerivWithin_cotTerm_bounded_uniformly
    {k : ℕ} {K : Set ℂ} (A B : ℝ) (hB : 0 < B)
    (hKAB : K ⊆ (↑) '' verticalStrip A B) (n : ℕ) {a : ℂ} (ha : a ∈ K) :
    ‖iteratedDerivWithin k (fun z ↦ cotTerm z n) ℍₒ a‖ ≤ cotTermUpperBound k A B hB n := by
  rcases hKAB ha with ⟨a, haAB, rfl⟩
  simp only [eqOn_iteratedDerivWithin_cotTerm_upperHalfPlaneSet k n a.im_pos, Complex.norm_mul,
    norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast, one_mul, cotTermUpperBound,
    Int.reduceNeg, norm_zpow, Real.norm_eq_abs, two_mul, add_mul]
  gcongr
  have h1 := summand_bound_of_mem_verticalStrip (k := k + 1) (by positivity) ![1, n + 1] hB haAB
  have h2 := abs_norm_eq_max_natAbs_neg n ▸ summand_bound_of_mem_verticalStrip (k := k + 1)
    (by positivity) ![1, -(n + 1)] hB haAB
  apply norm_add_le_of_le
  · simpa (disch := positivity) [sub_eq_add_neg, ← Real.rpow_intCast, abs_norm_eq_max_natAbs,
      abs_of_nonneg] using h1
  · simpa (disch := positivity) [sub_eq_add_neg, ← Real.rpow_intCast, abs_norm_eq_max_natAbs,
      abs_of_nonneg] using h2

lemma summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm {k : ℕ} (hk : 1 ≤ k) :
    SummableLocallyUniformlyOn (fun n ↦ iteratedDerivWithin k (fun z ↦ cotTerm z n) ℍₒ) ℍₒ := by
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_upperHalfPlaneSet
  intro K hK hKc
  lift K to Set ℍ using hK
  obtain ⟨A, B, hB, HABK⟩ := subset_verticalStrip_of_isCompact
    (isEmbedding_coe.isCompact_iff.mpr hKc)
  exact ⟨cotTermUpperBound k A B hB, summable_cotTermUpperBound A B hB hk,
    iteratedDerivWithin_cotTerm_bounded_uniformly A B hB <| by gcongr⟩

lemma differentiableOn_iteratedDerivWithin_cotTerm (n l : ℕ) :
    DifferentiableOn ℂ (iteratedDerivWithin l (fun z ↦ cotTerm z n) ℍₒ) ℍₒ := by
  suffices DifferentiableOn ℂ (fun z : ℂ ↦ (-1) ^ l * l ! * ((z + (n + 1)) ^ (-1 - l : ℤ) +
    (z - (n + 1)) ^ (-1 - l : ℤ))) ℍₒ by
    exact this.congr fun z hz ↦ eqOn_iteratedDerivWithin_cotTerm_upperHalfPlaneSet l n hz
  apply DifferentiableOn.const_mul
  apply DifferentiableOn.add <;> refine DifferentiableOn.zpow (by fun_prop) <| .inl fun x hx ↦ ?_
  · simpa [add_eq_zero_iff_neg_eq'] using (UpperHalfPlane.ne_intCast (.mk x hx) (-(n + 1))).symm
  · simpa [sub_eq_zero] using (UpperHalfPlane.ne_intCast (.mk x hx) (n + 1))

private lemma aux_summable_add {k : ℕ} (hk : 1 ≤ k) (x : ℂ) :
  Summable fun (n : ℕ) ↦ (x + (n + 1)) ^ (-1 - k : ℤ) := by
  apply ((summable_nat_add_iff 1).mpr (summable_int_iff_summable_nat_and_neg.mp
        (EisensteinSeries.linear_right_summable x 1 (k := k + 1) (by lia))).1).congr
  simp [← zpow_neg, sub_eq_add_neg]

private lemma aux_summable_sub {k : ℕ} (hk : 1 ≤ k) (x : ℂ) :
  Summable fun (n : ℕ) ↦ (x - (n + 1)) ^ (-1 - k : ℤ) := by
  apply ((summable_nat_add_iff 1).mpr (summable_int_iff_summable_nat_and_neg.mp
        (EisensteinSeries.linear_right_summable x 1 (k := k + 1) (by lia))).2).congr
  simp [← zpow_neg, sub_eq_add_neg]

variable {z : ℂ}

-- We have this auxiliary ugly version on the lhs so the rhs looks nicer.
private lemma aux_iteratedDeriv_tsum_cotTerm {k : ℕ} (hk : 1 ≤ k) (hz : z ∈ ℍₒ) :
    (-1) ^ k * (k !) * z ^ (-1 - k : ℤ) +
      iteratedDerivWithin k (fun z ↦ ∑' n : ℕ, cotTerm z n) ℍₒ z =
    (-1) ^ k * k ! * ∑' n : ℤ, (z + n) ^ (-1 - k : ℤ) := by
  rw [iteratedDerivWithin_tsum k isOpen_upperHalfPlaneSet hz
    (fun t ht ↦ summable_cotTerm (coe_mem_integerComplement ⟨t, ht⟩))
    (fun l hl hl2 ↦ summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm hl)
    (fun n l z hl hz ↦ (differentiableOn_iteratedDerivWithin_cotTerm n l).differentiableAt
    (isOpen_upperHalfPlaneSet.mem_nhds hz))]
  conv =>
    enter [1, 2, 1, n]
    rw [eqOn_iteratedDerivWithin_cotTerm_upperHalfPlaneSet k n (by simp [hz])]
  rw [tsum_of_add_one_of_neg_add_one (by simpa using aux_summable_add hk z)
    (by simpa [sub_eq_add_neg] using aux_summable_sub hk z),
    tsum_mul_left, Summable.tsum_add (aux_summable_add hk z) (aux_summable_sub hk z)]
  push_cast
  ring_nf

lemma iteratedDerivWithin_cot_sub_inv_eq_add_mul_tsum {k : ℕ} (hk : 1 ≤ k) (hz : z ∈ ℍₒ) :
    iteratedDerivWithin k (fun x : ℂ ↦ π * cot (π * x) - 1 / x) ℍₒ z =
    -(-1) ^ k * k ! * (z ^ (-1 - k : ℤ)) + (-1) ^ k * k ! * ∑' n : ℤ, (z + n) ^ (-1 - k : ℤ) := by
  simp only [← aux_iteratedDeriv_tsum_cotTerm hk hz, one_div, neg_mul, neg_add_cancel_left]
  refine iteratedDerivWithin_congr (fun z hz ↦ ?_) hz
  simpa [cotTerm] using (cot_series_rep' (UpperHalfPlane.coe_mem_integerComplement ⟨z, hz⟩))

private lemma iteratedDerivWithin_cot_pi_mul_sub_inv {z : ℂ} (hz : z ∈ ℍₒ) :
    iteratedDerivWithin k (fun x : ℂ ↦ π * cot (π * x) - 1 / x) ℍₒ z =
    (iteratedDerivWithin k (fun x : ℂ ↦ π * cot (π * x)) ℍₒ z) -
    (-1) ^ k * k ! * (z ^ (-1 - k : ℤ)) := by
  simp_rw [sub_eq_add_neg]
  rw [iteratedDerivWithin_fun_add hz isOpen_upperHalfPlaneSet.uniqueDiffOn]
  · simpa [iteratedDerivWithin_fun_neg] using iteratedDerivWithin_one_div k
      isOpen_upperHalfPlaneSet hz
  · exact ContDiffWithinAt.mul (by fun_prop) (cot_pi_mul_contDiffWithinAt k
      (UpperHalfPlane.coe_mem_integerComplement ⟨z, hz⟩))
  · simp only [one_div]
    apply ContDiffWithinAt.neg
    exact ContDiffWithinAt.inv (by fun_prop) (ne_zero ⟨z, hz⟩)

lemma iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_zpow {k : ℕ} (hk : 1 ≤ k) {z : ℂ} (hz : z ∈ ℍₒ) :
    iteratedDerivWithin k (fun x : ℂ ↦ π * cot (π * x)) ℍₒ z =
    (-1) ^ k * k ! * ∑' n : ℤ, (z + n) ^ (-1 - k : ℤ) := by
  have h0 := iteratedDerivWithin_cot_pi_mul_sub_inv k hz
  rw [iteratedDerivWithin_cot_sub_inv_eq_add_mul_tsum hk hz, add_comm] at h0
  rw [← add_left_inj (-(-1) ^ k * k ! * z ^ (-1 - k : ℤ)), h0]
  ring

/-- The series expansion of the iterated derivative of `π cot (π z)`. -/
theorem iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow {k : ℕ} (hk : 1 ≤ k) {z : ℂ}
    (hz : z ∈ ℍₒ) :
    iteratedDerivWithin k (fun x : ℂ ↦ π * cot (π * x)) ℍₒ z =
      (-1) ^ k * k ! * ∑' n : ℤ, 1 / (z + n) ^ (k + 1) := by
  convert iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_zpow hk hz with n
  rw [show (-1 - k : ℤ) = -(k + 1 :) by norm_cast; lia, zpow_neg_coe_of_pos _ (by lia),
    one_div]

end iteratedDeriv
