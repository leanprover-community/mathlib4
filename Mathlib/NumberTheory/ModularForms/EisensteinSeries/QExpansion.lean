/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.TsumDivsorsAntidiagonal
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Eisenstein series q-expansions

We give the q-expansion of Eisenstein series of weight `k` and level 1. In particular we show that
for even `k` with `3 ≤ k` Eisenstein series can we written as
`1 - (2k / bernoulli k) ∑' n, σ_{k-1}(n) q^n` where `q = exp(2πiz)` and `σ_{k-1}(n)` is the sum of
the `(k-1)`-th powers of the divisors of `n`.

-/

open Set Metric TopologicalSpace Function Filter Complex ArithmeticFunction
  ModularForm EisensteinSeries

open scoped Topology Real Nat Complex Pointwise

open _root_.UpperHalfPlane hiding I

local notation "ℍₒ" => upperHalfPlaneSet

private lemma iteratedDerivWithin_cexp_aux (k m : ℕ) (p : ℝ) {S : Set ℂ} (hs : IsOpen S) :
    EqOn (iteratedDerivWithin k (fun s : ℂ ↦ cexp (2 * π * I * m * s / p)) S)
    (fun s ↦ (2 * π * I * m / p) ^ k * cexp (2 * π * I * m * s / p)) S := by
  apply EqOn.trans (iteratedDerivWithin_of_isOpen hs)
  intro x hx
  have : (fun s ↦ cexp (2 * π * I * m * s / p)) = fun s ↦ cexp (((2 * π * I * m) / p) * s) := by
    ext z
    ring_nf
  simp only [this, iteratedDeriv_cexp_const_mul]
  ring_nf

private lemma aux_IsBigO_mul (k l : ℕ) (p : ℝ) {f : ℕ → ℂ}
    (hf : f =O[atTop] fun n ↦ ((n ^ l) : ℝ)) :
    (fun n ↦ f n * (2 * π * I * n / p) ^ k) =O[atTop] fun n ↦ (↑(n ^ (l + k)) : ℝ) := by
  have h0 : (fun n : ℕ ↦ (2 * π * I * n / p) ^ k) =O[atTop] fun n ↦ ((n ^ k) : ℝ) := by
    have h1 : (fun n : ℕ ↦ (2 * π * I * n / p) ^ k) =
        fun n : ℕ ↦ ((2 * π * I / p) ^ k) * n ^ k := by
      ext z
      ring
    simpa [h1] using isBigO_ofReal_right.mp (Asymptotics.isBigO_const_mul_self
      ((2 * π * I / p) ^ k) (fun (n : ℕ) ↦ (↑(n ^ k) : ℝ)) atTop)
  simp only [Nat.cast_pow]
  convert hf.mul h0
  ring

open BoundedContinuousFunction in
/-- The infinte sum of `k`-th iterated derivative of the complex exponential multiplied by a
function that grows polynomially is absolutely and uniformly convergent. -/
theorem summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp (k l : ℕ) {f : ℕ → ℂ} {p : ℝ}
    (hp : 0 < p) (hf : f =O[atTop] (fun n ↦ ((n ^ l) : ℝ))) :
    SummableLocallyUniformlyOn (fun n ↦ (f n) •
      iteratedDerivWithin k (fun z ↦ cexp (2 * π * I * z / p) ^ n) ℍₒ) ℍₒ := by
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_upperHalfPlaneSet
  intro K hK hKc
  have : CompactSpace K := isCompact_univ_iff.mp (isCompact_iff_isCompact_univ.mp hKc)
  let c : ContinuousMap K ℂ := ⟨fun r : K ↦ Complex.exp (2 * π * I * r / p), by fun_prop⟩
  let r : ℝ := ‖mkOfCompact c‖
  have hr : ‖r‖ < 1 := by
    simp only [norm_norm, r, norm_lt_iff_of_compact Real.zero_lt_one, mkOfCompact_apply,
      ContinuousMap.coe_mk, c]
    intro x
    have h1 : cexp (2 * π * I * (x / p)) = cexp (2 * π * I * x / p) := by
      ring_nf
    simpa using h1 ▸ norm_exp_two_pi_I_lt_one ⟨((x : ℂ) / p), by aesop⟩
  refine ⟨_, by simpa using (summable_norm_mul_geometric_of_norm_lt_one' hr
    (Asymptotics.isBigO_norm_left.mpr (aux_IsBigO_mul k l p hf))), fun n z hz ↦ ?_⟩
  have h0 := pow_le_pow_left₀ (norm_nonneg _) (norm_coe_le_norm (mkOfCompact c) ⟨z, hz⟩) n
  simp only [norm_mkOfCompact, mkOfCompact_apply, ContinuousMap.coe_mk, ← exp_nsmul', Pi.smul_apply,
    iteratedDerivWithin_cexp_aux k n p isOpen_upperHalfPlaneSet (hK hz), smul_eq_mul,
    norm_mul, norm_pow, Complex.norm_div, norm_ofNat, norm_real, Real.norm_eq_abs, norm_I, mul_one,
    norm_natCast, abs_norm, ge_iff_le, r, c] at *
  rw [← mul_assoc]
  gcongr
  convert h0
  rw [← norm_pow, ← exp_nsmul']

/-- This is a version of `summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp` for level one
and q-expansion coefficients all `1`. -/
theorem summableLocallyUniformlyOn_iteratedDerivWithin_cexp (k : ℕ) :
    SummableLocallyUniformlyOn
      (fun n ↦ iteratedDerivWithin k (fun z ↦ cexp (2 * π * I * z) ^ n) ℍₒ) ℍₒ := by
  have h0 : (fun n : ℕ ↦ (1 : ℂ)) =O[atTop] fun n ↦ ((n ^ 1) : ℝ) := by
    simp only [Asymptotics.isBigO_iff, norm_one, norm_pow, Real.norm_natCast,
      eventually_atTop, ge_iff_le]
    exact ⟨1, 1, fun b hb ↦ by norm_cast; simp [hb]⟩
  simpa using summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp k 1 (p := 1)
    (by norm_num) h0

lemma differentiableAt_iteratedDerivWithin_cexp (n a : ℕ) {s : Set ℂ} (hs : IsOpen s)
    {r : ℂ} (hr : r ∈ s) : DifferentiableAt ℂ
      (iteratedDerivWithin a (fun z ↦ cexp (2 * π * I * z) ^ n) s) r := by
  apply DifferentiableOn.differentiableAt _ (hs.mem_nhds hr)
  suffices DifferentiableOn ℂ (iteratedDeriv a (fun z ↦ cexp (2 * π * I * z) ^ n)) s by
    apply this.congr (iteratedDerivWithin_of_isOpen hs)
  fun_prop

lemma iteratedDerivWithin_tsum_cexp_eq (k : ℕ) (z : ℍ) :
    iteratedDerivWithin k (fun z ↦ ∑' n : ℕ, cexp (2 * π * I * z) ^ n) ℍₒ z =
    ∑' n : ℕ, iteratedDerivWithin k (fun s : ℂ ↦ cexp (2 * π * I * s) ^ n) ℍₒ z := by
  rw [iteratedDerivWithin_tsum k isOpen_upperHalfPlaneSet (by simpa using z.2)]
  · exact fun x hx ↦ summable_geometric_iff_norm_lt_one.mpr
      (UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨x, hx⟩)
  · exact fun n _ _ ↦ summableLocallyUniformlyOn_iteratedDerivWithin_cexp n
  · exact fun n l z hl hz ↦ differentiableAt_iteratedDerivWithin_cexp n l
      isOpen_upperHalfPlaneSet hz

lemma contDiffOn_tsum_cexp (k : ℕ∞) :
    ContDiffOn ℂ k (fun z : ℂ ↦ ∑' n : ℕ, cexp (2 * π * I * z) ^ n) ℍₒ :=
  contDiffOn_of_differentiableOn_deriv fun m _ z hz ↦
  (((summableLocallyUniformlyOn_iteratedDerivWithin_cexp m).differentiableOn
  isOpen_upperHalfPlaneSet (fun n _ hz ↦ differentiableAt_iteratedDerivWithin_cexp n m
  isOpen_upperHalfPlaneSet hz)) z hz).congr (fun z hz ↦ iteratedDerivWithin_tsum_cexp_eq m ⟨z, hz⟩)
  (iteratedDerivWithin_tsum_cexp_eq m ⟨z, hz⟩)

private lemma iteratedDerivWithin_tsum_exp_aux_eq {k : ℕ} (hk : 1 ≤ k) (z : ℍ) :
    iteratedDerivWithin k (fun z ↦ ((π * I) -
    (2 * π * I) * ∑' n : ℕ, cexp (2 * π * I * z) ^ n)) ℍₒ z =
    -(2 * π * I) ^ (k + 1) * ∑' n : ℕ, n ^ k * cexp (2 * π * I * z) ^ n := by
  have : iteratedDerivWithin k (fun z ↦ ((π * I) -
    (2 * π * I) * ∑' n : ℕ, cexp (2 * π * I * z) ^ n)) ℍₒ z =
    -(2 * π * I) * ∑' n : ℕ, iteratedDerivWithin k (fun s : ℂ ↦ cexp (2 * π * I * s) ^ n) ℍₒ z := by
    rw [iteratedDerivWithin_const_sub hk, iteratedDerivWithin_fun_neg,
      iteratedDerivWithin_const_mul (by simpa using z.2) (isOpen_upperHalfPlaneSet.uniqueDiffOn)]
    · simp only [iteratedDerivWithin_tsum_cexp_eq, neg_mul]
    · exact (contDiffOn_tsum_cexp k).contDiffWithinAt (by simpa using z.2)
  have h : -(2 * π * I * (2 * π * I) ^ k) * ∑' (n : ℕ), n ^ k * cexp (2 * π * I * z) ^ n =
        -(2 * π * I) * ∑' n : ℕ, (2 * π * I * n) ^ k * cexp (2 * π * I * z) ^ n := by
    simp_rw [← tsum_mul_left]
    congr
    ext y
    ring
  simp only [this, neg_mul, pow_succ', h, neg_inj, mul_eq_mul_left_iff, mul_eq_zero,
    OfNat.ofNat_ne_zero, ofReal_eq_zero, Real.pi_ne_zero, or_self, I_ne_zero, or_false]
  congr
  ext n
  have := exp_nsmul' (p := 1) (a := 2 * π * I) (n := n)
  simp_rw [div_one] at this
  simpa [this, UpperHalfPlane.coe] using
    iteratedDerivWithin_cexp_aux k n 1 isOpen_upperHalfPlaneSet z.2

/-- This is one key identity relating infinite series to q-expansions which shows that
`∑' n, 1 / (z + n) ^ (k + 1) = ((-2 π I) ^ (k + 1) / k !) * ∑' n, n ^ k q ^n` where
`q = cexp (2 π I z)`. -/
theorem EisensteinSeries.qExpansion_identity {k : ℕ} (hk : 1 ≤ k) (z : ℍ) :
    ∑' n : ℤ, 1 / ((z : ℂ) + n) ^ (k + 1) = ((-2 * π * I) ^ (k + 1) / k !) *
    ∑' n : ℕ, n ^ k * cexp (2 * π * I * z) ^ n := by
  have : (-1) ^ k * k ! * ∑' n : ℤ, 1 / ((z : ℂ) + n) ^ (k + 1) =
    -(2 * π * I) ^ (k + 1) * ∑' n : ℕ, n ^ k * cexp (2 * π * I * z) ^ n := by
    rw [← iteratedDerivWithin_tsum_exp_aux_eq hk z,
      ← iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow hk (by simpa using z.2)]
    exact iteratedDerivWithin_congr (fun x hx ↦ by (simpa using pi_mul_cot_pi_q_exp ⟨x, hx⟩))
      (by simpa using z.2)
  simp_rw [(eq_inv_mul_iff_mul_eq₀ (by simp [Nat.factorial_ne_zero])).mpr this, ← tsum_mul_left]
  congr
  ext n
  rw [show (-2 * π * I) ^ (k + 1) = (-1) ^ (k + 1) * (2 * π * I) ^ (k + 1) by rw [← neg_pow]; ring]
  field_simp
  ring_nf
  simp [Nat.mul_two]

lemma summable_pow_mul_cexp (k : ℕ) (e : ℕ+) (z : ℍ) :
    Summable fun c : ℕ ↦ (c : ℂ) ^ k * cexp (2 * π * I * e * z) ^ c := by
  have he : 0 < (e * (z : ℂ)).im := by
    simpa using z.2
  apply ((summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp 0 k (p := 1)
    (f := fun n ↦ (n ^ k : ℂ)) (by norm_num)
    (by simp [← Complex.isBigO_ofReal_right, Asymptotics.isBigO_refl])).summable he).congr
  grind [ofReal_one, iteratedDerivWithin_zero, Pi.smul_apply, smul_eq_mul]

/-- This is a version of `EisensteinSeries.qExpansion_identity` for positive naturals,
which shows that  `∑' n, 1 / (z + n) ^ (k + 1) = ((-2 π I) ^ (k + 1) / k !) * ∑' n : ℕ+, n ^ k q ^n`
where `q = cexp (2 π I z)`. -/
theorem EisensteinSeries.qExpansion_identity_pnat {k : ℕ} (hk : 1 ≤ k) (z : ℍ) :
    ∑' n : ℤ, 1 / ((z : ℂ) + n) ^ (k + 1) = ((-2 * π * I) ^ (k + 1) / k !) *
    ∑' n : ℕ+, n ^ k * cexp (2 * π * I * z) ^ (n : ℕ) := by
  rw [EisensteinSeries.qExpansion_identity hk z, ← tsum_zero_pnat_eq_tsum_nat]
  · simp [show k ≠ 0 by grind]
  · apply (summable_pow_mul_cexp k 1 z).congr
    simp

lemma summable_prod_eisSummand {k : ℕ} (hk : 3 ≤ k) (z : ℍ) :
    Summable fun x : ℤ × ℤ ↦ eisSummand k ![x.1, x.2] z := by
  rw [← summable_norm_iff, ← (piFinTwoEquiv fun _ ↦ ℤ).summable_iff, piFinTwoEquiv_apply]
  apply (summable_norm_eisSummand (by linarith) z).congr
  simp [eisSummand]

lemma tsum_eisSummand_eq_tsum_sigma_cexp {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (z : ℍ) :
    ∑' v, eisSummand k v z = 2 * riemannZeta k + 2 * ((-2 * π * I) ^ k / (k - 1)!) *
    ∑' (n : ℕ+), σ (k - 1) n * cexp (2 * π * I * z) ^ (n : ℕ) := by
  rw [← (piFinTwoEquiv fun _ ↦ ℤ).symm.tsum_eq, Summable.tsum_prod
    (by apply summable_prod_eisSummand hk z), tsum_int_eq_zero_add_two_mul_tsum_pnat]
  · have (b : ℕ+) := qExpansion_identity_pnat (k := k - 1) (by grind)
      ⟨b * z , by simpa using z.2⟩
    simp only [coe_mk_subtype, show k - 1 + 1 = k by grind, one_div, neg_mul, mul_assoc, eisSummand,
      Fin.isValue, piFinTwoEquiv_symm_apply, Fin.cons_zero, Int.cast_zero, zero_mul, Fin.cons_one,
      zero_add, zpow_neg, zpow_natCast, Int.cast_natCast, nsmul_eq_mul, Nat.cast_ofNat,
      two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (by grind) hk2, add_right_inj,
      mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false] at *
    conv =>
      enter [1, 1, c]
      rw [this c]
    simp_rw [tsum_mul_left, ← mul_assoc, ← tsum_prod_pow_eq_tsum_sigma (k - 1)
      (norm_exp_two_pi_I_lt_one z), ← tsum_mul_left, ← exp_nsmul]
    exact tsum_congr₂ (fun c d ↦ by ring_nf)
  · intro n
    nth_rw 1 [(tsum_comp_neg _).symm]
    congr
    ext y
    simp only [eisSummand, Fin.isValue, piFinTwoEquiv_symm_apply, Fin.cons_zero, Int.cast_neg,
      neg_mul, Fin.cons_one, zpow_neg, zpow_natCast, ← Even.neg_pow hk2 (n * (z : ℂ) + y),
      neg_add_rev, inv_inj]
    ring
  · simpa using (summable_prod_eisSummand hk z).prod

lemma eisSummand_of_gammaSet_eq_divIntMap (k : ℤ) (z : ℍ) {n : ℕ} (v : gammaSet 1 n 0) :
    eisSummand k v z = ((n : ℂ) ^ k)⁻¹ * eisSummand k (divIntMap n v) z := by
  simp_rw [eisSummand]
  nth_rw 1 2 [gammaSet_eq_gcd_mul_divIntMap v.2]
  simp only [Fin.isValue, Pi.smul_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, zpow_neg,
    ← mul_inv, ← mul_zpow, inv_inj]
  ring_nf

lemma tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries {k : ℕ} (hk : 3 ≤ k) (z : ℍ) :
    ∑' (v : Fin 2 → ℤ), eisSummand k v z = (riemannZeta k) * (eisensteinSeries (N := 1) 0 k z) := by
  rw [← gammaSetDivGcdSigmaEquiv.symm.tsum_eq]
  have hk1 : 1 < k := by omega
  have hk2 : 3 ≤ (k : ℤ) := mod_cast hk
  conv =>
    enter [1, 1, c]
    rw [gammaSetDivGcdSigmaEquiv_symm_eq]
  rw [eisensteinSeries, Summable.tsum_sigma, zeta_nat_eq_tsum_of_gt_one hk1,
    tsum_mul_tsum_of_summable_norm (by simp [hk1])
    (by apply (summable_norm_eisSummand hk2 z).subtype)]
  · simp_rw [one_div]
    rw [Summable.tsum_prod']
    · apply tsum_congr
      intro b
      by_cases hb : b = 0
      · simp [hb, CharP.cast_eq_zero, eisSummand_of_gammaSet_eq_divIntMap k z,
          show ((0 : ℂ) ^ k)⁻¹ = 0 by aesop]
      · have : NeZero b := ⟨by simp [hb]⟩
        simpa [eisSummand_of_gammaSet_eq_divIntMap k z, zpow_natCast, tsum_mul_left, hb] using
          (gammaSetDivGcdEquiv b).tsum_eq (fun v ↦ eisSummand k v z)
    · apply summable_mul_of_summable_norm (f := fun (n : ℕ) ↦ ((n : ℂ) ^ k)⁻¹)
        (g := fun (v : gammaSet 1 1 0) ↦ eisSummand k v z) (by simp [hk1])
      apply (summable_norm_eisSummand hk2 z).subtype
    · exact fun b ↦ by simpa using (Summable.of_norm (by apply (summable_norm_eisSummand
        hk2 z).subtype)).mul_left (a := ((b : ℂ) ^ k)⁻¹)
  · apply ((gammaSetDivGcdSigmaEquiv.symm.summable_iff (f := fun v ↦ eisSummand k v z)).mpr
      (summable_norm_eisSummand hk2 z).of_norm).congr
    simp

/-- The q-Expansion of normalised Eisenstein series of level one with `riemannZeta` term. -/
lemma EisensteinSeries.q_expansion_riemannZeta {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (z : ℍ) :
    E hk z = 1 + (1 / riemannZeta k) * ((-2 * π * I) ^ k / (k - 1)!) *
    ∑' n : ℕ+, σ (k - 1) n * cexp (2 * π * I * z) ^ (n : ℤ) := by
  have : eisensteinSeries_MF (k := k) (by omega) 0 z = eisensteinSeries_SIF (N := 1) 0 k z := rfl
  rw [E, ModularForm.IsGLPos.smul_apply, this, eisensteinSeries_SIF_apply 0 k z, eisensteinSeries]
  have HE1 := tsum_eisSummand_eq_tsum_sigma_cexp (by omega) hk2 z
  have HE2 := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries (by omega) z
  have z2 : riemannZeta k ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_lt_re ?_
    grind [natCast_re, Nat.one_lt_cast]
  simp only [eisSummand, Fin.isValue, UpperHalfPlane.coe, zpow_neg, zpow_natCast, neg_mul,
    eisensteinSeries, ← inv_mul_eq_iff_eq_mul₀ z2, ne_eq, one_div, smul_eq_mul] at *
  simp_rw [← HE2, HE1, mul_add]
  grind

private lemma eisensteinSeries_coeff_identity {k : ℕ} (hk2 : Even k) (hkn0 : k ≠ 0) :
  (1 / (riemannZeta k)) * ((-2 * π * I) ^ k / (k - 1)!) = -(2 * k / bernoulli k) := by
  have hk0 : k / 2 ≠ 0 := by grind
  have hk1 : 2 * (k / 2) = k := Nat.two_mul_div_two_of_even hk2
  have hk11 : 2 * (((k / 2) : ℕ) : ℂ) = k := by norm_cast
  have hkf : ((k - 1)! : ℂ) ≠ 0 := by
    norm_cast
    apply Nat.factorial_ne_zero
  have h3 : (-2 * π * I) ^ k = (-1) ^ k * 2 ^ k * π ^ k * (-1) ^ (k / 2) := by
    simp_rw [mul_pow]
    nth_rw 3 [← hk1]
    rw [neg_pow, pow_mul, I_sq]
  have := riemannZeta_two_mul_nat hk0
  rw [hk1, hk11] at this
  rw [h3, this, (Nat.mul_factorial_pred hkn0).symm]
  field_simp
  have : ((k * (k - 1)! : ℕ) : ℂ) * 1 * 2 ^ k * (-1) ^ (k / 2) / (bernoulli k) =
    (k * (k - 1)! : ℂ) * 2 ^ k * (-1) ^ (k / 2) * (1 / bernoulli k) := by
    grind
  rw [Even.neg_one_pow hk2, this, show k = 1 + (k - 1) by omega]
  grind

/-- The q-Expansion of normalised Eisenstein series of level one with `bernoulli` term. -/
lemma EisensteinSeries.q_expansion_bernoulli {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (z : ℍ) :
    E hk z = 1 + -(2 * k / bernoulli k) *
    ∑' n : ℕ+, σ (k - 1) n * cexp (2 * π * I * z) ^ (n : ℤ) := by
  have h := q_expansion_riemannZeta hk hk2 z
  rw [eisensteinSeries_coeff_identity hk2 (by omega)] at h
  exact h
