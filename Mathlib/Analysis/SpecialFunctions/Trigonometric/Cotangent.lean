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
import Mathlib.Topology.Algebra.InfiniteSum.MultipliableTendstoUniformly

/-!
# Cotangent

This file contains lemmas about the cotangent function, including useful series expansions.
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
    (UpperHalfPlane.abs_exp_two_pi_I_lt_one z)).symm, add_comm, geom_series_mul_one_add
      (Complex.exp (2 * π * I * (z : ℂ))) (UpperHalfPlane.abs_exp_two_pi_I_lt_one _)]
  ring

section MittagLeffler

lemma int_comp_not_zero2 (x : ℂ_ℤ) (n : ℕ) : 1 + -x.1 ^ 2 / (n + 1) ^ 2 ≠ 0 := by
  intro h
  rw [add_eq_zero_iff_eq_neg, neg_div', eq_div_iff] at h
  simp only [one_mul, neg_neg, sq_eq_sq_iff_eq_or_eq_neg] at h
  rcases h with h1| h2
  · have := not_exists.mp x.2 (n + 1)
    aesop
  · have := not_exists.mp x.2 (-(n + 1))
    rw [← neg_eq_iff_eq_neg ] at h2
    rw [← h2] at this
    simp only [neg_add_rev, Int.reduceNeg, Int.cast_add, Int.cast_neg, Int.cast_one,
      Int.cast_natCast, not_true_eq_false] at *
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
    exact Nat.cast_add_one_ne_zero n

theorem tendsto_euler_sin_prod' (x : ℂ) (h0 : x ≠ 0) :
    Tendsto (fun n : ℕ => ∏ i : ℕ in Finset.range n, (1 + -x ^ 2 / (↑i + 1) ^ 2)) atTop
      (𝓝 (sin (π * x) / (π * x))) := by
  rw [show (sin (π * x) / (π * x)) = sin (↑π * x) * (1 / (↑π * x)) by ring]
  apply (Filter.Tendsto.mul_const (b := 1 / (π * x)) (tendsto_euler_sin_prod x)).congr
  intro n
  have : (1 / (π * x)) * (π * x) = 1 := by
    apply div_mul_cancel₀
    have := Real.pi_ne_zero
    aesop
  rw [mul_comm, ← mul_assoc, this, one_mul]
  congr
  ext y
  ring

lemma euler_sin_tprod (x : ℂ_ℤ) :
    ∏' i : ℕ, (1 + -x.1 ^ 2 / (i + 1) ^ 2) = Complex.sin (π * x.1) / (π * x.1) := by
  rw [← Multipliable.hasProd_iff, Multipliable.hasProd_iff_tendsto_nat]
  apply tendsto_euler_sin_prod' x.1 (ℂ_ℤ_not_zero x)
  repeat {
  apply Complex.summable_multipliable_one_add
  · rw [← summable_norm_iff]
    simpa using summable_pow_div_add x.1 2 2 1
  · apply int_comp_not_zero2 x}

theorem aux_diff_lem (n : ℕ) :
    DifferentiableOn ℂ (fun z : ℂ => ∏ j in Finset.range n, (1 + -z ^ 2 / (j + 1) ^ 2))
      {z : ℂ | ¬ ∃ (n : ℤ), z = n} := by
  apply DifferentiableOn.finset_prod
  refine fun i _ =>
    DifferentiableOn.add (differentiableOn_const 1)
      (DifferentiableOn.div_const
        (DifferentiableOn.neg
          (DifferentiableOn.pow (Differentiable.differentiableOn differentiable_id) 2))
            (((i : ℂ) + 1) ^ 2))

lemma aux_u_lem (Z : Set ℂ_ℤ) (hZ : IsCompact Z) : ∃ u : ℕ → ℝ, Summable u ∧
    ∀ (j : ℕ) z, z ∈ Z → (‖-z.1 ^ 2 / (j + 1) ^ 2‖) ≤ u j := by
  have hf : ContinuousOn (fun x : ℂ_ℤ => Complex.abs (-x.1 ^ 2)) Z := by
    apply ContinuousOn.comp
    let g := fun x : ℂ_ℤ => -x.1 ^ 2
    apply Continuous.continuousOn Complex.continuous_abs (s := ((g '' Z)))
    apply (ContinuousOn.neg (ContinuousOn.pow (Continuous.continuousOn continuous_subtype_val) 2))
    exact Set.mapsTo_image (fun x ↦ -x.1 ^ 2) Z
  have := IsCompact.bddAbove_image hZ hf
  simp only [map_neg_eq_map, map_pow, bddAbove_def, Set.mem_image, Subtype.exists, not_exists,
    exists_and_right, forall_exists_index, and_imp] at this
  obtain ⟨s, hs⟩ := this
  use (fun n : ℕ => Complex.abs (s / (n + 1) ^ 2))
  constructor
  · simpa using summable_pow_div_add (s : ℂ) 1 2 1 (by omega)
  · intro n x hx
    simp only [norm_div, norm_neg, norm_pow, Complex.norm_eq_abs, map_div₀, abs_ofReal, map_pow]
    gcongr
    apply le_trans (hs _ _ (by aesop) (rfl)) (le_abs_self s)

theorem tendstoUniformlyOn_compact_euler_sin_prod (Z : Set ℂ_ℤ) (hZ : IsCompact Z) :
    TendstoUniformlyOn
      (fun n : ℕ => fun z : ℂ_ℤ => ∏ j in Finset.range n, (1 + -z.1 ^ 2 / (j + 1) ^ 2))
        (fun x => (Complex.sin (↑π * x) / (↑π * x))) atTop Z := by
  simp_rw [← euler_sin_tprod]
  obtain ⟨u, hu, hu2⟩ := aux_u_lem Z hZ
  apply prod_tendstoUniformlyOn_tprod' Z hZ u hu hu2
  · refine fun x n => by apply int_comp_not_zero2 x
  · intro n
    apply ContinuousOn.div_const
    apply (ContinuousOn.neg (ContinuousOn.pow (Continuous.continuousOn continuous_subtype_val) 2))

open Finset

theorem sin_pi_z_ne_zero (z : ℂ_ℤ) : Complex.sin (π * z) ≠ 0 := by
  apply Complex.sin_ne_zero_iff.2
  intro k
  rw [mul_comm]
  by_contra h
  simp only [mul_eq_mul_right_iff, ofReal_eq_zero] at h
  cases' h with h h
  · have := z.2
    aesop
  · exact Real.pi_ne_zero h

theorem tendsto_logDeriv_euler_sin_div (x : ℂ_ℤ) :
    Tendsto (fun n : ℕ =>
      logDeriv (fun z => ∏ j in Finset.range n, (1 + -(z : ℂ) ^ 2 / (j + 1) ^ 2)) x)
        atTop (𝓝 <| logDeriv (fun t => (Complex.sin (π * t) / (π * t))) x) := by
  apply logDeriv_tendsto
      (fun n : ℕ => fun z => ∏ j in Finset.range n, (1 + -z ^ 2 / (j + 1) ^ 2))
        _ ℂ_ℤ_IsOpen x
  · rw [tendstoLocallyUniformlyOn_iff_forall_isCompact ℂ_ℤ_IsOpen]
    · intro K hK hK2
      have hZ := IsCompact.image (isCompact_iff_isCompact_univ.mp hK2) (continuous_inclusion hK)
      have := tendstoUniformlyOn_compact_euler_sin_prod ((Set.inclusion hK)'' ⊤) hZ
      rw [Metric.tendstoUniformlyOn_iff] at *
      simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.image_univ, Set.range_inclusion, gt_iff_lt,
        Set.top_eq_univ, Subtype.forall, not_exists, eventually_atTop, ge_iff_le] at *
      intro ε hε
      obtain ⟨N, hN⟩ := this ε hε
      refine ⟨N, fun n hn y hy => hN n hn ⟨y, (by simpa using hK hy)⟩ (by aesop)⟩
  · simp only [not_exists, eventually_atTop, ge_iff_le]
    refine ⟨1, fun b _ => by simpa using (aux_diff_lem b)⟩
  · simp only [Set.mem_setOf_eq, ne_eq, div_eq_zero_iff, mul_eq_zero, ofReal_eq_zero, not_or]
    refine ⟨sin_pi_z_ne_zero x , Real.pi_ne_zero , ℂ_ℤ_not_zero x⟩

theorem logDeriv_sin_div (z : ℂ_ℤ) :
    logDeriv (fun t => (Complex.sin (π * t) / (π * t))) z = π * cot (π * z) - 1 / z := by
  have : (fun t => (Complex.sin (π * t)/ (π * t))) = fun z =>
    (Complex.sin ∘ fun t => π * t) z / (π * z) := by
    ext1
    simp only [Pi.div_apply, Function.comp_apply]
  rw [this, logDeriv_div _ (by apply sin_pi_z_ne_zero) ?_
    (DifferentiableAt.comp _ (Complex.differentiableAt_sin) (by fun_prop)) (by fun_prop),
    logDeriv_comp (Complex.differentiableAt_sin) (by fun_prop), Complex.logDeriv_sin,
    deriv_const_mul _ (by fun_prop), deriv_id'', logDeriv_const_mul, logDeriv_id']
  field_simp [mul_comm]
  · simpa only [ne_eq, ofReal_eq_zero] using Real.pi_ne_zero
  · simp only [Set.mem_setOf_eq, ne_eq, mul_eq_zero, ofReal_eq_zero, not_or]
    refine ⟨Real.pi_ne_zero, ℂ_ℤ_not_zero _⟩

theorem aux_logDeriv_factor_eq (x : ℂ_ℤ) (i : ℕ) :
    logDeriv (fun (z : ℂ) ↦ 1 + -z ^ 2 / (i + 1) ^ 2) x.1 =
        1 / (x.1 - (i + 1)) + 1 / (x.1 + (i + 1)) := by
  simp only [Set.mem_setOf_eq, logDeriv_apply, differentiableAt_const, deriv_const_add',
    deriv_div_const, deriv.neg', differentiableAt_id', deriv_pow'', Nat.cast_ofNat,
    Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, one_div]
  simp_rw [div_eq_mul_inv]
  set i1 := ((x : ℂ) + (i+1))⁻¹
  set i2 := ((x : ℂ) - (i+1))⁻¹
  set i3 := ((i + 1 : ℂ)^2)⁻¹
  set i4 := (1 + -x^2 * i3)⁻¹
  have h1 : ((x : ℂ) + (i + 1)) * i1 = 1 := by
    refine Complex.mul_inv_cancel ?h
    simpa using ℂ_ℤ_add_ne_zero x (i + 1)
  have h2 : ((x : ℂ) - (i + 1)) * i2 = 1 := by
    apply Complex.mul_inv_cancel
    rw [sub_eq_add_neg]
    simpa using ℂ_ℤ_add_ne_zero x (-(i + 1))
  have h3 : ((i + 1 : ℂ)^2) * i3 = 1 := by
    apply Complex.mul_inv_cancel
    norm_cast
    exact Nat.add_one_ne_zero ((((i + 1).pow 1).mul i).add (((i + 1).pow 0).mul i))
  have h4 : (1 + -x^2 * i3) * i4 = 1 := by
    apply Complex.mul_inv_cancel (int_comp_not_zero2 x i)
  linear_combination
    (2 * i4 * i2 * i1 * ↑i + 2 * i4 * i2 * i1 + 2 * i4 * i1) * h3 +
          (2 * i2 * i1 * ↑i + 2 * i2 * i1 + 2 * i1) * h4 +
        (2 * i3 * i4 * ↑i + 2 * i3 * i4 - 1 * i1) * h2 +
      (2 * ↑x * i3 * i4 * i2 * ↑i - 2 * i3 * i4 * i2 * ↑i ^ 2 + 2 * ↑x * i3 * i4 * i2 -
                    4 * i3 * i4 * i2 * ↑i +
                  2 * ↑x * i3 * i4 -
                2 * i3 * i4 * i2 -
              2 * i3 * i4 * ↑i -
            2 * i3 * i4 +
          i2) *
        h1

lemma logDeriv_of_prod (x : ℂ_ℤ) (n : ℕ) :
    logDeriv (fun (z : ℂ) => ∏ j in Finset.range n, (1 + -z ^ 2 / (j + 1) ^ 2)) x =
     ∑ j in Finset.range n, (1 / ((x : ℂ) - (j + 1)) + 1 / (x + (j + 1))) := by
    rw [logDeriv_prod]
    congr
    ext i
    apply aux_logDeriv_factor_eq x i
    · exact fun i _ ↦ int_comp_not_zero2 x i
    · intro i _
      simp only [Set.mem_setOf_eq, differentiableAt_const, differentiableAt_const_add_iff,
        differentiableAt_neg_iff, differentiableAt_id', DifferentiableAt.pow,
        DifferentiableAt.div_const]

theorem tendsto_logDeriv_euler_cot_sub (x : ℂ_ℤ) :
    Tendsto (fun n : ℕ => ∑ j in Finset.range n, (1 / ((x : ℂ) - (j + 1)) + 1 / (x + (j + 1))))
      atTop (𝓝 <| π * cot (π * x)- 1 / x) := by
  simp_rw [← logDeriv_sin_div x, ← logDeriv_of_prod x]
  simpa using tendsto_logDeriv_euler_sin_div x

lemma half_le (a : ℝ) (ha : a < 1/2) : 1 / 2 ≤ |a - 1| := by
  rw [← neg_lt_neg_iff] at ha
  have hb := (Real.add_lt_add_iff_left 1).mpr ha
  rw [abs_sub_comm]
  have : (1 : ℝ) + -(1/2) = 1/2 := by
    ring
  rw [this, Mathlib.Tactic.RingNF.add_neg] at hb
  have : |1 - a| = 1 - a := by
    rw [abs_eq_self]
    linarith
  rw [this]
  apply hb.le

theorem lhs_summable (z : ℂ_ℤ) :
    Summable fun n : ℕ => 1 / ((z : ℂ) - (n + 1)) + 1 / (z + (n + 1)) := by
  have h : (fun (n : ℕ) => 1 / ((z : ℂ) - (n + 1)) + 1 / (z + (n + 1))) =
    fun (n : ℕ) => 2 * z.1 * (1 / (z ^ 2 - (n + 1) ^ 2)):= by
      ext1 n
      rw [one_div_add_one_div]
      ring
      · simpa [sub_eq_add_neg] using ℂ_ℤ_add_ne_zero z (-(n + 1) : ℤ)
      · simpa using (ℂ_ℤ_add_ne_zero z ((n : ℤ) + 1))
  rw [h]
  apply Summable.mul_left
  apply summable_norm_iff.mp
  have := (tendsto_const_div_pow (‖z.1^2‖) 2 (by omega))
  simp only [Metric.tendsto_atTop, gt_iff_lt, ge_iff_le, dist_zero_right, norm_div, norm_pow,
    Real.norm_eq_abs, _root_.sq_abs, RCLike.norm_natCast] at this
  obtain ⟨B, hB⟩ := this (1/2) (one_half_pos)
  have hB2 : ∀ (n : ℕ), B ≤ n → 1/2 ≤ |‖z.1‖^2 / n^2 -1| := fun n hn => half_le _ (hB n hn)
  apply Summable.comp_nat_add (k := B)
  have hs : Summable fun n : ℕ => (1 / (2 : ℝ) * (n + B + 1) ^ 2)⁻¹ := by
    simp_rw [mul_inv, inv_eq_one_div, add_assoc]
    apply Summable.mul_left
    have := summable_nat_add_iff (f := fun x => 1 / ((x^2) : ℝ)) (B + 1)
    simpa using this
  apply Summable.of_nonneg_of_le (by simp) _ hs
  simp only [ one_div, norm_inv]
  intro b
  have HT := abs_norm_sub_norm_le ((z.1 / (b + B + 1))^2) 1
  have H2 : 2⁻¹ ≤ ‖(z.1/(b + B + 1))^2 - 1‖ := by
    apply le_trans _ HT
    simp only [Complex.norm_eq_abs, one_div, mul_inv_rev, inv_inv, div_pow, norm_div, norm_pow,
      norm_one] at *
    convert (hB2 (b + B + 1) (by omega))
    norm_cast
    exact abs_natCast (b + B + 1)
  have : z.1^2 - (((b + B) : ℕ) + 1)^2 = ((z.1 / ((b + B) + 1))^2 - 1) * ((b + B) + 1)^2 := by
      have H3 : ((b : ℂ) + (B : ℂ) + 1)^2 ≠ 0 := by
        norm_cast
        norm_num
      field_simp [H3]
  rw [inv_le_inv, this, norm_mul]
  · gcongr
    · norm_cast
  · rw [this, norm_mul]
    apply mul_pos (by linarith)
    simp only [norm_pow, Complex.norm_eq_abs]
    apply pow_pos
    rw [AbsoluteValue.pos_iff Complex.abs]
    norm_cast
  · simp only [inv_pos, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
    apply pow_pos
    norm_cast
    exact Nat.zero_lt_succ (b + B)

theorem cot_series_rep' (z : ℂ_ℤ) : π * Complex.cot (π * z) - 1 / z =
    ∑' n : ℕ, (1 / ((z : ℂ) - (n + 1)) + 1 / (z + (n + 1))) := by
  rw [HasSum.tsum_eq]
  apply (Summable.hasSum_iff_tendsto_nat (lhs_summable z)).mpr
    (tendsto_logDeriv_euler_cot_sub z)

theorem cot_series_rep (z : ℂ_ℤ) :
    π * Complex.cot (π * z) = 1 / z + ∑' n : ℕ+, (1 / ((z : ℂ) - n) + 1 / (z + n)) := by
  have := tsum_pnat_eq_tsum_add_one fun n => 1 / ((z : ℂ) - n) + 1 / (z + n)
  have h1 := cot_series_rep' z
  simp only [one_div, Nat.cast_add, Nat.cast_one] at *
  rw [this, ← h1]
  ring

end MittagLeffler
