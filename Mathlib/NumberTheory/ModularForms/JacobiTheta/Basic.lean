/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology

#align_import number_theory.modular_forms.jacobi_theta.basic from "leanprover-community/mathlib"@"57f9349f2fe19d2de7207e99b0341808d977cdcf"

/-! # Jacobi's theta function

This file defines the Jacobi theta function

$$\theta(\tau) = \sum_{n \in \mathbb{Z}} \exp (i \pi n ^ 2 \tau),$$

and proves the modular transformation properties `θ (τ + 2) = θ τ` and
`θ (-1 / τ) = (-I * τ) ^ (1 / 2) * θ τ`, using Poisson's summation formula for the latter. We also
show that `θ` is differentiable on `ℍ`, and `θ(τ) - 1` has exponential decay as `im τ → ∞`.
-/


open Complex Real Asymptotics Filter

open scoped Real BigOperators UpperHalfPlane

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

/-- Jacobi's theta function `∑' (n : ℤ), exp (π * I * n ^ 2 * τ)`. -/
noncomputable def jacobiTheta (z : ℂ) : ℂ :=
  ∑' n : ℤ, cexp (π * I * (n : ℂ) ^ 2 * z)
#align jacobi_theta jacobiTheta

theorem norm_exp_mul_sq_le {z : ℂ} (hz : 0 < z.im) (n : ℤ) :
    ‖cexp (π * I * (n : ℂ) ^ 2 * z)‖ ≤ rexp (-π * z.im) ^ n.natAbs := by
  let y := rexp (-π * z.im)
  have h : y < 1 := exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr pi_pos) hz)
  refine' (le_of_eq _).trans (_ : y ^ n ^ 2 ≤ _)
  · rw [Complex.norm_eq_abs, Complex.abs_exp]
    have : (↑π * I * (n : ℂ) ^ 2 * z).re = -π * z.im * (n : ℝ) ^ 2 := by
      rw [(by push_cast; ring : ↑π * I * (n : ℂ) ^ 2 * z = ↑(π * (n : ℝ) ^ 2) * (z * I)),
        ofReal_mul_re, mul_I_re]
      ring
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (sq_nonneg n)
    rw [this, exp_mul, ← Int.cast_pow, rpow_int_cast, hm, zpow_ofNat]
  · have : n ^ 2 = ↑(n.natAbs ^ 2) := by rw [Nat.cast_pow, Int.natAbs_sq]
    rw [this, zpow_ofNat]
    exact pow_le_pow_of_le_one (exp_pos _).le h.le ((sq n.natAbs).symm ▸ n.natAbs.le_mul_self)
#align norm_exp_mul_sq_le norm_exp_mul_sq_le

theorem exists_summable_bound_exp_mul_sq {R : ℝ} (hR : 0 < R) :
    ∃ bd : ℤ → ℝ, Summable bd ∧ ∀ {τ : ℂ} (_ : R ≤ τ.im) (n : ℤ),
      ‖cexp (π * I * (n : ℂ) ^ 2 * τ)‖ ≤ bd n := by
  let y := rexp (-π * R)
  have h : y < 1 := exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr pi_pos) hR)
  refine' ⟨fun n => y ^ n.natAbs, summable_int_of_summable_nat _ _, fun hτ n => _⟩; pick_goal 3
  · refine' (norm_exp_mul_sq_le (hR.trans_le hτ) n).trans _
    refine' pow_le_pow_of_le_left (exp_pos _).le (Real.exp_le_exp.mpr _) _
    rwa [mul_le_mul_left_of_neg (neg_lt_zero.mpr pi_pos)]
  all_goals
    simpa only [Int.natAbs_neg, Int.natAbs_ofNat] using
      summable_geometric_of_lt_1 (Real.exp_pos _).le h
#align exists_summable_bound_exp_mul_sq exists_summable_bound_exp_mul_sq

theorem summable_exp_mul_sq {z : ℂ} (hz : 0 < z.im) :
    Summable fun n : ℤ => cexp (π * I * (n : ℂ) ^ 2 * z) :=
  let ⟨_, h, h'⟩ := exists_summable_bound_exp_mul_sq hz
  .of_norm_bounded _ h (h' <| le_refl _)
#align summable_exp_mul_sq summable_exp_mul_sq

theorem jacobiTheta_two_add (z : ℂ) : jacobiTheta (2 + z) = jacobiTheta z := by
  refine' tsum_congr fun n => _
  suffices cexp (↑π * I * (n : ℂ) ^ 2 * 2) = 1 by rw [mul_add, Complex.exp_add, this, one_mul]
  rw [(by push_cast; ring : ↑π * I * ↑n ^ 2 * 2 = ↑(n ^ 2) * (2 * π * I)), Complex.exp_int_mul,
    Complex.exp_two_pi_mul_I, one_zpow]
#align jacobi_theta_two_add jacobiTheta_two_add

theorem jacobiTheta_T_sq_smul (τ : ℍ) : jacobiTheta ↑(ModularGroup.T ^ 2 • τ) = jacobiTheta τ := by
  suffices ↑(ModularGroup.T ^ 2 • τ) = (2 : ℂ) + ↑τ by simp_rw [this, jacobiTheta_two_add]
  have : ModularGroup.T ^ (2 : ℕ) = ModularGroup.T ^ (2 : ℤ) := rfl
  simp_rw [this, UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd]
  norm_cast
set_option linter.uppercaseLean3 false in
#align jacobi_theta_T_sq_smul jacobiTheta_T_sq_smul

theorem jacobiTheta_S_smul (τ : ℍ) :
    jacobiTheta ↑(ModularGroup.S • τ) = (-I * τ) ^ (1 / 2 : ℂ) * jacobiTheta τ := by
  unfold jacobiTheta
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk]
  have ha : 0 < (-I * τ).re := by
    rw [neg_mul, neg_re, mul_re, I_re, I_im, zero_mul, one_mul, zero_sub, neg_neg]
    exact τ.im_pos
  have ha' : (-I * τ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne.def, cpow_eq_zero_iff]
    contrapose! ha
    rw [ha.1, zero_re]
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have := Complex.tsum_exp_neg_mul_int_sq ha
  rw [mul_comm ((1 : ℂ) / _) _, mul_one_div, eq_div_iff ha', mul_comm _ (_ ^ _), eq_comm] at this
  have expo1 : ∀ n : ℤ, -↑π / (-I * ↑τ) * (n : ℂ) ^ 2 = ↑π * I * (n : ℂ) ^ 2 * (-↑τ)⁻¹ := by
    intro n
    field_simp [hτ, I_ne_zero]
    ring_nf
    rw [I_sq, mul_neg, mul_one, neg_neg]
  simp_rw [expo1] at this
  have expo2 : ∀ n : ℤ, -↑π * (-I * ↑τ) * (n : ℂ) ^ 2 = ↑π * I * (n : ℂ) ^ 2 * ↑τ := by
    intro n
    ring_nf
  simp_rw [expo2] at this
  exact this
set_option linter.uppercaseLean3 false in
#align jacobi_theta_S_smul jacobiTheta_S_smul

theorem hasSum_nat_jacobiTheta {z : ℂ} (hz : 0 < im z) :
    HasSum (fun n : ℕ => cexp (π * I * ((n : ℂ) + 1) ^ 2 * z)) ((jacobiTheta z - 1) / 2) := by
  have := (summable_exp_mul_sq hz).hasSum.sum_nat_of_sum_int
  rw [← @hasSum_nat_add_iff' ℂ _ _ _ _ 1] at this
  simp_rw [Finset.sum_range_one, Int.cast_neg, Int.cast_ofNat, Nat.cast_zero, neg_zero,
    Int.cast_zero, sq (0 : ℂ), mul_zero, zero_mul, neg_sq, ← mul_two,
    Complex.exp_zero, add_sub_assoc, (by norm_num : (1 : ℂ) - 1 * 2 = -1), ← sub_eq_add_neg,
    Nat.cast_add, Nat.cast_one] at this
  convert this.div_const 2 using 1
  simp_rw [mul_div_cancel (G₀ := ℂ) _ two_ne_zero]
#align has_sum_nat_jacobi_theta hasSum_nat_jacobiTheta

theorem jacobiTheta_eq_tsum_nat {z : ℂ} (hz : 0 < im z) :
    jacobiTheta z = ↑1 + ↑2 * ∑' n : ℕ, cexp (π * I * ((n : ℂ) + 1) ^ 2 * z) := by
  rw [(hasSum_nat_jacobiTheta hz).tsum_eq, mul_div_cancel' _ (two_ne_zero' ℂ), ← add_sub_assoc,
    add_sub_cancel']
#align jacobi_theta_eq_tsum_nat jacobiTheta_eq_tsum_nat

/-- An explicit upper bound for `‖jacobiTheta τ - 1‖`. -/
theorem norm_jacobiTheta_sub_one_le {z : ℂ} (hz : 0 < im z) :
    ‖jacobiTheta z - 1‖ ≤ 2 / (1 - rexp (-π * z.im)) * rexp (-π * z.im) := by
  suffices ‖∑' n : ℕ, cexp (π * I * ((n : ℂ) + 1) ^ 2 * z)‖ ≤
      rexp (-π * z.im) / (1 - rexp (-π * z.im)) by
    calc
      ‖jacobiTheta z - 1‖ = ↑2 * ‖∑' n : ℕ, cexp (π * I * ((n : ℂ) + 1) ^ 2 * z)‖ := by
        rw [sub_eq_iff_eq_add'.mpr (jacobiTheta_eq_tsum_nat hz), norm_mul, Complex.norm_eq_abs,
          Complex.abs_two]
      _ ≤ 2 * (rexp (-π * z.im) / (1 - rexp (-π * z.im))) := by
        rwa [mul_le_mul_left (zero_lt_two' ℝ)]
      _ = 2 / (1 - rexp (-π * z.im)) * rexp (-π * z.im) := by rw [div_mul_comm, mul_comm]
  have : ∀ n : ℕ, ‖cexp (π * I * ((n : ℂ) + 1) ^ 2 * z)‖ ≤ rexp (-π * z.im) ^ (n + 1) := by
    intro n
    simpa only [Int.cast_add, Int.cast_one] using norm_exp_mul_sq_le hz (n + 1)
  have s : HasSum (fun n : ℕ =>
      rexp (-π * z.im) ^ (n + 1)) (rexp (-π * z.im) / (1 - rexp (-π * z.im))) := by
    simp_rw [pow_succ, div_eq_mul_inv, hasSum_mul_left_iff (Real.exp_ne_zero _)]
    exact hasSum_geometric_of_lt_1 (exp_pos (-π * z.im)).le
      (exp_lt_one_iff.mpr <| mul_neg_of_neg_of_pos (neg_lt_zero.mpr pi_pos) hz)
  have aux : Summable fun n : ℕ => ‖cexp (π * I * ((n : ℂ) + 1) ^ 2 * z)‖ :=
    .of_nonneg_of_le (fun n => norm_nonneg _) this s.summable
  exact (norm_tsum_le_tsum_norm aux).trans ((tsum_mono aux s.summable this).trans_eq s.tsum_eq)
#align norm_jacobi_theta_sub_one_le norm_jacobiTheta_sub_one_le

/-- The norm of `jacobiTheta τ - 1` decays exponentially as `im τ → ∞`. -/
theorem isBigO_at_im_infty_jacobiTheta_sub_one :
    (fun τ => jacobiTheta τ - 1) =O[comap im atTop] fun τ => rexp (-π * τ.im) := by
  simp_rw [IsBigO, IsBigOWith, Filter.eventually_comap, Filter.eventually_atTop]
  refine' ⟨2 / (1 - rexp (-π)), 1, fun y hy z hz =>
    (norm_jacobiTheta_sub_one_le (hz.symm ▸ zero_lt_one.trans_le hy : 0 < im z)).trans _⟩
  rw [Real.norm_eq_abs, Real.abs_exp]
  refine' mul_le_mul_of_nonneg_right _ (exp_pos _).le
  rw [div_le_div_left (zero_lt_two' ℝ), sub_le_sub_iff_left, exp_le_exp, neg_mul, neg_le_neg_iff]
  · exact le_mul_of_one_le_right pi_pos.le (hz.symm ▸ hy)
  · rw [sub_pos, exp_lt_one_iff, neg_mul, neg_lt_zero]
    exact mul_pos pi_pos (hz.symm ▸ zero_lt_one.trans_le hy)
  · rw [sub_pos, exp_lt_one_iff, neg_lt_zero]; exact pi_pos
set_option linter.uppercaseLean3 false in
#align is_O_at_im_infty_jacobi_theta_sub_one isBigO_at_im_infty_jacobiTheta_sub_one

theorem differentiableAt_jacobiTheta {z : ℂ} (hz : 0 < im z) :
    DifferentiableAt ℂ jacobiTheta z := by
  suffices ∀ (y : ℝ) (_ : 0 < y),
      DifferentiableOn ℂ (fun z => ∑' n : ℤ, cexp (π * I * (n : ℂ) ^ 2 * z)) {w : ℂ | y < im w} by
    let ⟨y, hy, hy'⟩ := exists_between hz
    exact (this y hy).differentiableAt
      ((Complex.continuous_im.isOpen_preimage _ isOpen_Ioi).mem_nhds hy')
  intro y hy
  have h1 : ∀ (n : ℤ) (w : ℂ) (_ : y < im w),
      DifferentiableWithinAt ℂ (fun v : ℂ => cexp (π * I * (n : ℂ) ^ 2 * v)) {z : ℂ | y < im z} w :=
    fun n w _ => (differentiableAt_id.const_mul _).cexp.differentiableWithinAt
  have h2 : IsOpen {w : ℂ | y < im w} := continuous_im.isOpen_preimage _ isOpen_Ioi
  obtain ⟨bd, bd_s, le_bd⟩ := exists_summable_bound_exp_mul_sq hy
  exact differentiableOn_tsum_of_summable_norm bd_s h1 h2 fun i w hw => le_bd (le_of_lt hw) i
#align differentiable_at_jacobi_theta differentiableAt_jacobiTheta

theorem continuousAt_jacobiTheta {z : ℂ} (hz : 0 < im z) : ContinuousAt jacobiTheta z :=
  (differentiableAt_jacobiTheta hz).continuousAt
#align continuous_at_jacobi_theta continuousAt_jacobiTheta
