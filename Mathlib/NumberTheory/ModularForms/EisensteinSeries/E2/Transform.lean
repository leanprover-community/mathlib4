/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

/-!
# Slash action on E2

We show how the Eisenstein series `E2` transforms under the slash action of `SL(2, ℤ)`.
In particular, we show that it is invariant under the action of `T = [[1, 1], [0, 1]] ` and we
compute how it  transforms under the action of `S = [[0, -1], [1, 0]]` in term of a correction term
`D2`.

-/

open UpperHalfPlane hiding I

open ModularForm EisensteinSeries  TopologicalSpace ModularGroup Filter Complex MatrixGroups Finset
  Set SummationFilter

open scoped Real Topology

noncomputable section

/-- This is an auxiliary correction term for proving how E2 transforms. It allows us to work with
nicer indexing sets for our infinite sums. -/
private def δ (x : Fin 2 → ℤ) : ℂ := if x = ![0,0] then 1 else if x = ![0, -1] then 2 else 0

@[simp]
private lemma δ_eq : δ ![0,0] = 1 := by simp [δ]

@[simp]
private lemma δ_eq_two : δ ![0, -1] = 2 := by simp [δ]

namespace EisensteinSeries

/-- This gives term gives and alternative infinte sum for G2 which is absolutely convergent. -/
abbrev G2Term (z : ℍ) (m : Fin 2 → ℤ) : ℂ := (((m 0 : ℂ) * z + m 1) ^ 2 * (m 0 * z + m 1 + 1))⁻¹

/-- The map that swaps the two co-ordinates of a `Fin 2 → α` -/
def swap {α : Type*} : (Fin 2 → α) → (Fin 2 → α) := fun x ↦ ![x 1, x 0]

@[simp]
lemma swap_apply {α : Type*} (b : Fin 2 → α) : swap b = ![b 1, b 0] := rfl

lemma swap_involutive {α : Type*} (b : Fin 2 → α) : swap (swap b) = b := by
  ext i
  fin_cases i <;> rfl

/-- An equivalence between `Fin 2 → α` and itself given by swapping the two co-ordinates -/
def swap_equiv {α : Type*} : Equiv (Fin 2 → α) (Fin 2 → α) := Equiv.mk swap swap
  (by rw [Function.LeftInverse]; apply swap_involutive)
  (by rw [Function.RightInverse]; apply swap_involutive)

section AuxiliaryLemmas

private lemma aux_sum_Ico_S_indentity (z : ℍ) (N : ℕ) :
    ((z : ℂ) ^ 2)⁻¹ * (∑ x ∈ Ico (-N : ℤ) N, ∑' (n : ℤ), (((x : ℂ) * (-↑z)⁻¹ + n) ^ 2)⁻¹) =
    ∑' (n : ℤ), ∑ x ∈ Ico (-N : ℤ) N, (((n : ℂ) * z + x) ^ 2)⁻¹ := by
  simp_rw [inv_neg, mul_neg]
  rw [Finset.mul_sum, Summable.tsum_finsetSum
    (by apply fun i hi => linear_left_summable (ne_zero z) (i : ℤ) (k := 2) (by omega))]
  apply sum_congr rfl fun n hn ↦ ?_
  rw [← tsum_mul_left, ← tsum_comp_neg]
  apply tsum_congr fun d ↦ ?_
  field_simp [ne_zero z]
  grind

private lemma G2_S_act (z : ℍ) :
    Tendsto (fun N : ℕ ↦ (∑' (n : ℤ), ∑ m ∈ Ico (-N : ℤ) N, (1 / ((n : ℂ) * z + m) ^ 2))) atTop
    (𝓝 ((z.1 ^ 2)⁻¹ * G2 (S • z))) := by
  rw [G2_eq_tsum_IcoFilter, ← tsum_mul_left]
  have := ((Summable_IccFilter_G2_Ico (S • z)).mul_left (z.1 ^ 2)⁻¹).hasSum
  simp only [HasSum, IcoFilter, tendsto_map'_iff, modular_S_smul, ← Nat.map_cast_int_atTop] at *
  apply this.congr (fun N ↦ ?_)
  simpa [UpperHalfPlane.coe, e2Summand, eisSummand, UpperHalfPlane.mk, ← mul_sum]
    using (aux_sum_Ico_S_indentity z N)

private lemma telescope_aux (z : ℂ) (m : ℤ) (b : ℕ) :
    ∑ n ∈ Ico (-b : ℤ) b, (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1)) =
    1 / (m * z - b) - 1 / (m * z + b) := by
  induction b with
  | zero => aesop
  | succ b ihb =>
    simp only [Nat.cast_add, Nat.cast_one, one_div, Finset.sum_sub_distrib] at *
    rw [Ico_succ_succ, Finset.sum_union (by simp), Finset.sum_union (by simp),
      Finset.sum_pair (by grind), Finset.sum_pair (by grind), add_sub_add_comm]
    simp only [ihb, neg_add_rev, Int.reduceNeg, Int.cast_add, Int.cast_neg, Int.cast_one,
      Int.cast_natCast]
    ring

lemma tendsto_zero_inv_linear (z : ℂ) (b : ℤ) :
    Tendsto (fun d : ℕ ↦ 1 / ((b : ℂ) * z + d)) atTop (𝓝 0) := by
  apply Asymptotics.IsBigO.trans_tendsto ?_ tendsto_inverse_atTop_nhds_zero_nat
  have := (Asymptotics.isBigO_sup.mp (Int.cofinite_eq ▸ linear_inv_isBigO_right b z)).2
  simpa [← Nat.map_cast_int_atTop, Asymptotics.isBigO_map] using this

lemma tendsto_zero_inv_linear_sub (z : ℍ) (b : ℤ) :
    Tendsto (fun d : ℕ ↦ 1 / ((b : ℂ) * z - d)) atTop (𝓝 0) := by
  have := (tendsto_zero_inv_linear z (-b)).neg
  simp only [Int.cast_neg, neg_mul, one_div, neg_zero, ← inv_neg] at *
  exact this.congr (fun _ ↦ by ring)

private lemma G2_S_action' (z : ℍ) : ∑'[IcoFilter ℤ] n : ℤ, (∑' m : ℤ, 1 / ((m : ℂ) * z + n) ^ 2) =
    (((z : ℂ) ^ 2)⁻¹ * G2 (S • z)) := by
  apply HasSum.tsum_eq
  rw [HasSum_IcoFilter_iff]
  apply (G2_S_act z).congr (fun x ↦ ?_)
  rw [Summable.tsum_finsetSum]
  exact fun i hi => by simpa using linear_left_summable (ne_zero z) (i : ℤ) (k := 2) (by omega)

lemma tsum_IcoFilter_eq_zero (z : ℍ) (m : ℤ) :
    ∑'[IcoFilter ℤ] n : ℤ, (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1)) = 0 := by
  apply HasSum.tsum_eq
  rw [HasSum_IcoFilter_iff]
  conv =>
    enter [1, N]
    rw [telescope_aux z m N]
  simpa using Filter.Tendsto.sub (tendsto_zero_inv_linear_sub z m) (tendsto_zero_inv_linear z m)

private lemma linear_sub_linear_eq (z : ℍ) (a b m : ℤ) (hm : m ≠ 0 ∨ (a ≠ 0 ∧ b ≠ 0)) :
    1 / ((m : ℂ) * z + a) - 1 / (m * z + b) = (b - a) * (1 / ((m * z + a) * (m * z + b))) := by
  rw [← one_div_mul_sub_mul_one_div_eq_one_div_add_one_div]
  · simp only [one_div, add_sub_add_left_eq_sub, mul_inv_rev]
    ring
  · simpa using UpperHalfPlane.linear_ne_zero z (cd := ![m, a]) (by aesop)
  · simpa using UpperHalfPlane.linear_ne_zero z (cd := ![m, b]) (by aesop)

lemma summable_one_div_linear_sub_one_div_linear (z : ℍ) (a b : ℤ) :
    Summable fun m : ℤ ↦ 1 / (m * (z : ℂ) + a) - 1 / (m * z + b) := by
  have := Summable.mul_left (b - a : ℂ) (summable_linear_mul_linear (ne_zero z) a b)
  rw [← Finset.summable_compl_iff (s := {0})] at *
  apply this.congr
  intro m
  rw [linear_sub_linear_eq z a b m (by grind)]
  simp

private lemma summable_one_div_linear_sub_one_div_linear_succ (z : ℍ) (a : ℤ) :
    Summable fun b : ℤ ↦ 1 / ((a : ℂ) * z + b) - 1 / ((a : ℂ) * z + b + 1) := by
  have := (summable_linear_add_mul_linear_add z a a)
  rw [← Finset.summable_compl_iff (s := {0, -1})] at *
  apply this.congr (fun b ↦ ?_)
  have := linear_sub_linear_eq z b (b + 1) a (by grind)
  simp only [Int.reduceNeg, add_assoc, mul_inv_rev, one_div, Int.cast_add, Int.cast_one,
    add_sub_cancel_left, one_mul] at *
  rw [this, mul_comm]

private lemma aux_tsum_identity_1 (z : ℍ) (d : ℕ+) :
    ∑' (m : ℤ), (1 / ((m : ℂ) * z - d) - 1 / (m * z + d)) = -(2 / d) +
    ∑' m : ℕ+, (1 / ((m : ℂ) * z - d) + 1 / (-m * z + -d) - 1 / ((m : ℂ) * z + d) -
    1 / (-m * z + d)) := by
  rw [eq_neg_add_iff_add_eq (b := 2 / (d : ℂ)), tsum_int_eq_zero_add_tsum_pnat]
  · simp only [Int.cast_zero, zero_mul, zero_sub, one_div, zero_add, Int.cast_natCast, Int.cast_neg,
      neg_mul]
    ring_nf
    rw [← Summable.tsum_add]
    · grind
    · apply (summable_pnat_iff_summable_nat.mpr ((summable_int_iff_summable_nat_and_neg.mp
        (summable_one_div_linear_sub_one_div_linear z (-d) d)).1)).congr
      grind [Int.cast_natCast, Int.cast_neg, one_div]
    · apply (summable_pnat_iff_summable_nat.mpr ((summable_int_iff_summable_nat_and_neg.mp
        (summable_one_div_linear_sub_one_div_linear z (-d) d)).2)).congr
      grind [Int.cast_neg, Int.cast_natCast, neg_mul, one_div]
  · apply (summable_one_div_linear_sub_one_div_linear z (-d) d).congr
    grind [Int.cast_neg, Int.cast_natCast, one_div, sub_left_inj, inv_inj]

private lemma aux_tsum_identity_2 (z : ℍ) (d : ℕ+) :
    ∑' m : ℕ+, (1 / ((m : ℂ) * z - d) + 1 / (-m * z + -d) - (1 / (m * z + d)) -
    1 / (-m * z + d)) = 2 / z * ∑' m : ℕ+, (1 / (-(d : ℂ) / z - m) + 1 / (-d / z + m)) := by
  rw [← Summable.tsum_mul_left]
  · apply tsum_congr (fun m ↦ ?_)
    simp_rw [sub_eq_add_neg, ← div_neg, add_comm]
    ring_nf
    field_simp [ne_zero z]
  · have := (Summable_cotTerm (x := -d / (z : ℂ))
      (by simpa using int_div_upperHalfPlane_mem_integerComplement z (-d) (by aesop)))
    simp only [cotTerm, one_div] at *
    conv at this =>
      enter [1, n]
      rw [show ((n : ℂ) + 1) = (n + 1 : ℕ) by norm_cast]
    rw [summable_nat_add_iff (f := fun n ↦ (-d / (z : ℂ) - n)⁻¹ + (-d / (z : ℂ) + n)⁻¹)] at this
    exact Summable.subtype this (Nat.succ 0).le

private lemma aux_tendsto_tsum_cexp_pnat (z : ℍ) :
    Tendsto (fun N : ℕ+ ↦ ∑' (n : ℕ+), cexp (2 * π * I * (-N / z)) ^ (n : ℕ)) atTop (𝓝 0) := by
  have := tendsto_zero_geometric_tsum_pnat (UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨-1 / z,
    by simpa using (pnat_div_upperHalfPlane_im_pos 1 z)⟩)
  simp only [neg_div, one_div, coe_mk_subtype, mul_neg, ← exp_nsmul, smul_neg, nsmul_eq_mul,
    Nat.cast_mul] at *
  apply this.congr fun n ↦ ?_
  congr
  grind [one_div, coe_mk_subtype, mul_neg, smul_neg, nsmul_eq_mul, Nat.cast_mul, neg_inj]

private theorem aux_tendsto_tsum (z : ℍ) : Tendsto (fun n : ℕ ↦ 2 / z *
    ∑' (m : ℕ+), (1 / (-(n : ℂ) / z - m) + 1 / (-n / z + m))) atTop (𝓝 (-2 * π * I / z)) := by
  suffices Tendsto (fun n : ℕ+ ↦ (2 / (z : ℂ) * ∑' (m : ℕ+),
      (1 / (-(n : ℂ) / z - m) + 1 / (-n / z + m)))) atTop (𝓝 (-2 * π * I / z)) by
    rw [← tendsto_comp_val_Ioi_atTop]
    exact this
  have H0 : (fun n : ℕ+ ↦ (2 / z * ∑' (m : ℕ+), (1 / (-(n : ℂ) / z - m) + 1 / (-n / z + m)))) =
      (fun N : ℕ+ ↦ (-2 * π * I / z) - (2 / z * (2 * π * I)) *
      (∑' n : ℕ+, cexp (2 * π * I * (-N / z)) ^ (n : ℕ)) + 2 / N) := by
    ext N
    have h2 := cot_series_rep (UpperHalfPlane.coe_mem_integerComplement
      (⟨-N / z, pnat_div_upperHalfPlane_im_pos N z⟩))
    rw [pi_mul_cot_pi_q_exp, ← sub_eq_iff_eq_add',coe_mk_subtype, one_div, inv_div, neg_mul] at *
    rw [← h2, ← tsum_zero_pnat_eq_tsum_nat
      (by simpa using norm_exp_two_pi_I_lt_one ⟨-N / z, pnat_div_upperHalfPlane_im_pos N z⟩)]
    field_simp [ne_zero z]
    ring
  rw [H0]
  nth_rw 2 [show -2 * π * I / z = (-2 * π * I / z) - (2 / z * (2 * π * I)) * 0 + 2 * 0 by ring]
  apply Tendsto.add (Tendsto.sub (by simp) ((aux_tendsto_tsum_cexp_pnat z).const_mul _))
  apply Tendsto.const_mul
  simpa using tendsto_comp_val_Ioi_atTop.mpr (tendsto_zero_inv_linear z 0)

private lemma tendsto_tsum_one_div_linear_sub_succ_eq (z : ℍ) :
    Tendsto (fun N : ℕ+ ↦ ∑ n ∈ Ico (-N : ℤ) N,
    ∑' m : ℤ, (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1))) atTop (𝓝 (-2 * π * I / z)) := by
  have : (fun N : ℕ+ ↦ ∑ n ∈ (Ico (-N : ℤ) N),
      ∑' m : ℤ , (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1))) = (fun N : ℕ+ ↦
      ∑' m : ℤ , ∑ n ∈ Ico (-N : ℤ) N, (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1))) := by
    ext n
    rw [Summable.tsum_finsetSum (fun i hi ↦ ?_)]
    apply (summable_one_div_linear_sub_one_div_linear z (i : ℤ) (i + 1 : ℤ)).congr
    grind [one_div, Int.cast_add, Int.cast_one, sub_right_inj, inv_inj]
  conv at this =>
    enter [2, n]
    conv =>
      enter [1, m]
      rw [telescope_aux z]
    rw [show (n : ℂ) = (n : ℕ+) by simp, aux_tsum_identity_1 z]
  rw [this, show -2 * π * I / z = 0 + -2 * π * I / z by ring]
  apply Tendsto.add
  · have : Tendsto (fun x : ℕ ↦ -(2 / (x : ℂ))) atTop (𝓝 0) := by
      simpa [tendsto_zero_iff_norm_tendsto_zero] using Filter.Tendsto.const_div_atTop
        (g := fun n : ℕ ↦ ‖(n : ℂ)‖) (r := 2) (by simpa using tendsto_natCast_atTop_atTop)
    exact tendsto_comp_val_Ioi_atTop.mpr this
  · simp_rw [aux_tsum_identity_2]
    exact tendsto_comp_val_Ioi_atTop.mpr (aux_tendsto_tsum z)

--these are the two key lemmas
private lemma tsumFilter_tsum_eq (z : ℍ) :
    ∑'[IcoFilter ℤ] n : ℤ, ∑' m : ℤ, (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1)) =
    -2 * π * I / z := by
  apply HasSum.tsum_eq
  simp only [one_div, neg_mul, HasSum, IcoFilter, ← Nat.map_cast_int_atTop, Filter.map_map,
    tendsto_map'_iff] at *
  suffices H : Tendsto (fun N : ℕ ↦ ∑ n ∈ Ico (-N : ℤ) N,
      ∑' m : ℤ, (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1))) atTop (𝓝 (-2 * π * I / z)) by
    simpa using H.congr (by simp)
  exact tendsto_comp_val_Ioi_atTop.mp (tendsto_tsum_one_div_linear_sub_succ_eq z)

private lemma tsum_tsumFilter_eq (z : ℍ) :
    ∑' m : ℤ, ∑'[IcoFilter ℤ] n : ℤ, (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1)) = 0 := by
  convert tsum_zero
  exact tsum_IcoFilter_eq_zero z _

end AuxiliaryLemmas

section transform

lemma G2Term_add_delta_summable (z : ℍ) :
    Summable fun (m : Fin 2 → ℤ) ↦ (G2Term z m + δ m):= by
  have H :  Summable (fun m ↦ (G2Term z m)) := by
    apply summable_inv_of_isBigO_rpow_norm_inv (a := 3) (by linarith)
    simpa [pow_three, pow_two, ← mul_assoc] using ((isBigO_linear_add_const_vec z 0 1).mul
      (isBigO_linear_add_const_vec z 0 0)).mul (isBigO_linear_add_const_vec z 0 0)
  let s : Finset (Fin 2 → ℤ) := {![0,0], ![0,-1]}
  rw [← Finset.summable_compl_iff s]
  apply (H.subtype sᶜ).congr (fun b ↦ ?_)
  have hb1 : b.1 ≠ ![0, 0] := by aesop
  have hb2 : b.1 ≠ ![0, -1] := by aesop
  simp [δ, hb1, hb2]

private lemma aux_identity (z : ℍ) (b n : ℤ) : ((b : ℂ) * z + n + 1)⁻¹ * (((b : ℂ) * z + n) ^ 2)⁻¹ +
    (δ ![b, n]) + (((b : ℂ) * z + n)⁻¹ - ((b : ℂ) * z + n + 1)⁻¹) = (((b : ℂ) * z + n) ^ 2)⁻¹ := by
  by_cases h : b = 0 ∧ n = 0
  · simp [h.1, h.2]
  · simp only [not_and] at h
    by_cases hb : b = 0
    · by_cases hn : n = -1
      · simp only [hb, Int.cast_zero, zero_mul, hn, Int.reduceNeg, Int.cast_neg, Int.cast_one,
        zero_add, neg_add_cancel, inv_zero, even_two, Even.neg_pow, one_pow, inv_one, mul_one,
        δ_eq_two, inv_neg, sub_zero]
        ring
      · have hn0 : (n : ℂ) ≠ 0 := by aesop
        have hn1 : (n : ℂ) + 1 ≠ 0 := by norm_cast; grind
        simp only [hb, δ, Matrix.vecCons_inj, h hb, hn]
        grind
    · simp only [δ, Matrix.vecCons_inj, hb]
      have h0 : ((b : ℂ) * z + n + 1) ≠ 0 := by
        simpa [add_assoc] using linear_ne_zero (cd := ![b, n + 1]) z (by aesop)
      have h1 : ((b : ℂ) * z + n) ≠ 0 := by
        simpa using linear_ne_zero (cd := ![b, n]) z (by aesop)
      grind

/-- This shows `G2` can be defined as a certain absolutely convergent double sum. -/
lemma G2_eq_tsum_G2Term (z : ℍ) : G2 z = ∑' m, ∑' n, (G2Term z ![m, n] + δ ![m, n]) := by
  set t := ∑' m, ∑' n, (G2Term z ![m, n] + δ ![m, n])
  rw [G2, show t = t + 0 by ring, ← tsum_tsumFilter_eq z, ← Summable.tsum_add]
  · rw [← tsum_eq_of_summable_unconditional (L := symCondInt)]
    · congr
      ext a
      rw [e2Summand, tsum_eq_of_summable_unconditional (L := IcoFilter ℤ)
        (summable_one_div_linear_sub_one_div_linear_succ z a), ← Summable.tsum_add _
        (summable_one_div_linear_sub_one_div_linear_succ z a)]
      · apply tsum_congr (fun b ↦ ?_)
        simp only [eisSummand, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, Int.reduceNeg, zpow_neg, G2Term, mul_inv_rev, one_div,
          aux_identity z a b, inv_inj]
        rfl
      · have := G2Term_add_delta_summable z
        simp only [G2Term, Fin.isValue, mul_inv_rev, ← (finTwoArrowEquiv _).symm.summable_iff,
          finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one] at *
        exact this.prod_factor _
    · conv =>
        enter [1, N]
        rw [tsum_IcoFilter_eq_zero z N, add_zero]
      exact ((finTwoArrowEquiv _).symm.summable_iff.mpr (G2Term_add_delta_summable z)).prod
  · apply (((finTwoArrowEquiv _).symm.summable_iff.mpr (G2Term_add_delta_summable z)).prod).congr
    simp
  · exact summable_zero.congr (fun b ↦ (by simp [← tsum_IcoFilter_eq_zero z b]))

private lemma G2_S_action_eq_tsum_G2Term (z : ℍ) : ((z : ℂ) ^ 2)⁻¹ * G2 (S • z) - -2 * π * I / z =
    ∑' n : ℤ, ∑' m : ℤ, (G2Term z ![m, n] + δ ![m, n]) := by
  rw [← tsumFilter_tsum_eq z, ← (G2_S_action' z),
    ← tsum_eq_of_summable_unconditional (L := IcoFilter ℤ), ← Summable.tsum_sub]
  · apply tsum_congr (fun N ↦ ?_)
    rw [← Summable.tsum_sub]
    · apply tsum_congr (fun M ↦ ?_)
      simp only [one_div, G2Term, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, mul_inv_rev]
      nth_rw 1 [← aux_identity z M N]
      ring
    · simpa using linear_left_summable (ne_zero z) N (k := 2) (by norm_num)
    · simpa [add_assoc] using summable_one_div_linear_sub_one_div_linear z N (N + 1)
  · apply HasSum.summable (a := (z.1 ^ 2)⁻¹ * G2 (S • z))
    rw [HasSum_IcoFilter_iff]
    apply (G2_S_act z).congr (fun x ↦ ?_)
    rw [Summable.tsum_finsetSum (fun i hi ↦ ?_)]
    simpa using linear_left_summable (ne_zero z) i (k := 2) (by norm_num)
  · apply HasSum.summable (a := -2 * π * I / z)
    rw [HasSum_IcoFilter_iff, ← tendsto_comp_val_Ioi_atTop]
    exact tendsto_tsum_one_div_linear_sub_succ_eq z
  · have := G2Term_add_delta_summable z
    rw [← swap_equiv.summable_iff, ← (finTwoArrowEquiv _).symm.summable_iff] at this
    simpa using Summable.prod this

private lemma tsum_prod_G2Term_eq (z : ℍ) : ∑' (m : Fin 2 → ℤ), (G2Term z m + δ m) =
    ∑' m : ℤ, ∑' n : ℤ, (G2Term z ![m, n] + (δ ![m, n])) := by
  rw [ ← (finTwoArrowEquiv _).symm.tsum_eq]
  have := G2Term_add_delta_summable z
  simp only [Fin.isValue, finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, mul_inv_rev] at *
  rw [← (finTwoArrowEquiv _).symm.summable_iff] at this
  exact Summable.tsum_prod' this (this.prod_factor)

private lemma tsum_prod_G2Term_eq' (z : ℍ) : ∑' (m : Fin 2 → ℤ), (G2Term z m + δ m) =
    ∑' n : ℤ, ∑' m : ℤ, (G2Term z ![m, n] + δ ![m, n]) := by
  have := (G2Term_add_delta_summable z)
  simp only [mul_inv_rev, Fin.isValue, ← (finTwoArrowEquiv _).symm.summable_iff] at this
  rw [Summable.tsum_comm', tsum_prod_G2Term_eq]
  · apply this.congr
    grind [Fin.isValue, finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_inv_rev]
  · simpa [mul_inv_rev] using this.prod_factor
  · have H := (G2Term_add_delta_summable z)
    rw [← swap_equiv.summable_iff, ← (finTwoArrowEquiv _).symm.summable_iff] at H
    simpa using H.prod_factor

/-- This is the key identity for how `G2` transforms under the slash action by `S`. -/
lemma G2_S_transform (z : ℍ) : G2 z = ((z : ℂ) ^ 2)⁻¹ * G2 (S • z) - -2 * π * I / z := by
  rw [G2_S_action_eq_tsum_G2Term, G2_eq_tsum_G2Term z , ← tsum_prod_G2Term_eq', tsum_prod_G2Term_eq]

lemma G2_T_transform : (G2 ∣[(2 : ℤ)] T) = G2 := by
  ext z
  simp_rw [SL_slash_def, modular_T_smul z]
  simp only [G2_q_exp, coe_vadd, ofReal_one, T, denom_apply, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.cons_val_one, Int.cast_zero, zero_mul, Int.cast_one, zero_add, Int.reduceNeg, zpow_neg,
    one_zpow, inv_one, mul_one, ← exp_periodic.nat_mul 1 (2 * π * I * z), Nat.cast_one, one_mul,
    sub_right_inj,mul_eq_mul_left_iff, mul_eq_zero, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true,
    pow_eq_zero_iff, ofReal_eq_zero, Real.pi_ne_zero, or_self, or_false]
  grind

lemma G2_slash_action (γ : SL(2, ℤ)) : G2 ∣[(2 : ℤ)] γ = G2 - D2 γ := by
  have := Subgroup.closure_induction (p := fun γ _ ↦ G2 ∣[(2 : ℤ)] γ = G2 - D2 γ)
    (k := ({S, T})) ?_ (by simp only [SlashAction.slash_one, D2_one, sub_zero])
  · refine this ?_ ?_ (by simp [SpecialLinearGroup.SL2Z_generators])
    · intro a b ha hb HA HB
      rw [D2_mul, SlashAction.slash_mul, HA, sub_eq_add_neg, SlashAction.add_slash, HB]
      ext z
      simp only [SlashAction.neg_slash, SL_slash, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
      ring
    · intro g hg hg2
      have H1 : (G2 ∣[(2 : ℤ)] g)∣[(2 : ℤ)] g⁻¹ = (G2 - D2 g)∣[(2 : ℤ)] g⁻¹ := by
        rw [hg2]
      simp_rw [← SlashAction.slash_mul, sub_eq_add_neg, SlashAction.add_slash, mul_inv_cancel,
        SlashAction.slash_one, SL_slash, SlashAction.neg_slash] at H1
      nth_rw 2 [H1]
      have := D2_inv g
      simp only [SL_slash] at this
      rw [← sub_eq_add_neg, this, SL_slash, sub_neg_eq_add, add_sub_cancel_right]
  · intro a ha
    simp only [mem_insert_iff, mem_singleton_iff, SL_slash] at *
    rcases ha with h1 | h2
    · ext z
      have := SlashInvariantForm.slash_S_apply G2 2 z
      rw [SL_slash] at this
      simp only [Pi.sub_apply, h1, D2_S z, this, mul_comm, G2_S_transform z, modular_S_smul]
      ring_nf
      simp_rw [inv_pow, mul_eq_mul_right_iff]
      aesop
    · simpa only [h2, D2_T, sub_zero] using G2_T_transform

lemma E2_slash_action (γ : SL(2, ℤ)) : E2 ∣[(2 : ℤ)] γ = E2 - (1 / (2 * riemannZeta 2)) • D2 γ := by
  ext z
  simp [E2, SL_smul_slash, G2_slash_action γ, mul_sub]

lemma G2_differentiableOn : DifferentiableOn ℂ (↑ₕG2) upperHalfPlaneSet := by
  have := G2_q_exp
  apply DifferentiableOn.congr (f := fun z => 2 * riemannZeta 2 - 8 * ↑π ^ 2 * ∑' (n : ℕ+),
    ↑((ArithmeticFunction.sigma 1) ↑n) * cexp (2 * ↑π * I * ↑z) ^ (n : ℤ))
  --apply DifferentiableOn.add_const
  --sorry
  sorry
  · intro z hz
    have H := this ⟨z, hz⟩
    convert H
    simp
    have := UpperHalfPlane.ofComplex_apply ⟨z, hz⟩
    simp at this
    rw [this]

end transform

end EisensteinSeries
