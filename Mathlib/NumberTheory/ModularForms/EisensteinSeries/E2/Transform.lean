/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

/-!
# Slash action on E2

We show how the Eisenstein series `E2` transforms under the slash action of `SL(2, ℤ)`.
In particular, we show that it is invariant under the action of `T = [[1, 1], [0, 1]]` and we
compute how it transforms under the action of `S = [[0, -1], [1, 0]]` in term of a correction term
`D2`.

The proof relies on writing the Eisenstein series `G2` as an absolutely convergent infinite sum of
terms of the form `(((m 0 : ℂ) * z + m 1) ^ 2 * (m 0 * z + m 1 + 1))⁻¹ + δ(m)` for
`m : Fin 2 → ℤ` where `δ(m)` is a small correction term. This allows us to link the sum when acted
on by `S` (which swaps the co-ordinates of `m`) to the original sum plus some extra terms which
give rise to the correction term `D2`.
-/

@[expose] public section

open UpperHalfPlane hiding I

open ModularForm ModularGroup Filter Complex MatrixGroups
 Set SummationFilter

open scoped Real Topology

noncomputable section

namespace EisensteinSeries

/-- This is an auxiliary correction term for proving how E2 transforms. It allows us to work with
nicer indexing sets for our infinite sums. The key is the `aux_identity` below. -/
def δ (x : Fin 2 → ℤ) : ℂ := if x = ![0,0] then 1 else if x = ![0, -1] then 2 else 0

@[simp]
private lemma δ_eq : δ ![0,0] = 1 := by simp [δ]

@[simp]
private lemma δ_eq_two : δ ![0, -1] = 2 := by simp [δ]

/-- This term gives an alternative infinite sum for G2 which is absolutely convergent. -/
abbrev G2Term (z : ℍ) (m : Fin 2 → ℤ) : ℂ :=
    (((m 0 : ℂ) * z + m 1) ^ 2 * (m 0 * z + m 1 + 1))⁻¹ + δ m

--Do we have this already? if not where should this go?
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

section transform

lemma G2Term_summable (z : ℍ) : Summable fun m ↦ G2Term z m := by
  have H : Summable (fun m ↦ (G2Term z m) - δ m) := by
    simp_rw [G2Term, add_sub_cancel_right]
    apply summable_of_isBigO_rpow_norm (a := 3) (by linarith)
    simpa [pow_three, pow_two, ← mul_assoc] using ((isBigO_linear_add_const_vec z 0 1).mul
      (isBigO_linear_add_const_vec z 0 0)).mul (isBigO_linear_add_const_vec z 0 0)
  let s : Finset (Fin 2 → ℤ) := {![0,0], ![0,-1]}
  rw [← Finset.summable_compl_iff s]
  apply (H.subtype sᶜ).congr (fun b ↦ ?_)
  have hb1 : b.1 ≠ ![0, 0] := by aesop
  have hb2 : b.1 ≠ ![0, -1] := by aesop
  simp [δ, hb1, hb2]

--This is the version we use the most.
lemma G2Term_prod_summable (z : ℍ) : Summable (fun p : ℤ × ℤ ↦ G2Term z ![p.1, p.2]) := by
  apply (finTwoArrowEquiv _).symm.summable_iff.mpr (G2Term_summable z)

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
lemma G2_eq_tsum_G2Term (z : ℍ) : G2 z = ∑' m, ∑' n, G2Term z ![m, n] := by
  set t := ∑' m, ∑' n, (G2Term z ![m, n])
  rw [G2, show t = t + 0 by ring, ← tsum_tsumFilter_sub_eq z, ← Summable.tsum_add]
  · rw [← tsum_eq_of_summable_unconditional (L := symmetricIcc ℤ)]
    · congr
      ext a
      rw [e2Summand, tsum_eq_of_summable_unconditional
        (summable_right_one_div_linear_sub_one_div_linear_succ z a), ← Summable.tsum_add
        ((G2Term_prod_summable z).prod_factor _)
        (summable_right_one_div_linear_sub_one_div_linear_succ z a)]
      apply tsum_congr (fun b ↦ ?_)
      simp only [eisSummand, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, Int.reduceNeg, zpow_neg, G2Term, mul_inv_rev, one_div,
          aux_identity z a b, inv_inj]
      rfl
    · conv =>
        enter [1, N]
        rw [tsum_symmetricIco_linear_sub_linear_add_one_eq_zero z N, add_zero]
      exact (G2Term_prod_summable z).prod
  · grind [(G2Term_prod_summable z).prod.congr]
  · exact summable_zero.congr
      (fun b ↦ (by simp [← tsum_symmetricIco_linear_sub_linear_add_one_eq_zero z b]))

private lemma G2_S_action_eq_tsum_G2Term (z : ℍ) : ((z : ℂ) ^ 2)⁻¹ * G2 (S • z) - -2 * π * I / z =
    ∑' n : ℤ, ∑' m : ℤ, G2Term z ![m, n] := by
  rw [← tsumFilter_tsum_sub_eq z, ← (tsum_symmetricIco_tsum_eq_S_act z),
    ← tsum_eq_of_summable_unconditional (L := symmetricIco ℤ), ← Summable.tsum_sub]
  · apply tsum_congr (fun N ↦ ?_)
    rw [← Summable.tsum_sub]
    · apply tsum_congr (fun M ↦ ?_)
      simp only [one_div, G2Term, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, mul_inv_rev]
      nth_rw 1 [← aux_identity z M N]
      ring
    · simpa using linear_left_summable (ne_zero z) N (k := 2) (by norm_num)
    · simpa [add_assoc] using summable_left_one_div_linear_sub_one_div_linear z N (N + 1)
  · apply HasSum.summable (a := (z.1 ^ 2)⁻¹ * G2 (S • z))
    rw [hasSum_symmetricIco_int_iff]
    apply (tendsto_double_sum_S_act z).congr (fun x ↦ ?_)
    rw [Summable.tsum_finsetSum (fun i hi ↦ ?_)]
    simpa using linear_left_summable (ne_zero z) i (k := 2) (by norm_num)
  · apply HasSum.summable (a := -2 * π * I / z)
    rw [hasSum_symmetricIco_int_iff, ← tendsto_comp_val_Ioi_atTop]
    exact tendsto_tsum_one_div_linear_sub_succ_eq z
  · have := G2Term_summable z
    rw [← swap_equiv.summable_iff, ← (finTwoArrowEquiv _).symm.summable_iff] at this
    exact this.prod

private lemma tsum_G2Term_eq_tsum (z : ℍ) : ∑' (m : Fin 2 → ℤ), G2Term z m =
    ∑' m : ℤ, ∑' n : ℤ, G2Term z ![m, n] := by
  rw [ ← (finTwoArrowEquiv _).symm.tsum_eq]
  exact Summable.tsum_prod' (G2Term_prod_summable z) ((G2Term_prod_summable z).prod_factor)

private lemma tsum_G2Term_eq_tsum' (z : ℍ) : ∑' (m : Fin 2 → ℤ), G2Term z m =
    ∑' n : ℤ, ∑' m : ℤ, G2Term z ![m, n] := by
  rw [Summable.tsum_comm', tsum_G2Term_eq_tsum]
  · apply (G2Term_prod_summable z).congr
    grind [finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_inv_rev]
  · simpa [mul_inv_rev] using (G2Term_prod_summable z).prod_factor
  · have H := G2Term_summable z
    rw [← swap_equiv.summable_iff, ← (finTwoArrowEquiv _).symm.summable_iff] at H
    simpa using H.prod_factor

/-- This is the key identity for how `G2` transforms under the slash action by `S`. -/
lemma G2_S_transform (z : ℍ) : G2 z = ((z : ℂ) ^ 2)⁻¹ * G2 (S • z) - -2 * π * I / z := by
  rw [G2_S_action_eq_tsum_G2Term, G2_eq_tsum_G2Term z , ← tsum_G2Term_eq_tsum',
  tsum_G2Term_eq_tsum]

lemma G2_T_transform : G2 ∣[(2 : ℤ)] T = G2 := by
  ext z
  simp_rw [SL_slash_def, modular_T_smul z]
  simp only [G2_eq_tsum_cexp, coe_vadd, ofReal_one, T, denom_apply, Fin.isValue, Matrix.of_apply,
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

end transform

end EisensteinSeries
