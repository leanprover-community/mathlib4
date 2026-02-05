/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/

module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Defs
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# Summability of E2

We collect here lemmas about the summability of the Eisenstein series `E2` that will be used to
prove how it transforms under the slash action.

## Main Results

The key results concern the difference between two different orders of summation for the
telescoping series `∑_{m,n} (1/(mz + n) - 1/(mz + n + 1))`:

1. **`tsum_symmetricIco_tsum_sub_eq`**: Summing first over `n` (in symmetric intervals), then `m`:
   `∑'[symmetricIco] n : ℤ, ∑' m : ℤ, (1/(mz+n) - 1/(mz+n+1)) = -2πi/z`

2. **`tsum_tsum_symmetricIco_sub_eq`**: Summing first over `m`, then `n` (in symmetric intervals):
   `∑' m : ℤ, ∑'[symmetricIco] n : ℤ, (1/(mz+n) - 1/(mz+n+1)) = 0`

The difference `-2πi/z` between these two orderings is precisely the correction term
`D2` that appears in the transformation formula for `G2` under the action of `S`.

## Proof Strategy

1. For fixed `m ≠ 0`, the inner sum over `n` telescopes to zero (each term cancels with its
   neighbor), establishing the first identity.

2. For fixed `n`, the inner sum over `m` can be computed using the cotangent series expansion.
   As `n → ±∞` in symmetric intervals, these sums contribute `-2πi/z`.

-/

open UpperHalfPlane hiding I σ

open Filter Complex Finset SummationFilter

open scoped Interval Real Topology BigOperators Nat ArithmeticFunction.sigma

@[expose] public noncomputable section

namespace EisensteinSeries

variable (z : ℍ)

local notation "𝕢" z:100 => cexp (2 * π * I * z)

private lemma G2_partial_sum_eq (N : ℕ) : ∑ m ∈ Icc (-N : ℤ) N, e2Summand m z =
    2 * riemannZeta 2 + ∑ m ∈ range N, -8 * π ^ 2 *
      ∑' n : ℕ+, n * 𝕢 z ^ ((m + 1) * n) := by
  rw [sum_Icc_of_even_eq_range (e2Summand_even z), Finset.sum_range_succ', smul_add,
    nsmul_eq_mul, Nat.cast_zero, e2Summand_zero_eq_two_riemannZeta_two]
  ring_nf
  simp only [e2Summand, eisSummand, add_comm, Nat.cast_add, Nat.cast_one, Fin.isValue,
    Matrix.cons_val_zero, Int.cast_add, Int.cast_natCast, Int.cast_one, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Int.reduceNeg, zpow_neg, mul_comm, mul_sum]
  congr with a
  have H2 := qExpansion_identity_pnat (k := 1) (by grind)
    ⟨(a + 1) * z, by simpa [show 0 < ((a + 1) : ℝ) by positivity] using z.2⟩
  simp only [add_comm, Nat.reduceAdd, one_div, mul_comm, mul_neg, even_two,
    Even.neg_pow, Nat.factorial_one, Nat.cast_one, div_one, pow_one] at H2
  simp_rw [zpow_ofNat, H2, ← tsum_mul_left, ← tsum_neg, ← exp_nsmul]
  refine tsum_congr fun b ↦ ?_
  ring_nf
  grind [I_sq, exp_add]

private lemma aux_G2_tendsto : Tendsto
    (fun N ↦ ∑ m ∈ range N, -8 * π ^ 2 * ∑' n : ℕ+, n * 𝕢 z ^ ((m + 1) * n)) atTop
    (𝓝 (-8 * π ^ 2 * ∑' n : ℕ+, σ 1 n * 𝕢 z ^ (n : ℕ))) := by
  have : -8 * π ^ 2 * ∑' n : ℕ+, σ 1 n * 𝕢 z ^ (n : ℕ) =
      ∑' m : ℕ, (-8 * π ^ 2 * ∑' n : ℕ+, n * 𝕢 z ^ ((m + 1) * n)) := by
    have := tsum_prod_pow_eq_tsum_sigma 1 (norm_exp_two_pi_I_lt_one z)
    rw [tsum_pnat_eq_tsum_succ (f := fun d ↦ ∑' c : ℕ+, c ^ 1 * 𝕢 z ^ (d * c : ℕ))] at this
    simp [← tsum_mul_left, ← this]
  rw [this]
  refine (Summable.mul_left _ ?_).hasSum.comp tendsto_finset_range
  rw [← summable_pnat_iff_summable_succ (f := fun b ↦ ∑' c : ℕ+, c * 𝕢 z ^ (b * c : ℕ))]
  apply (summable_prod_mul_pow 1 (norm_exp_two_pi_I_lt_one z)).prod.congr
  simp [← exp_nsmul]

lemma hasSum_e2Summand_symmetricIcc : HasSum (e2Summand · z)
    (2 * riemannZeta 2 - 8 * π ^ 2 * ∑' n : ℕ+, σ 1 n * 𝕢 z ^ (n : ℕ)) (symmetricIcc ℤ) := by
  simpa [HasSum, -symmetricIcc_filter, symmetricIcc_eq_map_Icc_nat, Function.comp_def,
    G2_partial_sum_eq] using (aux_G2_tendsto z).const_add _

lemma summable_e2Summand_symmetricIcc : Summable (e2Summand · z) (symmetricIcc ℤ) :=
  (hasSum_e2Summand_symmetricIcc z).summable

lemma G2_eq_tsum_cexp : G2 z = 2 * riemannZeta 2 - 8 * π ^ 2 * ∑' n : ℕ+, σ 1 n * 𝕢 z ^ (n : ℕ) :=
  (hasSum_e2Summand_symmetricIcc z).tsum_eq

lemma tendsto_e2Summand_atTop_nhds_zero : Tendsto (e2Summand · z) atTop (𝓝 0) :=
  (summable_e2Summand_symmetricIcc z).tendsto_zero_of_even_summable_symmetricIcc (e2Summand_even _)

lemma hasSum_e2Summand_symmetricIco : HasSum (e2Summand · z)
    (2 * riemannZeta 2 - 8 * π ^ 2 * ∑' n : ℕ+, σ 1 n * 𝕢 z ^ (n : ℕ)) (symmetricIco ℤ) := by
  apply (hasSum_e2Summand_symmetricIcc z).hasSum_symmetricIco_of_hasSum_symmetricIcc
  simpa using (tendsto_e2Summand_atTop_nhds_zero z).neg.comp tendsto_natCast_atTop_atTop

lemma summable_e2Summand_symmetricIco : Summable (e2Summand · z) (symmetricIco ℤ) :=
  (hasSum_e2Summand_symmetricIco z).summable

lemma G2_eq_tsum_symmetricIco : G2 z = ∑'[symmetricIco ℤ] m, e2Summand m z := by
  rw [G2, tsum_symmetricIcc_eq_tsum_symmetricIco (summable_e2Summand_symmetricIcc z)]
  simpa using (tendsto_e2Summand_atTop_nhds_zero z).neg.comp tendsto_natCast_atTop_atTop

section Auxiliary

open ModularGroup

variable (z : ℍ)

private lemma one_div_linear_sub_one_div_linear_eq (a b m : ℤ) (hm : m ≠ 0 ∨ (a ≠ 0 ∧ b ≠ 0)) :
    1 / ((m : ℂ) * z + a) - 1 / (m * z + b) = (b - a) * (1 / ((m * z + a) * (m * z + b))) := by
  rw [← one_div_mul_sub_mul_one_div_eq_one_div_add_one_div]
  · grind [one_div, add_sub_add_left_eq_sub, mul_inv_rev]
  · simpa using linear_ne_zero z (cd := ![m, a]) (by aesop)
  · simpa using linear_ne_zero z (cd := ![m, b]) (by aesop)

lemma summable_left_one_div_linear_sub_one_div_linear (a b : ℤ) :
    Summable fun m : ℤ ↦ 1 / (m * (z : ℂ) + a) - 1 / (m * z + b) := by
  have := Summable.mul_left (b - a : ℂ) (summable_linear_left_mul_linear_left (ne_zero z) a b)
  rw [← Finset.summable_compl_iff (s := {0})] at *
  apply this.congr (fun m ↦ ?_)
  grind [one_div_linear_sub_one_div_linear_eq z a b m (by grind)]

lemma summable_right_one_div_linear_sub_one_div_linear_succ (m : ℤ) :
    Summable fun b : ℤ ↦ 1 / (m * (z : ℂ) + b) - 1 / (m * z + b + 1) := by
  have := summable_linear_right_add_one_mul_linear_right z m m
  rw [← Finset.summable_compl_iff (s := {0, -1})] at *
  apply this.congr (fun b ↦ ?_)
  simpa [add_assoc, mul_comm] using
    (one_div_linear_sub_one_div_linear_eq z b (b + 1) m (by grind)).symm

/- Acting by `S` (which sends `z` to `-z ⁻¹`) swaps the sums and pulls out a factor of
`(z ^ 2)⁻¹`. -/
private lemma aux_sum_Ico_S_identity (N : ℕ) :
    ((z : ℂ) ^ 2)⁻¹ * (∑ x ∈ Ico (-N : ℤ) N, ∑' (n : ℤ), (((x : ℂ) * (-↑z)⁻¹ + n) ^ 2)⁻¹) =
    ∑' (n : ℤ), ∑ x ∈ Ico (-N : ℤ) N, (((n : ℂ) * z + x) ^ 2)⁻¹ := by
  simp_rw [inv_neg, mul_neg, mul_sum]
  rw [Summable.tsum_finsetSum (fun i hi ↦ by apply linear_left_summable (ne_zero z) i le_rfl)]
  apply sum_congr rfl fun n hn ↦ ?_
  rw [← tsum_mul_left, ← tsum_comp_neg]
  apply tsum_congr (by grind [ne_zero z])

lemma tendsto_double_sum_S_act :
    Tendsto (fun N : ℕ ↦ (∑' (n : ℤ), ∑ m ∈ Ico (-N : ℤ) N, (1 / ((n : ℂ) * z + m) ^ 2))) atTop
    (𝓝 ((z.1 ^ 2)⁻¹ * G2 (S • z))) := by
  rw [G2_eq_tsum_symmetricIco, ← tsum_mul_left]
  have := ((summable_e2Summand_symmetricIco (S • z)).mul_left (z.1 ^ 2)⁻¹).hasSum
  simp only [HasSum, symmetricIco, tendsto_map'_iff, modular_S_smul, ← Nat.map_cast_int_atTop] at *
  apply this.congr (fun N ↦ ?_)
  simpa [e2Summand, eisSummand, ← mul_sum] using aux_sum_Ico_S_identity z N

lemma tsum_symmetricIco_tsum_eq_S_act :
    ∑'[symmetricIco ℤ] n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * z + n) ^ 2 =
    ((z : ℂ) ^ 2)⁻¹ * G2 (S • z) := by
  apply HasSum.tsum_eq
  rw [hasSum_symmetricIco_int_iff]
  apply (tendsto_double_sum_S_act z).congr (fun x ↦ ?_)
  rw [Summable.tsum_finsetSum]
  exact fun i hi ↦ by simpa using linear_left_summable (ne_zero z) i le_rfl

private lemma telescope_aux (z : ℂ) (m : ℤ) (b : ℕ) :
    ∑ n ∈ Ico (-b : ℤ) b, (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1)) =
    1 / (m * z - b) - 1 / (m * z + b) := by
  convert sum_Ico_int_sub b (fun n ↦ 1 / ((m : ℂ) * z + n)) using 2 <;>
  simp [add_assoc, sub_eq_add_neg]

lemma tsum_symmetricIco_linear_sub_linear_add_one_eq_zero (m : ℤ) :
    ∑'[symmetricIco ℤ] n : ℤ, (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1)) = 0 := by
  apply HasSum.tsum_eq
  simp_rw [hasSum_symmetricIco_int_iff, telescope_aux z m]
  simpa using (tendsto_zero_inv_linear_sub z m).sub (tendsto_zero_inv_linear z m)

/- We split the sum over `ℤ` into a sum over `ℕ+` but of four terms.-/
private lemma aux_tsum_identity_1 (d : ℕ+) :
    ∑' (m : ℤ), (1 / ((m : ℂ) * z - d) - 1 / (m * z + d)) = -(2 / d) +
    ∑' m : ℕ+, (1 / ((m : ℂ) * z - d) + 1 / (-m * z + -d) - 1 / (m * z + d) -1 / (-m * z + d)) := by
  rw [eq_neg_add_iff_add_eq (b := 2 / (d : ℂ)), tsum_int_eq_zero_add_tsum_pnat]
  · simp only [Int.cast_zero, zero_mul, zero_sub, one_div, zero_add, Int.cast_natCast, Int.cast_neg,
      neg_mul]
    ring_nf
    rw [← Summable.tsum_add]
    · grind
    · apply (summable_pnat_iff_summable_nat.mpr ((summable_int_iff_summable_nat_and_neg.mp
        (summable_left_one_div_linear_sub_one_div_linear z (-d) d)).1)).congr
      grind [Int.cast_natCast]
    · apply (summable_pnat_iff_summable_nat.mpr ((summable_int_iff_summable_nat_and_neg.mp
        (summable_left_one_div_linear_sub_one_div_linear z (-d) d)).2)).congr
      grind [Int.cast_neg, Int.cast_natCast, neg_mul, one_div]
  · simpa using summable_left_one_div_linear_sub_one_div_linear z (-d) d

/- The sum of four terms can now be combined into a sum where `z` has changed for `-1 / z`.-/
private lemma aux_tsum_identity_2 (d : ℕ+) :
    ∑' m : ℕ+, (1 / ((m : ℂ) * z - d) + 1 / (-m * z + -d) - (1 / (m * z + d)) -
    1 / (-m * z + d)) = 2 / z * ∑' m : ℕ+, (1 / (-(d : ℂ) / z - m) + 1 / (-d / z + m)) := by
  rw [← Summable.tsum_mul_left]
  · apply tsum_congr (by grind [sub_eq_add_neg, ← div_neg, ne_zero z])
  · have := summable_cotTerm (by simpa using z.int_div_mem_integerComplement (n := -d) (by aesop))
    simp only [cotTerm, one_div] at *
    simp only [← Nat.cast_add_one] at this
    rw [summable_nat_add_iff (f := fun n ↦ (-d / (z : ℂ) - n)⁻¹ + (-d / (z : ℂ) + n)⁻¹)] at this
    apply this.subtype

private lemma aux_tendsto_tsum_cexp_pnat :
    Tendsto (fun N : ℕ+ ↦ ∑' (n : ℕ+), cexp (2 * π * I * (-N / z)) ^ (n : ℕ)) atTop (𝓝 0) := by
  have := tendsto_zero_geometric_tsum_pnat (norm_exp_two_pi_I_lt_one ⟨_, im_pnat_div_pos 1 z⟩)
  simp only [← exp_nsmul, nsmul_eq_mul, Nat.cast_mul] at *
  exact this.congr <| by grind

/- Now this sum of terms with `-1 / z` tendsto `-2 * π * I / z` which is exactly `D2_S`. The key is
to use the cotangent series to write this as a sum of exponentials.-/
private lemma aux_tendsto_tsum : Tendsto (fun n : ℕ ↦ 2 / z *
    ∑' (m : ℕ+), (1 / (-(n : ℂ) / z - m) + 1 / (-n / z + m))) atTop (𝓝 (-2 * π * I / z)) := by
  rw [← PNat.tendsto_comp_val_iff]
  have H0 : (fun n : ℕ+ ↦ (2 / z * ∑' (m : ℕ+), (1 / (-(n : ℂ) / z - m) + 1 / (-n / z + m)))) =
      (fun n : ℕ+ ↦ (-2 * π * I / z) - (2 / z * (2 * π * I)) *
      (∑' m : ℕ+, cexp (2 * π * I * (-n / z)) ^ (m : ℕ)) + 2 / n) := by
    ext N
    have h2 := cot_series_rep <| coe_mem_integerComplement ⟨-N / z, im_pnat_div_pos N z⟩
    rw [pi_mul_cot_pi_q_exp, ← sub_eq_iff_eq_add', one_div, inv_div, neg_mul, ← h2,
      ← tsum_zero_pnat_eq_tsum_nat
      (by simpa using norm_exp_two_pi_I_lt_one ⟨-N / z, im_pnat_div_pos N z⟩)] at *
    field [ne_zero z]
  rw [H0]
  nth_rw 2 [show -2 * π * I / z = (-2 * π * I / z) - (2 / z * (2 * π * I)) * 0 + 2 * 0 by ring]
  refine aux_tendsto_tsum_cexp_pnat z |>.const_mul _ |>.const_sub _ |>.add (.const_mul _ ?_)
  exact PNat.tendsto_comp_val_iff.mpr tendsto_inv_atTop_nhds_zero_nat

/- This shows that the limit of the conditional sum over larger intervals tends
to `-2 * π * I / z`. We will then show, in `tsum_tsum_symmetricIco_sub_eq` that if we swap the
order of the sum it tends to `0` instead. -/
lemma tendsto_tsum_one_div_linear_sub_succ_eq :
    Tendsto (fun N : ℕ+ ↦ ∑ n ∈ Ico (-N : ℤ) N,
    ∑' m : ℤ, (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1))) atTop (𝓝 (-2 * π * I / z)) := by
  have (N : ℕ+) :
      ∑ n ∈ Ico (-N : ℤ) N, ∑' m : ℤ , (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1))
      = ∑' m : ℤ , ∑ n ∈ Ico (-N : ℤ) N, (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1)) := by
    rw [Summable.tsum_finsetSum (fun i hi ↦ ?_)]
    apply (summable_left_one_div_linear_sub_one_div_linear z i (i + 1)).congr
    grind
  simp only [telescope_aux, aux_tsum_identity_1] at this
  rw [funext this, show -2 * π * I / z = 0 + -2 * π * I / z by ring]
  apply Tendsto.add
  · simpa [← PNat.tendsto_comp_val_iff] using
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)).const_mul (-2)
  · simpa only [aux_tsum_identity_2, ← PNat.tendsto_comp_val_iff] using aux_tendsto_tsum z

/- These are the two key lemmas, which show that swapping the order of summation gives
results differing by the term `-2 * π * I / z`. -/
lemma tsum_symmetricIco_tsum_sub_eq :
    ∑'[symmetricIco ℤ] n : ℤ, ∑' m : ℤ, (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1)) =
    -2 * π * I / z := by
  apply HasSum.tsum_eq
  simpa [HasSum, ← Nat.map_cast_int_atTop, ← PNat.tendsto_comp_val_iff]
    using tendsto_tsum_one_div_linear_sub_succ_eq z

lemma tsum_tsum_symmetricIco_sub_eq :
    ∑' m : ℤ, ∑'[symmetricIco ℤ] n : ℤ, (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1)) = 0 := by
  convert tsum_zero
  exact tsum_symmetricIco_linear_sub_linear_add_one_eq_zero z _

end Auxiliary

end EisensteinSeries
