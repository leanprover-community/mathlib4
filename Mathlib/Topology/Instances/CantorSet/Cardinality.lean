/-
Copyright (c) 2025 Francesco Vercellesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Vercellesi
-/
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Topology.Instances.CantorSet.Basic

/-!
# Cardinality of the Ternary Cantor Set

This file proves that the ternary Cantor set has the cardinality of the continuum.

## Main results

* `cantor_set_continuum_card`: The ternary Cantor set has the cardinality of the continuum.
-/

open Cardinal

variable (χ : ℕ → ({0, 2} : Set ℤ))

/-- The infinite series which maps bijectively binary sequences
to elements of the ternary Cantor set -/
noncomputable def cantorSet_series :=
  fun i ↦ χ i * (1 / 3 : ℝ) ^ i * (1 / 3)

lemma partial_sums_cantorSet_series_in_cantorSet (n : ℕ) :
    ∑ i ∈ Finset.range n, cantorSet_series χ i ∈ cantorSet := by
  revert χ
  induction n with
  | zero =>
    simp [zero_mem_cantorSet]
  | succ n ih =>
    intro χ
    apply (Subtype.coe_prop (χ 0)).elim
    all_goals
      intro
      simp_all only [Finset.sum_range_succ', cantorSet_series, Int.cast_zero,
        zero_mul, add_zero, Set.mem_singleton_iff,
        Finset.sum_range_succ', Int.cast_ofNat, pow_zero, mul_one]
      rw [←Finset.sum_mul]
      ring_nf
      first | apply third_in_cantorSet | apply third_plus_two_thirds_in_cantorSet
      exact ih (fun i ↦ χ (1 + i))

lemma cantorSet_series_summable : Summable (cantorSet_series χ) := by
  have summable_geo : Summable (fun i ↦ 2 / 3 * (1 / 3 : ℝ) ^ i) := by
    apply Summable.mul_left
    exact summable_geometric_of_lt_one (by simp) (by norm_num)
  refine Summable.of_nonneg_of_le ?_ ?_ summable_geo
  all_goals
    intro i
    apply (Subtype.coe_prop (χ i)).elim <;>
      (simp_all [cantorSet_series]; try ring_nf; try field_simp; try (intros; rfl))

/-- For any given binary sequence, its series converges to an element of the ternary Cantor set -/
lemma cantorSet_series_in_cantorSet : tsum (cantorSet_series χ) ∈ cantorSet := by
  have ⟨l, hl⟩ := cantorSet_series_summable χ
  have partial_sums_cauchy : CauchySeq (fun n ↦ ∑ i ∈ Finset.range n, cantorSet_series χ i) := by
    apply Filter.Tendsto.cauchySeq (x := l)
    exact (Summable.hasSum_iff_tendsto_nat (cantorSet_series_summable χ)).mp hl
  have ⟨l', ⟨_, hl'⟩⟩ := cauchySeq_tendsto_of_isComplete
    isComplete_cantorSet
    (partial_sums_cantorSet_series_in_cantorSet χ)
    partial_sums_cauchy
  rw [HasSum.tsum_eq hl]
  rw [Summable.hasSum_iff_tendsto_nat (cantorSet_series_summable χ)] at hl
  rwa [tendsto_nhds_unique hl hl']

/-- For any given binary sequence, the sum of its series as an element of the ternary Cantor set -/
@[simp]
noncomputable def cantorSet_series_sum :=
  Subtype.mk (tsum (cantorSet_series χ)) (cantorSet_series_in_cantorSet χ)

/-- `cantorSet_series_sum` is an injective function -/
lemma sum_of_cantorSet_series_injective : Function.Injective cantorSet_series_sum := by
  have diff (χ₁ χ₂ : _) : χ₁ ≠ χ₂ → cantorSet_series_sum χ₁ ≠ cantorSet_series_sum χ₂ := by
    intro h
    let n := Nat.find (Function.ne_iff.mp h)
    have hn := Nat.find_spec (Function.ne_iff.mp h)
    simp only [cantorSet_series_sum, ne_eq, Subtype.mk.injEq]
    rw [←Summable.sum_add_tsum_nat_add (n + 1) (cantorSet_series_summable χ₁)]
    rw [←Summable.sum_add_tsum_nat_add (n + 1) (cantorSet_series_summable χ₂)]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have first_eq :
        ∑ x ∈ Finset.range n, cantorSet_series χ₁ x =
        ∑ x ∈ Finset.range n, cantorSet_series χ₂ x := by
      refine Finset.sum_congr rfl ?_
      have (x : ℕ) (hx : x < n) :=
        Subtype.ext_iff.mp (not_ne_iff.mp (Nat.find_min (Function.ne_iff.mp h) hx))
      simp_all [cantorSet_series]
    rw [add_assoc, add_assoc, first_eq, add_right_inj _]
    rw [←sub_eq_zero, sub_add_eq_sub_sub, add_sub_right_comm, add_sub_assoc]
    rw [←eq_neg_iff_add_eq_zero]
    apply (fun h x ↦ h (congrArg abs x) : |_| ≠ |_| → _ ≠ _)
    have first_ge_two_thirds :
        |cantorSet_series χ₁ n - cantorSet_series χ₂ n| ≥ 2 / 3 * (1 / 3) ^ n := by
      simp only [cantorSet_series, one_div, inv_pow]
      rw [←mul_sub_right_distrib, abs_mul, ←mul_sub_right_distrib, abs_mul]
      rw [(by aesop : |(3 : ℝ)⁻¹| = 3⁻¹), (by aesop : |((3 : ℝ) ^ n)⁻¹| = ((3 : ℝ) ^ n)⁻¹)]
      have eq : |(χ₁ n : ℝ) - ↑↑(χ₂ n)| = 2 := by
        match (Subtype.coe_prop (χ₁ n)), (Subtype.coe_prop (χ₂ n)) with
        | Or.inl hχ₁, Or.inl hχ₂ | Or.inr hχ₁, Or.inr hχ₂ =>
          exact False.elim (hn (Subtype.ext (Eq.trans hχ₁ hχ₂.symm)))
        | Or.inr hχ₁, Or.inl hχ₂ | Or.inl hχ₁, Or.inr hχ₂ =>
          simp_all
      rw [eq]
      linarith
    have tail_le_third :
        |∑' (i : ℕ), cantorSet_series χ₂ (i + (n + 1))
        - ∑' (i : ℕ), cantorSet_series χ₁ (i + (n + 1))| ≤ 1 / 3 * (1 / 3) ^ n := by
      simp only [cantorSet_series]
      rw [tsum_mul_right, tsum_mul_right]
      ring_nf
      conv in (occs := 1) (_ * _ * _) => rw [mul_right_comm]
      conv in (occs := 3) (_ * _ * _) => rw [mul_assoc, mul_right_comm, ←mul_assoc]
      conv in (occs := 1) (∑' _, _) => rw [tsum_mul_right]
      conv in (occs := 2) (∑' _, _) => rw [tsum_mul_right]
      rw [(by ring : ((-1 : ℝ) / 3) = -(1 / 3))]
      rw [mul_neg, ←sub_eq_add_neg, ←sub_mul, ←sub_mul, abs_mul, abs_mul]
      rw [(by aesop : |(1 : ℝ) / 3| = (1 : ℝ) / 3),
        (by aesop : |(((1 : ℝ) / 3) ^ n)| = (((1 : ℝ) / 3) ^ n))]
      simp only [one_div, inv_pow, inv_pos, Nat.ofNat_pos, mul_le_mul_iff_left₀, pow_pos,
        mul_le_iff_le_one_left]
      have merge_sums := Summable.tsum_sub
        (cantorSet_series_summable (fun i ↦ χ₂ (1 + i + n)))
        (cantorSet_series_summable (fun i ↦ χ₁ (1 + n + i)))
      simp only [cantorSet_series, one_div, inv_pow] at merge_sums
      rw [←merge_sums]
      simp only [←sub_mul]
      let χ₃ : ℕ → ({0, 2} : Set ℤ) := fun i ↦ Subtype.mk |χ₂ (1 + i + n) - χ₁ (1 + n + i)| <| by
        apply (Subtype.coe_prop (χ₁ (1 + n + i))).elim <;>
          apply (Subtype.coe_prop (χ₂ (1 + i + n))).elim <;>
            simp_all
      have eq₃ :
            (fun i ↦ |(χ₂ (1 + i + n) : ℝ) - χ₁ (1 + n + i)| * (1 / 3) ^ i * (1 / 3)) =
            (fun i ↦ cantorSet_series χ₃ i) := by
          simp [χ₃, cantorSet_series]
      have norm_diff_summable :
          Summable
          fun i ↦ ‖((χ₂ (1 + i + n) : ℝ) - (χ₁ (1 + n + i)))  * (1 / 3 : ℝ) ^ i * (1 / 3)‖ := by
        simp only [Real.norm_eq_abs, abs_mul]
        conv =>
          arg 1; intro n
          rw [(by aesop : |(1 : ℝ) / 3| = (1 : ℝ) / 3),
            (by aesop : |(((1 : ℝ) / 3) ^ n)| = (((1 : ℝ) / 3) ^ n))]
        rw [eq₃]
        exact cantorSet_series_summable χ₃
      have le_abs := norm_tsum_le_tsum_norm norm_diff_summable
      simp only [one_div, inv_pow, Real.norm_eq_abs, norm_mul, norm_inv, norm_pow] at le_abs
      calc
        _ ≤ _ := le_abs
        _ ≤ _ := by
          conv in (_ * _ * _) =>
            rw [(by aesop : |(3 : ℝ)|⁻¹ = 1 / 3), (by aesop : (|(3 : ℝ)| ^ i)⁻¹ = (1 / 3) ^ i)]
          rw [eq₃]
          exact (cantorSet_subset_unitInterval (cantorSet_series_in_cantorSet χ₃)).right
    have diseq : (1 : ℝ) / 3 * (1 / 3) ^ n < 2 / 3 * (1 / 3) ^ n := by
      simp
      linarith
    simp only [neg_sub]
    apply ne_of_gt
    calc
      _ ≤ _ := tail_le_third
      _ < _ := diseq
      _ ≤ _ := first_ge_two_thirds
  exact Function.injective_iff_pairwise_ne.mpr diff

/-- The ternary Cantor set has the cardinality of the continuum -/
theorem cantor_set_continuum_card : #cantorSet = continuum := by
  apply le_antisymm
  · rw [←Cardinal.mk_real]
    exact Cardinal.mk_set_le cantorSet
  · have := Cardinal.mk_le_of_injective sum_of_cantorSet_series_injective
    simp_all
