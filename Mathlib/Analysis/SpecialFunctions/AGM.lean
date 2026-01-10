/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Real.Sqrt

/-!
# The arithmetic-geometric mean

Starting with two nonnegative real numbers, repeatedly replace them with their arithmetic and
geometric means. By the AM-GM inequality, the smaller number (geometric mean) will monotonically
increase and the larger number (arithmetic mean) will monotonically decrease.

The two monotone sequences converge to the same limit – the arithmetic-geometric mean (AGM).
This file defines the AGM in the `NNReal` namespace and proves some of its basic properties.

## References

* https://en.wikipedia.org/wiki/Arithmetic–geometric_mean
-/

@[expose] public section

namespace NNReal

/-- The AM–GM inequality for two `NNReal`s, with means in canonical form. -/
lemma sqrt_mul_le_half_add (x y : ℝ≥0) : sqrt (x * y) ≤ (x + y) / 2 := by
  rw [sqrt_le_iff_le_sq, div_pow, le_div_iff₀' (by positivity), ← mul_assoc]
  norm_num
  exact four_mul_le_sq_add ..

open Function Filter Topology

/-- `agmSequences x y` returns the pair of sequences converging to the arithmetic-geometric mean
starting from `x` and `y`, with the sequence of geometric means first. -/
noncomputable def agmSequences (x y : ℝ≥0) : (ℕ → ℝ≥0) × (ℕ → ℝ≥0) :=
  Equiv.arrowProdEquivProdArrow _ _ _ ((fun p ↦ (sqrt (p.1 * p.2), (p.1 + p.2) / 2))^[·] (x, y))

variable {x y : ℝ≥0} {m n : ℕ}

lemma agmSequences_fst_comm : (agmSequences x y).1 (n + 1) = (agmSequences y x).1 (n + 1) := by
  simp [agmSequences, mul_comm, add_comm]

lemma agmSequences_snd_comm : (agmSequences x y).2 (n + 1) = (agmSequences y x).2 (n + 1) := by
  simp [agmSequences, mul_comm, add_comm]

lemma agmSequences_fst_le_snd : (agmSequences x y).1 (n + 1) ≤ (agmSequences x y).2 (n + 1) := by
  simp_rw [agmSequences, Equiv.arrowProdEquivProdArrow_apply, iterate_succ', comp_apply]
  exact sqrt_mul_le_half_add ..

lemma agmSequences_fst_monotone : Monotone fun n ↦ (agmSequences x y).1 (n + 1) := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  nth_rw 2 [agmSequences]
  simp_rw [Equiv.arrowProdEquivProdArrow_apply]
  rw [iterate_succ', comp_apply]
  change _ ≤ sqrt ((agmSequences x y).1 (n + 1) * (agmSequences x y).2 (n + 1))
  nth_rw 1 [sqrt_mul, ← mul_self_sqrt ((agmSequences x y).1 (n + 1))]
  exact mul_le_mul_right (sqrt_le_sqrt.mpr agmSequences_fst_le_snd) _

lemma agmSequences_snd_antitone : Antitone fun n ↦ (agmSequences x y).2 (n + 1) := by
  refine antitone_nat_of_succ_le fun n ↦ ?_
  nth_rw 1 [agmSequences]
  simp_rw [Equiv.arrowProdEquivProdArrow_apply]
  rw [iterate_succ', comp_apply]
  change ((agmSequences x y).1 (n + 1) + (agmSequences x y).2 (n + 1)) / 2 ≤ _
  rw [add_div]
  nth_rw 2 [← add_halves ((agmSequences x y).2 (n + 1))]
  exact add_le_add_left (div_le_div_of_nonneg_right agmSequences_fst_le_snd zero_le_two) _

/-- All geometric means are upper-bounded by all arithmetic means. -/
lemma agmSequences_fst_le_agmSequences_snd :
    (agmSequences x y).1 (m + 1) ≤ (agmSequences x y).2 (n + 1) := by
  rcases le_or_gt m n with h | h
  · exact (agmSequences_fst_monotone h).trans agmSequences_fst_le_snd
  · exact agmSequences_fst_le_snd.trans (agmSequences_snd_antitone h.le)

lemma dist_agmSequences_le_two_inv_pow_mul :
    dist ((agmSequences x y).1 n) ((agmSequences x y).2 n) ≤ 2⁻¹ ^ n * dist x y := by
  induction n with
  | zero => simp [agmSequences]
  | succ n ih =>
    set p := (agmSequences x y).1 n
    set q := (agmSequences x y).2 n
    simp_rw [agmSequences, Equiv.arrowProdEquivProdArrow_apply, iterate_succ', comp_apply]
    change dist (sqrt (p * q)) ((p + q) / 2) ≤ _
    rw [dist_comm, dist_eq, ← NNReal.coe_sub (sqrt_mul_le_half_add ..), abs_eq]
    calc
      _ ≤ ((p + q) / 2 - min p q).toReal := by
        gcongr
        rw [← mul_self_sqrt (min p q), sqrt_mul]
        gcongr
        · exact min_le_left ..
        · exact min_le_right ..
      _ = 2⁻¹ * dist p q := by
        rw [← add_halves (min p q), ← add_div, ← tsub_div, NNReal.coe_div, NNReal.coe_two,
          div_eq_inv_mul]
        congr
        rcases le_or_gt p q with h | h
        · rw [min_eq_left h, add_tsub_add_eq_tsub_left, dist_comm, dist_eq,
            abs_of_nonneg (by simpa), NNReal.coe_sub h]
        · rw [min_eq_right h.le, add_tsub_add_eq_tsub_right, dist_eq,
            abs_of_nonneg (by simpa using h.le), NNReal.coe_sub h.le]
      _ ≤ _ := by
        rw [pow_succ', mul_assoc]
        gcongr

/-- The arithmetic and geometric means tend to each other. -/
lemma tendsto_dist_agmSequences_atTop_zero :
    Tendsto (fun n ↦ dist ((agmSequences x y).1 n) ((agmSequences x y).2 n)) atTop (𝓝 0) := by
  refine squeeze_zero (fun _ ↦ dist_nonneg) (fun _ ↦ dist_agmSequences_le_two_inv_pow_mul) ?_
  rw [← zero_mul (dist x y)]
  exact (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).mul_const _

/-- The arithmetic-geometric mean of two `NNReal`s, defined as the infimum of arithmetic means. -/
noncomputable def agm (x y : ℝ≥0) : ℝ≥0 :=
  ⨅ n, (agmSequences x y).2 (n + 1)

lemma agm_comm : agm x y = agm y x := by
  unfold agm
  conv_rhs =>
    enter [1, n]
    rw [agmSequences_snd_comm]

lemma agm_eq_ciInf : agm x y = ⨅ n, (agmSequences x y).2 (n + 1) := rfl

lemma agm_le_agmSequences_snd : agm x y ≤ (agmSequences x y).2 (n + 1) := ciInf_le' _ n

lemma agm_le_max : agm x y ≤ max x y := by
  rcases le_or_gt x y with h | h
  · rw [max_eq_right h]
    apply (agm_le_agmSequences_snd (n := 0)).trans
    simp_rw [agmSequences, Equiv.arrowProdEquivProdArrow_apply, zero_add, iterate_one, add_div]
    nth_rw 2 [← add_halves y]
    gcongr
  · rw [max_eq_left h.le]
    apply (agm_le_agmSequences_snd (n := 0)).trans
    simp_rw [agmSequences, Equiv.arrowProdEquivProdArrow_apply, zero_add, iterate_one, add_div]
    nth_rw 2 [← add_halves x]
    gcongr

/-- The AGM is also the supremum of the geometric means. -/
lemma agm_eq_ciSup : agm x y = ⨆ n, (agmSequences x y).1 (n + 1) := by
  sorry

lemma agmSequences_fst_le_agm : (agmSequences x y).1 (n + 1) ≤ agm x y := by
  rw [agm_eq_ciSup]
  refine le_ciSup (f := fun n ↦ (agmSequences x y).1 (n + 1)) ?_ n
  rw [bddAbove_def]
  use (x.agmSequences y).2 (0 + 1)
  simp_rw [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  exact fun _ ↦ agmSequences_fst_le_agmSequences_snd

lemma min_le_agm : min x y ≤ agm x y := by
  rcases le_or_gt x y with h | h
  · rw [min_eq_left h]
    refine le_trans ?_ (agmSequences_fst_le_agm (n := 0))
    simp_rw [agmSequences, Equiv.arrowProdEquivProdArrow_apply, zero_add, iterate_one, sqrt_mul]
    nth_rw 1 [← mul_self_sqrt x]
    gcongr
  · rw [min_eq_right h.le]
    refine le_trans ?_ (agmSequences_fst_le_agm (n := 0))
    simp_rw [agmSequences, Equiv.arrowProdEquivProdArrow_apply, zero_add, iterate_one, sqrt_mul]
    nth_rw 1 [← mul_self_sqrt y]
    gcongr

lemma agm_self : agm x x = x := by
  apply le_antisymm
  · nth_rw 3 [← max_self x]
    exact agm_le_max
  · nth_rw 1 [← min_self x]
    exact min_le_agm

lemma agm_zero_left : agm 0 x = 0 :=
  sorry

lemma agm_zero_right : agm x 0 = 0 := by
  rw [agm_comm, agm_zero_left]

/-- The AGM is unchanged if `x` and `y` are replaced by their geometric and arithmetic means. -/
lemma agm_eq_agm_geometric_arithmetic_means : agm x y = agm (sqrt (x * y)) ((x + y) / 2) := by
  sorry

lemma agm_mem_uIoo_of_pos_of_ne (hx : 0 < x) (hy : 0 < y) (h : x ≠ y) : agm x y ∈ Set.uIoo x y := by
  sorry

/-- The AGM distributes over multiplication. -/
lemma agm_mul_distrib {k : ℝ≥0} : agm (k * x) (k * y) = k * agm x y := by
  unfold agm agmSequences
  simp_rw [mul_iInf, Equiv.arrowProdEquivProdArrow_apply]
  congr! with n
  suffices (fun p ↦ (sqrt (p.1 * p.2), (p.1 + p.2) / 2))^[n + 1] (k * x, k * y) =
      k • (fun p ↦ (sqrt (p.1 * p.2), (p.1 + p.2) / 2))^[n + 1] (x, y) by
    simpa using congr_arg Prod.snd this
  set m := n + 1
  induction m with
  | zero => simp
  | succ m ih =>
    simp_rw [iterate_succ', comp_apply, ih, Prod.smul_mk, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    congr
    · rw [mul_mul_mul_comm, sqrt_mul, sqrt_mul_self]
    · rw [← mul_add, mul_div_assoc]

end NNReal
