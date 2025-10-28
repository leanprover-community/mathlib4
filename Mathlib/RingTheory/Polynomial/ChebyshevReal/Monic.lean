/-
Copyright (c) 2020 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
import Mathlib.RingTheory.Polynomial.ChebyshevReal.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.Algebra.Polynomial

/-!
# Chebyshev polynomials over the reals: leading coefficient

* Chebyshev polynomials minimize deviation from zero,
  following proof in https://math.stackexchange.com/a/978145/1277

## Main statements

* `min_abs_of_monic` provides a lower bound on the maximum of |P(x)| on [-1, 1] for monic P
* `min_abs_of_monic_extrema` characterizes the equality case
-/

namespace Polynomial

open Finset

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι] {s : Finset ι}

theorem C_prod (c : ι → F) :
  ∏ i ∈ s, C (c i) = C (∏ i ∈ s, (c i)) := by
  induction s using Finset.induction
  case empty => simp
  case insert a t ha hind =>
    rw [prod_insert ha, hind, prod_insert ha, C_mul]

theorem degree_of_linear_product (c : ι → F) :
  (∏ i ∈ s, (X - C (c i))).degree = ↑(s.card) := by
  induction s using Finset.induction
  case empty => simp
  case insert a t ha hind =>
  rw [prod_insert ha, card_insert_of_notMem ha]
  rw [degree_mul, hind, degree_X_sub_C, add_comm]
  push_cast; rfl

theorem coeff_of_linear_product (c : ι → F) :
  (∏ i ∈ s, (X - C (c i))).coeff #s = 1 := by
  induction s using Finset.induction
  case empty => simp
  case insert a t ha hind =>
  rw [prod_insert ha, card_insert_of_notMem ha]
  rw [sub_mul, coeff_sub, coeff_X_mul, hind, coeff_C_mul]
  suffices (∏ i ∈ t, (X - C (c i))).coeff (#t + 1) = 0 by simp [this]
  apply coeff_eq_zero_of_degree_lt
  rw [degree_of_linear_product]
  apply Nat.cast_lt.mpr
  omega

end Polynomial

namespace Lagrange

open Polynomial

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]

theorem interpolate_poly [DecidableEq F] {s : Finset ι} {v : ι → F} (hvs : Set.InjOn v s)
  {P : Polynomial F} (hP : P.degree < s.card) :
  (interpolate s v) (fun (i : ι) => P.eval (v i)) = P := by
  let t : Finset F := s.image v
  have ht : t.card = s.card := Finset.card_image_iff.mpr hvs
  apply eq_of_degrees_lt_of_eval_finset_eq t
  · rw [ht]
    apply degree_interpolate_lt _ hvs
  · rw [ht]
    exact hP
  · intro x hx
    obtain ⟨i, hi, hx⟩ := Finset.mem_image.mp hx
    rw [← hx, eval_interpolate_at_node _ hvs hi]

theorem basis_topCoeff {s : Finset ι} {v : ι → F} {i : ι} (hi : i ∈ s) :
  (Lagrange.basis s v i).coeff (s.card - 1) = (∏ j ∈ s.erase i, ((v i) - (v j)))⁻¹ := by
  rw [Lagrange.basis]
  unfold basisDivisor
  rw [Finset.prod_mul_distrib, ← Finset.prod_inv_distrib, C_prod, coeff_C_mul]
  suffices s.card - 1 = (s.erase i).card by
    rw [this, coeff_of_linear_product, mul_one]
  rw [Finset.card_erase_of_mem hi]

theorem interpolate_leadingCoeff [DecidableEq F] (s : Finset ι) (v : ι → F) (hvs : Set.InjOn v s)
  {P : Polynomial F} (hP : s.card = P.degree + 1) :
  P.leadingCoeff = ∑ i ∈ s, (P.eval (v i)) / ∏ j ∈ s.erase i, ((v i) - (v j)) := by
  have P_degree : P.degree = ↑(s.card - 1) := by
    cases h : P.degree
    case bot => rw [h] at hP; simp at hP
    case coe d => rw [h] at hP; simp [ENat.coe_inj.mp hP]; rfl
  have P_natDegree : P.natDegree = s.card - 1 := natDegree_eq_of_degree_eq_some P_degree
  have s_card : s.card > 0 := by
    by_contra! h
    have : s.card = 0 := by omega
    rw [this, P_degree] at hP
    have := ENat.coe_inj.mp hP
    dsimp at this
    omega
  have hP' : P.degree < s.card := by rw [P_degree, Nat.cast_lt]; omega
  rw [leadingCoeff, P_natDegree]
  rw (occs := [1]) [← interpolate_poly hvs hP']
  rw [interpolate_apply, finset_sum_coeff]
  congr! with i hi
  rw [coeff_C_mul, basis_topCoeff hi]
  field_simp

end Lagrange

namespace Polynomial.Chebyshev

open Polynomial
open Real

private lemma node_in_range {n j : ℕ} (hn : n ≠ 0) (hj : j ≤ n) :
  j * π / n ∈ Set.Icc 0 π := by
  constructor
  · positivity
  · calc j * π / n ≤ n * π / n := by gcongr
    _ = π := by rw [mul_div_assoc, mul_div_cancel₀]; convert hn; exact Nat.cast_eq_zero

private lemma node_product_positive {n : ℕ} {i : ℕ} (hi : i ∈ Finset.Icc 0 n) :
  (-1)^i * ∏ j ∈ (Finset.Icc 0 n).erase i, (cos (i * π / n) - cos (j * π / n)) > 0 := by
  by_cases n = 0
  case pos hn =>
    subst hn
    have : i = 0 := by simp at hi; exact hi
    subst i
    simp
  case neg hn =>
  replace hi := Finset.mem_Icc.mp hi
  have : (∏ j ∈ Finset.Ico 0 i, ((-1) * (cos (i * π / n) - cos (j * π / n)))) *
    ∏ j ∈ Finset.Ioc i n, (cos (i * π / n) - cos (j * π / n)) > 0 := by
    apply mul_pos
    case ha =>
      apply Finset.prod_pos
      intro j hj
      replace hj := Finset.mem_Ico.mp hj
      rw [neg_one_mul, neg_sub]
      apply sub_pos_of_lt
      apply Real.strictAntiOn_cos
      · apply node_in_range <;> omega
      · apply node_in_range <;> omega
      gcongr
      exact hj.2
    case hb =>
      apply Finset.prod_pos
      intro j hj
      replace hj := Finset.mem_Ioc.mp hj
      apply sub_pos_of_lt
      apply Real.strictAntiOn_cos
      · apply node_in_range <;> omega
      · apply node_in_range <;> omega
      gcongr
      exact hj.1
  convert this using 1
  rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.Ico_zero_eq_range, Finset.card_range,
    mul_assoc, ← Nat.Ico_zero_eq_range]
  congr
  have : (Finset.Icc 0 n).erase i = (Finset.Ico 0 i) ∪ Finset.Ioc i n := by
    ext j
    rw [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union, Finset.mem_Ico, Finset.mem_Ioc]
    constructor
    case mp =>
      intro hj
      by_cases j < i
      case pos => left; omega
      case neg => right; omega
    case mpr => intro hj; cases hj <;> omega
  rw [this, Finset.prod_union]
  apply Finset.disjoint_left.mpr
  intro j hj₁
  by_contra! hj₂
  replace hj₁ := Finset.mem_Ico.mp hj₁
  replace hj₂ := Finset.mem_Ioc.mp hj₂
  linarith

private lemma convex_combination {n : ℕ} (hn : n ≠ 0)
  {P : ℝ[X]} (hP : P.degree = n) :
  ∃ (c : ℕ → ℝ),
    (∀ i ∈ Finset.Icc 0 n, 0 < c i) ∧
    (∑ i ∈ Finset.Icc 0 n, c i = 2^(n - 1)) ∧
    (∑ i ∈ Finset.Icc 0 n, (c i) * ((-1)^i * P.eval (cos (i * π / n))) = P.leadingCoeff) := by
  use fun i => ((-1)^i * ∏ j ∈ (Finset.Icc 0 n).erase i, (cos (i * π / n) - cos (j * π / n)))⁻¹
  constructor
  · intro i hi
    apply inv_pos.mpr
    exact node_product_positive hi
  have hinj : Set.InjOn (fun (i : ℕ) => cos (i * π / n)) (Finset.Icc 0 n) := by
    intro i hi j hj h
    dsimp at h
    suffices i * π / n = j * π / n by field_simp at this; norm_cast at this
    apply injOn_cos
    · apply node_in_range hn; simp at hi; exact hi
    · apply node_in_range hn; simp at hj; exact hj
    exact h
  constructor
  · trans ∑ i ∈ Finset.Icc 0 n, (T ℝ n).eval (cos (i * π / n)) /
      ∏ j ∈ (Finset.Icc 0 n).erase i, (cos (i * π / n) - cos (j * π / n))
    · congr with i
      have : (T ℝ n).eval (cos (i * π / n)) = (-1)^i := by
        convert T_node_eval (show (n : ℤ) ≠ 0 by omega) i
      rw [this, mul_inv, ← inv_pow, ← div_eq_mul_inv]
      congr
      norm_num
    · rw [← Lagrange.interpolate_leadingCoeff]
      · simp
      · exact hinj
      · simp
  · rw [Lagrange.interpolate_leadingCoeff (Finset.Icc 0 n) (fun i => cos (i * π / n))]
    · congr with i
      rw [mul_comm, ← div_eq_mul_inv, mul_div_mul_left]
      simp
    · exact hinj
    · simp [hP]

theorem bddAbove_poly_interval (P : ℝ[X]) :
  BddAbove { abs (P.eval x) | x ∈ Set.Icc (-1) 1 } := by
  have hK : IsCompact (Set.Icc (-1 : ℝ) 1) := isCompact_Icc
  have hcont : ContinuousOn (fun x => abs (P.eval x)) (Set.Icc (-1) 1) := by
    apply Continuous.continuousOn
    have := P.continuous
    continuity
  change BddAbove ((fun x => abs (P.eval x)) '' Set.Icc (-1) 1)
  exact IsCompact.bddAbove_image hK hcont

private lemma pointwise_bound (P : ℝ[X]) (n i : ℕ) :
  (-1)^i * P.eval (cos (i * π / n)) ≤ sSup { abs (P.eval x) | x ∈ Set.Icc (-1) 1 } := by
  suffices abs (P.eval (cos (i * π / n))) ≤ sSup { abs (P.eval x) | x ∈ Set.Icc (-1) 1 } by
    cases neg_one_pow_eq_or ℝ i with
    | inl h => rw [h, one_mul]; exact (abs_le'.mp this).1
    | inr h => rw [h, neg_one_mul]; exact (abs_le'.mp this).2
  apply le_csSup (bddAbove_poly_interval P)
  rw [Set.mem_setOf_eq]
  use cos (i * π / n)
  constructor
  · apply Set.mem_Icc.mpr
    apply abs_le.mp
    exact abs_cos_le_one _
  rfl

theorem min_abs_of_monic {n : ℕ} (hn : n ≠ 0)
  (P : ℝ[X]) (Pdeg : P.degree = n) (Pmonic : P.Monic) :
  1/2^(n - 1) ≤ sSup { abs (P.eval x) | x ∈ Set.Icc (-1) 1 } := by
  set M := sSup { abs (P.eval x) | x ∈ Set.Icc (-1) 1 }
  suffices 1 ≤ M * 2^(n - 1) by calc
    1/2^(n - 1) ≤ (M * 2^(n - 1))/2^(n - 1) := by gcongr
    _ = M := by rw [mul_div_assoc, div_self, mul_one]; simp
  obtain ⟨c, hpos, hsum, hform⟩ := convex_combination hn Pdeg
  calc 1 = P.leadingCoeff := Pmonic.symm
    _ = ∑ i ∈ Finset.Icc 0 n, (c i) * ((-1)^i * P.eval (cos (i * π / n))) := hform.symm
    _ ≤ ∑ i ∈ Finset.Icc 0 n, (c i) * M := by
      gcongr with i hi
      · exact le_of_lt (hpos i hi)
      exact pointwise_bound P n i
    _ = M * 2^(n - 1) := by
      rw [← Finset.sum_mul, mul_comm, hsum]

noncomputable def normalized_T (n : ℕ) : ℝ[X] := (Polynomial.C (1 / 2^(n - 1))) * T ℝ n

@[simp]
theorem normalized_T_eval (n : ℕ) (x : ℝ) :
  (normalized_T n).eval x = ((T ℝ n).eval x) / 2^(n - 1) := by
  unfold normalized_T
  rw [eval_mul, eval_C]
  field_simp

theorem min_abs_of_monic_extrema {n : ℕ} (hn : n ≠ 0)
  (P : ℝ[X]) (Pdeg : P.degree = n) (Pmonic : P.Monic) :
  1/2^(n - 1) = sSup { abs (P.eval x) | x ∈ Set.Icc (-1) 1 } ↔ P = normalized_T n := by
  constructor
  case mp =>
    intro h
    obtain ⟨c, hpos, hsum, hform⟩ := convex_combination hn Pdeg
    have hnonneg : ∀ i ∈ Finset.Icc 0 n,
      0 ≤ (c i) * (1/2^(n - 1) - (-1)^i * P.eval (cos (i * π / n))) := by
      intro i hi
      apply mul_nonneg (le_of_lt (hpos i hi))
      have := pointwise_bound P n i
      linarith
    have hsum : ∑ i ∈ Finset.Icc 0 n,
      (c i) * (1/2^(n - 1) - (-1)^i * P.eval (cos (i * π / n))) = 0 := by
      trans ∑ i ∈ Finset.Icc 0 n,
        ((c i) * (1/2^(n - 1)) - (c i) * ((-1)^i * P.eval (cos (i * π / n))))
      · congr with i; rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, hform, Pmonic, mul_div_cancel₀]
      · norm_num
      positivity
    have heq := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
    apply eq_of_degrees_lt_of_eval_finset_eq (T_extrema n)
    · rw [Pdeg, T_extrema_card]; norm_cast; omega
    · unfold normalized_T
      rw [degree_C_mul, T_degree_real, T_extrema_card]
      · norm_cast; omega
      positivity
    intro x hx
    unfold T_extrema at hx
    obtain ⟨i, hi, hx⟩ := Finset.mem_image.mp hx
    norm_cast at hx
    rw [← hx, normalized_T_eval]
    have : (T ℝ n).eval (cos (i * π / n)) = (-1)^i := by
      convert T_node_eval (show (n : ℤ) ≠ 0 by omega) i
    rw [this]
    have := eq_of_sub_eq_zero ((mul_eq_zero_iff_left (ne_of_gt (hpos i hi))).mp (heq i hi))
    rw [div_eq_mul_inv (b := 2^(n-1)), ← one_div, this, ← mul_assoc, ← sq, ← pow_mul]
    simp
  case mpr =>
    intro hP
    subst hP
    apply eq_of_le_of_ge
    · apply le_csSup (bddAbove_poly_interval _)
      rw [Set.mem_setOf_eq]
      use 1
      constructor
      · simp
      rw [normalized_T_eval, T_eval_one]
      simp
    · apply csSup_le
      · use abs ((normalized_T n).eval 1)
        rw [Set.mem_setOf_eq]
        use 1
        simp
      · intro y
        rw [Set.mem_setOf_eq]
        rintro ⟨x, hx, hy⟩
        rw [← hy, normalized_T_eval, abs_div]
        have : (0 : ℝ) < 2^(n - 1) := by positivity
        rw [abs_of_pos this]
        gcongr
        apply T_bounded_of_bounded'
        apply abs_le.mpr
        exact Set.mem_Icc.mp hx

end Polynomial.Chebyshev
