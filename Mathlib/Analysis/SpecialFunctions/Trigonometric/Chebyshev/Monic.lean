/-
Copyright (c) 2025 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Chebyshev polynomials over the reals: leading coefficient
* Chebyshev polynomials minimize deviation from zero,
  following proof in https://math.stackexchange.com/a/978145/1277
## Main statements
* `min_abs_of_monic` provides a lower bound on the maximum of |P(x)| on [-1, 1] for monic P
* `min_abs_of_monic_extrema` characterizes the equality case
-/

namespace Polynomial.Chebyshev

open Polynomial Real

lemma mem_Icc {n j : ℕ} (hn : n ≠ 0) (hj : j ∈ Finset.range (n + 1)) : j * π / n ∈ Set.Icc 0 π := by
  refine ⟨by positivity, ?_⟩
  · replace hj : (j : ℝ) ≤ n := Finset.mem_range.mp hj |> Nat.le_of_lt_succ |> Nat.cast_le.mpr
    linear_combination (norm := (field_simp; ring_nf; rfl)) (π / n) * hj

lemma prod_pos {n : ℕ} {i : ℕ} (hi : i ∈ Finset.range (n + 1)) :
    0 < (-1) ^ i * ∏ j ∈ (Finset.range (n + 1)).erase i, (cos (i * π / n) - cos (j * π / n)) := by
  by_cases n = 0
  case pos hn => aesop
  case neg hn =>
  have h₁ : 0 < ∏ j ∈ Finset.range i, ((-1) * (cos (i * π / n) - cos (j * π / n))) := by
    apply Finset.prod_pos
    intro j hj
    have : cos (i * π / n) < cos (j * π / n) := by
      apply Real.strictAntiOn_cos (mem_Icc hn (by grind)) (mem_Icc hn hi)
      have : (j : ℝ) < i := by aesop
      linear_combination (π / n) * this
    linarith
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range] at h₁
  have h₂ : 0 < ∏ j ∈ Finset.Ioc i n, (cos (i * π / n) - cos (j * π / n)) := by
    apply Finset.prod_pos
    intro j hj
    have : cos (j * π / n) < cos (i * π / n) := by
      apply Real.strictAntiOn_cos (mem_Icc hn hi) (mem_Icc hn (by grind))
      have : (i : ℝ) < j := by aesop
      linear_combination (π / n) * this
    linarith
  have union : (Finset.range (n + 1)).erase i = (Finset.range i) ∪ Finset.Ioc i n := by grind
  have disjoint : Disjoint (Finset.range i) (Finset.Ioc i n) := by grind [Finset.disjoint_iff_ne]
  rw [union, Finset.prod_union disjoint, ← mul_assoc]
  exact mul_pos h₁ h₂

lemma leadingCoeff_formula {n : ℕ} (hn : n ≠ 0) {P : ℝ[X]} (hP : P.degree = n) :
    ∃ (c : ℕ → ℝ),
    (∀ i ∈ Finset.range (n + 1), 0 < c i) ∧
    (∑ i ∈ Finset.range (n + 1), c i = 2 ^ (n - 1)) ∧
    (∑ i ∈ Finset.range (n + 1), (c i) * ((-1) ^ i * P.eval (cos (i * π / n))) = P.leadingCoeff) :=
    by
  have cos_inj : Set.InjOn (fun (i : ℕ) => cos (i * π / n)) (Finset.range (n + 1)) := by
    refine injOn_cos.comp ?_ (fun i hi => mem_Icc hn hi)
    intro i hi j hj hij
    suffices (i : ℝ) = j by norm_cast at this
    linear_combination (norm := field) (n / π) * hij
  have deg {Q : ℝ[X]} (hQ : Q.degree = n) : (Finset.range (n + 1)).card = Q.degree + 1 := by
    simp [Finset.card_range, hQ]
  use fun i =>
    ((-1) ^ i * ∏ j ∈ (Finset.range (n + 1)).erase i, (cos (i * π / n) - cos (j * π / n)))⁻¹
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · exact fun i hi => prod_pos hi |> inv_pos.mpr
  · have := Lagrange.leadingCoeff_eq_sum cos_inj (deg (degree_T_real n))
    rw [leadingCoeff_T_real, Int.natAbs_natCast] at this
    rw [this]
    congr! 1 with i hi
    dsimp
    have : (T ℝ n).eval (cos (i * π / n)) = (-1) ^ i := by
      have := T_real_eval_at_extremum (Int.ofNat_ne_zero.mpr hn) i
      aesop
    rw [this, mul_inv, ← div_eq_mul_inv, ← inv_pow, inv_neg_one]
  · rw [Lagrange.leadingCoeff_eq_sum cos_inj (deg hP)]
    congr! 1 with i hi
    field

theorem bddAbove (P : ℝ[X]) : BddAbove { |P.eval x| | x ∈ Set.Icc (-1) 1 } :=
  have := P.continuous
  have hcont : ContinuousOn (fun x => |P.eval x|) (Set.Icc (-1) 1) :=
    Continuous.continuousOn (by continuity)
  IsCompact.bddAbove_image isCompact_Icc hcont

lemma P_eval_bound (P : ℝ[X]) (n i : ℕ) :
    (-1) ^ i * P.eval (cos (i * π / n)) ≤ sSup { |P.eval x| | x ∈ Set.Icc (-1) 1 } := by
  suffices |P.eval (cos (i * π / n))| ≤ sSup { |P.eval x| | x ∈ Set.Icc (-1) 1 } by
    cases neg_one_pow_eq_or ℝ i with
    | inl h => rw [h, one_mul]; exact (abs_le'.mp this).1
    | inr h => rw [h, neg_one_mul]; exact (abs_le'.mp this).2
  refine le_csSup (bddAbove P) (Set.mem_setOf.mpr ⟨cos (i * π / n), ⟨?_, rfl⟩⟩)
  exact Set.mem_Icc.mpr <| abs_le.mp <| abs_cos_le_one _

end Polynomial.Chebyshev

@[expose] public section

namespace Polynomial.Chebyshev

open Polynomial Real

theorem min_abs_of_monic {n : ℕ} (hn : n ≠ 0) (P : ℝ[X]) (Pdeg : P.degree = n) (Pmonic : P.Monic) :
    1/2^(n - 1) ≤ sSup { abs (P.eval x) | x ∈ Set.Icc (-1) 1 } := by
  set M := sSup { abs (P.eval x) | x ∈ Set.Icc (-1) 1 }
  suffices 1 ≤ M * 2^(n - 1) by calc
    1/2^(n - 1) ≤ (M * 2^(n - 1))/2^(n - 1) := by gcongr
    _ = M := by rw [mul_div_assoc, div_self, mul_one]; simp
  obtain ⟨c, hpos, hsum, hform⟩ := leadingCoeff_formula hn Pdeg
  calc 1 = P.leadingCoeff := Pmonic.symm
    _ = ∑ i ∈ Finset.range (n + 1), (c i) * ((-1)^i * P.eval (cos (i * π / n))) := hform.symm
    _ ≤ ∑ i ∈ Finset.range (n + 1), (c i) * M := by
      gcongr with i hi
      · exact le_of_lt (hpos i hi)
      exact P_eval_bound P n i
    _ = M * 2^(n - 1) := by
      rw [← Finset.sum_mul, mul_comm, hsum]

/-- `normalized_T n` is `T n` normalized to a monic polynomial. -/
noncomputable def normalized_T (n : ℕ) : ℝ[X] := (Polynomial.C (1 / 2^(n - 1))) * T ℝ n

@[simp]
theorem normalized_T_eval (n : ℕ) (x : ℝ) :
    (normalized_T n).eval x = ((T ℝ n).eval x) / 2^(n - 1) := by
  unfold normalized_T
  rw [eval_mul, eval_C]
  field_simp

theorem min_abs_of_monic_extrema {n : ℕ} (hn : n ≠ 0) (P : ℝ[X])
    (Pdeg : P.degree = n) (Pmonic : P.Monic) :
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
    · rw [Pdeg, card_T_extrema]; norm_cast; omega
    · unfold normalized_T
      rw [degree_C_mul, degree_T_real, card_T_extrema]
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
    · apply le_csSup (bddAbove _)
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
