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

* `le_sup_abs_eval_of_monic` provides a lower bound on the maximum of |P(x)| on [-1, 1] for monic P
* `sup_abs_eval_eq_iff_of_monic` characterizes the equality case
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
  · have := Lagrange.leadingCoeff_eq_sum cos_inj (deg (degree_T ℝ n))
    rw [leadingCoeff_T, Int.natAbs_natCast] at this
    rw [this]
    congr! 1 with i hi
    dsimp
    have : ((n : ℤ) : ℝ) * (i * π / n) = (i : ℤ) * π := by norm_cast; field_simp
    rw [T_real_cos, this, cos_int_mul_pi, zpow_natCast, mul_inv, ← div_eq_mul_inv, ← inv_pow,
      inv_neg_one]
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

theorem le_sup_abs_eval_of_monic {n : ℕ} (hn : n ≠ 0)
    {P : ℝ[X]} (Pdeg : P.degree = n) (Pmonic : P.Monic) :
    1 / 2 ^ (n - 1) ≤ sSup { |P.eval x| | x ∈ Set.Icc (-1) 1 } := by
  suffices 1 ≤ 2 ^ (n - 1) * sSup { |P.eval x| | x ∈ Set.Icc (-1) 1 } by field_simp; assumption
  obtain ⟨c, hpos, hsum, hform⟩ := leadingCoeff_formula hn Pdeg
  calc 1 = P.leadingCoeff := Pmonic.symm
    _ = ∑ i ∈ Finset.range (n + 1), (c i) * ((-1)^i * P.eval (cos (i * π / n))) := hform.symm
    _ ≤ ∑ i ∈ Finset.range (n + 1), (c i) * sSup { |P.eval x| | x ∈ Set.Icc (-1) 1 } := by
      gcongr with i hi
      · exact le_of_lt (hpos i hi)
      · exact P_eval_bound P n i
    _ = 2 ^ (n - 1) * sSup { |P.eval x| | x ∈ Set.Icc (-1) 1 } := by
      rw [← Finset.sum_mul, hsum]

theorem sup_abs_eval_eq_iff_of_monic {n : ℕ} (hn : n ≠ 0) (P : ℝ[X])
    (Pdeg : P.degree = n) (Pmonic : P.Monic) :
     sSup { |P.eval x| | x ∈ Set.Icc (-1) 1 } = 1 / 2 ^ (n - 1) ↔
     P = (1 / 2 ^ (n - 1) : ℝ) • (T ℝ n) :=
    by
  constructor
  case mp =>
    intro hsSup
    let extrema := (Finset.range (n + 1)).image (fun (k : ℕ) => cos (k * π / n))
    have card_extrema : extrema.card = n + 1 := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      apply injOn_cos.comp (by aesop)
      intro k hk
      apply Set.mem_Icc.mpr
      constructor
      · positivity
      · field_simp
        norm_cast
        grind
    apply eq_of_degrees_lt_of_eval_finset_eq extrema
    · rw [Pdeg, card_extrema]; norm_cast; simp
    · rw [smul_eq_C_mul, degree_C_mul (by positivity), degree_T, card_extrema]
      norm_cast; simp
    obtain ⟨c, hpos, hsum, hform⟩ := leadingCoeff_formula hn Pdeg
    rw [Pmonic] at hform
    let T' := (1 / 2 ^ (n - 1) : ℝ) • (T ℝ n)
    have Tform (i : ℕ) :
        (-1) ^ i * T'.eval (cos (i * π / n)) = 1 / 2 ^ (n - 1) := by
      have : ((n : ℤ) : ℝ) * (i * π / n) = (i : ℤ) * π := by norm_cast; field_simp
      rw [eval_smul, smul_eq_mul, T_real_cos, this, cos_int_mul_pi]
      suffices ((-1) ^ i : ℝ) * (-1) ^ (i : ℤ) = 1 by grind
      simp [← sq, ← pow_mul']
    replace hform :
      ∑ i ∈ Finset.range (n + 1), (c i) * ((-1) ^ i * P.eval (cos (i * π / n))) =
      ∑ i ∈ Finset.range (n + 1), (c i) * ((-1) ^ i * T'.eval (cos (i * π / n))) := by
      simp_rw [hform, Tform, ← Finset.sum_mul, hsum]
      simp
    replace hform := ge_of_eq hform
    contrapose! hform
    obtain ⟨θ, hθ, hPθ⟩ := hform
    obtain ⟨i₀, hi₀, hi₀θ⟩ := Finset.mem_image.mp hθ
    have h_le {i : ℕ} (hi : i ∈ Finset.range (n + 1)) :
      c i * ((-1) ^ i * P.eval (cos (i * π / n))) ≤
      c i * ((-1) ^ i * T'.eval (cos (i * π / n))) := by
      rw [Tform i, ← hsSup]
      exact mul_le_mul_of_nonneg_left (P_eval_bound P n i) (le_of_lt (hpos i hi))
    have h_lt₀ :
      c i₀ * ((-1) ^ i₀ * P.eval (cos (i₀ * π / n))) <
      c i₀ * ((-1) ^ i₀ * T'.eval (cos (i₀ * π / n))) := by
      apply lt_of_le_of_ne (h_le hi₀)
      rw [hi₀θ]
      contrapose! hPθ
      rw [← mul_assoc, ← mul_assoc] at hPθ
      refine mul_left_cancel₀ ?_ hPθ
      have := hpos i₀ hi₀
      positivity
    exact Finset.sum_lt_sum (fun i hi => h_le hi) ⟨i₀, hi₀, h_lt₀⟩
  case mpr =>
    intro hP
    apply eq_of_le_of_ge
    · refine csSup_le (by use |P.eval 1|; grind) (fun x hx => ?_)
      obtain ⟨θ, hθ, hx⟩ := Set.mem_setOf.mp hx
      have := (abs_eval_T_real_le_one_iff (Int.ofNat_ne_zero.mpr hn) θ).mp (abs_le.mpr hθ)
      aesop
    · refine le_csSup (bddAbove P) ⟨1, ⟨by grind, by aesop⟩⟩

end Polynomial.Chebyshev
