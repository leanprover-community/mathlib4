/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import Mathlib.Algebra.Order.Chebyshev

/-!
# The Newton and Maclaurin inequalities for symmetric polynomials

This file defines the normalized elementary symmetric polynomials
`s.nesymm k = s.esymm k / (s.card.choose k)` for a multiset `s` of real numbers, and establishes
two basic inequalities:

* **Newton's inequality**: `s.nesymm k * s.nesymm (k + 2) ≤ (s.nesymm (k + 1)) ^ 2`.
* **Maclaurin's inequality**: `(s.nesymm (k + 1)) ^ k ≤ (s.nesymm k) ^ (k + 1)` if `s` is
  nonnegative.

Some variant forms of these two inequalities are also given.

TODO: determine the equality cases of the two inequalities.

-/

@[expose] public section

namespace Multiset

open Polynomial Real

variable {s : Multiset ℝ} {n k : ℕ}

private theorem exists_esymm_derivative (hs : s.card = n + 1) :
    ∃ t : Multiset ℝ, t.card = n ∧
      ∀ k ≤ n, (n + 1) * t.esymm k = (n + 1 - k) * s.esymm k := by
  set f : ℝ[X] := (s.map (X + C ·)).prod with hf
  set g : ℝ[X] := C ((n : ℝ) + 1)⁻¹ * f.derivative
  set t := g.roots.map (- ·)
  have : f.natDegree = n + 1 := by
    rw [hf, natDegree_multiset_prod_of_monic]
    · simp [hs, add_comm]
    · grind [mem_map, monic_X_add_C]
  have : f.derivative.coeff n = (n : ℝ) + 1 := by
    grind [coeff_derivative, Monic.coeff_natDegree, monic_multiset_prod_of_monic, monic_X_add_C]
  have : f.derivative.natDegree ≤ n := by grind [natDegree_derivative_le]
  have : f.derivative.natDegree ≥ n := le_natDegree_of_ne_zero (by grind)
  have : g.natDegree = n := by grind [natDegree_C_mul]
  have : g.Splits := by grind [splits_iff_card_roots, roots_C_mul, card_roots_le_derivative,
    f.derivative.card_roots', Splits.multisetProd, mem_map, Splits.X_add_C]
  have : g = (t.map (X + C ·)).prod := by
    grind [prod_multiset_X_sub_C_of_monic_of_roots_card_eq, splits_iff_card_roots, map_map,
      Monic, leadingCoeff]
  have : t.card = n := by grind [card_map, splits_iff_card_roots]
  refine ⟨t, this, fun k hk ↦ ?_⟩
  have : ((n - k + 1 : ℕ) : ℝ) = n + 1 - k := by simp [Nat.cast_sub hk]; grind
  have : g.coeff (n - k) = t.esymm k := by grind [prod_X_add_C_coeff]
  grind [coeff_derivative, prod_X_add_C_coeff]

private theorem exists_esymm_div_choose (hs : s.card = n + 1) : ∃ t : Multiset ℝ, t.card = n ∧
    ∀ k ≤ n, t.esymm k / (n.choose k) = s.esymm k / ((n + 1).choose k) := by
  obtain ⟨t, htc, ht⟩ := exists_esymm_derivative hs
  refine ⟨t, htc, fun k hk ↦ ?_⟩
  rw [div_eq_div_iff]
  · apply mul_left_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0)
    grind [Nat.cast_sub, (mod_cast n.choose_mul_succ_eq k : (n.choose k : ℝ) * (n + 1) =
      ((n + 1).choose k : ℝ) * (n + 1 - k : ℕ) )]
  all_goals exact_mod_cast (Nat.choose_pos (by omega)).ne'

/-- The normalized elementary symmetric functions: `s.nesymm k = s.esymm k / (s.card.choose k)`. -/
noncomputable def nesymm (s : Multiset ℝ) (k : ℕ) : ℝ := s.esymm k / (s.card.choose k)

/-- The base case of the Newton identity. -/
private theorem newton_base (s : Multiset ℝ) (n : ℕ) (hs : s.card = n) :
    (n : ℝ) ^ 2 * (2 * s.esymm 2) ≤ (n : ℝ) * ((n : ℝ) - 1) * (s.esymm 1) ^ 2 := by
  subst hs
  rw [esymm_one, two_mul_esymm_two s]
  nlinarith [mul_nonneg s.card.cast_nonneg (sub_nonneg.mpr (sq_sum_le_card_mul_sum_sq s))]

private theorem newton_aux (n : ℕ) : ∀ s : Multiset ℝ, s.card = n → ∀ k, k + 2 ≤ n →
    s.nesymm k * s.nesymm (k + 2) ≤ (s.nesymm (k + 1)) ^ 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs k hk
    rcases eq_or_lt_of_le hk with rfl | _
    · by_cases h0 : 0 ∈ s
      · nth_rewrite 2 [nesymm]
        rw [← hs, esymm_card, prod_eq_zero h0]
        grind [sq_nonneg]
      · have : 2 * (k + 2) * (s.esymm k * s.esymm (k + 2)) ≤ (k + 1) * (s.esymm (k + 1)) ^ 2 := by
          rw [esymm_map_inv h0 (by omega : k + 1 ≤ s.card),
          esymm_map_inv h0 (by omega : k ≤ s.card),
          hs, (by grind : (k + 2) - (k + 1) = 1), (by grind : (k + 2) - k = 2)]
          have := newton_base (s.map (·⁻¹)) (k + 2) (by grind [card_map])
          push_cast at this
          nlinarith [sq_nonneg (s.esymm (k + 2))]
        have : ((k + 2).choose k : ℝ) * 2 = (k + 2) * (k + 1) := by
          norm_cast
          rw [← (k + 2).choose_symm (by omega), (by omega : k + 2 - k = 2)]
          rcases k.even_or_odd with ⟨m, rfl⟩ | ⟨m, rfl⟩ <;> grind [Nat.choose_two_right]
        have : ((k + 2).choose (k + 1) : ℝ) = k + 2 := by
          rw [(by rfl : k + 1 = k + 2 - 1), (k + 2).choose_symm (k := 1) (by omega)]
          simp
        unfold nesymm
        field_simp
        rw [hs, this, div_le_div_iff₀ (mod_cast (by grind [Nat.choose_pos])) (by positivity)]
        simp
        nlinarith
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      grind [nesymm, exists_esymm_div_choose hs]

/-- **Newton's inequality** (normalized form) : the normalized elementary symmetric functions are
log-concave. -/
theorem nesymm_mul_nesymm_le_sq_nesymm (s : Multiset ℝ) (k : ℕ) :
    s.nesymm k * s.nesymm (k + 2) ≤ (s.nesymm (k + 1)) ^ 2 := by
  rcases le_or_gt (k + 2) s.card with hk | hk
  · exact newton_aux s.card s rfl k hk
  · simp only [nesymm, hk, esymm_eq_zero_of_card_lt, zero_div]
    nlinarith

/-- **Newton's inequality** (unnormalized form) -/
theorem esymm_mul_esymm_le_sq_esymm (s : Multiset ℝ) (k : ℕ) :
    (s.card.choose (k + 1)) ^ 2 * (s.esymm k * s.esymm (k + 2))
      ≤ (s.card.choose k) * (s.card.choose (k + 2)) * (s.esymm (k + 1)) ^ 2 := by
  rcases le_or_gt (k + 2) s.card with hk | hk
  · have : (0 : ℝ) < s.card.choose k := mod_cast Nat.choose_pos (by omega)
    have : (0 : ℝ) < s.card.choose (k + 1) := mod_cast Nat.choose_pos (by omega)
    have : (0 : ℝ) < s.card.choose (k + 2) := mod_cast Nat.choose_pos hk
    have h := nesymm_mul_nesymm_le_sq_nesymm s k
    simp only [nesymm] at h
    field_simp at h
    nlinarith
  · simp only [hk, esymm_eq_zero_of_card_lt, mul_zero]
    positivity

/-- **Newton's inequality** (reduced form) -/
theorem esymm_mul_esymm_le_sq_esymm' (s : Multiset ℝ) (k : ℕ) :
    ((k : ℝ) + 2) * ((s.card : ℝ) - k) * (s.esymm k * s.esymm (k + 2))
    ≤ ((k : ℝ) + 1) * ((s.card : ℝ) - k - 1) * (s.esymm (k + 1)) ^ 2 := by
  rcases (by omega : k + 2 ≤ s.card ∨ k + 1 = s.card ∨ s.card < k + 1) with _ | h | _
  · have : (0 : ℝ) < (s.card.choose (k + 1)) ^ 2 :=
      sq_pos_of_pos (mod_cast Nat.choose_pos (by omega))
    have : (0 : ℝ) ≤ (k + 2) * (s.card - k) :=
      mul_nonneg (by positivity) (by rw [sub_nonneg]; exact_mod_cast (by omega))
    have : (k + 2) * (s.card - k) * ((s.card.choose k : ℝ) * (s.card.choose (k + 2)))
        = (k + 1) * (s.card - k - 1) * (s.card.choose (k + 1)) ^ 2 := by
      rw [(by rw [Nat.cast_sub (by omega)]; grind : (s.card : ℝ) - k - 1 = (s.card - (k + 1) : ℕ)),
        ← Nat.cast_sub (by omega)]
      norm_cast
      grind [Nat.choose_succ_right_eq]
    nlinarith [esymm_mul_esymm_le_sq_esymm s k]
  · rw [esymm_eq_zero_of_card_lt (k := k + 2) (by omega)]
    simp [← h]
  · rw [esymm_eq_zero_of_card_lt (k := k + 2) (by omega),
      esymm_eq_zero_of_card_lt (k := k + 1) (by omega)]
    simp

private theorem esymm_succ_eq_zero_of_esymm_eq_zero
    (hs : ∀ x ∈ s, 0 ≤ x) (h : s.esymm k = 0) : s.esymm (k + 1) = 0 := by
  rw [esymm]
  refine sum_eq_zero fun y hy ↦ ?_
  simp only [mem_map, mem_powersetCard] at hy
  obtain ⟨w, ⟨hws, hwc⟩, rfl⟩ := hy
  obtain ⟨z, hzw⟩ := card_pos_iff_exists_mem.mp (by omega : 0 < w.card)
  obtain ⟨w', rfl⟩ := exists_cons_of_mem hzw
  have : w' ∈ s.powersetCard k := (mem_powersetCard.mpr ⟨(le_cons_self w' z).trans hws,
    by simpa using hwc⟩)
  have {t : Multiset ℝ} (ht : t ∈ s.powersetCard k) : 0 ≤ t.prod :=
    prod_nonneg fun z hz ↦ hs z (mem_of_le (mem_powersetCard.mp ht).1 hz)
  grind [prod_cons, le_antisymm, single_le_sum, mem_map, mem_map_of_mem, esymm]

/-- The elementary symmetric functions of a nonnegative multiset are nonnegative. -/
theorem esymm_nonneg {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
    {s : Multiset R} (hs : ∀ x ∈ s, 0 ≤ x) (k : ℕ) : 0 ≤ s.esymm k := by
  grind [esymm, sum_nonneg, mem_map, prod_nonneg, mem_of_le, mem_powersetCard]

/-- The normalized elementary symmetric functions of a nonnegative multiset are nonnegative. -/
theorem nesymm_nonneg {s : Multiset ℝ} (hs : ∀ x ∈ s, 0 ≤ x) (k : ℕ) : 0 ≤ nesymm s k :=
  div_nonneg (esymm_nonneg hs k) (by positivity)

/-- **Maclaurin's inequality (successor form).** If `s` is nonnegative then
`(s.nesymm (k + 1)) ^ k ≤ (s.nesymm k) ^ (k + 1)`. -/
theorem pow_nesymm_le (hs : ∀ x ∈ s, 0 ≤ x) : (s.nesymm (k + 1)) ^ k ≤ (s.nesymm k) ^ (k + 1) := by
  rcases le_or_gt (k + 1) s.card with hkn | hkn
  · induction k with
    | zero => simp [nesymm]
    | succ k ih =>
      by_cases hp1 : s.nesymm (k + 1) = 0
      · have : s.nesymm (k + 2) = 0 := by
          rw [nesymm, esymm_succ_eq_zero_of_esymm_eq_zero hs, zero_div]
          rw [nesymm, div_eq_zero_iff] at hp1
          exact hp1.resolve_right (mod_cast (Nat.choose_pos (by omega)).ne')
        grind
      · have : 0 < (s.nesymm (k + 1)) ^ k := by grind [nesymm_nonneg, pow_pos]
        have : (s.nesymm (k + 2)) ^ (k + 1) * (s.nesymm (k + 1)) ^ k
            ≤ (s.nesymm (k + 1)) ^ (k + 2) * (s.nesymm (k + 1)) ^ k := calc
            _ ≤ _ := mul_le_mul_of_nonneg_left (ih (by omega)) (pow_nonneg (nesymm_nonneg hs _) _)
            _ = (s.nesymm k * s.nesymm (k + 2)) ^ (k + 1) := by rw [mul_pow, mul_comm]
            _ ≤ _ := pow_le_pow_left₀ (mul_nonneg (nesymm_nonneg hs _) (nesymm_nonneg hs _))
              (nesymm_mul_nesymm_le_sq_nesymm s k) _
            _ = _ := by rw [← pow_mul, ← pow_add]; grind
        nlinarith
  · rw [nesymm, esymm_eq_zero_of_card_lt (k := k + 1) (by omega)]
    by_cases hk : k = 0
    · simp_all [nesymm]
    simp only [zero_div, ne_eq, hk, not_false_eq_true, zero_pow]
    positivity [nesymm_nonneg hs k]

/-- **Maclaurin's inequality (antitone form).** If `s` is nonnegative then
`(s.nesymm k)^(k⁻¹)` is antitone for `k ≥ 1`. -/
theorem rpow_nesymm_antitone (hs : ∀ x ∈ s, 0 ≤ x) :
    AntitoneOn (fun k ↦ (s.nesymm k) ^ (k : ℝ)⁻¹) {k | 1 ≤ k} := by
  rw [← antitone_add_nat_iff_antitoneOn_nat_Ici]
  refine antitone_add_nat_of_succ_le (f := fun k ↦ (s.nesymm k) ^ ((k : ℝ)⁻¹)) (fun k _ ↦ ?_)
  have : 0 ≤ s.nesymm (k + 1) := nesymm_nonneg hs _
  calc
    _ = ((s.nesymm (k + 1)) ^ k) ^ (((k : ℝ) * (k + 1 : ℕ))⁻¹) := by
      rw [← rpow_natCast (s.nesymm _) k, ← rpow_mul (by positivity)]
      congr; field_simp
    _ ≤ _ := rpow_le_rpow (pow_nonneg this k) (pow_nesymm_le hs) (by positivity)
    _ = _ := by
      rw [← rpow_natCast (s.nesymm k) _, ← rpow_mul (nesymm_nonneg hs _)]
      congr; grind

end Multiset
