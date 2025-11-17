/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/

import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Data.Pi.Interval

/-!
# Mahler measure of integer polynomials

In this file we define the Mahler measure of a polynomial over `ℤ[X]` and prove some basic
properties.

## Main results

- `Polynomial.card_mahlerMeasure_le_prod`: an upper bound on the number of integer polynomials
  of degree at most `n` and Mahler measure at most `B`, also known as Northcott's Theorem.
-/

namespace Polynomial

open Int

lemma one_le_mahlerMeasure_of_ne_zero {p : ℤ[X]} (hp : p ≠ 0) :
    1 ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure := by
  --add general estimate
  sorry

section Northcott

variable (n : ℕ) {B₁ B₂ : Fin (n + 1) → ℝ}

local notation3 "BoxPoly" =>
  {p : ℤ[X] | p.natDegree ≤ n ∧ ∀ i : Fin (n + 1), B₁ i ≤ p.coeff i ∧ p.coeff i ≤ B₂ i}

open Finset in
theorem card_eq_of_natDegree_le_of_coeff_le (h_B : ∀ i, ⌈B₁ i⌉ ≤ ⌊B₂ i⌋) :
    Nat.card BoxPoly = ∏ i : Fin (n + 1), (⌊B₂ i⌋ - ⌈B₁ i⌉ + 1).toNat  := by
  let Btop := fun i ↦ ⌊B₂ i⌋
  let Bbot := fun i ↦ ⌈B₁ i⌉
  let Box := Icc Bbot Btop
  let f : BoxPoly → Box := fun p => ⟨toFn (n + 1) p , by
    simp only [mem_Icc, Box, Bbot, Btop]
    refine ⟨fun i ↦ ceil_le.mpr (p.property.2 i).1, fun i ↦ le_floor.mpr (p.property.2 i).2⟩⟩
  let g : Box → BoxPoly := fun p => ⟨ofFn (n + 1) p, by
    refine ⟨Nat.le_of_lt_add_one <| ofFn_natDegree_lt (Nat.le_add_left 1 n) p.val, ?_⟩
    intro i
    obtain ⟨_, prop⟩ := p
    simp only [mem_Icc, Box] at prop
    simp only [Fin.is_lt, ofFn_coeff_eq_val_of_lt, Fin.eta]
    refine ⟨ceil_le.mp (prop.1 i), le_floor.mp (prop.2 i)⟩⟩
  have hfBij : f.Bijective := by
    refine Function.bijective_iff_has_inverse.mpr ⟨g, ?_, ?_⟩
    · intro p
      apply Subtype.ext
      simp [f, g, ofFn_comp_toFn_eq_id_of_natDegree_lt <| Nat.lt_succ_iff.mpr p.property.1]
    · intro ⟨_, _⟩
      ext i
      simp_all [toFn, f, g]
  rw [Nat.card_eq_of_bijective f hfBij, Nat.card_eq_finsetCard Box, Pi.card_Icc]
  simp_rw [card_Icc]
  grind

open Nat NNReal in
/-- An upper bound on the number of integer polynomials of degree at most `n` and Mahler measure at
most `B`, also known as Northcott's Theorem. -/
theorem card_mahlerMeasure_le_prod (n : ℕ) (B : ℝ≥0) :
    Nat.card {p : ℤ[X] | p.natDegree ≤ n ∧ (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ B} ≤
    ∏ i : Fin (n + 1), (2 * ⌊n.choose i * B⌋₊ + 1) := by
  have h_card :
      Nat.card {p : ℤ[X] | p.natDegree ≤ n ∧ ∀ i : Fin (n + 1), ‖p.coeff i‖ ≤ n.choose i * B} =
      ∏ i : Fin (n + 1), (2 * ⌊n.choose i * B⌋₊ + 1) := by
    have h_B (i : Fin (n + 1)) : ⌈- (n.choose i * B  : ℝ)⌉ ≤ ⌊(n.choose i * B : ℝ)⌋ := by
      simp only [ceil_neg, neg_le_self_iff, floor_nonneg]
      positivity
    conv => enter [1,1,1,1]; ext p; enter [2]; ext i; rw [norm_eq_abs, abs_le]
    rw [card_eq_of_natDegree_le_of_coeff_le n h_B]
    simp only [ceil_neg, sub_neg_eq_add, ← two_mul]
    apply congr_arg
    ext i
    zify
    rw [toNat_of_nonneg (by positivity), ← Int.natCast_floor_eq_floor (by positivity)]
    simp
    rfl
  rw [← h_card]
  apply card_mono <| finite_of_card_ne_zero _
  · gcongr with p hp
    intro hB d
    rw [show ‖p.coeff d‖ = ‖(p.map (Int.castRingHom ℂ)).coeff d‖ by aesop]
    apply le_trans <| (p.map (Int.castRingHom ℂ)).norm_coeff_le_binom_mahlerMeasure d
    gcongr
    · exact mahlerMeasure_nonneg (map (Int.castRingHom ℂ) p)
    · have h_deg : (map (Int.castRingHom ℂ) p).natDegree = p.natDegree := by
        rcases eq_or_ne p 0 with rfl | hp
        · simp
        · simp [hp]
      rw [h_deg]
      by_cases hd : d ≤ p.natDegree
      · exact choose_le_choose d hp
      · grind [choose_ne_zero_iff, choose_zero_right]
  · rw [h_card, Finset.prod_ne_zero_iff]
    omega

end Northcott

end Polynomial
