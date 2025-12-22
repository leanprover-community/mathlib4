/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
module

public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.Data.Pi.Interval
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Mahler measure of integer polynomials

The main purpose of this file is to prove some facts about the Mahler measure of integer
polynomials, in particular Northcott's Theorem for the Mahler measure.

## Main results
- `Polynomial.finite_mahlerMeasure_le`: Northcott's Theorem: the set of integer polynomials of
  degree at most `n` and Mahler measure at most `B` is finite.
- `Polynomial.card_mahlerMeasure_le_prod`: an upper bound on the number of integer polynomials
  of degree at most `n` and Mahler measure at most `B`.
- `Polynomial.cyclotomic_mahlerMeasure_eq_one`: the Mahler measure of a cyclotomic polynomial is 1.
-/

@[expose] public section

namespace Polynomial

open Int

lemma one_le_mahlerMeasure_of_ne_zero {p : ℤ[X]} (hp : p ≠ 0) :
    1 ≤ (p.map (castRingHom ℂ)).mahlerMeasure := by
  apply le_trans _ (p.map (castRingHom ℂ)).leading_coeff_le_mahlerMeasure
  rw [leadingCoeff_map_of_injective (castRingHom ℂ).injective_int, eq_intCast]
  norm_cast
  exact one_le_abs <| leadingCoeff_ne_zero.mpr hp

section Northcott

variable {n : ℕ} {B₁ B₂ : Fin (n + 1) → ℝ}

local notation3 "BoxPoly" =>
  {p : ℤ[X] | p.natDegree < n + 1 ∧ ∀ i, B₁ i ≤ p.coeff i ∧ p.coeff i ≤ B₂ i}

open Finset in
theorem card_eq_of_natDegree_le_of_coeff_le :
    Set.ncard BoxPoly = ∏ i, (⌊B₂ i⌋ - ⌈B₁ i⌉ + 1).toNat := by
  let e : BoxPoly ≃ Icc (⌈B₁ ·⌉) (⌊B₂ ·⌋) := {
    toFun p := ⟨toFn (n + 1) p, by
      have prop := p.property.2
      simpa using ⟨fun i ↦ ceil_le.mpr (prop i).1, fun i ↦ le_floor.mpr (prop i).2⟩⟩
    invFun p := ⟨ofFn (n + 1) p, by
      refine ⟨ofFn_natDegree_lt (Nat.le_add_left 1 n) p.val, fun i ↦ ?_⟩
      have prop := mem_Icc.mp p.property
      simpa using ⟨ceil_le.mp (prop.1 i), le_floor.mp (prop.2 i)⟩⟩
    left_inv p := by grind [ofFn_comp_toFn_eq_id_of_natDegree_lt]
    right_inv p := by grind [toFn_comp_ofFn_eq_id]
  }
  rw [Set.ncard_congr' e]
  norm_cast
  grind [Pi.card_Icc, card_Icc]

open Nat NNReal

private lemma card_mahlerMeasure (n : ℕ) (B : ℝ≥0) :
    Set.Finite {p : ℤ[X] | p.natDegree ≤ n ∧ (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ B} ∧
    Set.ncard {p : ℤ[X] | p.natDegree ≤ n ∧ (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ B} ≤
    ∏ i : Fin (n + 1), (2 * ⌊n.choose i * B⌋₊ + 1) := by
  simp_rw [← Nat.lt_add_one_iff (n := n)]
  have h_card :
      Set.ncard {p : ℤ[X] | p.natDegree < n + 1 ∧ ∀ i : Fin (n + 1), ‖p.coeff i‖ ≤ n.choose i * B} =
      ∏ i : Fin (n + 1), (2 * ⌊n.choose i * B⌋₊ + 1) := by
    conv => enter [1, 1, 1, p, 2, i]; rw [norm_eq_abs, abs_le]
    rw [card_eq_of_natDegree_le_of_coeff_le]
    simp only [ceil_neg, sub_neg_eq_add, ← two_mul]
    apply Finset.prod_congr rfl fun i _ ↦ ?_
    zify
    rw [toNat_of_nonneg (by positivity), ← Int.natCast_floor_eq_floor (by positivity)]
    norm_cast
  rw [← h_card]
  have h_subset :
      {p : ℤ[X] | p.natDegree < n + 1 ∧ (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ B} ⊆
      {p : ℤ[X] | p.natDegree < n + 1 ∧ ∀ i : Fin (n + 1), ‖p.coeff i‖ ≤ n.choose i * B} := by
    gcongr with p hp
    intro hB d
    rw [show ‖p.coeff d‖ = ‖(p.map (Int.castRingHom ℂ)).coeff d‖ by aesop]
    apply le_trans <| (p.map (Int.castRingHom ℂ)).norm_coeff_le_choose_mul_mahlerMeasure d
    gcongr
    · exact mahlerMeasure_nonneg _
    · grind [Polynomial.natDegree_map_le]
  have h_finite : {p : ℤ[X]| p.natDegree < n + 1 ∧
      ∀ (i : Fin (n + 1)), ‖p.coeff ↑i‖ ≤ ↑(n.choose ↑i) * ↑B}.Finite := by
    apply Set.finite_of_ncard_ne_zero
    rw [h_card, Finset.prod_ne_zero_iff]
    grind
  exact ⟨h_finite.subset h_subset, Set.ncard_le_ncard h_subset h_finite⟩

/-- **Northcott's Theorem:** the set of integer polynomials of degree at most `n` and
Mahler measure at most `B` is finite. -/
theorem finite_mahlerMeasure_le (n : ℕ) (B : ℝ≥0) :
    Set.Finite {p : ℤ[X] | p.natDegree ≤ n ∧ (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ B} :=
  (card_mahlerMeasure n B).1

/-- An upper bound on the number of integer polynomials of degree at most `n` and Mahler measure at
most `B`. -/
theorem card_mahlerMeasure_le_prod (n : ℕ) (B : ℝ≥0) :
    Set.ncard {p : ℤ[X] | p.natDegree ≤ n ∧ (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ B} ≤
    ∏ i : Fin (n + 1), (2 * ⌊n.choose i * B⌋₊ + 1) := (card_mahlerMeasure n B).2

end Northcott

section Cyclotomic

/-- The Mahler measure of a cyclotomic polynomial is 1. -/
theorem cyclotomic_mahlerMeasure_eq_one {R : Type*} [CommRing R] [Algebra R ℂ] (n : ℕ) :
    ((cyclotomic n R).map (algebraMap R ℂ)).mahlerMeasure = 1 := by
  rcases eq_or_ne n 0 with hn | hn
  · simp [hn]
  have : NeZero n := ⟨hn⟩
  suffices ∏ x ∈ primitiveRoots n ℂ, max 1 ‖x‖ = 1 by
    simpa [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, cyclotomic.monic n ℂ,
      Polynomial.cyclotomic.roots_eq_primitiveRoots_val]
  suffices ∀ x ∈ primitiveRoots n ℂ, ‖x‖ ≤ 1 from Multiset.prod_eq_one (by simpa)
  intro _ hz
  exact (IsPrimitiveRoot.norm'_eq_one (isPrimitiveRoot_of_mem_primitiveRoots hz) hn).le

end Cyclotomic

end Polynomial
