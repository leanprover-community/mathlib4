/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Multiset
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.Data.Pi.Interval
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
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
- `Polynomial.pow_eq_one_of_mahlerMeasure_eq_one`: if an integer polynomial has Mahler measure equal
  to 1, then all its complex nonzero roots are roots of unity.
- `Polynomial.cyclotomic_dvd_of_mahlerMeasure_eq_one`: if an integer non-constant polynomial has
  Mahler measure equal to 1 and is not a multiple of X, then it is divisible by a cyclotomic
  polynomial.
-/

public section

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
  {p : ℤ[X] | p.natDegree ≤ n ∧ ∀ i, B₁ i ≤ p.coeff i ∧ p.coeff i ≤ B₂ i}

open Finset in
theorem card_eq_of_natDegree_le_of_coeff_le :
    Set.ncard BoxPoly = ∏ i, (⌊B₂ i⌋ - ⌈B₁ i⌉ + 1).toNat := by
  let e : BoxPoly ≃ Icc (⌈B₁ ·⌉) (⌊B₂ ·⌋) := {
    toFun p := ⟨toFn (n + 1) p, by
      have prop := p.property.2
      simpa using ⟨fun i ↦ ceil_le.mpr (prop i).1, fun i ↦ le_floor.mpr (prop i).2⟩⟩
    invFun p := ⟨ofFn (n + 1) p, by
      refine ⟨Nat.le_of_lt_succ <| ofFn_natDegree_lt (Nat.le_add_left 1 n) p.val, fun i ↦ ?_⟩
      have prop := mem_Icc.mp p.property
      rw [ofFn_coeff_eq_val_of_lt _ i.2]
      exact ⟨ceil_le.mp (prop.1 i), le_floor.mp (prop.2 i)⟩
    ⟩
    left_inv p := by grind [ofFn_comp_toFn_eq_id_of_natDegree_lt]
    right_inv p := by grind [toFn_comp_ofFn_eq_id]
  }
  rw [Set.ncard_congr' e]
  norm_cast
  grind [Pi.card_Icc, card_Icc]

open NNReal

private lemma card_mahlerMeasure (n : ℕ) (B : ℝ≥0) :
    Set.Finite {p : ℤ[X] | p.natDegree ≤ n ∧ (p.map (castRingHom ℂ)).mahlerMeasure ≤ B} ∧
    Set.ncard {p : ℤ[X] | p.natDegree ≤ n ∧ (p.map (castRingHom ℂ)).mahlerMeasure ≤ B} ≤
    ∏ i : Fin (n + 1), (2 * ⌊n.choose i * B⌋₊ + 1) := by
  have h_card :
      Set.ncard {p : ℤ[X] | p.natDegree ≤ n ∧ ∀ i : Fin (n + 1), ‖p.coeff i‖ ≤ n.choose i * B} =
      ∏ i : Fin (n + 1), (2 * ⌊n.choose i * B⌋₊ + 1) := by
    conv => enter [1, 1, 1, p, 2, i]; rw [norm_eq_abs, abs_le]
    rw [card_eq_of_natDegree_le_of_coeff_le]
    simp only [ceil_neg, sub_neg_eq_add, ← two_mul]
    apply Finset.prod_congr rfl fun i _ ↦ ?_
    zify
    rw [toNat_of_nonneg (by positivity), ← natCast_floor_eq_floor (by positivity)]
    norm_cast
  rw [← h_card]
  have h_subset :
      {p : ℤ[X] | p.natDegree ≤ n ∧ (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ B} ⊆
      {p : ℤ[X] | p.natDegree ≤ n ∧ ∀ i : Fin (n + 1), ‖p.coeff i‖ ≤ n.choose i * B} := by
    gcongr with p hp
    intro hB d
    rw [show ‖p.coeff d‖ = ‖(p.map (castRingHom ℂ)).coeff d‖ by aesop]
    apply le_trans <| (p.map (castRingHom ℂ)).norm_coeff_le_choose_mul_mahlerMeasure d
    gcongr
    · exact mahlerMeasure_nonneg _
    · grind [Polynomial.natDegree_map_le]
  have h_finite : {p : ℤ[X]| p.natDegree ≤ n ∧
      ∀ (i : Fin (n + 1)), ‖p.coeff ↑i‖ ≤ ↑(n.choose ↑i) * ↑B}.Finite := by
    apply Set.finite_of_ncard_ne_zero
    rw [h_card, Finset.prod_ne_zero_iff]
    grind
  exact ⟨h_finite.subset h_subset, Set.ncard_le_ncard h_subset h_finite⟩

/-- **Northcott's Theorem:** the set of integer polynomials of degree at most `n` and
Mahler measure at most `B` is finite. -/
theorem finite_mahlerMeasure_le (n : ℕ) (B : ℝ≥0) :
    Set.Finite {p : ℤ[X] | p.natDegree ≤ n ∧ (p.map (castRingHom ℂ)).mahlerMeasure ≤ B} :=
  (card_mahlerMeasure n B).1

/-- An upper bound on the number of integer polynomials of degree at most `n` and Mahler measure at
most `B`. -/
theorem card_mahlerMeasure_le_prod (n : ℕ) (B : ℝ≥0) :
    Set.ncard {p : ℤ[X] | p.natDegree ≤ n ∧ (p.map (castRingHom ℂ)).mahlerMeasure ≤ B} ≤
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

variable {p : ℤ[X]} (h : (p.map (castRingHom ℂ)).mahlerMeasure = 1)

include h in
lemma norm_leadingCoeff_eq_one_of_mahlerMeasure_eq_one :
    ‖(p.map (castRingHom ℂ)).leadingCoeff‖ = 1 := by
  rcases eq_or_ne p 0 with _ | hp
  · simp_all
  have h_ineq := h ▸ (leading_coeff_le_mahlerMeasure <| p.map (castRingHom ℂ))
  rw [leadingCoeff_map_of_injective (castRingHom ℂ).injective_int, eq_intCast] at ⊢ h_ineq
  norm_cast at ⊢ h_ineq
  grind [leadingCoeff_eq_zero]

include h in
lemma abs_leadingCoeff_eq_one_of_mahlerMeasure_eq_one : |p.leadingCoeff| = 1 := by
  have := norm_leadingCoeff_eq_one_of_mahlerMeasure_eq_one h
  rw [leadingCoeff_map_of_injective (castRingHom ℂ).injective_int, eq_intCast] at this
  norm_cast at this

variable {z : ℂ} (hz₀ : z ≠ 0) (hz : z ∈ p.aroots ℂ)

include hz h in
/-- If an integer polynomial has Mahler measure equal to 1, then all its complex roots are integral
over ℤ. -/
theorem isIntegral_of_mahlerMeasure_eq_one : IsIntegral ℤ z := by
  have : p.leadingCoeff = 1 ∨ p.leadingCoeff = -1 := abs_eq_abs.mp <|
    abs_leadingCoeff_eq_one_of_mahlerMeasure_eq_one h
  have : (C (1 / p.leadingCoeff) * p).Monic := by aesop (add safe (by simp [Monic.def]))
  grind [IsIntegral, RingHom.IsIntegralElem, mem_roots', IsRoot.def, eval₂_mul, eval_map]

open Multiset in
include h hz in
/-- If an integer polynomial has Mahler measure equal to 1, then all its complex roots have norm at
most 1. -/
lemma norm_root_le_one_of_mahlerMeasure_eq_one : ‖z‖ ≤ 1 := by
  calc
  ‖z‖ ≤ max 1 ‖z‖ := le_max_right 1 ‖z‖
  _   ≤ ((p.map (castRingHom ℂ)).roots.map (fun a ↦ max 1 ‖a‖)).prod :=
        mem_le_prod_of_one_le (fun a ↦ le_max_left 1 ‖a‖) hz
  _   ≤ 1 := by grind [prod_max_one_norm_roots_le_mahlerMeasure_of_one_le_leadingCoeff,
        norm_leadingCoeff_eq_one_of_mahlerMeasure_eq_one]

open IntermediateField in
include hz₀ hz h in
/-- If an integer polynomial has Mahler measure equal to 1, then all its complex nonzero roots are
roots of unity. -/
theorem pow_eq_one_of_mahlerMeasure_eq_one : ∃ n, 0 < n ∧ z ^ n = 1 := by
/- We want to use `NumberField.Embeddings.pow_eq_one_of_norm_le_one` but it can only be applied to
elements of number fields. We thus first construct the number field `K` obtained by adjoining `z`
to `ℚ`.
-/
  let K := ℚ⟮z⟯
  let : NumberField K := {
    to_charZero := ℚ⟮z⟯.charZero,
    to_finiteDimensional := adjoin.finiteDimensional
      (isIntegral_of_mahlerMeasure_eq_one h hz).tower_top}
-- `y` is `z` as an element of `K`
  let y : K := ⟨z, mem_adjoin_simple_self ℚ z⟩
  suffices ∃ (n : ℕ) (_ : 0 < n), y ^ n = 1 by
    obtain ⟨n, hn₀, hn₁⟩ := this
    exact ⟨n, hn₀, congrArg (algebraMap K ℂ) hn₁⟩
  refine NumberField.Embeddings.pow_eq_one_of_norm_le_one (x := y) K ℂ (Subtype.coe_ne_coe.mp hz₀)
    (coe_isIntegral_iff.mp <| isIntegral_of_mahlerMeasure_eq_one h hz)
    fun φ ↦ norm_root_le_one_of_mahlerMeasure_eq_one h ?_
  rw [mem_aroots] at hz ⊢
  refine ⟨hz.1, ?_⟩
  have H (ψ : K →+* ℂ) : ψ ((aeval y) p) = (aeval (ψ y)) p := by
    conv_rhs => rw [← map_id (p := p)]
    exact p.map_aeval_eq_aeval_map (by ext; simp) y
  rw [← H, map_eq_zero_iff _ φ.injective,
    ← map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective ↥K ℂ), H]
  exact hz.2

include h hz₀ hz in
/-- If an integer polynomial has Mahler measure equal to 1, then all its complex nonzero roots are
roots of unity. -/
theorem isPrimitiveRoot_of_mahlerMeasure_eq_one : ∃ n, 0 < n ∧ IsPrimitiveRoot z n := by
  obtain ⟨_, _, hz_pow⟩ := pow_eq_one_of_mahlerMeasure_eq_one h hz₀ hz
  exact IsPrimitiveRoot.exists_pos hz_pow (by omega)

include h in
/-- If an integer non-constant polynomial has Mahler measure equal to 1 and is not a multiple of
`X`, then it is divisible by a cyclotomic polynomial. -/
theorem cyclotomic_dvd_of_mahlerMeasure_eq_one (hX : ¬ X ∣ p) (hpdeg : p.degree ≠ 0) :
    ∃ n, 0 < n ∧ cyclotomic n ℤ ∣ p := by
  have hpdegC : (p.map (castRingHom ℂ)).degree ≠ 0 := by
    rwa [p.degree_map_eq_of_injective (castRingHom ℂ).injective_int]
  obtain ⟨z, _⟩ := Splits.exists_eval_eq_zero (IsAlgClosed.splits <| p.map (castRingHom ℂ))
    hpdegC
  have hz₀ : z ≠ 0 := by
    contrapose! hX
    simp_all [X_dvd_iff, coeff_zero_eq_aeval_zero]
  have h_z_root : z ∈ p.aroots ℂ := by aesop
  obtain ⟨m, h_m_pos, h_prim⟩ := isPrimitiveRoot_of_mahlerMeasure_eq_one h hz₀ h_z_root
  use m, h_m_pos
  rw [cyclotomic_eq_minpoly h_prim h_m_pos]
  apply minpoly.isIntegrallyClosed_dvd <| isIntegral_of_mahlerMeasure_eq_one h h_z_root
  exact (mem_aroots.mp h_z_root).2

end Cyclotomic

end Polynomial
