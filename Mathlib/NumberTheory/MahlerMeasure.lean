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
polynomials, in particular Northcott's Theorem for the Mahler measure. Some results are also
provided in the special case of monic polynomials.

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

variable (n : ℕ) (B₁ B₂ : Fin (n + 1) → ℝ) (H : ℝ)

section defs

/-- The set of polynomials whose coefficients are bounded between `B₁` and `B₂`. This
construction is used as part of our proof of Northcott's theorem. -/
def boxPoly : Set ℤ[X] := {p : ℤ[X] | p.natDegree ≤ n ∧ ∀ i, B₁ i ≤ p.coeff i ∧ p.coeff i ≤ B₂ i}

/-- The set of polynomials whose Mahler measure is bounded by `H`. -/
def boxPolyₘ : Set ℤ[X] := {p : ℤ[X] | p.natDegree ≤ n ∧ (p.map (castRingHom ℂ)).mahlerMeasure ≤ H}

/-- The set of monic polynomials of degree `n + 1` whose coefficients are bounded by `H`. -/
def monicBoxPoly : Set ℤ[X] := {p : ℤ[X] | p.natDegree = n + 1 ∧ p.Monic ∧ p.supNorm ≤ H}

/-- The set of monic polynomials of degree `n + 1` whose Mahler measure is bounded by `H`. -/
def monicBoxPolyₘ : Set ℤ[X] :=
  {p : ℤ[X] | p.natDegree = n + 1 ∧ p.Monic ∧ (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ H }

theorem monicBoxPolyₘ_subset_monicBoxPoly :
    monicBoxPolyₘ n H ⊆ monicBoxPoly n ((n + 1).choose ((n + 1) / 2) * H) := by
  intro p ⟨hdeg, hmon, hM⟩
  let q := p.map (castRingHom ℂ)
  have hqdeg : q.natDegree = n + 1 :=
    (p.natDegree_map_eq_of_injective (castRingHom ℂ).injective_int).trans hdeg
  refine ⟨hdeg, hmon, ?_⟩
  calc
    p.supNorm = q.supNorm := by simp [q, supNorm_eq_iSup, Int.norm_eq_abs]
    _ ≤ q.natDegree.choose (q.natDegree / 2) * q.mahlerMeasure :=
      q.supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure
    _ ≤ (n + 1).choose ((n + 1) / 2) * H := by
      gcongr
      · exact q.mahlerMeasure_nonneg
      · simp [hqdeg]

lemma monicBoxPoly_subset_monicBoxPolyₘ : monicBoxPoly n H ⊆ monicBoxPolyₘ n (√(n + 2) * H) := by
  intro p ⟨hdeg, hmon, hsup⟩
  refine ⟨hdeg, hmon, ?_⟩
  let q := p.map (castRingHom ℂ)
  have hqdeg : q.natDegree = n + 1 :=
    (p.natDegree_map_eq_of_injective (castRingHom ℂ).injective_int).trans hdeg
  calc
    q.mahlerMeasure
      ≤ √(q.natDegree + 1) * q.supNorm := q.mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm
    _ = √(n + 2) * p.supNorm := by
      congr 1
      · congr 1; norm_cast; simp [hqdeg]
      · simp [q, supNorm_eq_iSup, Int.norm_eq_abs]
    _ ≤ √(n + 2) * H := by gcongr

end defs

@[simp]
theorem mem_monicBoxPoly {p : ℤ[X]} :
    p ∈ monicBoxPoly n H ↔ p.natDegree = n + 1 ∧ p.Monic ∧ p.supNorm ≤ H := Iff.rfl

@[simp]
theorem mem_monicBoxPolyₘ {p : ℤ[X]} :
    p ∈ monicBoxPolyₘ n H ↔ p.natDegree = n + 1 ∧ p.Monic ∧
    (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ H := Iff.rfl

theorem ncard_boxPoly : (boxPoly n B₁ B₂).ncard = ∏ i, (⌊B₂ i⌋ - ⌈B₁ i⌉ + 1).toNat := by
  trans Set.ncard (α := Fin (n + 1) → ℤ) (Finset.Icc (⌈B₁ ·⌉) (⌊B₂ ·⌋))
  · refine Set.ncard_congr' ⟨fun p ↦ ⟨toFn (n + 1) p, ?_⟩, fun p ↦ ⟨ofFn (n + 1) p, ?_⟩, ?_, ?_⟩
    · have prop := p.property.2
      simpa using ⟨fun i ↦ ceil_le.mpr (prop i).1, fun i ↦ le_floor.mpr (prop i).2⟩
    · refine ⟨Nat.le_of_lt_succ <| ofFn_natDegree_lt (Nat.le_add_left 1 n) p.val, fun i ↦ ?_⟩
      have prop := Finset.mem_Icc.mp p.property
      rw [ofFn_coeff_eq_val_of_lt _ i.2]
      exact ⟨ceil_le.mp (prop.1 i), le_floor.mp (prop.2 i)⟩
    · grind [boxPoly, ofFn_comp_toFn_eq_id_of_natDegree_lt]
    · grind [toFn_comp_ofFn_eq_id]
  · norm_cast
    grind [Pi.card_Icc, card_Icc]

@[deprecated (since := "2026-02-02")]
alias card_eq_of_natDegree_le_of_coeff_le := ncard_boxPoly

theorem ncard_monicBoxPoly (hH : 1 ≤ H) : (monicBoxPoly n H).ncard = (2 * ⌊H⌋₊ + 1) ^ (n + 1) := by
  have hH₀ : 0 ≤ H := by linarith
  calc
    (monicBoxPoly n H).ncard = (boxPoly n (fun _ ↦ -H) (fun _ ↦ H)).ncard := by
      refine Set.ncard_congr' ⟨fun p ↦ ⟨p.val - X ^ (n + 1), ?_⟩, fun p ↦ ⟨p.val + X ^ (n + 1), ?_⟩,
        fun _ ↦ by simp, fun _ ↦ by simp⟩
      · obtain ⟨hdeg, hmon, hsup⟩ := p.property
        constructor
        · by_cases! h0 : p.val - X ^ (n + 1) = 0
          · simp [h0]
          · rw [← Nat.lt_succ_iff, Nat.succ_eq_add_one, natDegree_lt_iff_degree_lt h0, ← hdeg,
              ← degree_eq_natDegree hmon.ne_zero]
            refine degree_sub_lt ?_ hmon.ne_zero (by simp [hmon])
            simp [degree_eq_natDegree hmon.ne_zero]
        · intro i
          simpa [ne_of_lt i.isLt, Int.norm_eq_abs, abs_le] using (le_supNorm p.val i).trans hsup
      · obtain ⟨hdeg, hcoeff⟩ := p.property
        have hdeg_lt : degree p.val < ↑(n + 1) :=
          lt_of_le_of_lt (natDegree_le_iff_degree_le.mp hdeg)
            (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le le_rfl))
        refine ⟨?_, by simpa [add_comm] using monic_X_pow_add hdeg_lt, ?_⟩
        · rw [natDegree_add_eq_right_of_natDegree_lt (by rw [natDegree_X_pow]; omega),
            natDegree_X_pow]
        · obtain ⟨j, hj⟩ := (p.val + X ^ (n + 1)).exists_eq_supNorm
          rw [hj, coeff_add, coeff_X_pow]
          obtain h | rfl | h := Nat.lt_trichotomy j (n + 1)
          · simpa [add_zero, h.ne] using abs_le.mpr (hcoeff ⟨j, h⟩)
          · simpa [coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le hdeg)] using hH
          · rw [if_neg h.ne', add_zero, coeff_eq_zero_of_natDegree_lt (by omega),
              norm_zero]
            linarith
    _ = (2 * ⌊H⌋₊ + 1) ^ (n + 1) := by
        simp only [ncard_boxPoly, ceil_neg, sub_neg_eq_add, ← two_mul, Finset.prod_const,
          Finset.card_univ, Fintype.card_fin]
        congr 1
        zify
        rw [toNat_of_nonneg (by linarith [Int.floor_nonneg.mpr hH₀]), ← natCast_floor_eq_floor hH₀]

theorem monicBoxPoly_empty_lt_one (hH : H < 1) : monicBoxPoly n H = ∅ := by
  ext p; simp only [mem_monicBoxPoly, Set.mem_empty_iff_false, iff_false]
  rintro ⟨_, hmon, hsup⟩
  simpa [hmon.coeff_natDegree, norm_one] using ((le_supNorm p p.natDegree).trans hsup).trans_lt hH

theorem ncard_monicBoxPoly_lt_one (hH : H < 1) : (monicBoxPoly n H).ncard = 0 := by
  simp [monicBoxPoly_empty_lt_one n H hH]

/-- Convenience theorem that combines `ncard_monicBoxPoly` and `ncard_monicBoxPoly_lt_one` into an
inequality -/
theorem ncard_monicBoxPoly_le : (monicBoxPoly n H).ncard ≤ (2 * ⌊H⌋₊ + 1) ^ (n + 1) := by
  by_cases! hH : 1 ≤ H <;> simp [hH, ncard_monicBoxPoly, ncard_monicBoxPoly_lt_one]

open NNReal

private lemma card_mahlerMeasure (n : ℕ) (B : ℝ≥0) :
    Set.Finite {p : ℤ[X] | p.natDegree ≤ n ∧ (p.map (castRingHom ℂ)).mahlerMeasure ≤ B} ∧
    Set.ncard {p : ℤ[X] | p.natDegree ≤ n ∧ (p.map (castRingHom ℂ)).mahlerMeasure ≤ B} ≤
    ∏ i : Fin (n + 1), (2 * ⌊n.choose i * B⌋₊ + 1) := by
  have h_card :
      Set.ncard {p : ℤ[X] | p.natDegree ≤ n ∧ ∀ i : Fin (n + 1), ‖p.coeff i‖ ≤ n.choose i * B} =
      ∏ i : Fin (n + 1), (2 * ⌊n.choose i * B⌋₊ + 1) := by
    simp_rw [norm_eq_abs, abs_le]
    rw [← boxPoly, ncard_boxPoly]
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

private lemma card_mahlerMeasure_monic (n : ℕ) (B : ℝ≥0) :
    Set.Finite {p : ℤ[X] | p.natDegree = n + 1 ∧ p.Monic ∧
      (p.map (castRingHom ℂ)).mahlerMeasure ≤ B} ∧
    Set.ncard {p : ℤ[X] | p.natDegree = n + 1 ∧ p.Monic ∧
      (p.map (castRingHom ℂ)).mahlerMeasure ≤ B} ≤
    (2 * ⌊(n + 1).choose ((n + 1) / 2) * (B : ℝ)⌋₊ + 1) ^ (n + 1) := by
  have h_subset : {p : ℤ[X] | p.natDegree = n + 1 ∧ p.Monic ∧
      (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ B} ⊆
      monicBoxPoly n (↑((n + 1).choose ((n + 1) / 2)) * ↑B) := by
    intro p ⟨hp_deg, hp_monic, hp_bound⟩
    refine ⟨hp_deg, hp_monic, ?_⟩
    have h_eq : p.supNorm = (p.map (castRingHom ℂ)).supNorm := by
      simp only [supNorm_eq_iSup, coeff_map, eq_intCast, Complex.norm_intCast, Int.norm_eq_abs]
    have h_deg : (p.map (castRingHom ℂ)).natDegree = n + 1 :=
      (natDegree_map_eq_of_injective (castRingHom ℂ).injective_int p).trans hp_deg
    rw [h_eq]
    calc (p.map (castRingHom ℂ)).supNorm
        ≤ (p.map (castRingHom ℂ)).natDegree.choose ((p.map (castRingHom ℂ)).natDegree / 2) *
          (p.map (castRingHom ℂ)).mahlerMeasure :=
          supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure _
      _ ≤ ↑((n + 1).choose ((n + 1) / 2)) * ↑B := by rw [h_deg]; gcongr
  have h_finite : (monicBoxPoly n (↑((n + 1).choose ((n + 1) / 2)) * ↑B)).Finite := by
    by_cases! h : 1 ≤ (↑((n + 1).choose ((n + 1) / 2)) : ℝ) * ↑B
    · exact Set.finite_of_ncard_ne_zero (by rw [ncard_monicBoxPoly _ _ h]; positivity)
    · suffices monicBoxPoly n (↑((n + 1).choose ((n + 1) / 2)) * ↑B) = ∅ by
        rw [this]; exact Set.finite_empty
      ext p; simp only [monicBoxPoly, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ hmon hsup
      have := (le_supNorm p p.natDegree).trans hsup
      rw [hmon.coeff_natDegree, norm_one] at this
      linarith
  exact ⟨h_finite.subset h_subset,
    (Set.ncard_le_ncard h_subset h_finite).trans (ncard_monicBoxPoly_le n _)⟩

/-- **Northcott's Theorem:** the set of integer polynomials of degree at most `n` and
Mahler measure at most `B` is finite. -/
theorem finite_mahlerMeasure_le (n : ℕ) (B : ℝ≥0) :
    Set.Finite {p : ℤ[X] | p.natDegree ≤ n ∧ (p.map (castRingHom ℂ)).mahlerMeasure ≤ B} :=
  (card_mahlerMeasure n B).1

/-- **Northcott's Theorem** restricted to monic polynomials -/
theorem finite_mahlerMeasure_monic_le (n : ℕ) (B : ℝ≥0) :
  Set.Finite {p : ℤ[X] | p.natDegree = n + 1 ∧ p.Monic ∧
    (p.map (castRingHom ℂ)).mahlerMeasure ≤ B} := (card_mahlerMeasure_monic n B).1

lemma finite_monicBoxPoly : (monicBoxPoly n H).Finite := by
  by_cases! h : 1 ≤ H
  · exact Set.finite_of_ncard_ne_zero (by rw [ncard_monicBoxPoly _ _ h]; positivity)
  · rw [monicBoxPoly_empty_lt_one _ _ h]
    exact Set.finite_empty

lemma finite_monicBoxPolyₘ : (monicBoxPolyₘ n H).Finite :=
  (finite_monicBoxPoly ..).subset (monicBoxPolyₘ_subset_monicBoxPoly n H)

/-- An upper bound on the number of integer polynomials of degree at most `n` and Mahler measure at
most `B`. -/
theorem card_mahlerMeasure_le_prod (n : ℕ) (B : ℝ≥0) :
    Set.ncard {p : ℤ[X] | p.natDegree ≤ n ∧ (p.map (castRingHom ℂ)).mahlerMeasure ≤ B} ≤
    ∏ i : Fin (n + 1), (2 * ⌊n.choose i * B⌋₊ + 1) := (card_mahlerMeasure n B).2

/-- An upper bound on the number of monic integer polynomials of degree at most `n + 1` and having
Mahler measure at most `B` -/
theorem card_mahlerMeasure_monic_le_pow (n : ℕ) (B : ℝ≥0) :
    Set.ncard {p : ℤ[X] | p.natDegree = n + 1 ∧ p.Monic ∧
      (p.map (castRingHom ℂ)).mahlerMeasure ≤ B} ≤
    (2 * ⌊(n + 1).choose ((n + 1) / 2) * (B : ℝ)⌋₊ + 1) ^ (n + 1) :=
  (card_mahlerMeasure_monic n B).2

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

set_option linter.style.whitespace false in -- manual alignment is not recognised
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
      (isIntegral_of_mahlerMeasure_eq_one h hz).tower_top }
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
