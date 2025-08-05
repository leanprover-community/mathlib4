/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# Degree of polynomials that are units
-/

noncomputable section

open Finsupp Finset Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

section Semiring

variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}

lemma natDegree_eq_zero_of_isUnit (h : IsUnit p) : natDegree p = 0 := by
  nontriviality R
  obtain ⟨q, hq⟩ := h.exists_right_inv
  have := natDegree_mul (left_ne_zero_of_mul_eq_one hq) (right_ne_zero_of_mul_eq_one hq)
  rw [hq, natDegree_one, eq_comm, add_eq_zero] at this
  exact this.1

lemma degree_eq_zero_of_isUnit [Nontrivial R] (h : IsUnit p) : degree p = 0 :=
  (natDegree_eq_zero_iff_degree_le_zero.mp <| natDegree_eq_zero_of_isUnit h).antisymm
    (zero_le_degree_iff.mpr h.ne_zero)

@[simp]
lemma degree_coe_units [Nontrivial R] (u : R[X]ˣ) : degree (u : R[X]) = 0 :=
  degree_eq_zero_of_isUnit ⟨u, rfl⟩

/-- Characterization of a unit of a polynomial ring over an integral domain `R`.
See `Polynomial.isUnit_iff_coeff_isUnit_isNilpotent` when `R` is a commutative ring. -/
lemma isUnit_iff : IsUnit p ↔ ∃ r : R, IsUnit r ∧ C r = p :=
  ⟨fun hp =>
    ⟨p.coeff 0,
      let h := eq_C_of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit hp)
      ⟨isUnit_C.1 (h ▸ hp), h.symm⟩⟩,
    fun ⟨_, hr, hrp⟩ => hrp ▸ isUnit_C.2 hr⟩

lemma not_isUnit_of_degree_pos (p : R[X]) (hpl : 0 < p.degree) : ¬ IsUnit p := by
  cases subsingleton_or_nontrivial R
  · simp [Subsingleton.elim p 0] at hpl
  intro h
  simp [degree_eq_zero_of_isUnit h] at hpl

lemma not_isUnit_of_natDegree_pos (p : R[X]) (hpl : 0 < p.natDegree) : ¬ IsUnit p :=
  not_isUnit_of_degree_pos _ (natDegree_pos_iff_degree_pos.mp hpl)

@[simp] lemma natDegree_coe_units (u : R[X]ˣ) : natDegree (u : R[X]) = 0 := by
  nontriviality R
  exact natDegree_eq_of_degree_eq_some (degree_coe_units u)

theorem coeff_coe_units_zero_ne_zero [Nontrivial R] (u : R[X]ˣ) : coeff (u : R[X]) 0 ≠ 0 := by
  conv in 0 => rw [← natDegree_coe_units u]
  rw [← leadingCoeff, Ne, leadingCoeff_eq_zero]
  exact Units.ne_zero _

theorem irreducible_iff_of_natDegree_eq_one (h : natDegree p = 1) :
    Irreducible p ↔ ∀ r q, C r * q = p ∨ q * C r = p → IsUnit r where
  mp irr r q := by
    have : p ≠ 0 := by rintro rfl; simp at h
    rintro (rfl | rfl) <;> rw [← isUnit_C] <;>
      simp only [natDegree_mul_of_mul_ne_zero this, natDegree_C, zero_add, add_zero] at h <;>
      replace hq := fun hq ↦ one_ne_zero (h.symm.trans (natDegree_eq_zero_of_isUnit hq))
    exacts [(irr.2 rfl).resolve_right hq, (irr.2 rfl).resolve_left hq]
  mpr prim := by
    refine ⟨fun hp ↦ one_ne_zero (h.symm.trans (natDegree_eq_zero_of_isUnit hp)), fun a b eq ↦ ?_⟩
    have hf : a * b ≠ 0 := eq ▸ fun hp ↦ one_ne_zero (h.symm.trans <| hp ▸ natDegree_zero)
    have eq' := congr(natDegree $eq)
    simp_rw [natDegree_mul_of_mul_ne_zero hf, h, eq_comm (a := 1),
      Nat.add_eq_one_iff, ← eq_C_coeff_zero_iff_natDegree_eq_zero] at eq'
    obtain ⟨eq', -⟩ | ⟨-, eq'⟩ := eq' <;> rw [eq'] at eq ⊢
    · exact .inl ((prim _ _ (.inl eq.symm)).map C)
    · exact .inr ((prim _ _ (.inr eq.symm)).map C)

end Semiring

section CommSemiring
variable [CommSemiring R] {a p : R[X]}

section NoZeroDivisors

variable [NoZeroDivisors R]

theorem irreducible_iff_isPrimitive_of_natDegree_eq_one (h : natDegree p = 1) :
    Irreducible p ↔ p.IsPrimitive := by
  simp_rw [irreducible_iff_of_natDegree_eq_one h,
    IsPrimitive, dvd_def, mul_comm, or_self, exists_imp, eq_comm]

theorem Monic.irreducible_of_degree_eq_one (hp1 : degree p = 1) (hm : Monic p) : Irreducible p :=
  (irreducible_iff_isPrimitive_of_natDegree_eq_one <| natDegree_eq_of_degree_eq_some hp1).mpr
    fun r dvd ↦ isUnit_of_dvd_one <| by
      simpa only [hm.leadingCoeff, leadingCoeff_C] using leadingCoeff_dvd_leadingCoeff dvd

theorem irreducible_X [Nontrivial R] : Irreducible (X : R[X]) :=
  monic_X.irreducible_of_degree_eq_one degree_X

end NoZeroDivisors

variable (hp : p.Monic)
include hp

lemma Monic.C_dvd_iff_isUnit {a : R} : C a ∣ p ↔ IsUnit a where
  mp h := isUnit_iff_dvd_one.mpr <| hp.coeff_natDegree ▸ (C_dvd_iff_dvd_coeff _ _).mp h p.natDegree
  mpr ha := (ha.map C).dvd

lemma Monic.degree_pos_of_not_isUnit (hu : ¬IsUnit p) : 0 < degree p :=
  hp.degree_pos.mpr fun hp' ↦ (hp' ▸ hu) isUnit_one

lemma Monic.natDegree_pos_of_not_isUnit (hu : ¬IsUnit p) : 0 < natDegree p :=
  hp.natDegree_pos.mpr fun hp' ↦ (hp' ▸ hu) isUnit_one

lemma degree_pos_of_not_isUnit_of_dvd_monic (ha : ¬IsUnit a) (hap : a ∣ p) : 0 < degree a := by
  contrapose! ha with h
  rw [Polynomial.eq_C_of_degree_le_zero h] at hap ⊢
  simpa [hp.C_dvd_iff_isUnit, isUnit_C] using hap

lemma natDegree_pos_of_not_isUnit_of_dvd_monic (ha : ¬IsUnit a) (hap : a ∣ p) : 0 < natDegree a :=
  natDegree_pos_iff_degree_pos.mpr <| degree_pos_of_not_isUnit_of_dvd_monic hp ha hap

end CommSemiring

end Polynomial
