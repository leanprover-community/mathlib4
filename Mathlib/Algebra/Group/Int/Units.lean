/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Nat.Units

/-!
# Units in the integers
-/


open Nat

namespace Int

/-! #### Units -/

variable {u v : ℤ}

lemma units_natAbs (u : ℤˣ) : natAbs u = 1 :=
  Units.ext_iff.1 <|
    Nat.units_eq_one
      ⟨natAbs u, natAbs ↑u⁻¹, by rw [← natAbs_mul, Units.mul_inv]; rfl, by
        rw [← natAbs_mul, Units.inv_mul]; rfl⟩

@[simp] lemma natAbs_of_isUnit (hu : IsUnit u) : natAbs u = 1 := units_natAbs hu.unit

lemma isUnit_eq_one_or (hu : IsUnit u) : u = 1 ∨ u = -1 := by
  simpa only [natAbs_of_isUnit hu] using natAbs_eq u

lemma isUnit_ne_iff_eq_neg (hu : IsUnit u) (hv : IsUnit v) : u ≠ v ↔ u = -v := by
  obtain rfl | rfl := isUnit_eq_one_or hu <;> obtain rfl | rfl := isUnit_eq_one_or hv <;> decide

lemma isUnit_eq_or_eq_neg (hu : IsUnit u) (hv : IsUnit v) : u = v ∨ u = -v :=
  or_iff_not_imp_left.2 (isUnit_ne_iff_eq_neg hu hv).1

lemma isUnit_iff : IsUnit u ↔ u = 1 ∨ u = -1 := by
  refine ⟨fun h ↦ isUnit_eq_one_or h, fun h ↦ ?_⟩
  rcases h with (rfl | rfl)
  · exact isUnit_one
  · exact ⟨⟨-1, -1, by decide, by decide⟩, rfl⟩

lemma eq_one_or_neg_one_of_mul_eq_one (h : u * v = 1) : u = 1 ∨ u = -1 :=
  isUnit_iff.1 (isUnit_of_mul_eq_one u v h)

lemma eq_one_or_neg_one_of_mul_eq_one' (h : u * v = 1) : u = 1 ∧ v = 1 ∨ u = -1 ∧ v = -1 := by
  have h' : v * u = 1 := mul_comm u v ▸ h
  obtain rfl | rfl := eq_one_or_neg_one_of_mul_eq_one h <;>
      obtain rfl | rfl := eq_one_or_neg_one_of_mul_eq_one h' <;> tauto

lemma eq_of_mul_eq_one (h : u * v = 1) : u = v :=
  (eq_one_or_neg_one_of_mul_eq_one' h).elim
    (and_imp.2 (·.trans ·.symm)) (and_imp.2 (·.trans ·.symm))

lemma mul_eq_one_iff_eq_one_or_neg_one : u * v = 1 ↔ u = 1 ∧ v = 1 ∨ u = -1 ∧ v = -1 := by
  refine ⟨eq_one_or_neg_one_of_mul_eq_one', fun h ↦ Or.elim h (fun H ↦ ?_) fun H ↦ ?_⟩ <;>
    obtain ⟨rfl, rfl⟩ := H <;> rfl

lemma eq_one_or_neg_one_of_mul_eq_neg_one' (h : u * v = -1) : u = 1 ∧ v = -1 ∨ u = -1 ∧ v = 1 := by
  obtain rfl | rfl := isUnit_eq_one_or (IsUnit.mul_iff.mp (Int.isUnit_iff.mpr (Or.inr h))).1
  · exact Or.inl ⟨rfl, one_mul v ▸ h⟩
  · simpa [Int.neg_mul] using h

lemma mul_eq_neg_one_iff_eq_one_or_neg_one : u * v = -1 ↔ u = 1 ∧ v = -1 ∨ u = -1 ∧ v = 1 := by
  refine ⟨eq_one_or_neg_one_of_mul_eq_neg_one', fun h ↦ Or.elim h (fun H ↦ ?_) fun H ↦ ?_⟩ <;>
    obtain ⟨rfl, rfl⟩ := H <;> rfl

lemma isUnit_iff_natAbs_eq : IsUnit u ↔ u.natAbs = 1 := by simp [natAbs_eq_iff, isUnit_iff]

alias ⟨IsUnit.natAbs_eq, _⟩ := isUnit_iff_natAbs_eq

@[norm_cast]
lemma ofNat_isUnit {n : ℕ} : IsUnit (n : ℤ) ↔ IsUnit n := by simp [isUnit_iff_natAbs_eq]

lemma isUnit_mul_self (hu : IsUnit u) : u * u = 1 :=
  (isUnit_eq_one_or hu).elim (fun h ↦ h.symm ▸ rfl) fun h ↦ h.symm ▸ rfl

lemma isUnit_add_isUnit_eq_isUnit_add_isUnit {a b c d : ℤ} (ha : IsUnit a) (hb : IsUnit b)
    (hc : IsUnit c) (hd : IsUnit d) : a + b = c + d ↔ a = c ∧ b = d ∨ a = d ∧ b = c := by
  rw [isUnit_iff] at ha hb hc hd
  aesop

lemma eq_one_or_neg_one_of_mul_eq_neg_one (h : u * v = -1) : u = 1 ∨ u = -1 :=
  Or.elim (eq_one_or_neg_one_of_mul_eq_neg_one' h) (fun H => Or.inl H.1) fun H => Or.inr H.1

end Int
