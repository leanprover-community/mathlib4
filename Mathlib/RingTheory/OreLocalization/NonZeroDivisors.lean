/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Kevin Klinge, Andrew Yang
-/
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.RingTheory.OreLocalization.Basic

/-!
# Ore Localization over nonZeroDivisors in monoids with zeros.
-/

open scoped nonZeroDivisors

namespace OreLocalization

variable {R : Type*} [MonoidWithZero R] {S : Submonoid R} [OreSet S]

theorem nontrivial_of_nonZeroDivisors [Nontrivial R] (hS : S ≤ R⁰) :
    Nontrivial R[S⁻¹] :=
  nontrivial_iff.mpr (fun e ↦ one_ne_zero <| hS e 1 (mul_zero _))

variable [Nontrivial R] [OreSet R⁰]

instance nontrivial : Nontrivial R[R⁰⁻¹] :=
  nontrivial_of_nonZeroDivisors (refl R⁰)

variable [NoZeroDivisors R]

open Classical in
/-- The inversion of Ore fractions for a ring without zero divisors, satisfying `0⁻¹ = 0` and
`(r /ₒ r')⁻¹ = r' /ₒ r` for `r ≠ 0`. -/
@[irreducible]
protected noncomputable def inv : R[R⁰⁻¹] → R[R⁰⁻¹] :=
  liftExpand
    (fun r s =>
      if hr : r = (0 : R) then (0 : R[R⁰⁻¹])
      else s /ₒ ⟨r, fun _ => eq_zero_of_ne_zero_of_mul_right_eq_zero hr⟩)
    (by
      intro r t s hst
      by_cases hr : r = 0
      · simp [hr]
      · by_cases ht : t = 0
        · exfalso
          apply nonZeroDivisors.coe_ne_zero ⟨_, hst⟩
          simp [ht]
        · simp only [hr, ht, dif_neg, not_false_iff, or_self_iff, mul_eq_zero, smul_eq_mul]
          apply OreLocalization.expand)

noncomputable instance inv' : Inv R[R⁰⁻¹] :=
  ⟨OreLocalization.inv⟩

open Classical in
protected theorem inv_def {r : R} {s : R⁰} :
    (r /ₒ s)⁻¹ =
      if hr : r = (0 : R) then (0 : R[R⁰⁻¹])
      else s /ₒ ⟨r, fun _ => eq_zero_of_ne_zero_of_mul_right_eq_zero hr⟩ := by
  with_unfolding_all rfl

protected theorem mul_inv_cancel (x : R[R⁰⁻¹]) (h : x ≠ 0) : x * x⁻¹ = 1 := by
  induction' x with r s
  rw [OreLocalization.inv_def, OreLocalization.one_def]
  have hr : r ≠ 0 := by
    rintro rfl
    simp at h
  simp only [hr]
  with_unfolding_all apply OreLocalization.mul_inv ⟨r, _⟩

protected theorem inv_zero : (0 : R[R⁰⁻¹])⁻¹ = 0 := by
  rw [OreLocalization.zero_def, OreLocalization.inv_def]
  simp

end OreLocalization
