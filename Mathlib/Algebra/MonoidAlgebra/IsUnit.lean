/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Algebra.Group.Irreducible.Lemmas
import Mathlib.Algebra.MonoidAlgebra.Defs

variable {M R : Type*} [Semiring R] {m : M} {r : R}

namespace MonoidAlgebra

variable [Monoid M]

theorem isUnit_single (hm : IsUnit m) (hr : IsUnit r) : IsUnit (single m r) :=
  (Prod.isUnit_iff (x := (r, m)).mpr ⟨hr, hm⟩).map singleHom

theorem isUnit_single_iff [Nontrivial R] : IsUnit (single m r) ↔ IsUnit m ∧ IsUnit r where
  mp h := by
    have hm : IsUnit m := by
      rw [isUnit_iff_exists_and_exists] at h ⊢
      simp_rw [eq_comm (b := (1 : M))]
      apply h.imp <;> refine fun ⟨a, eq⟩ ↦ of_not_not fun h ↦ one_ne_zero (α := R) ?_
      · exact .trans (by simp [eq, one_def]) (single_mul_apply_of_not_exists_mul r a h)
      · exact .trans (by simp [eq, one_def]) (mul_single_apply_of_not_exists_mul r a h)
    use hm
    obtain ⟨m, rfl⟩ := hm
    rw [isUnit_iff_exists_and_exists] at h ⊢
    apply h.imp <;>
      refine fun ⟨a, eq⟩ ↦ ⟨a ↑m⁻¹, .trans (.symm ?_) (congr($eq 1).trans Finsupp.single_eq_same)⟩
    · exact single_mul_apply_aux _ fun _ _ ↦ m.mul_eq_one_iff_inv_eq.trans eq_comm
    · exact mul_single_apply_aux _ fun _ _ ↦ m.mul_eq_one_iff_eq_inv
  mpr h := isUnit_single h.1 h.2

theorem isUnit_right_of_single (h : IsUnit (single m r)) : IsUnit r := by
  nontriviality R
  exact (isUnit_single_iff.mp h).2

end MonoidAlgebra

namespace AddMonoidAlgebra

variable [AddMonoid M]

theorem isUnit_single (hm : IsAddUnit m) (hr : IsUnit r) : IsUnit (single m r) :=
  MonoidAlgebra.isUnit_single (M := Multiplicative M) (isUnit_ofAdd_iff.mpr hm) hr

theorem isUnit_single_iff [Nontrivial R] : IsUnit (single m r) ↔ IsAddUnit m ∧ IsUnit r := by
  rw [MonoidAlgebra.isUnit_single_iff (M := Multiplicative M), ← isUnit_ofAdd_iff]; rfl

theorem isUnit_right_of_single (h : IsUnit (single m r)) : IsUnit r :=
  MonoidAlgebra.isUnit_right_of_single (M := Multiplicative M) h

end AddMonoidAlgebra
