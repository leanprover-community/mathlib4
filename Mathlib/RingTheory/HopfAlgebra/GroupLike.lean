/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.GroupLike

/-!
# Group-like elements in a Hopf algebra

This file proves that group-like elements in a Hopf algebra form a group.
-/

open HopfAlgebra

variable {R A : Type*}

section Semiring
variable [CommSemiring R] [Semiring A] [HopfAlgebra R A] {a b : A}

@[simp] lemma IsGroupLikeElem.antipode_mul_cancel (ha : IsGroupLikeElem R a) :
    antipode R a * a = 1 := by
  simpa [ha, -mul_antipode_lTensor_comul_apply] using mul_antipode_rTensor_comul_apply (R := R) a

@[simp] lemma IsGroupLikeElem.mul_antipode_cancel (ha : IsGroupLikeElem R a) :
    a * antipode R a = 1 := by
  simpa [ha, -mul_antipode_lTensor_comul_apply] using mul_antipode_lTensor_comul_apply (R := R) a

@[simp] protected lemma IsGroupLikeElem.antipode (ha : IsGroupLikeElem R a) :
    IsGroupLikeElem R (antipode R a) :=
  ha.of_mul_eq_one ha.mul_antipode_cancel ha.antipode_mul_cancel

@[simp] lemma IsGroupLikeElem.antipode_antipode (ha : IsGroupLikeElem R a) :
    antipode R (antipode R a) = a :=
  left_inv_eq_right_inv ha.antipode.antipode_mul_cancel ha.antipode_mul_cancel

namespace GroupLike

instance : Inv (GroupLike R A) where inv a := ⟨antipode R a, a.2.antipode⟩

@[simp] lemma val_inv (a : GroupLike R A) : ↑(a⁻¹) = (antipode R a : A) := rfl

instance : Group (GroupLike R A) where
  inv_mul_cancel a := by ext; simp

end GroupLike
end Semiring

variable [CommSemiring R] [CommSemiring A] [HopfAlgebra R A] {a b : A}

instance GroupLike.instCommGroup : CommGroup (GroupLike R A) where
  __ := instCommMonoid
  __ := instGroup
