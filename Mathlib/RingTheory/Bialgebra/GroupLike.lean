/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.GroupLike

/-!
# Group-like elements in a bialgebra

This file proves that group-like elements in a bialgebra form a monoid.
-/

@[expose] public section

open Coalgebra Bialgebra

variable {R A : Type*}

section Semiring
variable [CommSemiring R] [Semiring A] [Bialgebra R A] {a b : A}

/-- In a bialgebra, `1` is a group-like element. -/
lemma IsGroupLikeElem.one : IsGroupLikeElem R (1 : A) where
  counit_eq_one := counit_one
  comul_eq_tmul_self := comul_one

/-- Group-like elements in a bialgebra are stable under multiplication. -/
lemma IsGroupLikeElem.mul (ha : IsGroupLikeElem R a) (hb : IsGroupLikeElem R b) :
    IsGroupLikeElem R (a * b) where
  counit_eq_one := by simp [ha, hb]
  comul_eq_tmul_self := by simp [ha, hb]

variable (R A) in
/-- The group-like elements form a submonoid. -/
def groupLikeSubmonoid : Submonoid A where
  carrier := {a | IsGroupLikeElem R a}
  one_mem' := .one
  mul_mem' := .mul

/-- Group-like elements in a bialgebra are stable under power. -/
lemma IsGroupLikeElem.pow {n : ℕ} (ha : IsGroupLikeElem R a) : IsGroupLikeElem R (a ^ n) :=
  (groupLikeSubmonoid R A).pow_mem ha _

/-- Group-like elements in a bialgebra are stable under inverses, when they exist. -/
lemma IsGroupLikeElem.of_mul_eq_one (hab : a * b = 1) (hba : b * a = 1) (ha : IsGroupLikeElem R a) :
    IsGroupLikeElem R b where
  counit_eq_one :=
    left_inv_eq_right_inv (a := counit a) (by simp [← counit_mul, hba]) (by simp [ha])
  comul_eq_tmul_self := left_inv_eq_right_inv (a := comul a) (by simp [← comul_mul, hba])
    (by simp [ha, hab, Algebra.TensorProduct.one_def])

/-- Group-like elements in a bialgebra are stable under inverses, when they exist. -/
lemma isGroupLikeElem_iff_of_mul_eq_one (hab : a * b = 1) (hba : b * a = 1) :
    IsGroupLikeElem R a ↔ IsGroupLikeElem R b := ⟨.of_mul_eq_one hab hba, .of_mul_eq_one hba hab⟩

@[simp] lemma isGroupLikeElem_unitsInv {u : Aˣ} :
    IsGroupLikeElem R u⁻¹.val ↔ IsGroupLikeElem R u.val :=
  isGroupLikeElem_iff_of_mul_eq_one (by simp) (by simp)

alias ⟨IsGroupLikeElem.of_unitsInv, IsGroupLikeElem.unitsInv⟩ := isGroupLikeElem_unitsInv

namespace GroupLike

instance : One (GroupLike R A) where one := ⟨1, .one⟩
instance : Mul (GroupLike R A) where mul a b := ⟨a * b, a.2.mul b.2⟩
instance : Pow (GroupLike R A) ℕ where pow a n := ⟨a ^ n, a.2.pow⟩

@[simp] lemma val_one : (1 : GroupLike R A) = (1 : A) := rfl
@[simp] lemma val_mul (a b : GroupLike R A) : ↑(a * b) = (a * b : A) := rfl
@[simp] lemma val_pow (a : GroupLike R A) (n : ℕ) : ↑(a ^ n) = (a ^ n : A) := rfl

instance : Monoid (GroupLike R A) := val_injective.monoid val val_one val_mul val_pow

variable (R A) in
/-- `GroupLike.val` as a monoid hom. -/
@[simps] def valMonoidHom : GroupLike R A →* A where
  toFun := val
  map_one' := val_one
  map_mul' := val_mul

end GroupLike
end Semiring

variable [CommSemiring R] [CommSemiring A] [Bialgebra R A] {a b : A}

instance GroupLike.instCommMonoid : CommMonoid (GroupLike R A) :=
  val_injective.commMonoid val val_one val_mul val_pow
