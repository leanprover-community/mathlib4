/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Ring.Defs

/-!
# Semirings and rings

This file gives lemmas about semirings, rings and domains.
This is analogous to `Algebra.Group.Basic`,
the difference being that the former is about `+` and `*` separately, while
the present file is about their interaction.

For the definitions of semirings and rings see `Algebra.Ring.Defs`.
-/

variable {R : Type*}

open Function

namespace AddHom

/-- Left multiplication by an element of a type with distributive multiplication is an `AddHom`. -/
@[simps (config := .asFn)]
def mulLeft [Distrib R] (r : R) : AddHom R R where
  toFun := (r * ·)
  map_add' := mul_add r

/-- Left multiplication by an element of a type with distributive multiplication is an `AddHom`. -/
@[simps (config := .asFn)]
def mulRight [Distrib R] (r : R) : AddHom R R where
  toFun a := a * r
  map_add' _ _ := add_mul _ _ r

end AddHom

namespace AddMonoidHom

/-- Left multiplication by an element of a (semi)ring is an `AddMonoidHom` -/
def mulLeft [NonUnitalNonAssocSemiring R] (r : R) : R →+ R where
  toFun := (r * ·)
  map_zero' := mul_zero r
  map_add' := mul_add r

@[simp]
theorem coe_mulLeft [NonUnitalNonAssocSemiring R] (r : R) :
    (mulLeft r : R → R) = HMul.hMul r :=
  rfl

/-- Right multiplication by an element of a (semi)ring is an `AddMonoidHom` -/
def mulRight [NonUnitalNonAssocSemiring R] (r : R) : R →+ R where
  toFun a := a * r
  map_zero' := zero_mul r
  map_add' _ _ := add_mul _ _ r

@[simp]
theorem coe_mulRight [NonUnitalNonAssocSemiring R] (r : R) :
    (mulRight r) = (· * r) :=
  rfl

theorem mulRight_apply [NonUnitalNonAssocSemiring R] (a r : R) :
    mulRight r a = a * r :=
  rfl

end AddMonoidHom

section HasDistribNeg

section Mul

variable {α : Type*} [Mul α] [HasDistribNeg α]

open MulOpposite

instance instHasDistribNeg : HasDistribNeg αᵐᵒᵖ where
  neg_mul _ _ := unop_injective <| mul_neg _ _
  mul_neg _ _ := unop_injective <| neg_mul _ _

end Mul

section Group

variable {α : Type*} [Group α] [HasDistribNeg α]

@[simp]
theorem inv_neg' (a : α) : (-a)⁻¹ = -a⁻¹ := by
  rw [eq_comm, eq_inv_iff_mul_eq_one, neg_mul, mul_neg, neg_neg, inv_mul_cancel]

end Group

end HasDistribNeg

section NonUnitalCommRing

variable {α : Type*} [NonUnitalCommRing α]

attribute [local simp] add_assoc add_comm add_left_comm mul_comm

/-- Vieta's formula for a quadratic equation, relating the coefficients of the polynomial with
  its roots. This particular version states that if we have a root `x` of a monic quadratic
  polynomial, then there is another root `y` such that `x + y` is negative the `a_1` coefficient
  and `x * y` is the `a_0` coefficient. -/
theorem vieta_formula_quadratic {b c x : α} (h : x * x - b * x + c = 0) :
    ∃ y : α, y * y - b * y + c = 0 ∧ x + y = b ∧ x * y = c := by
  have : c = x * (b - x) := (eq_neg_of_add_eq_zero_right h).trans (by simp [mul_sub, mul_comm])
  refine ⟨b - x, ?_, by simp, by rw [this]⟩
  rw [this, sub_add, ← sub_mul, sub_self]

end NonUnitalCommRing

theorem succ_ne_self {α : Type*} [NonAssocRing α] [Nontrivial α] (a : α) : a + 1 ≠ a := fun h =>
  one_ne_zero ((add_right_inj a).mp (by simp [h]))

theorem pred_ne_self {α : Type*} [NonAssocRing α] [Nontrivial α] (a : α) : a - 1 ≠ a := fun h ↦
  one_ne_zero (neg_injective ((add_right_inj a).mp (by simp [← sub_eq_add_neg, h])))

section NoZeroDivisors

variable (α)

lemma IsLeftCancelMulZero.to_noZeroDivisors [NonUnitalNonAssocSemiring α]
    [IsLeftCancelMulZero α] : NoZeroDivisors α where
  eq_zero_or_eq_zero_of_mul_eq_zero {x _} h :=
    or_iff_not_imp_left.mpr fun ne ↦ mul_left_cancel₀ ne ((mul_zero x).symm ▸ h)

lemma IsRightCancelMulZero.to_noZeroDivisors [NonUnitalNonAssocSemiring α]
    [IsRightCancelMulZero α] : NoZeroDivisors α where
  eq_zero_or_eq_zero_of_mul_eq_zero {_ y} h :=
    or_iff_not_imp_right.mpr fun ne ↦ mul_right_cancel₀ ne ((zero_mul y).symm ▸ h)

instance (priority := 100) NoZeroDivisors.to_isCancelMulZero
    [NonUnitalNonAssocRing α] [NoZeroDivisors α] :
    IsCancelMulZero α where
  mul_left_cancel_of_ne_zero ha h := by
    rw [← sub_eq_zero, ← mul_sub] at h
    exact sub_eq_zero.1 ((eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_left ha)
  mul_right_cancel_of_ne_zero hb h := by
    rw [← sub_eq_zero, ← sub_mul] at h
    exact sub_eq_zero.1 ((eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_right hb)

/-- In a ring, `IsCancelMulZero` and `NoZeroDivisors` are equivalent. -/
lemma isCancelMulZero_iff_noZeroDivisors [NonUnitalNonAssocRing α] :
    IsCancelMulZero α ↔ NoZeroDivisors α :=
  ⟨fun _ => IsRightCancelMulZero.to_noZeroDivisors _, fun _ => inferInstance⟩

lemma NoZeroDivisors.to_isDomain [Ring α] [h : Nontrivial α] [NoZeroDivisors α] :
    IsDomain α :=
  { NoZeroDivisors.to_isCancelMulZero α, h with .. }

instance (priority := 100) IsDomain.to_noZeroDivisors [Semiring α] [IsDomain α] :
    NoZeroDivisors α :=
  IsRightCancelMulZero.to_noZeroDivisors α

instance Subsingleton.to_isCancelMulZero [Mul α] [Zero α] [Subsingleton α] : IsCancelMulZero α where
  mul_right_cancel_of_ne_zero hb := (hb <| Subsingleton.eq_zero _).elim
  mul_left_cancel_of_ne_zero hb := (hb <| Subsingleton.eq_zero _).elim

instance Subsingleton.to_noZeroDivisors [Mul α] [Zero α] [Subsingleton α] : NoZeroDivisors α where
  eq_zero_or_eq_zero_of_mul_eq_zero _ := .inl (Subsingleton.eq_zero _)

lemma isDomain_iff_cancelMulZero_and_nontrivial [Semiring α] :
    IsDomain α ↔ IsCancelMulZero α ∧ Nontrivial α :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => {}⟩

lemma isCancelMulZero_iff_isDomain_or_subsingleton [Semiring α] :
    IsCancelMulZero α ↔ IsDomain α ∨ Subsingleton α := by
  refine ⟨fun t ↦ ?_, fun h ↦ h.elim (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)⟩
  rw [or_iff_not_imp_right, not_subsingleton_iff_nontrivial]
  exact fun _ ↦ {}

lemma isDomain_iff_noZeroDivisors_and_nontrivial [Ring α] :
    IsDomain α ↔ NoZeroDivisors α ∧ Nontrivial α := by
  rw [← isCancelMulZero_iff_noZeroDivisors, isDomain_iff_cancelMulZero_and_nontrivial]

lemma noZeroDivisors_iff_isDomain_or_subsingleton [Ring α] :
    NoZeroDivisors α ↔ IsDomain α ∨ Subsingleton α := by
  rw [← isCancelMulZero_iff_noZeroDivisors, isCancelMulZero_iff_isDomain_or_subsingleton]

end NoZeroDivisors
