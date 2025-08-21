/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.TFAE

/-!
# Semirings and rings

This file gives lemmas about semirings, rings and domains.
This is analogous to `Algebra.Group.Basic`,
the difference being that the former is about `+` and `*` separately, while
the present file is about their interaction.

For the definitions of semirings and rings see `Algebra.Ring.Defs`.
-/

assert_not_exists Nat.cast_sub

variable {R S : Type*}

open Function

namespace AddHom

/-- Left multiplication by an element of a type with distributive multiplication is an `AddHom`. -/
@[simps -fullyApplied]
def mulLeft [Distrib R] (r : R) : AddHom R R where
  toFun := (r * ·)
  map_add' := mul_add r

/-- Left multiplication by an element of a type with distributive multiplication is an `AddHom`. -/
@[simps -fullyApplied]
def mulRight [Distrib R] (r : R) : AddHom R R where
  toFun a := a * r
  map_add' _ _ := add_mul _ _ r

end AddHom

namespace AddMonoidHom
variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] {a b : R}

/-- Left multiplication by an element of a (semi)ring is an `AddMonoidHom` -/
def mulLeft (r : R) : R →+ R where
  toFun := (r * ·)
  map_zero' := mul_zero r
  map_add' := mul_add r

@[simp, norm_cast] lemma coe_mulLeft (r : R) : (mulLeft r : R → R) = HMul.hMul r := rfl

/-- Right multiplication by an element of a (semi)ring is an `AddMonoidHom` -/
def mulRight (r : R) : R →+ R where
  toFun a := a * r
  map_zero' := zero_mul r
  map_add' _ _ := add_mul _ _ r

@[simp, norm_cast] lemma coe_mulRight (r : R) : (mulRight r) = (· * r) := rfl

lemma mulRight_apply (a r : R) : mulRight r a = a * r := rfl

/-- Multiplication of an element of a (semi)ring is an `AddMonoidHom` in both arguments.

This is a more-strongly bundled version of `AddMonoidHom.mulLeft` and `AddMonoidHom.mulRight`.

Stronger versions of this exists for algebras as `LinearMap.mul`, `NonUnitalAlgHom.mul`
and `Algebra.lmul`.
-/
def mul : R →+ R →+ R where
  toFun := mulLeft
  map_zero' := ext <| zero_mul
  map_add' a b := ext <| add_mul a b

lemma mul_apply (x y : R) : mul x y = x * y := rfl

@[simp, norm_cast] lemma coe_mul : ⇑(mul : R →+ R →+ R) = mulLeft := rfl
@[simp, norm_cast] lemma coe_flip_mul : ⇑(mul : R →+ R →+ R).flip = mulRight := rfl

/-- An `AddMonoidHom` preserves multiplication if pre- and post- composition with
`mul` are equivalent. By converting the statement into an equality of
`AddMonoidHom`s, this lemma allows various specialized `ext` lemmas about `→+` to then be applied.
-/
lemma map_mul_iff (f : R →+ S) :
    (∀ x y, f (x * y) = f x * f y) ↔ (mul : R →+ R →+ R).compr₂ f = (mul.comp f).compl₂ f :=
  Iff.symm ext_iff₂

lemma mulLeft_eq_mulRight_iff_forall_commute : mulLeft a = mulRight a ↔ ∀ b, Commute a b :=
  DFunLike.ext_iff

lemma mulRight_eq_mulLeft_iff_forall_commute : mulRight b = mulLeft b ↔ ∀ a, Commute a b :=
  DFunLike.ext_iff

end AddMonoidHom

namespace AddMonoid.End
section NonUnitalNonAssocSemiring
variable [NonUnitalNonAssocSemiring R]

/-- The left multiplication map: `(a, b) ↦ a * b`. See also `AddMonoidHom.mulLeft`. -/
@[simps!]
def mulLeft : R →+ AddMonoid.End R := .mul

/-- The right multiplication map: `(a, b) ↦ b * a`. See also `AddMonoidHom.mulRight`. -/
@[simps!]
def mulRight : R →+ AddMonoid.End R := (.mul : R →+ AddMonoid.End R).flip

end NonUnitalNonAssocSemiring

section NonUnitalNonAssocCommSemiring
variable [NonUnitalNonAssocCommSemiring R]

lemma mulRight_eq_mulLeft : mulRight = (mulLeft : R →+ AddMonoid.End R) :=
  AddMonoidHom.ext fun _ =>
    Eq.symm <| AddMonoidHom.mulLeft_eq_mulRight_iff_forall_commute.2 (.all _)

end NonUnitalNonAssocCommSemiring
end AddMonoid.End

section HasDistribNeg

section Mul

variable {α : Type*} [Mul α] [HasDistribNeg α]

open MulOpposite

instance MulOpposite.instHasDistribNeg : HasDistribNeg αᵐᵒᵖ where
  neg_mul _ _ := unop_injective <| mul_neg _ _
  mul_neg _ _ := unop_injective <| neg_mul _ _

end Mul

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

lemma IsLeftCancelMulZero.to_noZeroDivisors [MulZeroClass α]
    [IsLeftCancelMulZero α] : NoZeroDivisors α where
  eq_zero_or_eq_zero_of_mul_eq_zero {x _} h :=
    or_iff_not_imp_left.mpr fun ne ↦ mul_left_cancel₀ ne ((mul_zero x).symm ▸ h)

lemma IsRightCancelMulZero.to_noZeroDivisors [MulZeroClass α]
    [IsRightCancelMulZero α] : NoZeroDivisors α where
  eq_zero_or_eq_zero_of_mul_eq_zero {_ y} h :=
    or_iff_not_imp_right.mpr fun ne ↦ mul_right_cancel₀ ne ((zero_mul y).symm ▸ h)

section NonUnitalNonAssocRing

variable {R : Type*} [NonUnitalNonAssocRing R] {r : R}

lemma isLeftRegular_iff_right_eq_zero_of_mul : IsLeftRegular r ↔ ∀ x, r * x = 0 → x = 0 where
  mp h r' eq := h (by simp_rw [eq, mul_zero])
  mpr h r₁ r₂ eq := sub_eq_zero.mp <| h _ <| by simp_rw [mul_sub, eq, sub_self]

lemma isRightRegular_iff_left_eq_zero_of_mul : IsRightRegular r ↔ ∀ x, x * r = 0 → x = 0 where
  mp h r' eq := h (by simp_rw [eq, zero_mul])
  mpr h r₁ r₂ eq := sub_eq_zero.mp <| h _ <| by simp_rw [sub_mul, eq, sub_self]

lemma isRegular_iff_eq_zero_of_mul :
    IsRegular r ↔ (∀ x, r * x = 0 → x = 0) ∧ (∀ x, x * r = 0 → x = 0) := by
  rw [isRegular_iff, isLeftRegular_iff_right_eq_zero_of_mul, isRightRegular_iff_left_eq_zero_of_mul]

/-- A (not necessarily unital or associative) ring with no zero divisors has cancellative
multiplication on both sides. Since either left or right cancellative multiplication implies
the absence of zero divisors, the four conditions are equivalent to each other. -/
lemma noZeroDivisors_tfae : List.TFAE
    [NoZeroDivisors R, IsLeftCancelMulZero R, IsRightCancelMulZero R, IsCancelMulZero R] := by
  simp_rw [isLeftCancelMulZero_iff, isRightCancelMulZero_iff, isCancelMulZero_iff_forall_isRegular,
    isLeftRegular_iff_right_eq_zero_of_mul, isRightRegular_iff_left_eq_zero_of_mul,
    isRegular_iff_eq_zero_of_mul]
  tfae_have 1 ↔ 2 := noZeroDivisors_iff_right_eq_zero_of_mul
  tfae_have 1 ↔ 3 := noZeroDivisors_iff_left_eq_zero_of_mul
  tfae_have 1 ↔ 4 := noZeroDivisors_iff_eq_zero_of_mul
  tfae_finish

/-- In a ring, `IsCancelMulZero` and `NoZeroDivisors` are equivalent. -/
lemma isCancelMulZero_iff_noZeroDivisors : IsCancelMulZero R ↔ NoZeroDivisors R :=
  noZeroDivisors_tfae.out 3 0

variable (R) in
instance (priority := 100) NoZeroDivisors.to_isCancelMulZero
    [NoZeroDivisors R] : IsCancelMulZero R :=
  isCancelMulZero_iff_noZeroDivisors.mpr ‹_›

end NonUnitalNonAssocRing

lemma NoZeroDivisors.to_isDomain [Ring α] [h : Nontrivial α] [NoZeroDivisors α] :
    IsDomain α :=
  { NoZeroDivisors.to_isCancelMulZero α, h with .. }

instance (priority := 100) IsDomain.to_noZeroDivisors [Semiring α] [IsDomain α] :
    NoZeroDivisors α :=
  IsRightCancelMulZero.to_noZeroDivisors α

instance Subsingleton.to_isCancelMulZero [Mul α] [Zero α] [Subsingleton α] : IsCancelMulZero α where
  mul_right_cancel_of_ne_zero hb := (hb <| Subsingleton.eq_zero _).elim
  mul_left_cancel_of_ne_zero hb := (hb <| Subsingleton.eq_zero _).elim

-- This was previously a global instance,
-- but it has been implicated in slow typeclass resolutions,
-- so we scope it to the `Subsingleton` namespace.
lemma Subsingleton.to_noZeroDivisors [Mul α] [Zero α] [Subsingleton α] : NoZeroDivisors α where
  eq_zero_or_eq_zero_of_mul_eq_zero _ := .inl (Subsingleton.eq_zero _)

scoped[Subsingleton] attribute [instance] Subsingleton.to_noZeroDivisors

lemma isDomain_iff_cancelMulZero_and_nontrivial [Semiring α] :
    IsDomain α ↔ IsCancelMulZero α ∧ Nontrivial α :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ {}⟩

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

section DivisionMonoid
variable [DivisionMonoid R] [HasDistribNeg R] {a b : R}

lemma one_div_neg_one_eq_neg_one : (1 : R) / -1 = -1 :=
  have : -1 * -1 = (1 : R) := by rw [neg_mul_neg, one_mul]
  Eq.symm (eq_one_div_of_mul_eq_one_right this)

lemma one_div_neg_eq_neg_one_div (a : R) : 1 / -a = -(1 / a) :=
  calc
    1 / -a = 1 / (-1 * a) := by rw [neg_eq_neg_one_mul]
    _ = 1 / a * (1 / -1) := by rw [one_div_mul_one_div_rev]
    _ = 1 / a * -1 := by rw [one_div_neg_one_eq_neg_one]
    _ = -(1 / a) := by rw [mul_neg, mul_one]

lemma div_neg_eq_neg_div (a b : R) : b / -a = -(b / a) :=
  calc
    b / -a = b * (1 / -a) := by rw [← inv_eq_one_div, division_def]
    _ = b * -(1 / a) := by rw [one_div_neg_eq_neg_one_div]
    _ = -(b * (1 / a)) := by rw [neg_mul_eq_mul_neg]
    _ = -(b / a) := by rw [mul_one_div]

lemma neg_div (a b : R) : -b / a = -(b / a) := by
  rw [neg_eq_neg_one_mul, mul_div_assoc, ← neg_eq_neg_one_mul]

@[field_simps]
lemma neg_div' (a b : R) : -(b / a) = -b / a := by simp [neg_div]

@[simp]
lemma neg_div_neg_eq (a b : R) : -a / -b = a / b := by rw [div_neg_eq_neg_div, neg_div, neg_neg]

lemma neg_inv : -a⁻¹ = (-a)⁻¹ := by rw [inv_eq_one_div, inv_eq_one_div, div_neg_eq_neg_div]

lemma div_neg (a : R) : a / -b = -(a / b) := by rw [← div_neg_eq_neg_div]

@[simp]
lemma inv_neg : (-a)⁻¹ = -a⁻¹ := by rw [neg_inv]

@[deprecated (since := "2025-04-24")]
alias inv_neg' := inv_neg

lemma inv_neg_one : (-1 : R)⁻¹ = -1 := by rw [← neg_inv, inv_one]

end DivisionMonoid
