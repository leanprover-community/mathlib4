/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.Algebra.Group.Basic

/-!
# Self-inverse elements

This file defines self-inverse elements of a type with an inversion, i.e. elements `a` satisfying
`a⁻¹ = a`, and develops the API of the classes `IsSelfInvMonoid` and `IsSelfNegAddMonoid`, which
assert that every element is such.

## Main declarations

* `IsSelfInv a`: The element `a` satisfies `a⁻¹ = a`.
* `IsSelfNeg a`: The element `a` satisfies `-a = a`.
* `IsSelfInvMonoid.toCommGroup`: A monoid all of whose elements are self-inverse is a commutative
  group, in which inversion is the identity.

## Tags

involution, self-inverse, elementary abelian 2-group, boolean group, exponent two,
characteristic two
-/

@[expose] public section

variable {α : Type*}

section Inv

variable [Inv α] {a : α}

/-- An element `a` is *self-inverse* if `a⁻¹ = a`. -/
@[to_additive /-- An element `a` is *self-negative* if `-a = a`. -/]
def IsSelfInv (a : α) : Prop := a⁻¹ = a

@[to_additive]
lemma isSelfInv_iff : IsSelfInv a ↔ a⁻¹ = a := Iff.rfl

@[to_additive]
protected alias ⟨IsSelfInv.inv_eq, IsSelfInv.of_inv_eq⟩ := isSelfInv_iff

@[to_additive]
protected lemma IsSelfInv.eq_inv (h : IsSelfInv a) : a = a⁻¹ := h.symm

@[to_additive]
instance [DecidableEq α] : Decidable (IsSelfInv a) := decidable_of_iff _ isSelfInv_iff.symm

end Inv

@[to_additive (attr := simp)]
protected lemma IsSelfInv.one [InvOneClass α] : IsSelfInv (1 : α) := inv_one

@[to_additive (attr := simp)]
lemma isSelfInv_inv [InvolutiveInv α] {a : α} : IsSelfInv a⁻¹ ↔ IsSelfInv a := by
  rw [isSelfInv_iff, isSelfInv_iff, inv_inv, eq_comm]

@[to_additive]
protected alias ⟨_, IsSelfInv.inv⟩ := isSelfInv_inv

@[to_additive]
protected lemma IsSelfInv.conj [DivisionMonoid α] {a : α} (h : IsSelfInv a) (b : α) :
    IsSelfInv (b * a * b⁻¹) := by
  rw [isSelfInv_iff, mul_inv_rev, mul_inv_rev, inv_inv, h, mul_assoc]

@[to_additive]
lemma isSelfInv_conj_iff [Group α] {a b : α} : IsSelfInv (b * a * b⁻¹) ↔ IsSelfInv a :=
  ⟨fun h ↦ by simpa [mul_assoc] using h.conj b⁻¹, fun h ↦ h.conj b⟩

@[to_additive]
protected lemma IsSelfInv.pow [DivisionMonoid α] {a : α} (h : IsSelfInv a) (n : ℕ) :
    IsSelfInv (a ^ n) := by
  rw [isSelfInv_iff, ← inv_pow, h.inv_eq]

@[to_additive]
protected lemma IsSelfInv.zpow [DivisionMonoid α] {a : α} (h : IsSelfInv a) (n : ℤ) :
    IsSelfInv (a ^ n) := by
  rw [isSelfInv_iff, ← inv_zpow, h.inv_eq]

@[to_additive isSelfNeg_iff_two_nsmul_eq_zero]
lemma isSelfInv_iff_sq_eq_one [Group α] {a : α} : IsSelfInv a ↔ a ^ 2 = 1 := by
  rw [isSelfInv_iff, sq, inv_eq_iff_mul_eq_one]

section DivisionCommMonoid

variable [DivisionCommMonoid α] {a b : α}

@[to_additive]
protected lemma IsSelfInv.mul (ha : IsSelfInv a) (hb : IsSelfInv b) : IsSelfInv (a * b) := by
  rw [isSelfInv_iff, mul_inv, ha, hb]

@[to_additive]
protected lemma IsSelfInv.div (ha : IsSelfInv a) (hb : IsSelfInv b) : IsSelfInv (a / b) :=
  div_eq_mul_inv a b ▸ ha.mul hb.inv

end DivisionCommMonoid

/-!
### Monoids in which every element is self-inverse

`IsSelfInvMonoid M` asserts that `a * a = 1` for every `a : M`; it is defined in
`Mathlib/Algebra/Group/Monoid.lean`. Lemmas about `a ^ n` for varying `n` need `Even`/`Odd`, which
are not available at this point in the hierarchy, and live in
`Mathlib/Algebra/Group/SelfInv/Parity.lean`.

None of the lemmas below mentions multiplication in the additive sense, so they are shared by the
motivating examples: semirings of characteristic two (`Mathlib/Algebra/CharP/Two.lean`), Boolean
rings (`Mathlib/Algebra/Ring/BooleanRing.lean`) and modules over `ZMod 2`
(`Mathlib/Data/ZMod/Basic.lean`). Group-theoretically the hypothesis says that the exponent divides
two, and an additive group satisfying it is an `𝔽₂`-vector space, also called an elementary abelian
2-group.

The `simp` lemmas are `scoped`, so they fire only under `open scoped IsSelfInvMonoid` or
`open scoped IsSelfNegAddMonoid`. As global `simp` lemmas, `inv_eq` and `div_eq_mul` would change
the `simp` normal form throughout the library. `Mathlib/Algebra/CharP/Two.lean` re-exports the
additive set under `CharTwo` for characteristic-two rings.
-/

namespace IsSelfInvMonoid

variable {M : Type*}

section MulOne
variable [MulOne M] [IsSelfInvMonoid M]

@[to_additive]
theorem mul_self_eq_one (a : M) : a * a = 1 := IsSelfInvMonoid.mul_self a

end MulOne

section Monoid
variable [Monoid M] [IsSelfInvMonoid M]

@[to_additive two_nsmul]
protected theorem sq (a : M) : a ^ 2 = 1 := by rw [sq, IsSelfInvMonoid.mul_self]

/-- A power of a self-inverse element depends only on the parity of the exponent. -/
@[to_additive /-- A multiple of a self-negative element depends
only on the parity of the multiplier. -/]
theorem pow_eq_pow_mod_two (a : M) (n : ℕ) : a ^ n = a ^ (n % 2) := by
  have h : a ^ (n % 2 + 2 * (n / 2)) = a ^ (n % 2) := by
    rw [pow_add, pow_mul, IsSelfInvMonoid.sq, one_pow, mul_one]
  rw [← h, Nat.mod_add_div]

@[to_additive]
protected theorem mul_cancel_left (a b : M) : a * (a * b) = b := by
  rw [← mul_assoc, IsSelfInvMonoid.mul_self, one_mul]

@[to_additive]
protected theorem mul_cancel_right (a b : M) : a * b * b = a := by
  rw [mul_assoc, IsSelfInvMonoid.mul_self, mul_one]

@[to_additive]
theorem mul_mul_mul_cancel (a b c : M) : a * b * (b * c) = a * c := by
  rw [mul_assoc, ← mul_assoc b, IsSelfInvMonoid.mul_self, one_mul]

/-- A self-inverse monoid is commutative.

See `IsSelfInvMonoid.isMulCommutative` for the `IsMulCommutative` form, and
`IsSelfInvMonoid.toCommGroup` for the `CommGroup` structure. -/
@[to_additive /-- A self-negative additive monoid is commutative.

See `IsSelfNegAddMonoid.isAddCommutative` for the `IsAddCommutative` form, and
`IsSelfNegAddMonoid.toAddCommGroup` for the `AddCommGroup` structure. -/]
protected lemma mul_comm (a b : M) : a * b = b * a := by
  rw [← IsSelfInvMonoid.mul_cancel_left (b * a) (a * b), mul_mul_mul_cancel,
    IsSelfInvMonoid.mul_self, mul_one]

-- Deliberately not an instance, for the same performance reason that `CommGroup` provides no
-- `IsMulCommutative` instance; see the comment above `CommGroup` in
-- `Mathlib/Algebra/Group/Defs.lean`.
/-- Commutativity of a self-inverse monoid, packaged as an `IsMulCommutative`. -/
@[to_additive /-- Commutativity of a self-negative additive monoid, packaged as an
`IsAddCommutative`. -/]
theorem isMulCommutative : IsMulCommutative M where
  is_comm.comm := IsSelfInvMonoid.mul_comm

@[to_additive]
theorem mul_eq_iff_eq_mul {a b c : M} : a * b = c ↔ a = c * b :=
  ⟨fun h ↦ by rw [← h, IsSelfInvMonoid.mul_cancel_right],
    fun h ↦ by rw [h, IsSelfInvMonoid.mul_cancel_right]⟩

@[to_additive]
theorem eq_mul_iff_mul_eq {a b c : M} : a = b * c ↔ a * c = b :=
  ⟨fun h ↦ by rw [h, IsSelfInvMonoid.mul_cancel_right],
    fun h ↦ by rw [← h, IsSelfInvMonoid.mul_cancel_right]⟩

@[to_additive]
protected theorem mul_eq_one {a b : M} : a * b = 1 ↔ a = b :=
  ⟨fun h ↦ by rw [← IsSelfInvMonoid.mul_cancel_right a b, h, one_mul],
    fun h ↦ h ▸ IsSelfInvMonoid.mul_self a⟩

/-- A self-inverse monoid is a commutative group, in which inversion is the identity.

This is not an instance since it puts a new `Inv` on `M`. See note [reducible non-instances]. -/
@[to_additive /-- A self-negative additive monoid is an additive commutative group, in which
negation is the identity.

This is not an instance since it puts a new `Neg` on `M`. See note [reducible non-instances]. -/]
abbrev toCommGroup : CommGroup M where
  inv := id
  inv_mul_cancel := IsSelfInvMonoid.mul_self
  mul_comm := IsSelfInvMonoid.mul_comm

end Monoid

section DivInvMonoid
variable [DivInvMonoid M] [IsSelfInvMonoid M]

@[to_additive two_zsmul]
protected theorem zpow_two (a : M) : a ^ (2 : ℤ) = 1 := by
  rw [zpow_two, IsSelfInvMonoid.mul_self]

end DivInvMonoid

section DivisionMonoid
variable [DivisionMonoid M] [IsSelfInvMonoid M]

@[to_additive (attr := simp)]
protected lemma isSelfInv (a : M) : IsSelfInv a :=
  .of_inv_eq <| inv_eq_of_mul_eq_one_right <| IsSelfInvMonoid.mul_self a

@[to_additive]
theorem inv_eq (a : M) : a⁻¹ = a := (IsSelfInvMonoid.isSelfInv a).inv_eq

@[to_additive]
theorem inv_eq' : Inv.inv = (id : M → M) := funext inv_eq

@[to_additive]
theorem div_eq_mul (a b : M) : a / b = a * b := by rw [div_eq_mul_inv, inv_eq]

/-- A power of a self-inverse element is unchanged by negating the exponent. -/
@[to_additive neg_zsmul /-- A multiple of a self-negative element is unchanged by negating
the multiplier. -/]
protected theorem zpow_neg (a : M) (n : ℤ) : a ^ (-n) = a ^ n := by
  rw [zpow_neg, inv_eq]

end DivisionMonoid

/-- A group in which every element is self-inverse is an `IsSelfInvMonoid`. -/
@[to_additive /-- An additive group in which every element is self-negative is an
`IsSelfNegAddMonoid`. -/]
lemma of_isSelfInv [Group M] (h : ∀ a : M, IsSelfInv a) : IsSelfInvMonoid M where
  mul_self a := mul_eq_one_iff_inv_eq.mpr (h a).inv_eq

end IsSelfInvMonoid

@[to_additive]
lemma isSelfInvMonoid_iff_forall_isSelfInv {M : Type*} [Group M] :
    IsSelfInvMonoid M ↔ ∀ a : M, IsSelfInv a :=
  ⟨fun _ ↦ IsSelfInvMonoid.isSelfInv, .of_isSelfInv⟩

section InjSurj
variable {M N : Type*} [MulOne M] [MulOne N] (f : M → N)

/-- A type endowed with `1` and `*` is a self-inverse monoid, if it admits an injective map that
preserves `1` and `*` to a self-inverse monoid. -/
@[to_additive /-- A type endowed with `0` and `+` is a self-negative additive monoid, if it admits
an injective map that preserves `0` and `+` to a self-negative additive monoid. -/]
protected lemma Function.Injective.isSelfInvMonoid [IsSelfInvMonoid N] (hf : Injective f)
    (one : f 1 = 1) (mul : ∀ a b, f (a * b) = f a * f b) : IsSelfInvMonoid M where
  mul_self a := hf <| by rw [mul, IsSelfInvMonoid.mul_self, one]

/-- A type endowed with `1` and `*` is a self-inverse monoid, if it admits a surjective map that
preserves `1` and `*` from a self-inverse monoid. -/
@[to_additive /-- A type endowed with `0` and `+` is a self-negative additive monoid, if it admits
a surjective map that preserves `0` and `+` from a self-negative additive monoid. -/]
protected lemma Function.Surjective.isSelfInvMonoid [IsSelfInvMonoid M] (hf : Surjective f)
    (one : f 1 = 1) (mul : ∀ a b, f (a * b) = f a * f b) : IsSelfInvMonoid N where
  mul_self b := by obtain ⟨a, rfl⟩ := hf b; rw [← mul, IsSelfInvMonoid.mul_self, one]

end InjSurj

-- The `simp` attributes are attached in explicit namespace blocks rather than via
-- `to_additive (attr := scoped simp)`, because `scoped` resolves against the namespace open at the
-- attribute site and would put the additive lemmas in the `IsSelfInvMonoid` scope.
-- The names are fully qualified because the `protected` lemmas do not resolve by short name here.
namespace IsSelfInvMonoid

attribute [scoped simp] IsSelfInvMonoid.mul_self_eq_one IsSelfInvMonoid.sq
  IsSelfInvMonoid.mul_cancel_left IsSelfInvMonoid.mul_cancel_right
  IsSelfInvMonoid.mul_mul_mul_cancel IsSelfInvMonoid.inv_eq IsSelfInvMonoid.div_eq_mul
  IsSelfInvMonoid.zpow_two

end IsSelfInvMonoid

namespace IsSelfNegAddMonoid

attribute [scoped simp] IsSelfNegAddMonoid.add_self_eq_zero IsSelfNegAddMonoid.two_nsmul
  IsSelfNegAddMonoid.add_cancel_left IsSelfNegAddMonoid.add_cancel_right
  IsSelfNegAddMonoid.add_add_add_cancel IsSelfNegAddMonoid.neg_eq IsSelfNegAddMonoid.sub_eq_add
  IsSelfNegAddMonoid.two_zsmul

end IsSelfNegAddMonoid
