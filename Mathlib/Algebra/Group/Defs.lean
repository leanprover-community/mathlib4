/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.DivInvMonoid

/-!
# Groups

This file defines additive and multiplicative group structures. Division monoid structures are
defined in `Mathlib.Algebra.Group.DivInvMonoid`.
-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered Function.const_injective

open Function

variable {G : Type*}

/-- A `Group` is a `Monoid` with an operation `⁻¹` satisfying `a⁻¹ * a = 1`.

There is also a division operation `/` such that `a / b = a * b⁻¹`,
with a default so that `a / b = a * b⁻¹` holds by definition.

Use `Group.ofLeftAxioms` or `Group.ofRightAxioms` to define a group structure
on a type with the minimum proof obligations.
-/
class Group (G : Type*) extends DivInvMonoid G where
  protected inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1

/-- An `AddGroup` is an `AddMonoid` with a unary `-` satisfying `-a + a = 0`.

There is also a binary operation `-` such that `a - b = a + -b`,
with a default so that `a - b = a + -b` holds by definition.

Use `AddGroup.ofLeftAxioms` or `AddGroup.ofRightAxioms` to define an
additive group structure on a type with the minimum proof obligations.
-/
class AddGroup (A : Type*) extends SubNegMonoid A where
  protected neg_add_cancel : ∀ a : A, -a + a = 0

attribute [to_additive (attr := wikidata Q83478)] Group

section Group

variable [Group G] {a b : G}

@[to_additive (attr := simp)]
theorem inv_mul_cancel (a : G) : a⁻¹ * a = 1 :=
  Group.inv_mul_cancel a

@[to_additive]
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b :=
  left_inv_eq_right_inv (inv_mul_cancel a) h

@[to_additive (attr := simp)]
theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  rw [← inv_mul_cancel a⁻¹, inv_eq_of_mul (inv_mul_cancel a)]

@[to_additive (attr := simp) sub_self]
theorem div_self' (a : G) : a / a = 1 := by rw [div_eq_mul_inv, mul_inv_cancel a]

@[to_additive (attr := simp)]
theorem inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b := by
  rw [← mul_assoc, inv_mul_cancel, one_mul]

@[to_additive (attr := simp)]
theorem mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b := by
  rw [← mul_assoc, mul_inv_cancel, one_mul]

@[to_additive (attr := simp)]
theorem mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a := by
  rw [mul_assoc, mul_inv_cancel, mul_one]

@[to_additive (attr := simp)]
theorem mul_div_cancel_right (a b : G) : a * b / b = a := by
  rw [div_eq_mul_inv, mul_inv_cancel_right a b]

@[to_additive (attr := simp)]
theorem inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a := by
  rw [mul_assoc, inv_mul_cancel, mul_one]

@[to_additive (attr := simp)]
theorem div_mul_cancel (a b : G) : a / b * b = a := by
  rw [div_eq_mul_inv, inv_mul_cancel_right a b]

@[to_additive]
instance (priority := 100) Group.toDivisionMonoid : DivisionMonoid G where
  inv_inv a := by exact inv_eq_of_mul (inv_mul_cancel a)
  mul_inv_rev a b := by
    apply inv_eq_of_mul
    rw [mul_assoc, mul_inv_cancel_left, mul_inv_cancel]
  inv_eq_of_mul _ _ := by exact inv_eq_of_mul

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) Group.toCancelMonoid : CancelMonoid G where
  mul_right_cancel := fun a b c h ↦ by
    rw [← mul_inv_cancel_right b a, show b * a = c * a from h, mul_inv_cancel_right]
  mul_left_cancel := fun a {b c} h ↦ by
    rw [← inv_mul_cancel_left a b, show a * b = a * c from h, inv_mul_cancel_left]

end Group

/-- An additive commutative group is an additive group with commutative `(+)`. -/
class AddCommGroup (G : Type*) extends AddGroup G, AddCommMonoid G

/-- A commutative group is a group with commutative `(*)`. -/
-- There is intentionally no `IsMulCommutative` for `CommGroup` instance for performance reasons.
@[to_additive (attr := wikidata Q181296)]
class CommGroup (G : Type*) extends Group G, CommMonoid G

section CommGroup

variable [CommGroup G]

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CommGroup.toCancelCommMonoid : CancelCommMonoid G :=
  { ‹CommGroup G›, Group.toCancelMonoid with }

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CommGroup.toDivisionCommMonoid : DivisionCommMonoid G :=
  { ‹CommGroup G›, Group.toDivisionMonoid with }

@[to_additive (attr := simp)] lemma inv_mul_cancel_comm (a b : G) : a⁻¹ * b * a = b := by
  rw [mul_comm, mul_inv_cancel_left]

@[to_additive (attr := simp)]
lemma mul_inv_cancel_comm (a b : G) : a * b * a⁻¹ = b := by rw [mul_comm, inv_mul_cancel_left]

@[to_additive (attr := simp)] lemma inv_mul_cancel_comm_assoc (a b : G) : a⁻¹ * (b * a) = b := by
  rw [mul_comm, mul_inv_cancel_right]

@[to_additive (attr := simp)] lemma mul_inv_cancel_comm_assoc (a b : G) : a * (b * a⁻¹) = b := by
  rw [mul_comm, inv_mul_cancel_right]

end CommGroup


/-! We initialize the projections for the group structures for `@[simps]` here.

The lemmas generated for the `npow`/`zpow` projections will *not* apply to `x ^ y`, since the
argument order of these projections does not match the argument order of `^`. The `nsmul`/`zsmul`
lemmas are correct. -/
initialize_simps_projections Group
initialize_simps_projections AddGroup
initialize_simps_projections CommGroup
initialize_simps_projections AddCommGroup
