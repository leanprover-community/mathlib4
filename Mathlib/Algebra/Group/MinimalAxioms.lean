/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Group.Defs
import Mathlib.Init
import Mathlib.Tactic.Translate.ToAdditive

/-!
# Minimal Axioms for a Group

This file defines constructors to define a group structure on a Type, while proving only three
equalities.

## Main Definitions

* `Group.ofLeftAxioms`: Define a group structure on a Type by proving `∀ a, 1 * a = a` and
  `∀ a, a⁻¹ * a = 1` and associativity.
* `Group.ofRightAxioms`: Define a group structure on a Type by proving `∀ a, a * 1 = a` and
  `∀ a, a * a⁻¹ = 1` and associativity.

-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered

universe u

/-- Define a `Group` structure on a Type by proving `∀ a, 1 * a = a` and
`∀ a, a⁻¹ * a = 1`.
Note that this uses the default definitions for `npow`, `zpow` and `div`.
See note [reducible non-instances]. -/
@[to_additive
/-- Define an `AddGroup` structure on a Type by proving `∀ a, 0 + a = a` and
`∀ a, -a + a = 0`.
Note that this uses the default definitions for `nsmul`, `zsmul` and `sub`.
See note [reducible non-instances]. -/]
abbrev Group.ofLeftAxioms {G : Type u} [Mul G] [Inv G] [One G]
    (assoc : ∀ a b c : G, (a * b) * c = a * (b * c))
    (one_mul : ∀ a : G, 1 * a = a)
    (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1) : Group G :=
  { mul_assoc := assoc,
    one_mul := one_mul,
    inv_mul_cancel := inv_mul_cancel,
    mul_one := fun a => by
      have mul_inv_cancel : ∀ a : G, a * a⁻¹ = 1 := fun a =>
        calc a * a⁻¹ = 1 * (a * a⁻¹) := (one_mul _).symm
          _ = ((a * a⁻¹)⁻¹ * (a * a⁻¹)) * (a * a⁻¹) := by
            rw [inv_mul_cancel]
          _ = (a * a⁻¹)⁻¹ * (a * ((a⁻¹ * a) * a⁻¹)) := by
            simp only [assoc]
          _ = 1 := by
            rw [inv_mul_cancel, one_mul, inv_mul_cancel]
      rw [← inv_mul_cancel a, ← assoc, mul_inv_cancel a, one_mul] }

/-- Define a `Group` structure on a Type by proving `∀ a, a * 1 = a` and
`∀ a, a * a⁻¹ = 1`.
Note that this uses the default definitions for `npow`, `zpow` and `div`.
See note [reducible non-instances]. -/
@[to_additive
/-- Define an `AddGroup` structure on a Type by proving `∀ a, a + 0 = a` and
`∀ a, a + -a = 0`.
Note that this uses the default definitions for `nsmul`, `zsmul` and `sub`.
See note [reducible non-instances]. -/]
abbrev Group.ofRightAxioms {G : Type u} [Mul G] [Inv G] [One G]
    (assoc : ∀ a b c : G, (a * b) * c = a * (b * c))
    (mul_one : ∀ a : G, a * 1 = a)
    (mul_inv_cancel : ∀ a : G, a * a⁻¹ = 1) : Group G :=
  have inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1 := fun a =>
    calc a⁻¹ * a = (a⁻¹ * a) * 1 := (mul_one _).symm
      _ = (a⁻¹ * a) * ((a⁻¹ * a) * (a⁻¹ * a)⁻¹) := by
        rw [mul_inv_cancel]
      _ = ((a⁻¹ * (a * a⁻¹)) * a) * (a⁻¹ * a)⁻¹ := by
        simp only [assoc]
      _ = 1 := by
        rw [mul_inv_cancel, mul_one, mul_inv_cancel]
  { mul_assoc := assoc,
    mul_one := mul_one,
    inv_mul_cancel := inv_mul_cancel,
    one_mul := fun a => by
      rw [← mul_inv_cancel a, assoc, inv_mul_cancel, mul_one] }
