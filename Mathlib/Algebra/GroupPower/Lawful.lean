/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.GroupPower.Lemmas
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Module.Basic

/-!
# Lawful power operators on monoids and groups

This file provides a typeclass, `LawfulPow`, that generalizes the `Pow M ℕ` and `Pow G ℤ`
instances on monoids and groups.

Note this does not work for the `Pow G₀ ℤ` instance on a `GroupWithZero G₀`, due to the `pow_add`
field not handling `0 ^ 0`.

## TODO

Push these declarations much deeper into the import graph to allow us to merge the existing `pow`
and `zpow` lemmas.
-/


/-- A typeclass to indicate that the power operation on a monoid `M` by `R` is lawful. -/
class LawfulPow (M R : Type*) [Monoid M] [NonAssocSemiring R] extends _root_.Pow M R where
  pow_one (m : M) : m ^ (1 : R) = m
  pow_mul (m : M) (r₁ r₂ : R) : m ^ (r₁ * r₂) = (m ^ r₁) ^ r₂
  one_pow (r : R) : (1 : M) ^ r = 1
  mul_pow (m₁ m₂ : M) (hm : Commute m₁ m₂) (r : R) : (m₁ * m₂) ^ r = m₁ ^ r * m₂ ^ r
  pow_zero (m : M) : m ^ (0 : R) = 1
  pow_add (m : M) (r₁ r₂ : R) : m ^ (r₁ + r₂) = m ^ r₁ * m ^ r₂

instance {M : Type*} [Monoid M] : LawfulPow M ℕ where
  pow_one := pow_one
  pow_mul := pow_mul
  one_pow := one_pow
  mul_pow _m₁ _m₂ h := h.mul_pow
  pow_zero := pow_zero
  pow_add := pow_add

section Group
variable {M R} [Group M] [NonAssocRing R] [LawfulPow M R]

lemma LawfulPow.inv_pow (m : M) (r : R) :
    m⁻¹ ^ r = (m ^ r)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ←mul_pow, mul_left_inv, one_pow]
  exact (Commute.refl _).inv_left

lemma LawfulPow.pow_neg (m : M) (r : R) :
    m ^ (-r) = (m ^ r)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ←pow_add, add_left_neg, pow_zero]

end Group

namespace Multiplicative

/-- The power operation induced by multiplicativizing a module.

This is a more general case of the instances already in places for translating scalar multiplication
by `ℕ` and `ℤ` to the corresponding power operations.

TODO: generalize this to non-commutative `R` by using the right scalar action. -/
instance {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] :
    LawfulPow (Multiplicative M) R where
  pow m r := .ofAdd <| r • toAdd m
  pow_one _m := toAdd.injective <| one_smul R _
  pow_mul m r₁ r₂ := toAdd.injective <| mul_comm r₂ r₁ ▸ mul_smul r₂ r₁ (toAdd m)
  one_pow _r := toAdd.injective <| smul_zero _
  mul_pow _m₁ _m₂ _h _r := toAdd.injective <| smul_add _ _ _
  pow_zero _m := toAdd.injective <| zero_smul _ _
  pow_add _m _r₁ _r₂ := toAdd.injective <| add_smul _ _ _

end Multiplicative

namespace Additive

open LawfulPow

/-- The module structure induced by additivizing a lawful power.

This is a more general case of the instances already in places for translating powers
by `ℕ` and `ℤ` to the corresponding scalar multiplications. -/
instance {R M : Type*} [CommSemiring R] [CommMonoid M] [LawfulPow M R] :
    Module R (Additive M) where
  smul r m := .ofMul <| toMul m ^ r
  one_smul _m := toMul.injective <| pow_one _
  mul_smul r₁ r₂ m := toMul.injective <| mul_comm r₂ r₁ ▸ pow_mul (toMul m) r₂ r₁
  smul_zero _r := toMul.injective <| one_pow _
  smul_add _r _m₁ _m₂ := toMul.injective <| mul_pow _ _ (Commute.all _ _) _
  zero_smul _m := toMul.injective <| pow_zero _
  add_smul _r₁ _r₂ _m := toMul.injective <| pow_add _ _ _

end Additive
