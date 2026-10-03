/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Monoid

/-!
# The natural numbers form a monoid

This file contains the additive and multiplicative monoid instances on the natural numbers.

See note [foundational algebra order theory].
-/

public section

assert_not_exists MonoidWithZero DenselyOrdered

namespace Nat

/-! ### Instances -/

instance instMulOneClass : MulOneClass ℕ where
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one

instance instAddCancelMonoid : AddCancelMonoid ℕ where
  add := Nat.add
  add_assoc := Nat.add_assoc
  zero := Nat.zero
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero
  nsmul m n := m * n
  nsmul_zero := Nat.zero_mul
  nsmul_succ := succ_mul
  add_left_cancel _ _ _ := Nat.add_left_cancel
  add_right_cancel _ _ _ := Nat.add_right_cancel

instance instIsAddCommutative : IsAddCommutative ℕ := ⟨⟨Nat.add_comm⟩⟩

instance instMonoid : Monoid ℕ where
  mul := Nat.mul
  mul_assoc := Nat.mul_assoc
  one := Nat.succ Nat.zero
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one
  npow m n := n ^ m
  npow_zero := Nat.pow_zero
  npow_succ _ _ := rfl

instance instIsMulCommutative : IsMulCommutative ℕ := ⟨⟨Nat.mul_comm⟩⟩

-- These instances can also be found from the `LinearOrderedCommMonoidWithZero ℕ` instance by
-- typeclass search, but it is better practice to not rely on algebraic order theory to prove
-- purely algebraic results on concrete types. Eg the results can be made available earlier.

instance instIsMulTorsionFree : IsMulTorsionFree ℕ where
  pow_left_injective _ h _ _ := (Nat.pow_left_inj h).mp

instance instIsAddTorsionFree : IsAddTorsionFree ℕ where
  nsmul_right_injective _n hn _x _y hxy := Nat.mul_left_cancel (Nat.pos_of_ne_zero hn) hxy

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances being used to construct these instances non-computably.
-/

set_option linter.style.whitespace false -- manual alignment is not recognised

instance instAddMonoid        : AddMonoid ℕ        := by infer_instance
instance instSemigroup        : Semigroup ℕ        := by infer_instance
instance instAddSemigroup     : AddSemigroup ℕ     := by infer_instance
instance instOne              : One ℕ              := inferInstance

set_option linter.style.whitespace true

/-! ### Miscellaneous lemmas -/

-- We set the simp priority slightly lower than default; later more general lemmas will replace it.
@[simp 900] protected lemma nsmul_eq_mul (m n : ℕ) : m • n = m * n := rfl

end Nat
