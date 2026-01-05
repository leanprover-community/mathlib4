/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Damiano Testa, Kevin Buzzard
-/
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.GroupWithZero.Canonical

/-!
An example of a `LinearOrderedCommMonoidWithZero` in which the product of two positive
elements vanishes.

This is the monoid with 3 elements `0, ε, 1` where `ε ^ 2 = 0` and everything else is forced.
The order is `0 < ε < 1`.  Since `ε ^ 2 = 0`, the product of strictly positive elements can vanish.

Relevant Zulip chat:
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/mul_pos
-/


namespace Counterexample

/-- The three element monoid. -/
inductive Foo
  | zero
  | eps
  | one
  deriving DecidableEq

namespace Foo

instance inhabited : Inhabited Foo :=
  ⟨zero⟩

instance : Zero Foo :=
  ⟨zero⟩

instance : One Foo :=
  ⟨one⟩

local notation "ε" => eps

/-- The order on `Foo` is the one induced by the natural order on the image of `aux1`. -/
def aux1 : Foo → ℕ
  | 0 => 0
  | ε => 1
  | 1 => 2

/-- A tactic to prove facts by cases. -/
macro (name := boom) "boom" : tactic => `(tactic| (repeat' rintro ⟨⟩) <;> decide)

theorem aux1_inj : Function.Injective aux1 := by boom

instance linearOrder : LinearOrder Foo :=
  LinearOrder.lift' aux1 aux1_inj

/-- Multiplication on `Foo`: the only external input is that `ε ^ 2 = 0`. -/
def mul : Foo → Foo → Foo
  | 1, x => x
  | x, 1 => x
  | _, _ => 0

instance commMonoid : CommMonoid Foo where
  mul := mul
  one_mul := by boom
  mul_one := by boom
  mul_comm := by boom
  mul_assoc := by boom

instance : LinearOrderedCommMonoidWithZero Foo where
  __ := linearOrder
  __ := commMonoid
  zero_mul := by boom
  mul_zero := by boom
  mul_le_mul_left := by rintro ⟨⟩ ⟨⟩ h ⟨⟩ <;> revert h <;> decide
  zero_le_one := by decide
  bot := 0
  bot_le := by boom

theorem not_mul_pos : ¬∀ {M : Type} [LinearOrderedCommMonoidWithZero M],
    ∀ a b : M, 0 < a → 0 < b → 0 < a * b := by
  intro h
  specialize h ε ε (by boom) (by boom)
  exact (lt_irrefl 0 (h.trans_le (by boom))).elim

example : 0 < ε ∧ ε * ε = 0 := by boom

end Foo

end Counterexample
