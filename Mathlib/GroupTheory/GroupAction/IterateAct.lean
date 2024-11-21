/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Countable.Defs

/-!
# Monoid action by iterates of a map

In this file we define `IterateMulAct f`, `f : α → α`, as a one field structure wrapper over `ℕ`
that acts on `α` by iterates of `f`, `⟨n⟩ • x = f^[n] x`.

It is useful to convert between definitions and theorems about maps and monoid actions.
-/

/-- A structure with a single field `val : ℕ`
that additively acts on `α` by `⟨n⟩ +ᵥ x = f^[n] x`. -/
structure IterateAddAct {α : Type*} (f : α → α) where
  /-- The value of `n : IterateAddAct f`. -/
  val : ℕ

/-- A structure with a single field `val : ℕ` that acts on `α` by `⟨n⟩ • x = f^[n] x`. -/
@[to_additive (attr := ext)]
structure IterateMulAct {α : Type*} (f : α → α) where
  /-- The value of `n : IterateMulAct f`. -/
  val : ℕ

namespace IterateMulAct

variable {α : Type*} {f : α → α}

@[to_additive]
instance instCountable : Countable (IterateMulAct f) :=
  Function.Injective.countable fun _ _ ↦ IterateMulAct.ext

@[to_additive]
instance instCommMonoid : CommMonoid (IterateMulAct f) where
  one := ⟨0⟩
  mul m n := ⟨m.1 + n.1⟩
  mul_assoc a b c := by ext; apply Nat.add_assoc
  one_mul _ := by ext; apply Nat.zero_add
  mul_one _ := rfl
  mul_comm _ _ := by ext; apply Nat.add_comm
  npow n a := ⟨n * a.val⟩
  npow_zero _ := by ext; apply Nat.zero_mul
  npow_succ n a := by ext; apply Nat.succ_mul

@[to_additive]
instance instMulAction : MulAction (IterateMulAct f) α where
  smul n x := f^[n.val] x
  one_smul _ := rfl
  mul_smul _ _ := Function.iterate_add_apply f _ _

@[to_additive (attr := simp)]
theorem mk_smul (n : ℕ) (x : α) : mk (f := f) n • x = f^[n] x := rfl

end IterateMulAct
