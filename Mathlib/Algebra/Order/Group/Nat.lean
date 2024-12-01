/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Algebra.Group.Nat.Basic
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Data.Nat.Defs

/-!
# The naturals form a linear ordered monoid

This file contains the linear ordered monoid instance on the natural numbers.

See note [foundational algebra order theory].
-/

namespace Nat

/-! ### Instances -/

instance instCanonicallyLinearOrderedAddCommMonoid : CanonicallyLinearOrderedAddCommMonoid ℕ where
  __ := instLinearOrder
  bot := 0
  bot_le := Nat.zero_le
  add_le_add_left := @Nat.add_le_add_left
  le_self_add := Nat.le_add_right
  exists_add_of_le := Nat.exists_eq_add_of_le

instance instLinearOrderedCommMonoid : LinearOrderedCommMonoid ℕ where
  __ := instLinearOrder
  mul_le_mul_left _ _ h _ := mul_le_mul_left _ h

instance instLinearOrderedCancelAddCommMonoid : LinearOrderedCancelAddCommMonoid ℕ where
  __ := instLinearOrder
  add_le_add_left := @Nat.add_le_add_left
  le_of_add_le_add_left := @Nat.le_of_add_le_add_left

instance instOrderedSub : OrderedSub ℕ := by
  refine ⟨fun m n k ↦ ?_⟩
  induction n generalizing k with
  | zero => simp
  | succ n ih => simp only [sub_succ, pred_le_iff, ih, succ_add, add_succ]

/-! ### Miscellaneous lemmas -/

variable {α : Type*} {n : ℕ} {f : α → ℕ}

/-- See also `pow_left_strictMonoOn₀`. -/
protected lemma pow_left_strictMono (hn : n ≠ 0) : StrictMono (· ^ n : ℕ → ℕ) :=
  fun _ _ h ↦ Nat.pow_lt_pow_left h hn

lemma _root_.StrictMono.nat_pow [Preorder α] (hn : n ≠ 0) (hf : StrictMono f) :
    StrictMono (f · ^ n) := (Nat.pow_left_strictMono hn).comp hf

end Nat
