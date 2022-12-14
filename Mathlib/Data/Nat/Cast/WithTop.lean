/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Data.Nat.Basic

/-!
# Lemma about the coercion `ℕ → with_bot ℕ`.

An orphaned lemma about casting from `ℕ` to `with_bot ℕ`,
exiled here to minimize imports to `data.rat.order` for porting purposes.
-/


theorem Nat.cast_with_top (n : ℕ) : @coe ℕ (WithTop ℕ) (@coeToLift _ _ Nat.castCoe) n = n :=
  rfl
#align nat.cast_with_top Nat.cast_with_top

theorem Nat.cast_with_bot (n : ℕ) : @coe ℕ (WithBot ℕ) (@coeToLift _ _ Nat.castCoe) n = n :=
  rfl
#align nat.cast_with_bot Nat.cast_with_bot
