/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Oliver Nash
-/
import Mathlib.Order.Circular
import Mathlib.Order.Fin.Basic

/-! # The circular order on `Fin n`

This file adds a few results about the circular order on `Fin n`.

-/

instance (n : ℕ) : CircularOrder (Fin n) := LinearOrder.toCircularOrder _

variable {n : ℕ} {a b c : Fin n}

lemma Fin.btw_iff : btw a b c ↔ a ≤ b ∧ b ≤ c ∨ b ≤ c ∧ c ≤ a ∨ c ≤ a ∧ a ≤ b := .rfl
lemma Fin.sbtw_iff : sbtw a b c ↔ a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b := .rfl
