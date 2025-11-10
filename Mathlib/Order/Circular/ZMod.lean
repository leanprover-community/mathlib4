/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Oliver Nash, Yaël Dillies
-/
import Mathlib.Order.Circular
import Mathlib.Order.Fin.Basic
import Mathlib.Data.ZMod.Defs

/-!
# The circular order on `ZMod n`

This file defines the circular order on `ZMod n`.
-/

instance : CircularOrder ℤ := LinearOrder.toCircularOrder _

variable {a b c : ℤ}

lemma Int.btw_iff : btw a b c ↔ a ≤ b ∧ b ≤ c ∨ b ≤ c ∧ c ≤ a ∨ c ≤ a ∧ a ≤ b := .rfl
lemma Int.sbtw_iff : sbtw a b c ↔ a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b := .rfl

instance (n : ℕ) : CircularOrder (Fin n) := LinearOrder.toCircularOrder _

variable {n : ℕ} {a b c : Fin n}

lemma Fin.btw_iff : btw a b c ↔ a ≤ b ∧ b ≤ c ∨ b ≤ c ∧ c ≤ a ∨ c ≤ a ∧ a ≤ b := .rfl
lemma Fin.sbtw_iff : sbtw a b c ↔ a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b := .rfl

instance : ∀ (n : ℕ), CircularOrder (ZMod n)
  | 0 => inferInstanceAs <| CircularOrder ℤ
  | n + 1 => inferInstanceAs <| CircularOrder <| Fin <| n + 1
