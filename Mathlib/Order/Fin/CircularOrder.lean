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

lemma sbtw_iff {n : ℕ} (i j k : Fin n) :
    sbtw i j k ↔ (i < j ∧ j < k) ∨ (j < k ∧ k < i) ∨ (k < i ∧ i < j) :=
  Iff.rfl

lemma btw_iff {n : ℕ} (i j k : Fin n) :
    btw i j k ↔ (i ≤ j ∧ j ≤ k) ∨ (j ≤ k ∧ k ≤ i) ∨ (k ≤ i ∧ i ≤ j) :=
  Iff.rfl
