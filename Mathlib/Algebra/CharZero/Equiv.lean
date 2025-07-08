/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Group.Equiv.Defs

/-! # Transporting `CharZero` accross equivalences.

This file exists in order to avoid adding extra imports to other files in this subdirectory.
-/

def CharZero.ofAddMonoidEquiv {M N : Type*} [AddCommMonoidWithOne M] [AddCommMonoidWithOne N]
    [CharZero M] {e : M ≃+ N} (he : e 1 = 1) : CharZero N := by
  constructor
  have (n : ℕ) : (n : N) = e (n : M) := by
    induction n with
    | zero => simp
    | succ n ih => simp [ih, he]
  intro n m h
  rwa [this, this, EmbeddingLike.apply_eq_iff_eq, Nat.cast_inj] at h
