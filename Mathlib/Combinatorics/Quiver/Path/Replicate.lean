/-
Copyright (c) 2025 Matteo Cipollina, Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.Combinatorics.Quiver.Path

/-!
# Iterated composition of quiver paths

This file defines `Quiver.Path.replicate`, the `n`-fold composition of a loop with itself.
-/

@[expose] public section

namespace Quiver.Path

variable {V : Type*} [Quiver V] {a : V}

/-- Compose a loop with itself `n` times: `replicate n p` is `p.comp (p.comp (... p))`.
For `n = 0` this is the nil path. -/
def replicate : ℕ → Path a a → Path a a
  | 0, _ => .nil
  | n + 1, p => (replicate n p).comp p

@[simp] lemma replicate_zero (p : Path a a) : replicate 0 p = .nil := rfl

@[simp] lemma replicate_succ (n : ℕ) (p : Path a a) :
    replicate (n + 1) p = (replicate n p).comp p := rfl

@[simp]
lemma length_replicate (n : ℕ) (p : Path a a) : (replicate n p).length = n * p.length := by
  induction n with
  | zero => simp
  | succ k ih => simp [ih, Nat.succ_mul]

end Quiver.Path
