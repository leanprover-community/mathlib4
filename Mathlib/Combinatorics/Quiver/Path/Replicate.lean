/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Data.Nat.Init

/-!
# Iterated composition of quiver paths

This file defines `Quiver.Path.replicate`, the `n`-fold composition of a loop with itself.
-/

public section

namespace Quiver.Path

variable {V : Type*} [Quiver V] {a : V}

/--
Compose a loop with itself `n` times: `replicate n p` is `p.comp (p.comp (... p))`.
For `n = 0` this is the nil path.
-/
def replicate (n : ℕ) (p : Path a a) : Path a a :=
  match n with
  | 0 => Path.nil
  | k + 1 => (replicate k p).comp p

@[simp]
lemma length_replicate (n : ℕ) (p : Path a a) : (replicate n p).length = n * p.length := by
  induction n with
  | zero => simp [replicate, length_nil, Nat.zero_mul]
  | succ k ih =>
    simp only [replicate, length_comp, ih, Nat.add_comm, Nat.succ_mul]

end Quiver.Path
