/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura
-/

/-!
# Notation `ℕ` for the natural numbers.
-/

notation "ℕ" => Nat

/-- We replace the default recursion principle for the natural numbers. -/
-- TODO: Rename `succ` to `add_one`?
@[eliminator]
def Nat.rec' {motive : ℕ → Sort u}
    (zero : motive 0) (succ : (n : ℕ) → motive n → motive (n + 1)) : (t : ℕ) → motive t
  | 0 => zero
  | (t + 1) => succ t (Nat.rec' zero succ t)
