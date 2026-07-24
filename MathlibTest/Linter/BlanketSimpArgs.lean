import Mathlib.Tactic.Linter.BlanketSimpArgs
import Mathlib.Tactic.Nontriviality
import Mathlib.Tactic.SimpRw
import Mathlib.Algebra.Notation.Defs
import Mathlib.Logic.Unique

/-! Tests for the `blanketSimpArgs` linter. -/

set_option linter.blanketSimpArgs true

variable {M : Type} [Zero M] [One M] [Subsingleton M]

-- The bare lemma is linted against.

/--
warning: `Subsingleton.eq_zero` rewrites a bare variable, so `simp` tries it at every subterm and attempts to discharge its side conditions at each match, which can dominate the elaboration time of a proof.
Determine the side conditions at this use site instead, by applying the lemma to a term or by fixing its implicit arguments with named arguments, as in `Subsingleton.eq_zero (α := M)`.

Note: This linter can be disabled with `set_option linter.blanketSimpArgs false`
-/
#guard_msgs in
example (x : M) : x = 0 := by simp [Subsingleton.eq_zero]

-- The check is not tied to `Subsingleton.eq_zero`: any lemma of the same shape is flagged.

/--
warning: `Subsingleton.eq_one` rewrites a bare variable, so `simp` tries it at every subterm and attempts to discharge its side conditions at each match, which can dominate the elaboration time of a proof.
Determine the side conditions at this use site instead, by applying the lemma to a term or by fixing its implicit arguments with named arguments, as in `Subsingleton.eq_zero (α := M)`.

Note: This linter can be disabled with `set_option linter.blanketSimpArgs false`
-/
#guard_msgs in
example (x : M) : x = 1 := by simp [Subsingleton.eq_one]

-- All `simp`-like tactics are covered, including the `using` clause of `nontriviality`.

/--
warning: `Subsingleton.eq_zero` rewrites a bare variable, so `simp` tries it at every subterm and attempts to discharge its side conditions at each match, which can dominate the elaboration time of a proof.
Determine the side conditions at this use site instead, by applying the lemma to a term or by fixing its implicit arguments with named arguments, as in `Subsingleton.eq_zero (α := M)`.

Note: This linter can be disabled with `set_option linter.blanketSimpArgs false`
-/
#guard_msgs in
example (x : M) : x = 0 := by simp_rw [Subsingleton.eq_zero]

/--
warning: `Subsingleton.eq_zero` rewrites a bare variable, so `simp` tries it at every subterm and attempts to discharge its side conditions at each match, which can dominate the elaboration time of a proof.
Determine the side conditions at this use site instead, by applying the lemma to a term or by fixing its implicit arguments with named arguments, as in `Subsingleton.eq_zero (α := M)`.

Note: This linter can be disabled with `set_option linter.blanketSimpArgs false`
-/
#guard_msgs in
example {R : Type} [Zero R] (r : R) : r = r := by
  nontriviality R using Subsingleton.eq_zero
  rfl

-- Fixing the implicit arguments determines the side conditions; this is not linted.

#guard_msgs in
example (x : M) : x = 0 := by simp [Subsingleton.eq_zero (α := M)]

-- Applying the lemma to a term determines the side conditions; this is not linted.

#guard_msgs in
example (x : M) : x = 0 := by simp [Subsingleton.eq_zero x]

-- Ordinary simp lemmas with a proper head pattern are not linted.

#guard_msgs in
example (n : Nat) : id n = n := by simp [id_eq]

-- Local hypotheses are not linted.

#guard_msgs in
example (x : M) (h : ∀ y : M, y = 0) : x = 0 := by simp [h]

-- Unfolding a definition is not linted.

private def myId (n : Nat) : Nat := n

#guard_msgs in
example (n : Nat) : myId n = n := by simp [myId]
