/-
Copyright (c) 2025 Kenneth Goodman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenneth Goodman
-/
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.PushNeg
import Mathlib.Tactic.IntervalCases

/-!
# Lamé's Theorem

Lamé's theorem (1844) is the founding result of computational
complexity theory. It bounds the number of division steps in the
Euclidean algorithm using the Fibonacci sequence.

## Main results

- `Nat.euclidSteps`: counts the number of division steps in the
  Euclidean algorithm on natural number inputs.
- `Nat.fib_le_of_euclidSteps`: if the Euclidean algorithm on
  `(a, b)` with `b ≤ a` takes at least `n + 1` steps, then
  `fib (n + 1) ≤ b` and `fib (n + 2) ≤ a`.
- `Nat.euclidSteps_le_of_lt_fib`: if `b < fib (n + 1)`, then
  the Euclidean algorithm on `(a, b)` takes at most `n` steps.

## References

- Gabriel Lamé, *Note sur la limite du nombre des divisions dans
  la recherche du plus grand commun diviseur entre deux nombres
  entiers*, Comptes rendus de l'Académie des sciences, 1844.

## Tags

euclidean algorithm, fibonacci, lamé, complexity
-/

set_option autoImplicit false

namespace Nat

/-- The number of division steps in the Euclidean algorithm on
`(a, b)`. Returns `0` when `b = 0`, and
`1 + euclidSteps b (a % b)` otherwise. -/
def euclidSteps (a b : ℕ) : ℕ :=
  if b = 0 then 0
  else 1 + euclidSteps b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt a (Nat.pos_of_ne_zero ‹b ≠ 0›)

@[simp]
theorem euclidSteps_zero_right (a : ℕ) :
    euclidSteps a 0 = 0 := by
  simp [euclidSteps]

/-- When `b > 0`, one Euclidean step gives
`euclidSteps a b = 1 + euclidSteps b (a % b)`. -/
theorem euclidSteps_succ (a : ℕ) {b : ℕ} (hb : 0 < b) :
    euclidSteps a b = 1 + euclidSteps b (a % b) := by
  rw [euclidSteps]
  simp [Nat.not_eq_zero_of_lt (Nat.zero_lt_of_lt hb)]

/-- If the Euclidean algorithm takes at least one step, then
`b > 0`. -/
theorem euclidSteps_pos {a b : ℕ}
    (h : 0 < euclidSteps a b) : 0 < b := by
  by_contra hb
  push_neg at hb
  interval_cases b
  simp at h

/-- When `0 < b` and `b ≤ a`, we have `b + a % b ≤ a`. This
follows from `a / b ≥ 1`. -/
theorem add_mod_le {a b : ℕ} (hab : b ≤ a)
    (hb : 0 < b) : b + a % b ≤ a := by
  have h1 : 1 ≤ a / b := Nat.div_pos hab hb
  set q := a / b with hq_def
  set r := a % b with hr_def
  have h2 : q * b + r = a := Nat.div_add_mod' a b
  have h3 : b ≤ q * b := Nat.le_mul_of_pos_left b h1
  omega

/-- **Lamé's Theorem.** If the Euclidean algorithm on `(a, b)`
with `b ≤ a` takes at least `n + 1` steps, then
`fib (n + 1) ≤ b` and `fib (n + 2) ≤ a`.

This is the founding result of computational complexity: it was
the first theorem to bound an algorithm's running time using a
mathematical function (Lamé, 1844). -/
theorem fib_le_of_euclidSteps {a b : ℕ} (hab : b ≤ a)
    {n : ℕ} (hn : n + 1 ≤ euclidSteps a b) :
    fib (n + 1) ≤ b ∧ fib (n + 2) ≤ a := by
  induction n generalizing a b with
  | zero =>
    constructor
    · simp [fib_one]
      exact euclidSteps_pos
        (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
    · simp [fib_two]
      exact Nat.le_trans
        (Nat.one_le_iff_ne_zero.mpr
          (Nat.not_eq_zero_of_lt (euclidSteps_pos
            (Nat.lt_of_lt_of_le Nat.zero_lt_one hn))))
        hab
  | succ n ih =>
    have hb : 0 < b :=
      euclidSteps_pos
        (Nat.lt_of_lt_of_le (Nat.succ_pos _) hn)
    rw [euclidSteps_succ a hb] at hn
    have hn' : n + 1 ≤ euclidSteps b (a % b) := by
      omega
    have hmod_lt : a % b < b := Nat.mod_lt a hb
    have hmod_le : a % b ≤ b := Nat.le_of_lt hmod_lt
    have ⟨ih1, ih2⟩ := ih hmod_le hn'
    constructor
    · exact ih2
    · show fib (n + 1 + 2) ≤ a
      rw [show n + 1 + 2 = (n + 1) + 2 from rfl,
        @fib_add_two (n + 1)]
      change fib (n + 1) + fib (n + 2) ≤ a
      calc fib (n + 1) + fib (n + 2)
          ≤ a % b + b := by omega
        _ ≤ a := by
          have := add_mod_le hab hb; omega

/-- **Contrapositive of Lamé's theorem.** If `b < fib (n + 1)`,
then the Euclidean algorithm on `(a, b)` with `b ≤ a` takes at
most `n` steps. -/
theorem euclidSteps_le_of_lt_fib {a b : ℕ} (hab : b ≤ a)
    {n : ℕ} (hb : b < fib (n + 1)) :
    euclidSteps a b ≤ n := by
  by_contra h
  push_neg at h
  have ⟨h1, _⟩ := fib_le_of_euclidSteps hab h
  omega

end Nat
