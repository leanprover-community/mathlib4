/-
Copyright (c) 2025 Kenneth Goodman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenneth Goodman
-/
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Lamé's Theorem

Lamé's theorem (1844) is the founding result of computational
complexity theory. It bounds the number of division steps in the
Euclidean algorithm using the Fibonacci sequence.

## Main results

- `Nat.euclidSteps`: counts the number of division steps in the
  Euclidean algorithm on natural number inputs. This follows the
  same recursion as `Nat.gcd`, but counts steps instead of
  computing the result.
- `Nat.fib_le_of_euclidSteps`: **Lamé's theorem.** If the
  Euclidean algorithm on `(a, b)` with `b ≤ a` takes at least
  `n` steps with `n ≠ 0`, then `fib n ≤ b` and
  `fib (n + 1) ≤ a`.
- `Nat.euclidSteps_le_of_lt_fib`: if `b < fib (n + 1)`, then
  the Euclidean algorithm takes at most `n` steps.
- `Nat.euclidSteps_fib`: consecutive Fibonacci numbers are the
  worst case: `euclidSteps (fib (n+2)) (fib (n+1)) = n`.

## References

- Gabriel Lamé, *Note sur la limite du nombre des divisions dans
  la recherche du plus grand commun diviseur entre deux nombres
  entiers*, Comptes rendus de l'Académie des sciences, 1844.

## Tags

euclidean algorithm, fibonacci, lamé, complexity
-/

namespace Nat

/-- The number of division steps in the Euclidean algorithm on
`(a, b)`. Returns `0` when `b = 0`, and
`euclidSteps b (a % b) + 1` otherwise. -/
def euclidSteps (a b : ℕ) : ℕ :=
  if b = 0 then 0
  else euclidSteps b (a % b) + 1
termination_by b
decreasing_by exact Nat.mod_lt a (Nat.pos_of_ne_zero ‹b ≠ 0›)

@[simp]
theorem euclidSteps_zero_right (a : ℕ) :
    euclidSteps a 0 = 0 := by
  simp [euclidSteps]

/-- When `b ≠ 0`, one Euclidean step gives
`euclidSteps a b = euclidSteps b (a % b) + 1`. -/
theorem euclidSteps_of_ne_zero (a : ℕ) {b : ℕ}
    (hb : b ≠ 0) :
    euclidSteps a b = euclidSteps b (a % b) + 1 := by
  rw [euclidSteps]
  simp [hb]

/-- When `0 < b` and `b ≤ a`, we have `b + a % b ≤ a`. -/
theorem add_mod_le {a b : ℕ} (hab : b ≤ a)
    (hb : 0 < b) : b + a % b ≤ a := by
  have h1 : 1 ≤ a / b := Nat.div_pos hab hb
  set q := a / b
  set r := a % b
  have h2 : q * b + r = a := Nat.div_add_mod' a b
  have h3 : b ≤ q * b := Nat.le_mul_of_pos_left b h1
  omega

/-- **Lamé's Theorem.** If the Euclidean algorithm on `(a, b)`
with `b ≤ a` takes at least `n` steps (with `n ≠ 0`), then
`fib n ≤ b` and `fib (n + 1) ≤ a`.

This is the founding result of computational complexity: it was
the first theorem to bound an algorithm's running time using a
mathematical function (Lamé, 1844). -/
theorem fib_le_of_euclidSteps {a b : ℕ} (hab : b ≤ a)
    {n : ℕ} (hn₀ : n ≠ 0) (hn : n ≤ euclidSteps a b) :
    fib n ≤ b ∧ fib (n + 1) ≤ a := by
  induction n generalizing a b with
  | zero => exact absurd rfl hn₀
  | succ n ih =>
    have hb : b ≠ 0 := by
      intro h; subst h; simp at hn
    rw [euclidSteps_of_ne_zero a hb] at hn
    cases n with
    | zero =>
      exact ⟨Nat.pos_of_ne_zero hb,
        Nat.le_trans (Nat.pos_of_ne_zero hb) hab⟩
    | succ n =>
      have hmod_lt : a % b < b :=
        Nat.mod_lt a (Nat.pos_of_ne_zero hb)
      have hmod_le : a % b ≤ b := Nat.le_of_lt hmod_lt
      have ⟨ih1, ih2⟩ :=
        ih hmod_le (by omega) (by omega)
      constructor
      · exact ih2
      · change fib (n + 2 + 1) ≤ a
        rw [show n + 2 + 1 = (n + 1) + 2 from by omega,
          @fib_add_two (n + 1)]
        change fib (n + 1) + fib (n + 2) ≤ a
        calc fib (n + 1) + fib (n + 2)
            ≤ a % b + b := Nat.add_le_add ih1 ih2
          _ = b + a % b := by omega
          _ ≤ a := add_mod_le hab
              (Nat.pos_of_ne_zero hb)

/-- **Contrapositive of Lamé's theorem.** If `b < fib (n + 1)`,
then the Euclidean algorithm on `(a, b)` with `b ≤ a` takes at
most `n` steps. -/
theorem euclidSteps_le_of_lt_fib {a b : ℕ} (hab : b ≤ a)
    {n : ℕ} (hb : b < fib (n + 1)) :
    euclidSteps a b ≤ n := by
  by_contra h
  simp only [not_le] at h
  have ⟨h1, _⟩ := @fib_le_of_euclidSteps a b hab
    (n + 1) (by omega) (by omega)
  omega

/-- When `a < b`, one Euclidean step swaps the arguments:
`euclidSteps a b = euclidSteps b a + 1`. -/
theorem euclidSteps_of_lt {a b : ℕ} (hab : a < b) :
    euclidSteps a b = euclidSteps b a + 1 := by
  rw [euclidSteps_of_ne_zero a (by omega),
    Nat.mod_eq_of_lt hab]

/-- `fib (n + 2) % fib (n + 1) = fib n` for `1 < n`. -/
theorem fib_mod_fib_succ {n : ℕ} (hn : 1 < n) :
    fib (n + 2) % fib (n + 1) = fib n := by
  rw [fib_add_two, Nat.add_mod_right,
    Nat.mod_eq_of_lt (fib_lt_fib_succ hn)]

/-- **Tightness of Lamé's bound.** Consecutive Fibonacci numbers
are the worst case for the Euclidean algorithm:
`euclidSteps (fib (n + 2)) (fib (n + 1)) = n` for `n ≠ 0`. -/
theorem euclidSteps_fib {n : ℕ} (hn : n ≠ 0) :
    euclidSteps (fib (n + 2)) (fib (n + 1)) = n := by
  induction n with
  | zero => exact absurd rfl hn
  | succ n ih =>
    cases n with
    | zero =>
      change euclidSteps (fib 3) (fib 2) = 1
      rw [show fib 2 = 1 from rfl,
        show fib 3 = 2 from rfl]
      rw [euclidSteps_of_ne_zero _ (by omega)]
      simp
    | succ n =>
      have hfib_ne : fib (n + 2 + 1) ≠ 0 := by
        simp
      rw [euclidSteps_of_ne_zero _ hfib_ne,
        fib_mod_fib_succ (by omega : 1 < n + 2),
        ih (by omega)]

end Nat
