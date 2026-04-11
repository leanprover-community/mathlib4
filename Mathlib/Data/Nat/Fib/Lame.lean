/-
Copyright (c) 2026 Kenneth Goodman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenneth Goodman
-/
module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Tactic.IntervalCases

/-!
# Lamé's Theorem

Lamé's theorem (1844) is the founding result of computational complexity theory. It bounds the
number of division steps in the Euclidean algorithm using the Fibonacci sequence.

## Main results

- `Nat.euclidSteps`: counts the number of division steps in the Euclidean algorithm on natural
  number inputs. This follows the same recursion as `Nat.gcd`, but counts steps instead of
  computing the result.
- `Nat.fib_le_of_euclidSteps`: **Lamé's theorem.** If the Euclidean algorithm on `(a, b)` with
  `b ≤ a` takes at least `n` steps with `n ≠ 0`, then `fib n ≤ b` and `fib (n + 1) ≤ a`.
- `Nat.euclidSteps_le_of_lt_fib`: if `b < fib (n + 1)`, then the Euclidean algorithm takes at
  most `n` steps.
- `Nat.euclidSteps_fib`: consecutive Fibonacci numbers are the worst case:
  `euclidSteps (fib (n + 2)) (fib (n + 1)) = n`.

## References

- Gabriel Lamé, *Note sur la limite du nombre des divisions dans la recherche du plus grand commun
  diviseur entre deux nombres entiers*, Comptes rendus de l'Académie des sciences, 1844.

## Tags

euclidean algorithm, fibonacci, lamé, complexity
-/

@[expose] public section

namespace Nat

/-- The number of division steps in the Euclidean algorithm on `(a, b)`. Returns `0` when
`b = 0`, and `euclidSteps b (a % b) + 1` otherwise. -/
def euclidSteps (a b : ℕ) : ℕ :=
  if b = 0 then 0 else euclidSteps b (a % b) + 1
termination_by b
decreasing_by exact Nat.mod_lt a (Nat.pos_of_ne_zero ‹b ≠ 0›)

@[simp]
theorem euclidSteps_zero_right (a : ℕ) : euclidSteps a 0 = 0 := by
  simp [euclidSteps]

theorem euclidSteps_of_ne_zero (a : ℕ) {b : ℕ} (hb : b ≠ 0) :
    euclidSteps a b = euclidSteps b (a % b) + 1 := by
  rw [euclidSteps]
  simp [hb]

/-- **Lamé's Theorem.** If the Euclidean algorithm on `(a, b)` takes at least `n` steps, then
`fib n ≤ b` and `fib (n + 1) ≤ a`. -/
theorem fib_le_of_euclidSteps {a b : ℕ} (hab : b ≤ a) {n : ℕ} (hn₀ : n ≠ 0)
    (hn : n ≤ euclidSteps a b) : fib n ≤ b ∧ fib (n + 1) ≤ a := by
  induction n generalizing a b with
  | zero => contradiction
  | succ n ih =>
    have hb : b ≠ 0 := by intro h; subst h; simp at hn
    rw [euclidSteps_of_ne_zero a hb] at hn
    cases n with
    | zero => exact ⟨Nat.pos_of_ne_zero hb, Nat.le_trans (Nat.pos_of_ne_zero hb) hab⟩
    | succ n =>
      have hmod_le : a % b ≤ b := le_of_lt (Nat.mod_lt a (Nat.pos_of_ne_zero hb))
      obtain ⟨ih1, ih2⟩ := ih hmod_le (by omega) (by omega)
      refine ⟨ih2, ?_⟩
      calc fib (n + 2 + 1)
          = fib (n + 1) + fib (n + 2) := by
            rw [show n + 2 + 1 = (n + 1) + 2 by omega, fib_add_two]
        _ ≤ a % b + b := Nat.add_le_add ih1 ih2
        _ = b + a % b := by omega
        _ ≤ a := add_mod_le hab

theorem euclidSteps_le_of_lt_fib {a b : ℕ} (hab : b ≤ a) {n : ℕ} (hb : b < fib (n + 1)) :
    euclidSteps a b ≤ n := by
  by_contra h
  simp only [not_le] at h
  exact absurd hb (not_lt.mpr (fib_le_of_euclidSteps hab (by omega) (by omega)).1)

theorem euclidSteps_of_lt {a b : ℕ} (hab : a < b) : euclidSteps a b = euclidSteps b a + 1 := by
  rw [euclidSteps_of_ne_zero a (by omega), Nat.mod_eq_of_lt hab]

/-- Consecutive Fibonacci numbers achieve the worst case for the Euclidean algorithm. -/
theorem euclidSteps_fib {n : ℕ} (hn : n ≠ 0) :
    euclidSteps (fib (n + 2)) (fib (n + 1)) = n := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    cases n with
    | zero =>
      rw [euclidSteps_of_ne_zero _ (show fib 2 ≠ 0 by simp), show fib 3 % fib 2 = 0 from rfl]
      simp
    | succ n =>
      rw [euclidSteps_of_ne_zero _ (by simp), fib_mod_fib_succ (by omega : 1 < n + 2),
        ih (by omega)]

end Nat
