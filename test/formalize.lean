/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Tactic.Formalize
import Mathlib.Data.Nat.Prime
import Mathlib.Algebra.BigOperators.Basic

open BigOperators

/-!
These tests are all commented out as they rely on access to an LLM,
either GPT using an OpenAI API key in the environment variable `OPENAI_API_KEY` (preferred)
or a local LLM. (Run `#formalize` without an OpenAI API key for instructions.)
-/

-- #formalize "There are infinitely many primes numbers ending with a 7."
-- /-- There are infinitely many prime numbers ending with a 7. -/
-- theorem infinitely_many_primes_ending_with_7 : ∀ N : Nat, ∃ p, N < p ∧ p.Prime ∧ p % 10 = 7 :=
--   sorry

-- #formalize "Concatenation of lists is associative."
-- /-- Concatenation of lists is associative. -/
-- theorem List.append_assoc {α : Type u} : ∀ (L M N : List α), (L ++ M) ++ N = L ++ (M ++ N) :=
--   sorry

-- #formalize "The sum of the first n natural numbers."
-- /-- The sum of the first `n` natural numbers is equal to n * (n + 1) / 2. -/
-- theorem sum_of_first_n_natural_numbers (n : ℕ) :
--    (n * (n + 1)) / 2 = ∑ i in Finset.range (n + 1), i := sorry

-- #formalize "The only even prime number is 2."
-- -- /-- The only even prime number is 2. -/
-- theorem only_even_prime_is_two : ∀ p : Nat, p.Prime ∧ p % 2 = 0 → p = 2 := sorry

-- #formalize "The abc conjecture"
-- theorem abc_conjecture {a b c : ℤ} (h₁ : a * b * c ≠ 0) (h₂ : gcd a b = 1) (h₃ : gcd a c = 1)
--     (h₄ : gcd b c = 1) (h₅ : a + b = c) :
--     ∃ K : ℝ, ∀ ε > 0, abs (c : ℝ) ≤ K * (rad (a * b * c))^ε :=
--   sorry
