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

-- #formalize "Concatenation of lists is associative."

-- GPT4 suggests:
-- /-- Concatenation of lists is associative. -/
-- theorem List.append_assoc {α : Type u} : ∀ (L M N : List α), (L ++ M) ++ N = L ++ (M ++ N) :=
--   sorry

-- ggml-gpt4all-j-v1.3-groovy.bin suggests:
-- {(L1 L2 L3 L4 : List α)} (L1 L2 L3 L4) L5 := L5 :: (L1 L2 L3 L4 L5)

-- 7B/ggml-model-q4_0.bin suggests:
-- ∀ {n m : List α} (o : List α → Set α), ∀ {k l : List α},
--   k (m ++ l) = (k m) ++ (k l): sorry

-- #formalize "There are infinitely many primes numbers ending with a 7."

-- GPT4 suggests:
-- /-- There are infinitely many prime numbers ending with a 7. -/
-- theorem infinitely_many_primes_ending_with_7 : ∀ N : Nat, ∃ p, N < p ∧ p.Prime ∧ p % 10 = 7 :=
--   sorry

-- ggml-gpt4all-j-v1.3-groovy.bin suggests:
-- There are infinitely many prime numbers that end with a 7.

-- 7B/ggml-model-q4_0.bin suggests:
-- ∀ p : nat, 7 < 7p + 1 := sorry
-- \end{code}

-- #formalize "The sum of the first n natural numbers."

-- GPT4 suggests:
-- /-- The sum of the first `n` natural numbers is equal to n * (n + 1) / 2. -/
-- theorem sum_of_first_n_natural_numbers (n : ℕ) :
--    (n * (n + 1)) / 2 = ∑ i in Finset.range (n + 1), i := sorry

-- 7B/ggml-model-q4_0.bin suggests:
-- 1 + ... + 2n = ∑ n (n+1)/2
-- theorem nat_sum : ∀ n : Nat, 1 + ... + 2n = ∑ n (n+1)/2 := sorry

-- #formalize "The only even prime number is 2."

-- GPT4 suggests:
-- -- /-- The only even prime number is 2. -/
-- theorem only_even_prime_is_two : ∀ p : Nat, p.Prime ∧ p % 2 = 0 → p = 2 := sorry

-- 7B/ggml-model-q4_0.bin suggests:
-- 1 : Even ∧ prime := sorry
-- \end{code}

-- #formalize "The abc conjecture."

-- GPT4 suggests:
-- theorem abc_conjecture {a b c : ℤ} (h₁ : a * b * c ≠ 0) (h₂ : gcd a b = 1) (h₃ : gcd a c = 1)
--     (h₄ : gcd b c = 1) (h₅ : a + b = c) :
--     ∃ K : ℝ, ∀ ε > 0, abs (c : ℝ) ≤ K * (rad (a * b * c))^ε :=
--   sorry

-- 7B/ggml-model-q4_0.bin suggests:
-- Ɐn  : ⇐ ∃ p ∈ ℋ, ∀ k ≥ 2, ⌈pⁿ⌉ < k (whenever p is odd). ⇐ ⇐
-- theorem abc : ∀ k : Nat,
-- ∀ n : ℕ, ∀ m : ℕ, ∃ p ∈ ℋ, ∀ q ∈ ℋ, ⌈pⁿ⌉ < k → ⌈n^m⌉ = ⌈q^m⌉ :=
-- apply lebesgue_number_lemma with (hs := is_compact_s _ _ _ _ hc₁)
--                                 (hc₂ := s ⊆ ⋃ i, c i); clear hc₁;
--   refine (lebesgue_number_lemma _ _ _ _ hc₂);
--
-- ... and then pages more, much of which looks like pseudo-Isalbelle,
--   finally ending with some Java ...
--
-- private MotechRole getRoleService() {
--     return context.getBean(MotechRoleService.class);
-- }
