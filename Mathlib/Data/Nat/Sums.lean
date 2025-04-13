import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
open Nat
theorem sum_first_n_odds (n : ℕ) :
    (Finset.range n).sum (λ k => 2 * k + 1) = n^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [Finset.range_succ, Finset.sum_insert Finset.not_mem_range_self, ih]
    ring
