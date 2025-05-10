import Mathlib

open BigOperators
open Finset

example (n : ℕ ) : n * (n + 1) / 2 + n + 1 = (n + 1) * (n + 2) / 2 := by
  unify_denoms
  ring_nf

example (n : ℕ) : ∑ i ∈ Icc 0 n, i = (n * (n + 1)) / 2 := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Finset.sum_Icc_succ_top, hn]
    unify_denoms
    ring_nf

example (n : ℕ) : ∑ i ∈ Icc 0 n, i ^ 2 = (n * (n + 1) * (2* n + 1)) / 6 := by
  induction n with
  | zero => simp
  |succ n hn =>
    rw [Finset.sum_Icc_succ_top, hn]
    unify_denoms
    ring_nf

example (a b : ℤ ) (h : a ≠ b): (a ^ 3 - b ^ 3) / (a - b) = a ^ 2 + a * b + b ^ 2 := by
  unify_denoms!
  ring
  use a ^ 2 + a * b + b ^ 2
  ring

example {T : Type} [EuclideanDomain T] (a b : T) (h : a ≠ b): (a ^ 2 - b ^ 2) / (a - b) = a + b := by
  unify_denoms!
  ring
  rw [@sub_ne_zero]
  exact h
  use a + b
  ring
