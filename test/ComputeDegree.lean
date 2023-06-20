import Mathlib.Tactic.ComputeDegree

open scoped Polynomial
open Polynomial

variable {R : Type _} [Semiring R] {a b c d e : R}

example {R : Type _} [Ring R] (h : ∀ {p q : R[X]}, p.natDegree ≤ 0 → (p * q).natDegree = 0) :
    natDegree (- 1 * 1 : R[X]) = 0 := by
  apply h _
  compute_degree_le

-- check for making sure that `compute_degree_le` is `focus`ed
example : Polynomial.natDegree (Polynomial.C 4) ≤ 1 ∧ True := by
  constructor
  compute_degree_le
  trivial

example {R : Type _} [Ring R] :
    natDegree (- 1 * 1 : R[X]) ≤ 0 := by
  compute_degree_le

example {F} [Ring F] {a : F} :
    natDegree (X ^ 9 - C a * X ^ 10 : F[X]) ≤ 10 := by
  compute_degree_le

example :
    degree (X + (X * monomial 2 1 + X * X) ^ 2) ≤ 10 := by
  compute_degree_le

example : natDegree (7 * X : R[X]) ≤ 1 := by
  compute_degree_le

example : natDegree (1 : R[X]) ≤ 0 := by
  compute_degree_le

example : natDegree (2 : R[X]) ≤ 0 := by
  compute_degree_le

example : natDegree ((n : Nat) : R[X]) ≤ 0 := by
  compute_degree_le

example : natDegree (monomial 5 c * monomial 1 c + monomial 7 d +
    C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X) ≤ 10 := by
  compute_degree_le

example :
    natDegree (monomial 0 c * (monomial 0 c * C 1) + monomial 0 d + C 1 + C a * X ^ 0) ≤ 0 := by
  compute_degree_le

example {F} [Ring F] : natDegree (X ^ 4 + 3 : F[X]) ≤ 4 := by
  compute_degree_le

example : natDegree ((5 * X * C 3 : _root_.Rat[X]) ^ 4) ≤ 4 := by
  compute_degree_le

example : natDegree ((C a * X) ^ 4) ≤ 4 := by
  compute_degree_le

example : degree ((X : Int[X]) ^ 4) ≤ 4 := by
  compute_degree_le

example : natDegree ((X : Int[X]) ^ 4) ≤ 40 := by
  compute_degree_le

example : natDegree (C a * C b + X + monomial 3 4 * X) ≤ 4 := by
  compute_degree_le

variable {R : Type _} [Semiring R] {a b c d e : R}

example {F} [Ring F] {a : F} :
    natDegree (X ^ 3 + C a * X ^ 10 : F[X]) ≤ 10 := by
    compute_degree_le

example : natDegree (7 * X : R[X]) ≤ 1 := by
  compute_degree_le
