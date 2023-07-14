import Mathlib.Tactic.ComputeDegree

open Polynomial

variable {n : Nat} {z : Int} {f : Int[X]} (h : natDegree f ≤ 5)

/--  This example flows through all the matches in `direct` with a `natDegree` goal. -/
example : natDegree (- C z * X ^ 5 + (monomial 2 5) ^ 2 - 0 + 1 + IntCast.intCast 1 +
    NatCast.natCast 1 + (z : Int[X]) + (n : Int[X]) + f) ≤ 5 := by
  compute_degree_le!

/--  This example flows through all the matches in `direct` with a `degree` goal. -/
example : degree (- C z * X ^ 5 + (monomial 2 5) ^ 2 - 0 + 1 + IntCast.intCast 1 +
    NatCast.natCast 1 + (z : Int[X]) + (n : Int[X]) + f) ≤ 5 := by
  compute_degree_le!

/-!  The following examples exhaust all the match-leaves in `direct`. -/

--  OfNat.ofNat 0
example : natDegree (0 : Int[X]) ≤ 5 := by
  compute_degree_le!

--  OfNat.ofNat (non-zero)
example : natDegree (1 : Int[X]) ≤ 5 := by
  compute_degree_le!

--  NatCast.natCast
example : natDegree (NatCast.natCast 4 : Int[X]) ≤ 5 := by
  compute_degree_le!

--  Nat.cast
example : natDegree (n : Int[X]) ≤ 5 := by
  compute_degree_le!

--  IntCast.intCast
example : natDegree (IntCast.intCast 4 : Int[X]) ≤ 5 := by
  compute_degree_le!

--  Int.cast
example : natDegree (z : Int[X]) ≤ 5 := by
  compute_degree_le!

--  Polynomial.X
example : natDegree (X : Int[X]) ≤ 5 := by
  compute_degree_le!

--  Polynomial.C
example : natDegree (C n) ≤ 5 := by
  compute_degree_le!

--  Polynomial.monomial
example (h : n ≤ 5) : natDegree (monomial n (5 + n)) ≤ 5 := by
  compute_degree_le!

--  Expr.fvar
example {f : Nat[X]} : natDegree f ≤ natDegree f := by
  compute_degree_le
