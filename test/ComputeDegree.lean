import Mathlib.Tactic.ComputeDegree

open Polynomial

section native_mathlib4_tests

variable {n : Nat} {z : Int} {f : Int[X]} (h : natDegree f ≤ 5)

/--  This example flows through all the matches in `direct` with a `natDegree` goal. -/
example : natDegree (- C z * X ^ 5 + (monomial 2 5) ^ 2 - 0 + 1 + IntCast.intCast 1 +
    NatCast.natCast 1 + (z : Int[X]) + (n : Int[X]) + f) ≤ 5 := by
  compute_degree_le!

/--  This example flows through all the matches in `direct` with a `degree` goal. -/
example : degree (- C z * X ^ 5 + (monomial 2 5) ^ 2 - 0 + 1 + IntCast.intCast 1 +
    NatCast.natCast 1 + (z : Int[X]) + (n : Int[X]) + f) ≤ 5 := by
  set k := f with _h₀
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

end native_mathlib4_tests

section tests_from_mathlib3
variable {R : Type _} [Semiring R] {a b c d e : R}

-- test that `mdata` does not get in the way of the tactic
example : natDegree (7 * X : R[X]) ≤ 1 := by
  have : 0 ≤ 1 := zero_le_one
  compute_degree_le

-- possibly only a vestigial test from mathlib3: maybe to check for `instantiateMVars`?
example {R : Type _} [Ring R] (h : ∀ {p q : R[X]}, p.natDegree ≤ 0 → (p * q).natDegree = 0) :
    natDegree (- 1 * 1 : R[X]) = 0 := by
  apply h _
  compute_degree_le

-- check for making sure that `compute_degree_le` is `focus`ed
example : Polynomial.natDegree (Polynomial.C 4) ≤ 1 ∧ True := by
  constructor
  compute_degree_le!
  trivial

example {R : Type _} [Ring R] :
    natDegree (- 1 * 1 : R[X]) ≤ 0 := by
  compute_degree_le

example {F} [Ring F] {a : F} :
    natDegree (X ^ 9 - C a * X ^ 10 : F[X]) ≤ 10 := by
  compute_degree_le

example :
    degree (X + (X * monomial 2 1 + X * X) ^ 2) ≤ 10 := by
  compute_degree_le!

example : natDegree (7 * X : R[X]) ≤ 1 := by
  compute_degree_le

example : natDegree (0 : R[X]) ≤ 0 := by
  compute_degree_le

example : natDegree (1 : R[X]) ≤ 0 := by
  compute_degree_le

example : natDegree (2 : R[X]) ≤ 0 := by
  compute_degree_le

example : natDegree ((n : Nat) : R[X]) ≤ 0 := by
  compute_degree_le

example {R} [Ring R] {n : Int} : natDegree ((n : Int) : R[X]) ≤ 0 := by
  compute_degree_le

example {R} [Ring R] {n : Nat} : natDegree ((- n : Int) : R[X]) ≤ 0 := by
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
  compute_degree_le!

example : natDegree (C a * C b + X + monomial 3 4 * X) ≤ 4 := by
  compute_degree_le

variable {R : Type _} [Semiring R] {a b c d e : R}

example {F} [Ring F] {a : F} :
    natDegree (X ^ 3 + C a * X ^ 10 : F[X]) ≤ 10 := by
    compute_degree_le

example : natDegree (7 * X : R[X]) ≤ 1 := by
  compute_degree_le

end tests_from_mathlib3
