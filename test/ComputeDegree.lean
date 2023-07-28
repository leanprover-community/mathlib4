import Mathlib.Tactic.ComputeDegree

open Polynomial

section native_mathlib4_tests

variable {n : ℕ} {z : ℤ} {f : ℤ[X]} (hn : natDegree f ≤ 5) (hd : degree f ≤ 5)

/--  This example flows through all the matches in `direct` with a `natDegree` goal. -/
example : natDegree (- C z * X ^ 5 + (monomial 2 5) ^ 2 - 0 + 1 + IntCast.intCast 1 +
    NatCast.natCast 1 + (z : ℤ[X]) + (n : ℤ[X]) + f) ≤ 5 := by
  compute_degree!

example [Semiring R] : natDegree (OfNat.ofNat (OfNat.ofNat 0) : R[X]) ≤ 0 := by
  compute_degree

/--  This example flows through all the matches in `direct` with a `degree` goal. -/
example : degree (- C z * X ^ 5 + (monomial 2 5) ^ 2 - 0 + 1 + IntCast.intCast 1 +
    NatCast.natCast 1 + (z : ℤ[X]) + (n : ℤ[X]) + f) ≤ 5 := by
  set k := f with _h₀
  compute_degree!

/--  This example flows through all the matches in `direct` with a `degree` goal. -/
example [Ring R] (g : R[X]) (hg : degree g ≤ 5) : degree (- C (z : R) * X ^ 5 + (monomial 2 5) ^ 2
    - 0 + 1 + IntCast.intCast 1 + NatCast.natCast 1 + (z : R[X]) + (n : R[X]) + g) ≤ 5 := by
  set k := g with _h₀
  compute_degree!

example {N : WithBot ℕ} (nN : n ≤ N) : degree (- C z * X ^ n) ≤ N := by
  compute_degree!

example [Ring R] : coeff (1 : R[X]) 0 = 1 := by
  compute_degree!

example [Ring R] : coeff (1 : R[X]) 2 = 0 := by
  compute_degree!

example [Ring R] : coeff (1 : R[X]) n = if 0 = n then 1 else 0 := by
  compute_degree!

example [Ring R] (h : (0 : R) = 6) : coeff (1 : R[X]) 1 = 6 := by
  compute_degree!

/-!  The following examples exhaust all the match-leaves in `direct`. -/

--  OfNat.ofNat 0
example : natDegree (0 : ℤ[X]) ≤ 5 := by
  compute_degree!

--  OfNat.ofNat (non-zero)
example : natDegree (1 : ℤ[X]) ≤ 5 := by
  compute_degree!

--  NatCast.natCast
example : natDegree (NatCast.natCast 4 : ℤ[X]) ≤ 5 := by
  compute_degree!

--  Nat.cast
example : natDegree (Nat.cast n : ℤ[X]) ≤ 5 := by
  compute_degree!

--  IntCast.intCast
example : natDegree (IntCast.intCast 4 : ℤ[X]) ≤ 5 := by
  compute_degree!

--  Int.cast
example : natDegree (Int.cast z : ℤ[X]) ≤ 5 := by
  compute_degree!

--  Polynomial.X
example : natDegree (X : ℤ[X]) ≤ 5 := by
  compute_degree!

--  Polynomial.C
example : natDegree (C n) ≤ 5 := by
  compute_degree!

--  Polynomial.monomial
example (h : n ≤ 5) : natDegree (monomial n (5 + n)) ≤ 5 := by
  compute_degree!

--  Expr.fvar
example {f : ℕ[X]} : natDegree f ≤ natDegree f := by
  compute_degree

variable [Ring R]

--  OfNat.ofNat 0
example : natDegree (0 : R[X]) ≤ 5 := by
  compute_degree!

--  OfNat.ofNat (non-zero)
example : natDegree (1 : R[X]) ≤ 5 := by
  compute_degree!

--  NatCast.natCast
example : natDegree (NatCast.natCast 4 : R[X]) ≤ 5 := by
  compute_degree!

--  Nat.cast
example : natDegree (n : R[X]) ≤ 5 := by
  compute_degree!

--  IntCast.intCast
example : natDegree (IntCast.intCast 4 : R[X]) ≤ 5 := by
  compute_degree!

--  Int.cast
example : natDegree (z : R[X]) ≤ 5 := by
  compute_degree!

--  Polynomial.X
example : natDegree (X : R[X]) ≤ 5 := by
  compute_degree!

--  Polynomial.C
example : natDegree (C n) ≤ 5 := by
  compute_degree!

--  Polynomial.monomial
example (h : n ≤ 5) : natDegree (monomial n (5 + n : R)) ≤ 5 := by
  compute_degree!

--  Expr.fvar
example {f : R[X]} : natDegree f ≤ natDegree f := by
  compute_degree

end native_mathlib4_tests

section tests_from_mathlib3
variable {R : Type _} [Semiring R] {a b c d e : R}

-- test that `mdata` does not get in the way of the tactic
example : natDegree (7 * X : R[X]) ≤ 1 := by
  have : 0 ≤ 1 := zero_le_one
  compute_degree

-- possibly only a vestigial test from mathlib3: maybe to check for `instantiateMVars`?
example {R : Type _} [Ring R] (h : ∀ {p q : R[X]}, p.natDegree ≤ 0 → (p * q).natDegree = 0) :
    natDegree (- 1 * 1 : R[X]) = 0 := by
  apply h _
  compute_degree

-- check for making sure that `compute_degree` is `focus`ed
example : Polynomial.natDegree (Polynomial.C 4) ≤ 1 ∧ True := by
  constructor
  compute_degree!
  trivial

example {R : Type _} [Ring R] :
    natDegree (- 1 * 1 : R[X]) ≤ 0 := by
  compute_degree

example {F} [Ring F] {a : F} :
    natDegree (X ^ 9 - C a * X ^ 10 : F[X]) ≤ 10 := by
  compute_degree

example :
    degree (X + (X * monomial 2 1 + X * X) ^ 2) ≤ 10 := by
  compute_degree!

example : natDegree (7 * X : R[X]) ≤ 1 := by
  compute_degree

example : natDegree (0 : R[X]) ≤ 0 := by
  compute_degree

example : natDegree (1 : R[X]) ≤ 0 := by
  compute_degree

example : natDegree (2 : R[X]) ≤ 0 := by
  compute_degree

example : natDegree ((n : Nat) : R[X]) ≤ 0 := by
  compute_degree

example {R} [Ring R] {n : ℤ} : natDegree ((n : ℤ) : R[X]) ≤ 0 := by
  compute_degree

example {R} [Ring R] {n : ℕ} : natDegree ((- n : ℤ) : R[X]) ≤ 0 := by
  compute_degree

example : natDegree (monomial 5 c * monomial 1 c + monomial 7 d +
    C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X) ≤ 10 := by
  compute_degree

example :
    natDegree (monomial 0 c * (monomial 0 c * C 1) + monomial 0 d + C 1 + C a * X ^ 0) ≤ 0 := by
  compute_degree

example {F} [Ring F] : natDegree (X ^ 4 + 3 : F[X]) ≤ 4 := by
  compute_degree

example : natDegree ((5 * X * C 3 : _root_.Rat[X]) ^ 4) ≤ 4 := by
  compute_degree

example : natDegree ((C a * X) ^ 4) ≤ 4 := by
  compute_degree

example : degree ((X : ℤ[X]) ^ 4) ≤ 4 := by
  compute_degree

example : natDegree ((X : ℤ[X]) ^ 4) ≤ 40 := by
  compute_degree!

example : natDegree (C a * C b + X + monomial 3 4 * X) ≤ 4 := by
  compute_degree

variable {R : Type _} [Semiring R] {a b c d e : R}

example {F} [Ring F] {a : F} :
    natDegree (X ^ 3 + C a * X ^ 10 : F[X]) ≤ 10 := by
    compute_degree

example : natDegree (7 * X : R[X]) ≤ 1 := by
  compute_degree

end tests_from_mathlib3
