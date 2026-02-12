import Mathlib.Tactic.ComputeDegree

open Polynomial

variable {R : Type*}

section native_mathlib4_tests

variable {n : ℕ} {z : ℤ} {f : ℤ[X]} (hn : natDegree f ≤ 5) (hd : degree f ≤ 5)

/--  Flows through all the matches in `compute_degree`, with a `natDegree _ ≤ _` goal. -/
example : natDegree (- C z * X ^ 5 + (monomial 2 5) ^ 2 - 0 + 1 + IntCast.intCast 1 +
    NatCast.natCast 1 + (z : ℤ[X]) + (n : ℤ[X]) + f) ≤ 5 := by
  compute_degree!

example [Semiring R] : natDegree (OfNat.ofNat (OfNat.ofNat 0) : R[X]) ≤ 0 := by
  compute_degree

/--  Flows through all the matches in `compute_degree`, with a `degree _ ≤ _` goal. -/
example : degree (- C z * X ^ 5 + (C 0 + monomial 2 5) ^ 2 - 0 + 1 + IntCast.intCast 1 +
    NatCast.natCast 1 + (z : ℤ[X]) + (n : ℤ[X]) + f) ≤ 5 := by
  set k := f with _h₀
  compute_degree!

/--  Flows through all the matches in `compute_degree`, with a `natDegree _ = _` goal. -/
example : natDegree (- C 1 * X ^ 5 + (C 0 + monomial 2 5) ^ 2 - 0 + 1 + IntCast.intCast 1 +
    NatCast.natCast 1 + (z : ℤ[X]) + (n : ℤ[X])) = 5 := by
  set k := f with _h₀
  compute_degree!

/--  Flows through all the matches in `compute_degree`, with a `degree _ = _` goal. -/
example : degree (- C 1 * X ^ 5 + (C 0 + monomial 2 5) ^ 2 - 0 + 1 + IntCast.intCast 1 +
    NatCast.natCast 1 + (z : ℤ[X]) + (n : ℤ[X])) = 5 := by
  set k := f with _h₀
  compute_degree!

example : degree
    ((C 1 * X ^ 2 + C 2 * X + C 3) * (C 0 * X ^ 0 + C 2 * X ^ 1 + C 1 * X ^ 5) ^ 4) = 22 := by
  compute_degree!

--  Tests `Nat.cast_withBot`
example [Semiring R] [Nontrivial R] {n : ℕ} : degree (X ^ n : R[X]) = n := by compute_degree!

example [Nontrivial R] [Ring R] : degree
    (1 + X + X ^ 2 - X ^ 5 - X ^ 6 - 2 * X ^ 7 - X ^ 8 - X ^ 9 + X ^ 12 + X ^ 13 + X ^ 14 +
        X ^ 15 + X ^ 16 + X ^ 17 - X ^ 20 - X ^ 22 - X ^ 24 - X ^ 26 - X ^ 28 + X ^ 31 + X ^ 32 +
        X ^ 33 + X ^ 34 + X ^ 35 + X ^ 36 - X ^ 39 - X ^ 40 - 2 * X ^ 41 - X ^ 42 - X ^ 43 +
        X ^ 46 + X ^ 47 + X ^ 48 : R[X]) = 48 := by
  compute_degree!

/--  Flows through all the matches in `compute_degree`, with a `degree _ ≤ _` goal. -/
example [Ring R] (g : R[X]) (hg : degree g ≤ 5) : degree (- C (z : R) * X ^ 5 + (monomial 2 5) ^ 2
    - 0 + 1 + IntCast.intCast 1 + NatCast.natCast 1 + (z : R[X]) + (n : R[X]) + g) ≤ 5 := by
  set k := g with _h₀
  compute_degree!

example {N : WithBot ℕ} (nN : n ≤ N) : degree (- C z * X ^ n) ≤ N := by compute_degree!

example [Ring R] : coeff (1 : R[X]) 0 = 1 := by compute_degree!

example [Ring R] : coeff (1 : R[X]) 2 = 0 := by compute_degree!

example [Ring R] : coeff (1 : R[X]) n = if n = 0 then 1 else 0 := by compute_degree!

example [Ring R] (h : (0 : R) = 6) : coeff (1 : R[X]) 1 = 6 := by compute_degree!

/-! Test error messages -/

/--
error: The given degree is '0'.  However,

* the coefficient of degree 0 may be zero
* there is at least one term of naïve degree 2
* there may be a term of naïve degree 2
-/
#guard_msgs in
example : natDegree (X + X ^ 2 : ℕ[X]) = 0 := by compute_degree!

/--
error: 'compute_degree' inapplicable. The goal
  X.natDegree ≠ 0
is expected to be '≤', '<' or '='.
-/
#guard_msgs in
example : natDegree (X : ℕ[X]) ≠ 0 := by compute_degree!

/--
error:
'compute_degree' inapplicable. The LHS must be an application of 'natDegree', 'degree', or 'coeff'.
-/
#guard_msgs in
example : 0 ≤ 0 := by compute_degree!

/-!  The following examples exhaust all the match-leaves in `direct`. -/

--  OfNat.ofNat 0
example : natDegree (0 : ℤ[X]) ≤ 5 := by compute_degree!

--  OfNat.ofNat (non-zero)
example : natDegree (1 : ℤ[X]) ≤ 5 := by compute_degree!

--  NatCast.natCast
example : natDegree (NatCast.natCast 4 : ℤ[X]) ≤ 5 := by compute_degree!

--  Nat.cast
example : natDegree (Nat.cast n : ℤ[X]) ≤ 5 := by compute_degree!

--  IntCast.intCast
example : natDegree (IntCast.intCast 4 : ℤ[X]) ≤ 5 := by compute_degree!

--  Int.cast
example : natDegree (Int.cast z : ℤ[X]) ≤ 5 := by compute_degree!

--  Polynomial.X
example : natDegree (X : ℤ[X]) ≤ 5 := by compute_degree!

--  Polynomial.C
example : natDegree (C n) ≤ 5 := by compute_degree!

--  Polynomial.monomial
example (h : n ≤ 5) : natDegree (monomial n (5 + n)) ≤ 5 := by compute_degree!

--  Expr.fvar
example {f : ℕ[X]} : natDegree f ≤ natDegree f := by compute_degree

variable [Ring R]

--  OfNat.ofNat 0
example : natDegree (0 : R[X]) ≤ 5 := by compute_degree!

--  OfNat.ofNat (non-zero)
example : natDegree (1 : R[X]) ≤ 5 := by compute_degree!

--  NatCast.natCast
example : natDegree (NatCast.natCast 4 : R[X]) ≤ 5 := by compute_degree!

--  Nat.cast
example : natDegree (n : R[X]) ≤ 5 := by compute_degree!

--  IntCast.intCast
example : natDegree (IntCast.intCast 4 : R[X]) ≤ 5 := by compute_degree!

--  Int.cast
example : natDegree (z : R[X]) ≤ 5 := by compute_degree!

--  Polynomial.X
example : natDegree (X : R[X]) ≤ 5 := by compute_degree!

--  Polynomial.C
example : natDegree (C n) ≤ 5 := by compute_degree!

--  Polynomial.monomial
example (h : n ≤ 5) : natDegree (monomial n (5 + n : R)) ≤ 5 := by compute_degree!

--  Expr.fvar
example {f : R[X]} : natDegree f ≤ natDegree f := by compute_degree

example {R} [Semiring R] [Nontrivial R] : Monic (1 * X ^ 5 + X ^ 6 * monomial 10 1 : R[X]) := by
  monicity!

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

example {R : Type _} [Ring R] : natDegree (- 1 * 1 : R[X]) ≤ 0 := by compute_degree

example {F} [Ring F] {a : F} : natDegree (X ^ 9 - C a * X ^ 10 : F[X]) ≤ 10 := by compute_degree

example : degree (X + (X * monomial 2 1 + X * X) ^ 2) ≤ 10 := by compute_degree!

example : natDegree (7 * X : R[X]) ≤ 1 := by compute_degree

example : natDegree (0 : R[X]) ≤ 0 := by compute_degree

example : natDegree (1 : R[X]) ≤ 0 := by compute_degree

example : natDegree (2 : R[X]) ≤ 0 := by compute_degree

example {n : ℕ} : natDegree ((n : Nat) : R[X]) ≤ 0 := by compute_degree

example {R} [Ring R] {n : ℤ} : natDegree ((n : ℤ) : R[X]) ≤ 0 := by compute_degree

example {R} [Ring R] {n : ℕ} : natDegree ((- n : ℤ) : R[X]) ≤ 0 := by compute_degree

example : natDegree (monomial 5 c * monomial 1 c + monomial 7 d +
    C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X) ≤ 10 := by compute_degree

example :
    natDegree (monomial 0 c * (monomial 0 c * C 1) + monomial 0 d + C 1 + C a * X ^ 0) ≤ 0 := by
  compute_degree

example {F} [Ring F] : natDegree (X ^ 4 + 3 : F[X]) ≤ 4 := by compute_degree

example {F} [Ring F] : natDegree ((-1) • X ^ 4 + 3 : F[X]) ≤ 4 := by compute_degree

example : natDegree ((5 * X * C 3 : _root_.Rat[X]) ^ 4) ≤ 4 := by compute_degree

example : natDegree ((C a * X) ^ 4) ≤ 4 := by compute_degree

example : degree ((X : ℤ[X]) ^ 4) ≤ 4 := by compute_degree

example : natDegree ((X : ℤ[X]) ^ 4) ≤ 40 := by compute_degree!

example : natDegree (C a * C b + X + monomial 3 4 * X) ≤ 4 := by compute_degree

example {F} [Ring F] {a : F} : natDegree (X ^ 3 + C a * X ^ 10 : F[X]) ≤ 10 := by compute_degree

example : natDegree (7 * X : R[X]) ≤ 1 := by compute_degree

example {a : R} : natDegree (a • X ^ 5 : R[X]) ≤ 5 := by
  compute_degree

example : natDegree (2 • X ^ 5 : R[X]) ≤ 5 := by
  compute_degree

example {a : R} (a0 : a ≠ 0) : natDegree (a • X ^ 5 + X : R[X]) = 5 := by
  compute_degree!

example {a : R} (a0 : a ≠ 0) : degree (a • X ^ 5 + X ^ 2 : R[X]) = 5 := by
  compute_degree!; rfl

end tests_from_mathlib3

variable [CommRing R] [Nontrivial R] in
example : (X ^ 2 + 2 • X + C 1 : R[X]).natDegree = 2 := by
  compute_degree!
  simp [coeff_X]

example : (C 1 + X * 3 * (X + 3) ^ 4 : Polynomial ℤ).natDegree < 10 := by
  compute_degree!

example : (C 1 + X * 3 * (X + 3) ^ 4 : Polynomial ℤ).degree < 10 := by
  compute_degree!

variable [CommRing R] in
example : (X ^ 2 + 2 • X + C 1 : R[X]).natDegree < 3 := by
  compute_degree!
