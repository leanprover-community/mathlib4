/-
Copyright (c) 2026 Essam Abadir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Essam Abadir
-/
module

public import Mathlib.InformationTheory.EntropyNumber.Basic

@[expose] public section


/-!
# EntropyNat Polynomials

This file defines constructive polynomials over `EntropyNat` — functions built from
constants, the identity, addition, and multiplication — together with predicates
for polynomial-time functions and polynomial bounds.

## Main definitions

* `EntropyNumber.Polynomial` — inductive type of constructive polynomials over `EntropyNat`.
* `EntropyNumber.Polynomial.eval` — evaluate a polynomial at an `EntropyNat` input.
* `EntropyNat.IsPolynomial` — a function `EntropyNat → EntropyNat` is polynomial when it
  equals `P.eval` for some `EntropyNumber.Polynomial P`.
* `EntropyNat.IsBoundedByPolynomial` — a function `ℕ → ℕ` is bounded by a
  polynomial when there exists a `P` with `f n ≤ toNat (P.eval (ofNat n))` for
  all `n`.
* `EntropyNat.IsPolynomial.id` — the identity function is polynomial.

## Main results

(No standalone theorems beyond the `IsPolynomial.id` instance; this file
provides foundational definitions consumed by downstream complexity files.)
-/

open List

namespace InformationTheory

namespace EntropyNat

/--
**A constructive polynomial over `EntropyNat`.**

An `EntropyNumber.Polynomial` is any function on `EntropyNat`s that can be built from a
finite number of additions, multiplications, constants, and the identity
function.
-/
inductive Polynomial : Type
  | const (c : EntropyNat) : Polynomial
  | id : Polynomial
  | add (p₁ p₂ : Polynomial) : Polynomial
  | mul (p₁ p₂ : Polynomial) : Polynomial

/--
**Evaluate an `EntropyNumber.Polynomial`.**

Takes a polynomial `p` and an input `n`, and computes the result by recursively
applying the native `EntropyNat` arithmetic operations.
-/
@[simp]
def Polynomial.eval (p : Polynomial) (n : EntropyNat) : EntropyNat :=
  match p with
  | const c => c
  | id => n
  | add p₁ p₂ => EntropyNat.add (p₁.eval n) (p₂.eval n)
  | mul p₁ p₂ => EntropyNat.mul (p₁.eval n) (p₂.eval n)

/--
A predicate asserting that a function `f` from one `EntropyNat` to another is
computable by a native `EntropyNat` polynomial. The witness for this property is
the `EntropyNumber.Polynomial` structure itself.
-/
def IsPolynomial (f : EntropyNat → EntropyNat) : Prop :=
  ∃ (P : Polynomial), f = P.eval

/-- The identity function on `EntropyNat` is polynomial. -/
instance IsPolynomial.id : IsPolynomial _root_.id := by
  use Polynomial.id
  ext n
  simp [Polynomial.eval]

/--
A predicate asserting that a function `p : ℕ → ℕ` is bounded by a native
`EntropyNat` polynomial. This is the canonical definition of a polynomial bound.
-/
def IsBoundedByPolynomial (p : ℕ → ℕ) : Prop :=
  ∃ (P : Polynomial), ∀ n, p n ≤ toNat (P.eval (ofNat n))

end EntropyNat

end InformationTheory
