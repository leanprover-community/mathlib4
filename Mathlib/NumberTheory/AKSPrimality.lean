/-
Copyright (c) 2024 metakunt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: metakunt
-/
import Mathlib.Algebra.CharP.ExpChar
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Existence of a polynomially bounded runtime primality testing algorithm

In 2002 Agrawal, Kayal and Saxena have proven the existence of a polynomially bounded
primality testing algorithm.

The goal of this file is to show the existence of a simultaneously general, polynomial-time,
deterministic and unconditionally correct primality test.
- The primality test is general as it works for any number given, unlike specialized tests
  that work for only a subset of numbers (e.g Mersenne numbers or Fermat numbers).
- The algorithm runtime complexity is polynomially bounded by the number of digits.
- The runtime is deterministic, as opposed probablisitic tests such as Miller-Rabin.
  If the algorithm returns prime, the number is prime.
  If the algorithm returns composite, the number is composite.
- The algorithm is unconditionally correct as it does not depend on any unproven hypotheses.

## References

<https://en.wikipedia.org/wiki/AKS_primality_test>
The proof reference is <https://www3.nd.edu/~andyp/notes/AKS.pdf>.
The paper by the original authors is
<https://www.cse.iitk.ac.in/users/manindra/algebra/primality_v6.pdf>.

The goal is to formalise Theorem 2.2, but any subresults such as parts of Theorem 6.1,
Theorem 3.1 or Lemma 4.1 are also a big step in the right direction.

## Tags

prime number, polynomial prime number test, AKS, Agrawal-Kayal-Saxena
-/

section Theorem6dot1

variable {p r a n : ℕ}

[Fact p.Prime]

variable {K : Type*}

[Field K] [CharP K p]

variable {μ : primitiveRoots r K}

/-- Theorem 6.1 Claim 1 (i) part 1. -/
lemma prime_is_introspective_for_linear_factors :
    ((μ : K)-a)^p = μ^p-a := by
  simp[← frobenius_def]

end Theorem6dot1