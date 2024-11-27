/-
Copyright (c) 2024 metakunt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: metakunt
-/
import Mathlib

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

/-- Theorem 6.1 Claim 1 (i) part 1. -/
lemma aks_6d1c1ip1 (p r a : ℕ) [Fact p.Prime]
    (μ: primitiveRoots r (AlgebraicClosure (ZMod p))):
    ((μ: (AlgebraicClosure (ZMod p)))-a)^p = μ^p-a :=by
  let frob := by exact frobeniusEquiv (AlgebraicClosure (ZMod p)) p
  have hfrob_cast: (a^p)= (a:(AlgebraicClosure (ZMod p))) :=by
   exact frobenius_natCast (AlgebraicClosure (ZMod p)) p a
  have hfrob_a: (↑a)^p =frob.toFun (↑a) :=by rfl
  have hfrob_mu: ((↑μ ^ p)) = frob.toFun ((↑μ )):=by rfl
  have hfrob_sub: frob.toFun (↑μ - ↑a) = frob.toFun (↑μ ) - frob.toFun ↑a :=by
   exact RingEquiv.map_sub frob (↑μ) ↑a
  conv =>
    rhs
    rw[←hfrob_cast,hfrob_a,hfrob_mu,←hfrob_sub]
  rfl
