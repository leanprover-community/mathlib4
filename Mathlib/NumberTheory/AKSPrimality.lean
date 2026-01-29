/-
Copyright (c) 2026 metakunt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: metakunt
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Order.Interval.Set.Nat
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Existence of a polynomially bounded runtime primality testing algorithm

In 2002 Agrawal, Kayal and Saxena have proven the existence of a polynomially bounded
primality testing algorithm.

The goal of this file is to show the existence of a simultaneously general, polynomial-time,
deterministic and unconditionally correct primality test.
- The primality test is general as it works for any number given, unlike specialized tests
  that work for only a subset of numbers (e.g Mersenne numbers or Fermat numbers).
- The algorithm runtime complexity is polynomially bounded by the number of digits.
- The runtime is deterministic, as opposed probabilistic tests such as Miller-Rabin.
  If the algorithm returns prime, the number is prime.
  If the algorithm returns composite, the number is composite.
- The algorithm is unconditionally correct as it does not depend on any unproven hypotheses.

## References

<https://en.wikipedia.org/wiki/AKS_primality_test>
The proof reference is <https://www3.nd.edu/~andyp/notes/AKS.pdf>.
The paper by the original authors is
<https://www.cse.iitk.ac.in/users/manindra/algebra/primality_v6.pdf>.

## Main Theorems
- `is_prime_pow_of_quotient_of_ideal_span_of_primitive_root_generator_polynomial` this is the AKS
  Primality test. If `(X + a) ^ n = X ^ n + a` modulo `(ZMod n)[X] / X ^ r - 1` and some other
  minor conditions hold, then `n` is a prime power. The coefficients `a` are polynomially bounded
  in the digit size of `n`.


## Tags

prime number, polynomial prime number test, AKS, Agrawal-Kayal-Saxena
-/

open Polynomial Finset

namespace AKS

variable {K : Type*} [CommRing K] [IsDomain K]

/-- The introspective relation, named by the original authors. It appears that this is
a definition only used for the proof of the -/
private def introspective (f : K[X]) (n : ℕ) (r : ℕ) [NeZero r] : Prop :=
  ∀ μ ∈ (primitiveRoots r K), f.eval (μ ^ n) = (f.eval μ) ^ n

variable {r : ℕ} [NeZero r]

private theorem introspective_eq {μ : K} {f : K[X]} {n : ℕ} (h : IsPrimitiveRoot μ r)
    (hi : introspective f n r) : f.eval (μ ^ n) = (f.eval μ) ^ n := by
  have _ : r ≠ 0 := NeZero.out
  exact hi μ ((mem_primitiveRoots (by lia)).mpr h)

private theorem introspective_one {f : K[X]} : introspective f 1 r := by
  grind [introspective]

private theorem introspective_p {p a : ℕ} [Fact p.Prime] [ExpChar K p] :
    introspective (X - C (a:K)) p r := by
  intro μ hμ
  simp only [eval_sub, eval_X, eval_C]
  change (frobenius K p) μ - _ = (frobenius K p) (μ - a)
  simp

private theorem introspective_n_div_p {p a n : ℕ} [Fact p.Prime] [ExpChar K p]
    (h : introspective (X - C (a : K)) n r) (hd : p ∣ n) (hc : p.Coprime r) :
    introspective (X - C (a : K)) (n / p) r := by
  simp only [map_natCast, introspective] at ⊢ h
  intro μ hμ
  have h2 : p * (n / p) = n := Nat.mul_div_cancel' hd
  simp only [eval_sub, eval_X, eval_natCast] at h ⊢
  let π := IsPrimitiveRoot.primitiveRootsPowEquivOfCoprime (R := K) hc
  replace h := h (π.symm ⟨ μ, hμ ⟩) (by grind)
  have _ : π (π.symm ⟨ μ, hμ ⟩) = μ := by simp
  revert h
  refine (Eq.congr ?_ ?_).mp
  · nth_rw 1 [sub_left_inj, ← h2, pow_mul]
    congr
  · nth_rw 1 [← h2, pow_mul]
    congr
    change (frobenius K p) _ = _
    simp only [map_sub]
    congr
    simp

/-- The product of two polynomials is introspective. -/
private theorem introspective_mul_poly {n : ℕ} {f g : K[X]} (hf : introspective f n r)
    (hg : introspective g n r) : introspective (f * g) n r := by
  intro μ hm
  simp only [eval_mul, hf μ hm, hg μ hm]
  ring

/-- The product of coprime exponents is introspective. -/
private theorem introspective_mul_of_coprime {d e : ℕ} {f : K[X]} (hf : introspective f e r)
    (hg : introspective f d r) (h : e.Coprime r) : introspective f (e * d) r := by
  intro μ hm
  have mu : μ ^ e ∈ primitiveRoots r K := by
    have ll : 0 < r := Nat.pos_of_neZero r
    simp only [mem_primitiveRoots ll] at ⊢ hm
    exact IsPrimitiveRoot.pow_of_coprime hm e h
  rw [pow_mul, hg (μ ^ e) mu, hf μ hm]
  ring

/-- Necessary condition for the auxilliary proof. -/
private theorem introspective_of_multiset {p n b : ℕ} [Fact p.Prime] [ExpChar K p] (d e : ℕ)
    (s : Multiset (Fin b)) (hs : ∀ x : (Fin b), introspective (ofMultiset {(x.val : K)}) n r)
    (hcprm: n.Coprime r) (hdiv : p ∣ n) :
    (introspective (ofMultiset (s.map (fun x => (x.val : K)))) (p ^ d * (n / p) ^ e) r) := by
  simp only [ofMultiset_apply]
  have hcprm2 := Nat.Coprime.coprime_mul_right (Eq.symm (Nat.mul_div_cancel' hdiv) ▸ hcprm)
  induction s using Multiset.induction_on with
  | empty => simp [introspective]
  | cons x l h1 =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    refine introspective_mul_poly ?_ h1
    clear h1
    refine introspective_mul_of_coprime ?_ ?_ ?_
    · induction d with
      | zero => simp [introspective_one]
      | succ i hi =>
        simp only [map_natCast, pow_succ, mul_comm]
        exact introspective_mul_of_coprime introspective_p hi hcprm2
    · induction e with
      | zero => simp [introspective_one]
      | succ i hi =>
        simp only [pow_succ, mul_comm]
        refine introspective_mul_of_coprime ?_ hi ?_
        · have hsx := hs x
          simp only [ofMultiset_apply, Multiset.map_singleton, Multiset.prod_singleton] at hsx
          exact introspective_n_div_p hsx hdiv hcprm2
        · exact Nat.Coprime.coprime_div_left hcprm hdiv
    · exact Nat.Coprime.pow_left d hcprm2

end AKS

@[expose] public section

open Nat

/-- Adds a public declaration such that the linter succeeds. See the proof_wanted in the source
    code for the theorem statement. -/
theorem is_prime_pow_of_quotient_of_ideal_span_of_primitive_root_generator_polynomial_aux : True :=
  True.intro

/-- The AKS primality test. If `(X + a) ^ n = X ^ n + a` modulo `(ZMod n)[X] / X ^ r - 1`
  and some other minor conditions hold, then `n` is a prime power.
  TODO: Finish the proof. -/
proof_wanted is_prime_pow_of_quotient_of_ideal_span_of_primitive_root_generator_polynomial
    {n r a : ℕ} (hc : n.Coprime r) (hn : 3 ≤ n) (hl : a < n)
    (ha : a = Nat.floor ((√(φ n)) * (Real.logb 2 n))) (hc2 : ∀ y ∈ Icc 1 a, n.Coprime y)
    (hod : (Real.logb 2 n) ^ 2 < orderOf (n : (ZMod r))) (heq : ∀ y ∈ Icc 1 a,
    (Ideal.Quotient.mk (Ideal.span {(X : (ZMod n)[X]) ^ r - 1}))
      ((X : (ZMod n)[X]) ^ n - (C (y : (ZMod n)))) =
    (Ideal.Quotient.mk (Ideal.span {(X : (ZMod n)[X]) ^ r - 1}))
      (((X : (ZMod n)[X]) - (C (y : (ZMod n)))) ^ n)) : IsPrimePow n
