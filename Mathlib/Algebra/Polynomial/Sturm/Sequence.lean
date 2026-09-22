/-
Copyright (c) 2026 Tomaz Mascarenhas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Mascarenhas, Pedro Saccomani, Sarah Pereira
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Sturm sequences

This file defines the *Sturm sequence* (signed remainder sequence) of two polynomials `p` and `q`
over a field: the list `[p, q, -(p % q), …]` in which every entry from the third on is the negated
remainder of the division of the two previous entries, stopping at the last nonzero remainder.
It is the sequence produced by the Euclidean algorithm, up to signs.

For `q = derivative p` this is the sequence of Sturm's theorem, which counts the distinct real
roots of `p` in an interval as the difference of the numbers of sign variations
(`List.signVariations`) of the sequence evaluated at the endpoints. For `q = derivative p * g` it
is the sequence of the Sturm–Tarski theorem, which computes the sum of the signs of `g` at the
roots of `p`. This file only contains the algebraic properties of the sequence, which hold over any
field.

## Main definitions

* `Polynomial.sturmSeq p q`: the Sturm sequence of `p` and `q`, as a list of polynomials.

## Main results

* `Polynomial.sturmSeq_cons`: the unfolding equation
  `sturmSeq p q = p :: sturmSeq q (-p % q)` for `p ≠ 0`.
* `Polynomial.sturmSeq_zero_left`, `Polynomial.sturmSeq_zero_right`,
  `Polynomial.sturmSeq_eq_nil_iff`: the degenerate cases.
* `Polynomial.zero_notMem_sturmSeq`: no entry of a Sturm sequence is the zero polynomial.
* `Polynomial.dvd_of_mem_sturmSeq`: every common divisor of `p` and `q` divides every entry of
  `sturmSeq p q`.
* `Polynomial.sturmSeq_mul_left`: `sturmSeq (r * p) (r * q) = (sturmSeq p q).map (r * ·)` for
  `r ≠ 0`.

## Implementation notes

The definition is by well-founded recursion on the measure
`if p = 0 then 0 else if q = 0 then 1 else 2 + q.natDegree`. At every step the second argument goes
from `q` to `-p % q`, which is either `0` or of smaller degree than `q`; if `q = 0` the next call
is `sturmSeq 0 (-p)`, which is the base case. The two special values of the measure correspond to
these two terminal cases.
Proofs about `sturmSeq` should go through `sturmSeq_cons` and the functional induction principle
`sturmSeq.induct` and never unfold the definition.

## References

* [S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*][basu2006], §2.2.2
* [W. Li, *The Sturm–Tarski Theorem*, Archive of Formal Proofs][li2014]
-/

@[expose] public section

namespace Polynomial

variable {K : Type*} [Field K] [DecidableEq K]

/-- The Sturm sequence of `p` and `q`: the list `[p, q, -(p % q), …]` of successive negated
remainders, ending at the last nonzero one. -/
noncomputable def sturmSeq (p q : K[X]) : List K[X] :=
  if p = 0 then
    []
  else
    p :: (sturmSeq q (-p % q))
  termination_by if p = 0 then 0 else if q = 0 then 1 else 2 + natDegree q
  decreasing_by
    have hdeg := fun (h : -p % q ≠ 0) (hq : q ≠ 0) =>
      natDegree_lt_natDegree h (degree_mod_lt (-p) hq)
    grind

/-- The Sturm sequence of `0` and `q` is the empty sequence. -/
@[simp]
lemma sturmSeq_zero_left (q : K[X]) :
    sturmSeq 0 q = [] := by simp [sturmSeq]

/-- If `p` is not `0`, the Sturm sequence of `p` and `q` is `p` followed by the Sturm sequence of
`q` and `-p % q`. -/
lemma sturmSeq_cons {p q : K[X]} (hp : p ≠ 0) :
    sturmSeq p q = p :: sturmSeq q (-p % q) := by
  rw [sturmSeq, ite_eq_right hp]

@[simp]
lemma sturmSeq_eq_nil_iff {p q : K[X]} :
    sturmSeq p q = [] ↔ p = 0 := by
  constructor
  · intro hs
    by_contra hp
    rw [sturmSeq_cons hp] at hs
    exact List.cons_ne_nil _ _ hs
  · rintro rfl
    exact sturmSeq_zero_left q

@[simp]
lemma sturmSeq_zero_right (p : K[X]) :
    sturmSeq p 0 = if p = 0 then [] else [p] := by
  split_ifs with hp
  · exact sturmSeq_eq_nil_iff.mpr hp
  · rw [sturmSeq_cons hp, sturmSeq_zero_left]

lemma mem_sturmSeq_self {p q : K[X]} (hp : p ≠ 0) :
    p ∈ sturmSeq p q := by
  rw [sturmSeq_cons hp]; exact List.mem_cons_self

lemma zero_notMem_sturmSeq (p q : K[X]) : 0 ∉ sturmSeq p q := by
  induction p, q using sturmSeq.induct
  next q => simp
  next p q hp ih =>
    rw [sturmSeq_cons hp]
    simp [Ne.symm hp, ih]

lemma ne_zero_of_mem_sturmSeq {p q s : K[X]} (hs : s ∈ sturmSeq p q) : s ≠ 0 :=
  ne_of_mem_of_not_mem hs (zero_notMem_sturmSeq p q)

/-- The first entry of the Sturm sequence of a nonzero polynomial is the polynomial itself. -/
@[simp]
lemma head?_sturmSeq {p q : K[X]} (hp : p ≠ 0) :
    (sturmSeq p q).head? = some p := by
  rw [sturmSeq_cons hp, List.head?_cons]

/-- Every common divisor of `p` and `q` divides every entry of their Sturm sequence. In
particular this holds for `gcd p q`. -/
lemma dvd_of_mem_sturmSeq {d p q s : K[X]} (hp : d ∣ p) (hq : d ∣ q)
    (hs : s ∈ sturmSeq p q) : d ∣ s := by
  induction p, q using sturmSeq.induct
  next q => simp at hs
  next p q hp0 ih =>
    rw [sturmSeq_cons hp0, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact hp
    · exact ih hq ((EuclideanDomain.dvd_mod_iff hq).mpr (dvd_neg.mpr hp)) hs

/-- Multiplying both arguments by a nonzero polynomial multiplies every entry of the Sturm
sequence by it. -/
lemma sturmSeq_mul_left {r : K[X]} (hr : r ≠ 0) (p q : K[X]) :
    sturmSeq (r * p) (r * q) = (sturmSeq p q).map (r * ·) := by
  induction p, q using sturmSeq.induct
  next q => simp
  next p q hp ih =>
    rw [sturmSeq_cons (mul_ne_zero hr hp), sturmSeq_cons hp, List.map_cons, neg_mod,
      mul_mod_mul_left, ← mul_neg, ← neg_mod, ih]

end Polynomial
