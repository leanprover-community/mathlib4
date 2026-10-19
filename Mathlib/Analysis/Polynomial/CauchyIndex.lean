/-
Copyright (c) 2026 Tomaz Mascarenhas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Mascarenhas, Pedro Saccomani, Sarah Pereira
-/
module

public import Mathlib.Analysis.Polynomial.SignRight

/-!
# The Cauchy index of a real rational function

The Cauchy index of `q / p` on `(a, b)` counts the jumps of the rational function
`q / p` from `-∞` to `+∞` minus those from `+∞` to `-∞` at the poles in `(a, b)`.
It is the central quantity in Sturm's theorem and the Sturm–Tarski theorem
(via Tarski queries), and also underlies the Routh–Hurwitz stability criterion and
the counting of complex roots through winding numbers

## Main definitions

* `Polynomial.rootsInInterval p a b`: the distinct roots of `p` in `(a, b)`.
* `Polynomial.jumpVal p q x`: the jump of `q / p` at `x`.
* `Polynomial.cauchyIndex p q a b`: the Cauchy index of `q / p` on `(a, b)`, the sum of the jumps
  `jumpVal p q x` over the roots `x` of `p` in `(a, b)`.

## Main results

* `Polynomial.jumpVal_of_eval_ne_zero`: `q / p` has no jump away from the roots of `p`.
* `Polynomial.jumpVal_mul_mul`, `Polynomial.cauchyIndex_mul_mul`: a common factor of `p` and `q`
  does not change the jump or the Cauchy index.
* `Polynomial.jumpVal_mod`, `Polynomial.cauchyIndex_mod`: `q` can be replaced by `q % p`.
* `Polynomial.jumpVal_C_mul`, `Polynomial.cauchyIndex_C_mul`: scaling `q` by a constant `c` scales
  the jump and the Cauchy index by `sign c`.
* `Polynomial.jumpVal_derivative_mul`: at a root `x` of `p`, the jump of `derivative p * q / p` is
  `sign (q.eval x)`. This links the Cauchy index to the sign of `q` at the roots of `p`, as needed
  for the Sturm–Tarski theorem.

## Implementation notes

We follow the definition of [li2014]: the function `q / p` has a pole of odd order at `x` exactly
when `rootMultiplicity x p - rootMultiplicity x q` is odd (with truncated subtraction, so that this
difference is `0` when `q / p` has no pole at `x`), and only poles of odd order make the function
change sign. At such a pole the direction of the jump is the sign of `p * q` (which is equal to the
sign of `q / p`) immediately to the right of `x`, that is `signRight x (p * q)`.

All definitions and results are stated over `ℝ` because `signRight` is. Apart from `signRight`,
the proofs here only use the algebra of polynomials over a field, so they should generalise to
real closed fields together with `signRight` (see the implementation notes of
`Mathlib.Analysis.Polynomial.SignRight`).

## References

* [S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*][basu2006]
* [W. Li, *The Sturm–Tarski Theorem*, Archive of Formal Proofs][li2014]
-/

open Polynomial Set SignType

public noncomputable section

namespace Polynomial

/-! ### Roots in an interval -/

/-- The distinct roots of `p` in the open interval `(a, b)`. -/
def rootsInInterval (p : ℝ[X]) (a b : ℝ) : Finset ℝ :=
  p.roots.toFinset.filter (fun x => x ∈ Ioo a b)

@[simp]
lemma rootsInInterval_zero (a b : ℝ) : rootsInInterval 0 a b = ∅ := by simp [rootsInInterval]

lemma mem_rootsInInterval {p : ℝ[X]} {a b x : ℝ} :
    x ∈ rootsInInterval p a b ↔ (p ≠ 0 ∧ eval x p = 0) ∧ a < x ∧ x < b := by
  simp [rootsInInterval, mem_roots']

lemma rootsInInterval_mul {p q : ℝ[X]} (a b : ℝ) (hpq : p * q ≠ 0) :
    rootsInInterval (p * q) a b = rootsInInterval p a b ∪ rootsInInterval q a b := by
  unfold rootsInInterval
  rw [roots_mul hpq, Multiset.toFinset_add]
  exact Finset.filter_union (fun x => x ∈ Ioo a b) p.roots.toFinset q.roots.toFinset

/-! ### The jump of a rational function at a point -/

/-- The jump of the rational function `q / p` at `x`: `1` if it goes from `-∞` to `+∞`, `-1` if it
goes from `+∞` to `-∞`, and `0` otherwise (in particular when `q / p` has no pole at `x`). -/
def jumpVal (p q : ℝ[X]) (x : ℝ) : ℤ :=
  if Odd (rootMultiplicity x p - rootMultiplicity x q) then signRight x (p * q) else 0

@[simp]
lemma jumpVal_zero_right (p : ℝ[X]) (x : ℝ) : jumpVal p 0 x = 0 := by simp [jumpVal]

@[simp]
lemma jumpVal_zero_left (q : ℝ[X]) (x : ℝ) : jumpVal 0 q x = 0 := by simp [jumpVal]

@[simp]
lemma jumpVal_of_eval_ne_zero {p q : ℝ[X]} {x : ℝ} (hp : eval x p ≠ 0) : jumpVal p q x = 0 := by
  simp [jumpVal, rootMultiplicity_eq_zero hp]

lemma jumpVal_mul_mul {p q r : Polynomial ℝ} {x : ℝ} (hr : r ≠ 0) :
                    jumpVal (r * p) (r* q) x = jumpVal p q x := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  have h_sign : signRight x (r * p * (r * q)) = signRight x (p * q) := by
    rw [show r * p * (r * q) = (r * r) * (p * q) by ring, signRight_mul,
      signRight_mul_self hr, one_mul]
  have h_odd : Odd (rootMultiplicity x (r * p) - rootMultiplicity x (r * q)) =
               Odd (rootMultiplicity x p - rootMultiplicity x q) := by
    have hp'p : r * p ≠ 0 := mul_ne_zero hr hp
    have hp'q : r * q ≠ 0 := mul_ne_zero hr hq
    simp only [rootMultiplicity_mul hp'p, rootMultiplicity_mul hp'q, eq_iff_iff]
    rw [Nat.add_sub_add_left]
  simp only [jumpVal, h_sign, h_odd]

/-- There is no jump at `x` when `q / p` has no pole there. -/
lemma jumpVal_of_rootMultiplicity_le {p q : ℝ[X]} {x : ℝ}
    (h : rootMultiplicity x p ≤ rootMultiplicity x q) : jumpVal p q x = 0 := by
  simp [jumpVal, Nat.sub_eq_zero_of_le h]

/-- If `q` does not vanish at `x`, reducing `q` modulo `p` does not change the jump at `x`. -/
lemma jumpVal_mod_of_eval_ne_zero {p q : ℝ[X]} {x : ℝ} (hq : eval x q ≠ 0) :
    jumpVal p q x = jumpVal p (q % p) x := by
  by_cases hp : eval x p = 0
  · have hqp : eval x (q % p) ≠ 0 := by rwa [eval_mod_eq_self_of_root]
    simp only [jumpVal, rootMultiplicity_eq_zero hq, rootMultiplicity_eq_zero hqp, signRight_mul,
      signRight_mod hp hq]
  · rw [jumpVal_of_eval_ne_zero hp, jumpVal_of_eval_ne_zero hp]

lemma jumpVal_mod (p q : ℝ[X]) (x : ℝ) : jumpVal p q x = jumpVal p (q % p) x := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  rcases le_or_gt (rootMultiplicity x p) (rootMultiplicity x q) with h | h
  · -- No pole on either side: `(X - C x) ^ rootMultiplicity x p` also divides `q % p`.
    rw [jumpVal_of_rootMultiplicity_le h]
    rcases eq_or_ne (q % p) 0 with h0 | h0
    · rw [h0, jumpVal_zero_right]
    refine (jumpVal_of_rootMultiplicity_le ?_).symm
    rw [le_rootMultiplicity_iff h0, EuclideanDomain.dvd_mod_iff (pow_rootMultiplicity_dvd p x)]
    exact (le_rootMultiplicity_iff hq).mp h
  · -- Cancel `(X - C x) ^ rootMultiplicity x q` from `p` and `q`.
    have hp : p ≠ 0 := by rintro rfl; simp at h
    generalize hk : rootMultiplicity x q = k at h
    obtain ⟨p', rfl⟩ := (le_rootMultiplicity_iff hp).mp h.le
    obtain ⟨q', rfl, hq'⟩ : ∃ q', q = (X - C x) ^ k * q' ∧ eval x q' ≠ 0 :=
      hk ▸ ⟨_, (pow_mul_divByMonic_rootMultiplicity_eq q x).symm,
        eval_divByMonic_pow_rootMultiplicity_ne_zero x hq⟩
    have hX : (X - C x) ^ k ≠ 0 := pow_ne_zero k (X_sub_C_ne_zero x)
    rw [mul_mod_mul_left, jumpVal_mul_mul hX, jumpVal_mul_mul hX]
    exact jumpVal_mod_of_eval_ne_zero hq'

lemma jumpVal_C_mul (p q : ℝ[X]) (c x : ℝ) :
    jumpVal p (C c * q) x = sign c * jumpVal p q x := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  simp only [jumpVal, ← rootMultiplicity_C_mul (p := q) hc, mul_left_comm p (C c) q,
    signRight_C_mul]
  split_ifs <;> simp

lemma jumpVal_of_isCoprime {p q : Polynomial ℝ} {x : ℝ} (hp : eval x p = 0)
    (hpq_coprime : IsCoprime p q) :
    jumpVal p q x = jumpVal (q*p) 1 x := by
  if hpqz: (p = 0 ∨ q = 0) then
    rcases hpqz with h | h <;> simp [h]
  else
    push Not at hpqz
    have ⟨hpz, hqz⟩ := hpqz
    have hroot : eval x p ≠ 0 ∨ eval x q ≠ 0 := aeval_ne_zero_of_isCoprime hpq_coprime x
    have hq_root : eval x q ≠ 0 := hroot.resolve_left (not_not.mpr hp)
    have hq_multiplicity : rootMultiplicity x q = 0 := rootMultiplicity_eq_zero hq_root
    have h: rootMultiplicity x p - rootMultiplicity x q = rootMultiplicity x (p * q) := by
      have : p * q ≠ 0 := mul_ne_zero_iff.mpr hpqz
      have := rootMultiplicity_mul (x := x) this
      rw [hq_multiplicity] at this ⊢
      simp [this]
    have h_one : rootMultiplicity x 1 = 0 := rootMultiplicity_C 1 x
    simp only [jumpVal, h, h_one, tsub_zero, mul_one, mul_comm p q]

/-- The jump of `p * q` at a point where `p` does not vanish is the jump of `q`, signed by `p`. -/
lemma jumpVal_mul_one_of_eval_ne_zero {p q : Polynomial ℝ} {x : ℝ} (hp : eval x p ≠ 0) :
    jumpVal (p * q) 1 x = sign (eval x p) * jumpVal q 1 x := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  have hmul : rootMultiplicity x (p * q) = rootMultiplicity x q := by
    rw [rootMultiplicity_mul (mul_ne_zero hp0 hq), rootMultiplicity_eq_zero hp, zero_add]
  have h1 : rootMultiplicity x (1 : ℝ[X]) = 0 := rootMultiplicity_eq_zero (by simp)
  simp only [jumpVal, mul_one, hmul, h1, Nat.sub_zero, signRight_mul, signRight_of_eval_ne_zero hp]
  split_ifs <;> simp

lemma jumpVal_mul_one {p q : Polynomial ℝ} {x : ℝ} (hnroot : eval x p ≠ 0 ∨ eval x q ≠ 0) :
      jumpVal (p * q) 1 x =
        sign (eval x q) * jumpVal p 1 x + sign (eval x p) * jumpVal q 1 x := by
  rcases hnroot with h | h
  · rw [jumpVal_mul_one_of_eval_ne_zero h, jumpVal_of_eval_ne_zero h, mul_zero, zero_add]
  · rw [mul_comm p q, jumpVal_mul_one_of_eval_ne_zero h, jumpVal_of_eval_ne_zero h, mul_zero,
      add_zero]

lemma jumpVal_derivative_mul (p q : ℝ[X]) (x : ℝ) :
    p ≠ 0 → p.eval x = 0 → jumpVal p (derivative p * q) x = sign (q.eval x) := by
  intro hp hev
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  have deriv_ne_0 : derivative p ≠ 0 :=
    derivative_ne_zero.mpr (natDegree_pos_iff_degree_pos.mpr (degree_pos_of_root hp hev)).ne'
  have elim_p_order :
      rootMultiplicity x p - rootMultiplicity x (derivative p * q) = 1 - rootMultiplicity x q := by
    rw [rootMultiplicity_mul (mul_ne_zero deriv_ne_0 hq), derivative_rootMultiplicity_of_root hev]
    have : 1 ≤ rootMultiplicity x p := (rootMultiplicity_pos hp).mpr hev
    omega
  have hsign : signRight x (p * (derivative p * q)) = signRight x q := by
    rw [← mul_assoc, mul_comm p, signRight_mul, signRight_derivative_mul hp hev, one_mul]
  simp only [jumpVal, elim_p_order, hsign]
  rcases eq_or_ne (eval x q) 0 with hq0 | hq0
  · have : 1 - rootMultiplicity x q = 0 := by
      have := (rootMultiplicity_pos hq).mpr hq0; omega
    simp [this, hq0]
  · simp [rootMultiplicity_eq_zero hq0, signRight_of_eval_ne_zero hq0]

/-! ### The Cauchy index -/

/-- The Cauchy index of the rational function `q / p` on the open interval `(a, b)`: the sum of the
jumps of `q / p` at the roots of `p` in `(a, b)`. -/
def cauchyIndex (p q : ℝ[X]) (a b : ℝ) : ℤ :=
  ∑ x ∈ rootsInInterval p a b, jumpVal p q x

@[simp]
theorem cauchyIndex_zero_left (q : ℝ[X]) (a b : ℝ) : cauchyIndex 0 q a b = 0 := by
  simp [cauchyIndex]

@[simp]
theorem cauchyIndex_zero_right (p : ℝ[X]) (a b : ℝ) : cauchyIndex p 0 a b = 0 := by
  simp [cauchyIndex]

/-- A constant polynomial has no roots, so `q / C c` has Cauchy index `0`. -/
@[simp]
theorem cauchyIndex_C (c : ℝ) (q : ℝ[X]) (a b : ℝ) : cauchyIndex (C c) q a b = 0 := by
  simp [cauchyIndex, rootsInInterval]

/-- A common factor of `p` and `q` does not change the Cauchy index of `q / p`. -/
theorem cauchyIndex_mul_mul {p q r : ℝ[X]} {a b : ℝ} (hr : r ≠ 0) :
    cauchyIndex (r * p) (r * q) a b = cauchyIndex p q a b := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  unfold cauchyIndex
  simp only [jumpVal_mul_mul hr]
  have hsum : ∑ x ∈ rootsInInterval r a b \ rootsInInterval p a b, jumpVal p q x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_sdiff, mem_rootsInInterval, mem_rootsInInterval] at hx
    exact jumpVal_of_eval_ne_zero fun h => hx.2 ⟨⟨hp, h⟩, hx.1.2⟩
  have h_interval : rootsInInterval (r * p) a b =
      rootsInInterval p a b ∪ (rootsInInterval r a b \ rootsInInterval p a b) := by
    rw [Finset.union_sdiff_self_eq_union, mul_comm, rootsInInterval_mul a b (mul_ne_zero hp hr)]
  rw [h_interval, Finset.sum_union Finset.disjoint_sdiff, hsum, add_zero]

/-- The Cauchy index of `q / p` only depends on `q` modulo `p`. -/
theorem cauchyIndex_mod (p q : ℝ[X]) (a b : ℝ) :
    cauchyIndex p q a b = cauchyIndex p (q % p) a b :=
  Finset.sum_congr rfl fun x _ => jumpVal_mod p q x

/-- Scaling `q` by a constant `c` scales the Cauchy index of `q / p` by `sign c`. -/
theorem cauchyIndex_C_mul (p q : ℝ[X]) (c : ℝ) (a b : ℝ) :
    cauchyIndex p (C c * q) a b = sign c * cauchyIndex p q a b := by
  simp only [cauchyIndex, Finset.mul_sum, jumpVal_C_mul]

end Polynomial
