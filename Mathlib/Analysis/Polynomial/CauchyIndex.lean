/-
Copyright (c) 2026 Tomaz Mascarenhas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Mascarenhas, Pedro Saccomani, Sarah Pereira
-/
module

public import Mathlib.Analysis.Polynomial.SignRight
public import Mathlib.FieldTheory.RatFunc.Basic

/-!
# The Cauchy index of a real rational function

The Cauchy index of a rational function `f` on `(a, b)` counts the jumps of `f` from `-∞` to `+∞`
minus those from `+∞` to `-∞` at the poles of `f` in `(a, b)`. It is the central quantity in
Sturm's theorem and the Sturm–Tarski theorem (via Tarski queries), and also underlies the
Routh–Hurwitz stability criterion and the counting of complex roots through winding numbers.

## Main definitions

* `RatFunc.jump f x`: the jump of `f` at `x`.
* `RatFunc.cauchyIndex f a b`: the Cauchy index of `f` on `(a, b)`, the sum of the jumps of `f` at
  its poles in `(a, b)`.

## Main results

* `RatFunc.jump_div`: the jump of `q / p` computed from `p` and `q`, for any representation of the
  rational function as a quotient of polynomials.
* `RatFunc.jump_of_eval_denom_ne_zero`, `RatFunc.jump_algebraMap`: there is no jump away from the
  poles; in particular polynomials have no jumps.
* `RatFunc.jump_add_algebraMap`, `RatFunc.cauchyIndex_add_algebraMap`: adding a polynomial does not
  change the jump or the Cauchy index. In particular `q / p` can be replaced by `(q % p) / p`
  (`RatFunc.cauchyIndex_div_mod`).
* `RatFunc.jump_algebraMap_mul`: multiplying by a polynomial that does not vanish at `x` multiplies
  the jump at `x` by the sign of that polynomial at `x`.
* `RatFunc.jump_derivative_mul_div`: at a root `x` of `p`, the jump of `p' * q / p` is
  `sign (q.eval x)`. This links the Cauchy index to the sign of `q` at the roots of `p`, as needed
  for the Sturm–Tarski theorem.

## Implementation notes

The jump is defined algebraically, through the reduced representation `f = f.num / f.denom`. Since
`f.num` and `f.denom` are coprime, `f` has a pole of odd order at `x` exactly when
`rootMultiplicity x f.denom` is odd, and only poles of odd order make `f` change sign. At such a
pole the direction of the jump is the sign of `f.num * f.denom` (which is equal to the sign of `f`)
immediately to the right of `x`, that is `signRight x (f.num * f.denom)`. For an arbitrary
representation `f = q / p`, `RatFunc.jump_div` recovers the formula of [li2014]: the jump is
`signRight x (p * q)` when `rootMultiplicity x p - rootMultiplicity x q` is odd (with truncated
subtraction), and `0` otherwise.

All definitions and results are stated over `ℝ` because `signRight` is. Apart from `signRight`,
the proofs here only use the algebra of polynomials over a field, so they should generalise to
real closed fields together with `signRight` (see the implementation notes of
`Mathlib.Analysis.Polynomial.SignRight`).

## References

* [S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*][basu2006]
* [W. Li, *The Sturm–Tarski Theorem*, Archive of Formal Proofs][li2014]
-/

open Polynomial Set SignType
open scoped RatFunc

public noncomputable section

namespace RatFunc

/-! ### The jump of a rational function at a point -/

/-- The jump of the rational function `f` at `x`: `1` if it goes from `-∞` to `+∞`, `-1` if it
goes from `+∞` to `-∞`, and `0` otherwise (in particular when `f` has no pole at `x`). -/
def jump (f : ℝ⟮X⟯) (x : ℝ) : ℤ :=
  if Odd (rootMultiplicity x f.denom) then signRight x (f.num * f.denom) else 0

/-- There is no jump at a point that is not a pole. -/
lemma jump_of_eval_denom_ne_zero {f : ℝ⟮X⟯} {x : ℝ} (h : f.denom.eval x ≠ 0) : jump f x = 0 := by
  simp [jump, rootMultiplicity_eq_zero h]

@[simp]
lemma jump_algebraMap (p : ℝ[X]) (x : ℝ) : jump (algebraMap _ _ p) x = 0 :=
  jump_of_eval_denom_ne_zero (by simp)

@[simp]
lemma jump_zero (x : ℝ) : jump 0 x = 0 := by
  simpa using jump_algebraMap 0 x

/-- The jump of `q / p` at `x`, computed from any representation of the rational function as a
quotient of polynomials. -/
theorem jump_div {p : ℝ[X]} (q : ℝ[X]) (hp : p ≠ 0) (x : ℝ) :
    jump (algebraMap _ _ q / algebraMap _ _ p) x =
      if Odd (rootMultiplicity x p - rootMultiplicity x q) then (signRight x (p * q) : ℤ)
      else 0 := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  set f := algebraMap ℝ[X] ℝ⟮X⟯ q / algebraMap _ _ p
  have hn : f.num ≠ 0 := num_ne_zero (div_ne_zero (algebraMap_ne_zero hq) (algebraMap_ne_zero hp))
  have hd := f.denom_ne_zero
  have key : f.num * p = q * f.denom := (num_mul_eq_mul_denom_iff hp).2 rfl
  have hmult : rootMultiplicity x p - rootMultiplicity x q = rootMultiplicity x f.denom := by
    have h := congrArg (rootMultiplicity x) key
    rw [rootMultiplicity_mul (mul_ne_zero hn hp), rootMultiplicity_mul (mul_ne_zero hq hd)] at h
    have hcop : f.num.eval x ≠ 0 ∨ f.denom.eval x ≠ 0 :=
      aeval_ne_zero_of_isCoprime f.isCoprime_num_denom x
    have := hcop.imp rootMultiplicity_eq_zero rootMultiplicity_eq_zero
    omega
  have hsign : signRight x (f.num * f.denom) = signRight x (p * q) := by
    rw [← one_mul (signRight x (f.num * f.denom)), ← signRight_mul_self (x := x) hp,
      ← signRight_mul, show p * p * (f.num * f.denom) = f.denom * f.denom * (p * q) by
        linear_combination (p * f.denom) * key,
      signRight_mul, signRight_mul_self hd, one_mul]
  simp only [jump, hmult, hsign]

/-- Adding a polynomial does not change the jump. -/
@[simp]
theorem jump_add_algebraMap (f : ℝ⟮X⟯) (g : ℝ[X]) (x : ℝ) :
    jump (f + algebraMap _ _ g) x = jump f x := by
  have hd := f.denom_ne_zero
  have hf : f + algebraMap _ _ g =
      algebraMap ℝ[X] ℝ⟮X⟯ (f.num + g * f.denom) / algebraMap _ _ f.denom := by
    rw [map_add, map_mul, add_div, mul_div_cancel_right₀ _ (algebraMap_ne_zero hd), num_div_denom]
  rw [hf, jump_div _ hd]
  conv_rhs => rw [← num_div_denom f, jump_div _ hd]
  by_cases hx : f.denom.eval x = 0
  · have hn : f.num.eval x ≠ 0 :=
      (aeval_ne_zero_of_isCoprime f.isCoprime_num_denom x).resolve_right (not_not.mpr hx)
    have hng : (f.num + g * f.denom).eval x ≠ 0 := by simpa [hx] using hn
    simp only [rootMultiplicity_eq_zero hn, rootMultiplicity_eq_zero hng, signRight_mul,
      signRight_of_eval_ne_zero hn, signRight_of_eval_ne_zero hng, eval_add, eval_mul, hx,
      mul_zero, add_zero]
  · simp [rootMultiplicity_eq_zero hx]

/-- Multiplying by a polynomial `g` that does not vanish at `x` multiplies the jump at `x` by the
sign of `g` at `x`. -/
theorem jump_algebraMap_mul {g : ℝ[X]} {x : ℝ} (hg : g.eval x ≠ 0) (f : ℝ⟮X⟯) :
    jump (algebraMap _ _ g * f) x = sign (g.eval x) * jump f x := by
  have hd := f.denom_ne_zero
  have hg0 : g ≠ 0 := by rintro rfl; simp at hg
  have hf : algebraMap _ _ g * f = algebraMap ℝ[X] ℝ⟮X⟯ (g * f.num) / algebraMap _ _ f.denom := by
    rw [map_mul, mul_div_assoc, num_div_denom]
  rw [hf, jump_div _ hd]
  conv_rhs => rw [← num_div_denom f, jump_div _ hd]
  rcases eq_or_ne f.num 0 with h0 | h0
  · simp [h0]
  rw [rootMultiplicity_mul (mul_ne_zero hg0 h0), rootMultiplicity_eq_zero hg, zero_add,
    mul_left_comm f.denom g f.num, signRight_mul, signRight_of_eval_ne_zero hg]
  split_ifs <;> simp

/-- Scaling by a constant `c` scales the jump by `sign c`. -/
theorem jump_smul (c : ℝ) (f : ℝ⟮X⟯) (x : ℝ) : jump (c • f) x = sign c * jump f x := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply ℝ ℝ[X] ℝ⟮X⟯, Polynomial.algebraMap_eq,
    jump_algebraMap_mul (by simpa using hc), eval_C]

@[simp]
theorem jump_neg (f : ℝ⟮X⟯) (x : ℝ) : jump (-f) x = -jump f x := by
  rw [← neg_one_smul ℝ f, jump_smul]
  simp

/-- At a root `x` of `p`, the jump of `derivative p * q / p` is the sign of `q` at `x`. -/
theorem jump_derivative_mul_div {p : ℝ[X]} {x : ℝ} (hp : p ≠ 0) (hx : p.eval x = 0) (q : ℝ[X]) :
    jump (algebraMap _ _ (derivative p * q) / algebraMap _ _ p) x = sign (q.eval x) := by
  rw [jump_div _ hp]
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  have hp' : derivative p ≠ 0 :=
    derivative_ne_zero.mpr (natDegree_pos_iff_degree_pos.mpr (degree_pos_of_root hp hx)).ne'
  have hmult :
      rootMultiplicity x p - rootMultiplicity x (derivative p * q) = 1 - rootMultiplicity x q := by
    rw [rootMultiplicity_mul (mul_ne_zero hp' hq), derivative_rootMultiplicity_of_root hx]
    have : 1 ≤ rootMultiplicity x p := (rootMultiplicity_pos hp).mpr hx
    omega
  have hsign : signRight x (p * (derivative p * q)) = signRight x q := by
    rw [← mul_assoc, mul_comm p, signRight_mul, signRight_derivative_mul hp hx, one_mul]
  simp only [hmult, hsign]
  rcases eq_or_ne (q.eval x) 0 with hq0 | hq0
  · have : 1 - rootMultiplicity x q = 0 := by
      have := (rootMultiplicity_pos hq).mpr hq0
      omega
    simp [this, hq0]
  · simp [rootMultiplicity_eq_zero hq0, signRight_of_eval_ne_zero hq0]

/-! ### The Cauchy index -/

/-- The Cauchy index of the rational function `f` on the open interval `(a, b)`: the sum of the
jumps of `f` at its poles in `(a, b)`. The roots of `f.denom` are exactly the poles of `f`. -/
def cauchyIndex (f : ℝ⟮X⟯) (a b : ℝ) : ℤ :=
  ∑ x ∈ f.denom.roots.toFinset with (x ∈ Ioo a b), jump f x

/-- The Cauchy index can be computed as a sum over the roots of any nonzero multiple of the
denominator. -/
theorem cauchyIndex_eq_sum {f : ℝ⟮X⟯} {p : ℝ[X]} {a b : ℝ} (hp : p ≠ 0) (h : f.denom ∣ p) :
    cauchyIndex f a b = ∑ x ∈ p.roots.toFinset with (x ∈ Ioo a b), jump f x := by
  refine Finset.sum_subset (fun x hx => ?_) (fun x hx hx' => ?_)
  · rw [Finset.mem_filter, Multiset.mem_toFinset, mem_roots'] at hx ⊢
    exact ⟨⟨hp, eval_eq_zero_of_dvd_of_eval_eq_zero h hx.1.2⟩, hx.2⟩
  · rw [Finset.mem_filter, Multiset.mem_toFinset, mem_roots'] at hx hx'
    exact jump_of_eval_denom_ne_zero fun h0 => hx' ⟨⟨f.denom_ne_zero, h0⟩, hx.2⟩

/-- The Cauchy index of `q / p` is the sum of its jumps at the roots of `p`. -/
theorem cauchyIndex_div {p : ℝ[X]} (q : ℝ[X]) (hp : p ≠ 0) (a b : ℝ) :
    cauchyIndex (algebraMap _ _ q / algebraMap _ _ p) a b =
      ∑ x ∈ p.roots.toFinset with (x ∈ Ioo a b), jump (algebraMap _ _ q / algebraMap _ _ p) x :=
  cauchyIndex_eq_sum hp (denom_div_dvd q p)

@[simp]
theorem cauchyIndex_algebraMap (p : ℝ[X]) (a b : ℝ) : cauchyIndex (algebraMap _ _ p) a b = 0 :=
  Finset.sum_eq_zero fun x _ => jump_algebraMap p x

@[simp]
theorem cauchyIndex_zero (a b : ℝ) : cauchyIndex 0 a b = 0 := by
  simpa using cauchyIndex_algebraMap 0 a b

/-- Adding a polynomial does not change the Cauchy index. -/
@[simp]
theorem cauchyIndex_add_algebraMap (f : ℝ⟮X⟯) (g : ℝ[X]) (a b : ℝ) :
    cauchyIndex (f + algebraMap _ _ g) a b = cauchyIndex f a b := by
  have h : (f + algebraMap _ _ g).denom ∣ f.denom := by
    simpa using denom_add_dvd f (algebraMap _ _ g)
  rw [cauchyIndex_eq_sum f.denom_ne_zero h, cauchyIndex]
  simp only [jump_add_algebraMap]

/-- The Cauchy index of `q / p` only depends on `q` modulo `p`. -/
theorem cauchyIndex_div_mod (p q : ℝ[X]) (a b : ℝ) :
    cauchyIndex (algebraMap _ _ q / algebraMap _ _ p) a b =
      cauchyIndex (algebraMap _ _ (q % p) / algebraMap _ _ p) a b := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  conv_rhs => rw [← cauchyIndex_add_algebraMap _ (q / p)]
  rw [div_add' _ _ _ (algebraMap_ne_zero hp), ← map_mul, ← map_add, EuclideanDomain.mod_add_div']

/-- Scaling by a constant `c` scales the Cauchy index by `sign c`. -/
theorem cauchyIndex_smul (c : ℝ) (f : ℝ⟮X⟯) (a b : ℝ) :
    cauchyIndex (c • f) a b = sign c * cauchyIndex f a b := by
  have h : (c • f).denom ∣ f.denom := by
    simpa [Algebra.smul_def, IsScalarTower.algebraMap_apply ℝ ℝ[X] ℝ⟮X⟯] using
      denom_mul_dvd (algebraMap ℝ[X] ℝ⟮X⟯ (C c)) f
  rw [cauchyIndex_eq_sum f.denom_ne_zero h, cauchyIndex, Finset.mul_sum]
  simp only [jump_smul]

@[simp]
theorem cauchyIndex_neg (f : ℝ⟮X⟯) (a b : ℝ) : cauchyIndex (-f) a b = -cauchyIndex f a b := by
  rw [← neg_one_smul ℝ f, cauchyIndex_smul]
  simp

end RatFunc
