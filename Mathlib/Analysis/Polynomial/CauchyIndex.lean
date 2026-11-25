/-
Copyright (c) 2026 Tomaz Mascarenhas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Mascarenhas, Pedro Saccomani, Sarah Pereira
-/
module

public import Mathlib.Analysis.Polynomial.SignRight
public import Mathlib.FieldTheory.RatFunc.Basic

import Mathlib.Analysis.Polynomial.Order
import Mathlib.Basic.Sign.Basic

/-!
# The Cauchy index of a rational function

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
* `RatFunc.jump_eq_zero_of_eval_denom_ne_zero`, `RatFunc.jump_algebraMap`: there is no jump away
  from the poles; in particular polynomials have no jumps.
* `RatFunc.jump_add_algebraMap`, `RatFunc.cauchyIndex_add_algebraMap`: adding a polynomial does not
  change the jump or the Cauchy index. In particular `q / p` can be replaced by `(q % p) / p`
  (`RatFunc.cauchyIndex_div_mod`).
* `RatFunc.jump_algebraMap_mul`: multiplying by a polynomial that does not vanish at `x` multiplies
  the jump at `x` by the sign of that polynomial at `x`.
* `RatFunc.jump_derivative_mul_div`: at a root `x` of `p`, the jump of `p' * q / p` is
  `sign (q.eval x)`. This links the Cauchy index to the sign of `q` at the roots of `p`, as needed
  for the Sturm–Tarski theorem.
* `RatFunc.jump_inv_algebraMap`: the jump of `1 / p` at `x` is the sign of `p` immediately to the
  right of `x` if `x` is a root of `p` of odd multiplicity, and `0` otherwise.
* `RatFunc.jump_div_algebraMap`, `RatFunc.cauchyIndex_div_algebraMap`: dividing by a polynomial
  that does not vanish at `x` multiplies the jump at `x` by the sign of that polynomial at `x`;
  dividing by a polynomial of constant sign on `(a, b)` multiplies the Cauchy index on `(a, b)` by
  that sign.
* `RatFunc.jump_add_jump_inv`, `RatFunc.cauchyIndex_add_cauchyIndex_inv`: the jumps of `f` and
  `1 / f`, and hence their Cauchy indices, add up to those of `1 / (f.num * f.denom)`.
* `RatFunc.cauchyIndex_add_jump_add_cauchyIndex`: the Cauchy index is additive on adjacent
  intervals, counting the jump at the common endpoint.
* `RatFunc.cauchyIndex_congr_of_eval_denom_ne_zero`: shrinking the interval does not change the
  Cauchy index, as long as no pole is lost.
* `RatFunc.two_mul_cauchyIndex_inv_algebraMap`: the Cauchy index of `1 / p` on `(a, b)` is half
  the change of sign of `p` between `a` and `b`.
* `RatFunc.two_mul_cauchyIndex_add_cauchyIndex_inv`: the Cauchy indices of `f` and `1 / f` on
  `(a, b)` add up to half the change of sign of `f` between `a` and `b`.
  `RatFunc.two_mul_cauchyIndex_div_add_cauchyIndex_div` states this for an arbitrary quotient
  `q / p`, as needed for the recursion along a Sturm sequence.

## Implementation notes

The jump is defined algebraically, through the reduced representation `f = f.num / f.denom`. Since
`f.num` and `f.denom` are coprime, `f` has a pole of odd order at `x` exactly when
`rootMultiplicity x f.denom` is odd, and only poles of odd order make `f` change sign. At such a
pole the direction of the jump is the sign of `f.num * f.denom` (which is equal to the sign of `f`)
immediately to the right of `x`, that is `signRight x (f.num * f.denom)`. For an arbitrary
representation `f = q / p`, `RatFunc.jump_div` recovers the formula of [li2014]: the jump is
`signRight x (p * q)` when `rootMultiplicity x p - rootMultiplicity x q` is odd (with truncated
subtraction), and `0` otherwise.

Most results hold over any linearly ordered field. Those computing a Cauchy index from the signs
of a polynomial at the endpoints of the interval rely on the intermediate value theorem for
polynomials (`Polynomial.sign_eval_eq_of_forall_ne_zero`) and are stated over `ℝ`. We could also
state them over a field with `ConditionallyCompleteLinearOrder`, `Field`, `TopologicalSpace`,
`OrderTopology` and `IsStrictOrderedRing`, but any type satisfying these type classes is uniquely
isomorphic to ℝ. These lemmas should generalise to real closed fields.

## References

* [S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*][basu2006]
* [W. Li, *The Sturm–Tarski Theorem*, Archive of Formal Proofs][li2014]
-/

open Polynomial Set SignType
open scoped RatFunc

public noncomputable section

namespace RatFunc

/-! ### The jump of a rational function at a point -/

variable {K : Type*} [Field K] [LinearOrder K]

/-- The jump of the rational function `f` at `x`: `1` if it goes from `-∞` to `+∞`, `-1` if it
goes from `+∞` to `-∞`, and `0` otherwise (in particular when `f` has no pole at `x`). -/
def jump (f : K⟮X⟯) (x : K) : ℤ :=
  if Odd (f.denom.rootMultiplicity x) then signRight x (f.num * f.denom) else 0

/-- There is no jump at a point that is not a pole. -/
theorem jump_eq_zero_of_eval_denom_ne_zero {f : K⟮X⟯} {x : K} (h : f.denom.eval x ≠ 0) :
    f.jump x = 0 := by
  simp [jump, rootMultiplicity_eq_zero h]

@[simp]
theorem jump_algebraMap (p : K[X]) (x : K) : jump (algebraMap _ _ p) x = 0 :=
  jump_eq_zero_of_eval_denom_ne_zero (by simp)

@[simp]
theorem jump_zero (x : K) : jump 0 x = 0 := by
  simpa using jump_algebraMap 0 x

/-- The jump of `q / p` at `x`, computed from any representation of the rational function as a
quotient of polynomials.

Note that the statement uses truncated `ℕ` subtraction since if `x` is a root of both `p` and `q`
but with greater multiplicity in the numerator `q`, then there is no jump. -/
theorem jump_div [IsStrictOrderedRing K] (p q : K[X]) (x : K) :
    jump (algebraMap _ _ q / algebraMap _ _ p) x =
      if Odd (rootMultiplicity x p - rootMultiplicity x q) then (signRight x (p * q) : ℤ)
        else 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  set f := algebraMap K[X] K⟮X⟯ q / algebraMap _ _ p
  have hn : f.num ≠ 0 := num_ne_zero (div_ne_zero (algebraMap_ne_zero hq) (algebraMap_ne_zero hp))
  have hd := f.denom_ne_zero
  have key : f.num * p = q * f.denom := (num_mul_eq_mul_denom_iff hp).2 rfl
  have hmult : rootMultiplicity x p - rootMultiplicity x q = rootMultiplicity x f.denom := by
    have h := congrArg (rootMultiplicity x) key
    rw [rootMultiplicity_mul (mul_ne_zero hn hp), rootMultiplicity_mul (mul_ne_zero hq hd)] at h
    have := (aeval_ne_zero_of_isCoprime f.isCoprime_num_denom x).imp
      rootMultiplicity_eq_zero rootMultiplicity_eq_zero
    lia
  have hsign : signRight x (f.num * f.denom) = signRight x (p * q) := by
    have h : p * p * (f.num * f.denom) = f.denom * f.denom * (p * q) := by
      linear_combination (p * f.denom) * key
    simpa [signRight_mul x (_ * _), signRight_mul_self, hp, hd] using congrArg (signRight x) h
  simp only [jump, hmult, hsign]

/-- Adding a polynomial does not change the jump. -/
@[simp]
theorem jump_add_algebraMap [IsStrictOrderedRing K] (f : K⟮X⟯) (g : K[X]) (x : K) :
    jump (f + algebraMap _ _ g) x = jump f x := by
  have hd := f.denom_ne_zero
  have hf : f + algebraMap _ _ g =
      algebraMap K[X] K⟮X⟯ (f.num + g * f.denom) / algebraMap _ _ f.denom := by
    rw [map_add, map_mul, add_div, mul_div_cancel_right₀ _ (algebraMap_ne_zero hd), num_div_denom]
  rw [hf, jump_div]
  conv_rhs => rw [← num_div_denom f, jump_div]
  by_cases hx : f.denom.eval x = 0
  · have hn : f.num.eval x ≠ 0 :=
      (aeval_ne_zero_of_isCoprime f.isCoprime_num_denom x).resolve_right (not_not.mpr hx)
    have hng : (f.num + g * f.denom).eval x = f.num.eval x := by simp [hx]
    rw [rootMultiplicity_eq_zero hn, rootMultiplicity_eq_zero (hng.trans_ne hn), signRight_mul,
      signRight_mul, signRight_eq_of_eval_eq hng hn]
  · simp [rootMultiplicity_eq_zero hx]

@[simp]
theorem jump_algebraMap_add [IsStrictOrderedRing K] (f : K⟮X⟯) (g : K[X]) (x : K) :
    jump (algebraMap _ _ g + f) x = jump f x := by
  rw [add_comm, jump_add_algebraMap]

/-- Multiplying by a polynomial `g` that does not vanish at `x` multiplies the jump at `x` by the
sign of `g` at `x`. -/
theorem jump_algebraMap_mul [IsStrictOrderedRing K] {g : K[X]} {x : K} (hg : g.eval x ≠ 0)
    (f : K⟮X⟯) :
    jump (algebraMap _ _ g * f) x = sign (g.eval x) * jump f x := by
  have hd := f.denom_ne_zero
  have hg0 : g ≠ 0 := by rintro rfl; simp at hg
  have hf : algebraMap _ _ g * f = algebraMap K[X] K⟮X⟯ (g * f.num) / algebraMap _ _ f.denom := by
    rw [map_mul, mul_div_assoc, num_div_denom]
  rw [hf, jump_div]
  conv_rhs => rw [← num_div_denom f, jump_div]
  rcases eq_or_ne f.num 0 with h0 | h0
  · simp [h0]
  rw [rootMultiplicity_mul (mul_ne_zero hg0 h0), rootMultiplicity_eq_zero hg, zero_add,
    mul_left_comm f.denom g f.num, signRight_mul, signRight_of_eval_ne_zero hg]
  split_ifs <;> simp

/-- Scaling by a constant `c` scales the jump by `sign c`. -/
theorem jump_smul [IsStrictOrderedRing K] (c : K) (f : K⟮X⟯) (x : K) :
    jump (c • f) x = sign c * jump f x := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply K K[X] K⟮X⟯, Polynomial.algebraMap_eq,
    jump_algebraMap_mul (by simpa using hc), eval_C]

@[simp]
theorem jump_neg [IsStrictOrderedRing K] (f : K⟮X⟯) (x : K) : jump (-f) x = -jump f x := by
  rw [← neg_one_smul K f, jump_smul]
  simp

/-- At a root `x` of `p`, the jump of `derivative p * q / p` is the sign of `q` at `x`. -/
theorem jump_derivative_mul_div [IsStrictOrderedRing K] {p : K[X]} {x : K}
    (hp : p ≠ 0) (hx : p.eval x = 0) (q : K[X]) :
    jump (algebraMap _ _ (derivative p * q) / algebraMap _ _ p) x = sign (q.eval x) := by
  rw [jump_div]
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  have hp' : derivative p ≠ 0 :=
    derivative_ne_zero.mpr (natDegree_pos_iff_degree_pos.mpr (degree_pos_of_root hp hx)).ne'
  have hmult :
      rootMultiplicity x p - rootMultiplicity x (derivative p * q) = 1 - rootMultiplicity x q := by
    rw [rootMultiplicity_mul (mul_ne_zero hp' hq), derivative_rootMultiplicity_of_root hx]
    have : 1 ≤ rootMultiplicity x p := (rootMultiplicity_pos hp).mpr hx
    lia
  have hsign : signRight x (p * (derivative p * q)) = signRight x q := by
    rw [← mul_assoc, mul_comm p, signRight_mul, signRight_derivative_mul hp hx, one_mul]
  simp only [hmult, hsign]
  rcases eq_or_ne (q.eval x) 0 with hq0 | hq0
  · simp [Nat.sub_eq_zero_of_le ((rootMultiplicity_pos hq).mpr hq0), hq0]
  · simp [rootMultiplicity_eq_zero hq0, signRight_of_eval_ne_zero hq0]

/-! ### The `jump` of the inverse of a polynomial -/

/-- The jump of `1 / p` at `x`: the sign of `p` to the right of `x` if `x` is a root of `p` of odd
multiplicity, and `0` otherwise. -/
@[simp]
theorem jump_inv_algebraMap [IsStrictOrderedRing K] (p : K[X]) (x : K) :
    jump (algebraMap K[X] K⟮X⟯ p)⁻¹ x =
      if Odd (rootMultiplicity x p) then (signRight x p : ℤ) else 0 := by
  have h := jump_div p (1 : K[X]) x
  rwa [map_one, one_div, mul_one, rootMultiplicity_eq_zero (p := 1) (by simp), Nat.sub_zero] at h

/-- Dividing by a polynomial `g` that does not vanish at `x` multiplies the jump at `x` by the
sign of `g` at `x`. -/
theorem jump_div_algebraMap [IsStrictOrderedRing K] {g : K[X]} {x : K} (hg : g.eval x ≠ 0)
    (f : K⟮X⟯) : jump (f / algebraMap _ _ g) x = sign (g.eval x) * jump f x := by
  have hg0 : g ≠ 0 := by rintro rfl; simp at hg
  have h := jump_algebraMap_mul hg (f / algebraMap _ _ g)
  rw [mul_div_cancel₀ _ (algebraMap_ne_zero hg0)] at h
  rcases lt_or_gt_of_ne hg with hlt | hgt
  · simp_all [sign_neg hlt]
  · simp_all [sign_pos hgt]

/-- The jumps of `f` and of `1 / f` at `x` add up to the jump of `1 / (f.num * f.denom)`: since
`f.num` and `f.denom` are coprime, `x` is a pole of at most one of `f` and `1 / f`. -/
theorem jump_add_jump_inv [IsStrictOrderedRing K] (f : K⟮X⟯) (x : K) :
    jump f x + jump f⁻¹ x = jump (algebraMap K[X] K⟮X⟯ (f.num * f.denom))⁻¹ x := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hn : f.num ≠ 0 := num_ne_zero hf
  have hinv : f⁻¹ = algebraMap _ _ f.denom / algebraMap _ _ f.num := by
    rw [← inv_div, num_div_denom]
  have hcop : f.num.eval x ≠ 0 ∨ f.denom.eval x ≠ 0 :=
    aeval_ne_zero_of_isCoprime f.isCoprime_num_denom x
  rw [jump_inv_algebraMap, rootMultiplicity_mul (mul_ne_zero hn f.denom_ne_zero), hinv,
    jump_div _, jump]
  rcases hcop with h | h <;> simp [rootMultiplicity_eq_zero h]

/-! ### The Cauchy index -/

/-- The Cauchy index of the rational function `f` on the open interval `(a, b)`: the sum of the
jumps of `f` at its poles in `(a, b)`. The roots of `f.denom` are exactly the poles of `f`. -/
def cauchyIndex (f : K⟮X⟯) (a b : K) : ℤ :=
  ∑ x ∈ f.denom.roots.toFinset with x ∈ Ioo a b, f.jump x

/-- The Cauchy index can be computed as a sum over the roots of any nonzero multiple of the
denominator. -/
theorem cauchyIndex_eq_sum {f : K⟮X⟯} {p : K[X]} {a b : K} (hp : p ≠ 0) (h : f.denom ∣ p) :
    f.cauchyIndex a b = ∑ x ∈ p.roots.toFinset with x ∈ Ioo a b, f.jump x := by
  refine Finset.sum_subset (fun x hx => ?_) (fun x hx hx' => ?_)
  · rw [Finset.mem_filter, Multiset.mem_toFinset, mem_roots'] at hx ⊢
    exact ⟨⟨hp, eval_eq_zero_of_dvd_of_eval_eq_zero h hx.1.2⟩, hx.2⟩
  · rw [Finset.mem_filter, Multiset.mem_toFinset, mem_roots'] at hx hx'
    exact jump_eq_zero_of_eval_denom_ne_zero fun h0 => hx' ⟨⟨f.denom_ne_zero, h0⟩, hx.2⟩

/-- The Cauchy index of `q / p` is the sum of its jumps at the roots of `p`. -/
theorem cauchyIndex_div (p q : K[X]) (a b : K) :
    cauchyIndex (algebraMap _ _ q / algebraMap _ _ p) a b =
      ∑ x ∈ p.roots.toFinset with x ∈ Ioo a b, jump (algebraMap _ _ q / algebraMap _ _ p) x := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp [cauchyIndex]
  exact cauchyIndex_eq_sum hp (denom_div_dvd q p)

@[simp]
theorem cauchyIndex_algebraMap (p : K[X]) (a b : K) : cauchyIndex (algebraMap _ _ p) a b = 0 :=
  Finset.sum_eq_zero fun x _ => jump_algebraMap p x

@[simp]
theorem cauchyIndex_zero (a b : K) : cauchyIndex 0 a b = 0 := by
  simpa using cauchyIndex_algebraMap 0 a b

/-- The Cauchy index on an empty interval is zero. -/
theorem cauchyIndex_of_le (f : K⟮X⟯) {a b : K} (h : b ≤ a) : cauchyIndex f a b = 0 := by
  simp [cauchyIndex, Ioo_eq_empty_of_le h]

/-- Adding a polynomial does not change the Cauchy index. -/
@[simp]
theorem cauchyIndex_add_algebraMap [IsStrictOrderedRing K] (f : K⟮X⟯) (g : K[X]) (a b : K) :
    cauchyIndex (f + algebraMap _ _ g) a b = cauchyIndex f a b := by
  have h : (f + algebraMap _ _ g).denom ∣ f.denom := by
    simpa using denom_add_dvd f (algebraMap _ _ g)
  rw [cauchyIndex_eq_sum f.denom_ne_zero h, cauchyIndex]
  simp only [jump_add_algebraMap]

@[simp]
theorem cauchyIndex_algebraMap_add [IsStrictOrderedRing K] (f : K⟮X⟯) (g : K[X]) (a b : K) :
    cauchyIndex (algebraMap _ _ g + f) a b = cauchyIndex f a b := by
  rw [add_comm, cauchyIndex_add_algebraMap]

/-- The Cauchy index of `q / p` only depends on `q` modulo `p`. -/
theorem cauchyIndex_div_mod [IsStrictOrderedRing K] (p q : K[X]) (a b : K) :
    cauchyIndex (algebraMap _ _ q / algebraMap _ _ p) a b =
      cauchyIndex (algebraMap _ _ (q % p) / algebraMap _ _ p) a b := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  conv_rhs => rw [← cauchyIndex_add_algebraMap _ (q / p)]
  rw [div_add' _ _ _ (algebraMap_ne_zero hp), ← map_mul, ← map_add, EuclideanDomain.mod_add_div']

/-- Scaling by a constant `c` scales the Cauchy index by `sign c`. -/
theorem cauchyIndex_smul [IsStrictOrderedRing K] (c : K) (f : K⟮X⟯) (a b : K) :
    cauchyIndex (c • f) a b = sign c * cauchyIndex f a b := by
  have h : (c • f).denom ∣ f.denom := by
    simpa [Algebra.smul_def, IsScalarTower.algebraMap_apply K K[X] K⟮X⟯] using
      denom_mul_dvd (algebraMap K[X] K⟮X⟯ (C c)) f
  rw [cauchyIndex_eq_sum f.denom_ne_zero h, cauchyIndex, Finset.mul_sum]
  simp only [jump_smul]

@[simp]
theorem cauchyIndex_neg [IsStrictOrderedRing K] (f : K⟮X⟯) (a b : K) :
    cauchyIndex (-f) a b = -cauchyIndex f a b := by
  rw [← neg_one_smul K f, cauchyIndex_smul]
  simp

/-! ### Modifying the interval -/

/-- The Cauchy index vanishes on an interval without poles. -/
theorem cauchyIndex_eq_zero_of_forall_eval_denom_ne_zero {f : K⟮X⟯} {a b : K}
    (h : ∀ x ∈ Ioo a b, f.denom.eval x ≠ 0) : cauchyIndex f a b = 0 :=
  Finset.sum_eq_zero fun x hx =>
    jump_eq_zero_of_eval_denom_ne_zero (h x (Finset.mem_filter.mp hx).2)

/-- The Cauchy index is additive on adjacent intervals, counting the jump at the common
endpoint. -/
theorem cauchyIndex_add_jump_add_cauchyIndex (f : K⟮X⟯) {a r b : K} (har : a < r) (hrb : r < b) :
    cauchyIndex f a r + jump f r + cauchyIndex f r b = cauchyIndex f a b := by
  have hr : jump f r = ∑ x ∈ f.denom.roots.toFinset with x = r, jump f x := by
    rw [Finset.filter_eq']
    split_ifs with h
    · simp
    · rw [Finset.sum_empty]
      refine jump_eq_zero_of_eval_denom_ne_zero fun h0 => h ?_
      simp [f.denom_ne_zero, h0]
  simp only [cauchyIndex, hr, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine (Finset.sum_congr rfl fun x _ => ?_).symm
  rcases lt_trichotomy x r with h | rfl | h
  · simp [h, h.ne, h.not_gt, h.trans hrb]
  · simp [har, hrb]
  · simp [h, h.ne', h.not_gt, har.trans h]

/-- Shrinking the interval does not change the Cauchy index, as long as no pole is lost. -/
theorem cauchyIndex_congr_of_eval_denom_ne_zero {f : K⟮X⟯} {a₁ a₂ b₁ b₂ : K} (ha : a₁ ≤ a₂)
    (hb : b₂ ≤ b₁) (hfa : ∀ x ∈ Ioc a₁ a₂, f.denom.eval x ≠ 0)
    (hfb : ∀ x ∈ Ico b₂ b₁, f.denom.eval x ≠ 0) :
    cauchyIndex f a₁ b₁ = cauchyIndex f a₂ b₂ := by
  refine Finset.sum_congr (Finset.filter_congr fun x hx => ?_) fun _ _ => rfl
  have hx0 : f.denom.eval x = 0 := (mem_roots'.mp (Multiset.mem_toFinset.mp hx)).2
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ⟨ha.trans_lt h.1, h.2.trans_le hb⟩⟩
  · by_contra hxa
    exact hfa x ⟨h.1, not_lt.mp hxa⟩ hx0
  · by_contra hxb
    exact hfb x ⟨not_lt.mp hxb, h.2⟩ hx0

/-- Dividing by a polynomial `g` of constant sign `s` on `(a, b)` multiplies the Cauchy index on
`(a, b)` by `s`. -/
theorem cauchyIndex_div_algebraMap [IsStrictOrderedRing K] {g : K[X]} {s : SignType} {a b : K}
    (f : K⟮X⟯) (hs : s ≠ 0) (hg : ∀ x ∈ Ioo a b, sign (g.eval x) = s) :
    cauchyIndex (f / algebraMap _ _ g) a b = s * cauchyIndex f a b := by
  rcases (Ioo a b).eq_empty_or_nonempty with he | ⟨y, hy⟩
  · simp [cauchyIndex, he]
  have hgx {x : K} (hx : x ∈ Ioo a b) : g.eval x ≠ 0 := by
    rw [← sign_ne_zero, hg x hx]
    exact hs
  have hp : f.denom * g ≠ 0 :=
    mul_ne_zero f.denom_ne_zero (by rintro rfl; exact hgx hy eval_zero)
  -- `f / g = f.num / (f.denom * g)`, so the poles of `f / g` are roots of `f.denom * g`
  have hd : (f / algebraMap _ _ g).denom ∣ f.denom * g := by
    have h := denom_div_dvd f.num (f.denom * g)
    rwa [map_mul, ← div_div, num_div_denom] at h
  rw [cauchyIndex_eq_sum hp hd, cauchyIndex_eq_sum hp (dvd_mul_right _ _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.mem_filter] at hx
  rw [jump_div_algebraMap (hgx hx.2), hg x hx.2]

/-- The Cauchy index of `1 / p` on `(a, b)` is half the change of sign of `p` between `a` and
`b`. -/
theorem two_mul_cauchyIndex_inv_algebraMap {p : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    2 * cauchyIndex (algebraMap ℝ[X] ℝ⟮X⟯ p)⁻¹ a b = sign (p.eval b) - sign (p.eval a) := by
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p a b with
  | _ n ih =>
  have hp0 : p ≠ 0 := by rintro rfl; simp at ha
  -- on an empty interval both sides vanish
  rcases hab.eq_or_lt with rfl | hab
  · simp [cauchyIndex]
  by_cases hroot : ∀ x ∈ Ioo a b, p.eval x ≠ 0
  · -- no root in `(a, b)`: no jump, and `p` keeps its sign
    have hIcc : ∀ x ∈ uIcc a b, ¬p.IsRoot x := by
      rw [uIcc_of_le hab.le, ← insert_left_Ioc hab.le, ← insert_right_Ioo hab]
      exact forall_mem_insert.mpr ⟨ha, forall_mem_insert.mpr ⟨hb, hroot⟩⟩
    rw [sign_eval_eq_of_forall_ne_zero hIcc, sub_self,
      cauchyIndex_eq_zero_of_forall_eval_denom_ne_zero fun x hx h0 =>
        hroot x hx (eval_eq_zero_of_dvd_of_eval_eq_zero (denom_inv_algebraMap_dvd p) h0),
      mul_zero]
  -- otherwise split `(a, b)` at a root `r` and factor it out: `p = (X - C r) ^ m * g`
  push Not at hroot
  obtain ⟨r, ⟨har, hrb⟩, hr⟩ := hroot
  obtain ⟨g, hpg, hg⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp0 r
  have hm : 0 < rootMultiplicity r p := (rootMultiplicity_pos hp0).mpr hr
  generalize rootMultiplicity r p = m at hpg hm
  subst hpg
  have hgr : g.eval r ≠ 0 := fun h => hg (dvd_iff_isRoot.mpr h)
  have hg0 : g ≠ 0 := by rintro rfl; simp at hgr
  have hga : g.eval a ≠ 0 := by rintro h; simp [h] at ha
  have hgb : g.eval b ≠ 0 := by rintro h; simp [h] at hb
  have hdeg : g.natDegree < n := by
    rw [← hn, natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero r)) hg0, natDegree_pow,
      natDegree_X_sub_C]
    lia
  -- the sign of `(x - r) ^ m` on each side of `r`
  have hlt {x : ℝ} (hx : x < r) :
      sign (((X - C r) ^ m).eval x) = if Odd m then -1 else 1 := by
    rw [eval_pow, eval_sub, eval_X, eval_C]
    split_ifs with hodd
    · exact sign_neg (hodd.pow_neg (sub_neg.mpr hx))
    · exact sign_pos ((Nat.not_odd_iff_even.mp hodd).pow_pos (sub_ne_zero.mpr hx.ne))
  have hgt {x : ℝ} (hx : r < x) : sign (((X - C r) ^ m).eval x) = 1 := by
    rw [eval_pow, eval_sub, eval_X, eval_C]
    exact sign_pos (pow_pos (sub_pos.mpr hx) m)
  -- `1 / p = (1 / g) / (X - C r) ^ m`, so on each side of `r` the Cauchy index of `1 / p` is
  -- that of `1 / g` up to this sign
  have hfg : (algebraMap ℝ[X] ℝ⟮X⟯ ((X - C r) ^ m * g))⁻¹ =
      (algebraMap ℝ[X] ℝ⟮X⟯ g)⁻¹ / algebraMap _ _ ((X - C r) ^ m) := by
    rw [map_mul, mul_inv, div_eq_mul_inv, mul_comm]
  have hleft := cauchyIndex_div_algebraMap (a := a) (b := r) (algebraMap ℝ[X] ℝ⟮X⟯ g)⁻¹
    (s := if Odd m then -1 else 1) (by split_ifs <;> decide) fun x hx => hlt hx.2
  have hright := cauchyIndex_div_algebraMap (a := r) (b := b) (algebraMap ℝ[X] ℝ⟮X⟯ g)⁻¹
    one_ne_zero fun x hx => hgt hx.1
  -- at `r`, the jump is `sign (g.eval r)` if `m` is odd and `0` otherwise
  have hjump : jump (algebraMap ℝ[X] ℝ⟮X⟯ ((X - C r) ^ m * g))⁻¹ r =
      if Odd m then (sign (g.eval r) : ℤ) else 0 := by
    rw [jump_inv_algebraMap, rootMultiplicity_mul hp0, rootMultiplicity_X_sub_C_pow,
      rootMultiplicity_eq_zero hgr, add_zero, signRight_mul, signRight_X_sub_C_pow,
      signRight_of_eval_ne_zero hgr, one_mul]
  have ihl := ih _ hdeg har.le hga hgr rfl
  have ihr := ih _ hdeg hrb.le hgr hgb rfl
  rw [← cauchyIndex_add_jump_add_cauchyIndex _ har hrb, hjump, hfg, hleft, hright, eval_mul,
    eval_mul, sign_mul, sign_mul, hlt har, hgt hrb]
  split_ifs <;> simp only [coe_neg, coe_one, neg_mul, one_mul] <;> linarith

/-! ### The Cauchy index of a rational function and of its inverse -/

/-- The Cauchy indices of `f` and `1 / f` add up to the Cauchy index of
`1 / (f.num * f.denom)`. -/
theorem cauchyIndex_add_cauchyIndex_inv [IsStrictOrderedRing K] (f : K⟮X⟯) (a b : K) :
    cauchyIndex f a b + cauchyIndex f⁻¹ a b =
      cauchyIndex (algebraMap K[X] K⟮X⟯ (f.num * f.denom))⁻¹ a b := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hp : f.num * f.denom ≠ 0 := mul_ne_zero (num_ne_zero hf) f.denom_ne_zero
  rw [cauchyIndex_eq_sum hp (dvd_mul_left f.denom f.num),
    cauchyIndex_eq_sum hp ((denom_inv_dvd f).trans (dvd_mul_right f.num f.denom)),
    cauchyIndex_eq_sum hp (denom_inv_algebraMap_dvd _), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => jump_add_jump_inv f x

/-- The Cauchy indices of `f` and `1 / f` on `(a, b)` add up to half the change of sign of
`f.num * f.denom` (equivalently, of `f`) between `a` and `b`. -/
theorem two_mul_cauchyIndex_add_cauchyIndex_inv {f : ℝ⟮X⟯} {a b : ℝ} (hab : a ≤ b)
    (hna : f.num.eval a ≠ 0) (hda : f.denom.eval a ≠ 0)
    (hnb : f.num.eval b ≠ 0) (hdb : f.denom.eval b ≠ 0) :
    2 * (cauchyIndex f a b + cauchyIndex f⁻¹ a b) =
      sign ((f.num * f.denom).eval b) - sign ((f.num * f.denom).eval a) := by
  rw [cauchyIndex_add_cauchyIndex_inv]
  exact two_mul_cauchyIndex_inv_algebraMap hab (by simp [hna, hda]) (by simp [hnb, hdb])

/-- Away from the roots of `p`, the sign of `f.num * f.denom` for `f = q / p` is the sign of
`p * q`. -/
theorem sign_eval_num_mul_denom_div [IsStrictOrderedRing K] {p : K[X]} (q : K[X]) {x : K}
    (hp : p.eval x ≠ 0) :
    sign (((algebraMap K[X] K⟮X⟯ q / algebraMap _ _ p).num *
      (algebraMap K[X] K⟮X⟯ q / algebraMap _ _ p).denom).eval x) = sign ((p * q).eval x) := by
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  set f := algebraMap K[X] K⟮X⟯ q / algebraMap _ _ p
  have key : f.num * p = q * f.denom := (num_mul_eq_mul_denom_iff hp0).2 rfl
  have hd : f.denom.eval x ≠ 0 := fun h =>
    hp (eval_eq_zero_of_dvd_of_eval_eq_zero (denom_div_dvd q p) h)
  have h : (f.num * f.denom).eval x * p.eval x ^ 2 = (p * q).eval x * f.denom.eval x ^ 2 := by
    have := congrArg (eval x) key
    simp only [eval_mul] at this ⊢
    linear_combination (f.denom.eval x * p.eval x) * this
  have hp2 : 0 < p.eval x ^ 2 := by positivity
  have hd2 : 0 < f.denom.eval x ^ 2 := by positivity
  have := congrArg sign h
  rwa [sign_mul, sign_mul, sign_pos hp2, sign_pos hd2, mul_one, mul_one] at this

/-- The Cauchy indices of `q / p` and `p / q` on `(a, b)` add up to half the change of sign of
`p * q` between `a` and `b`, for any polynomials `p` and `q` not vanishing at `a` and `b`. -/
theorem two_mul_cauchyIndex_div_add_cauchyIndex_div {p q : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (hpa : p.eval a ≠ 0) (hqa : q.eval a ≠ 0)
    (hpb : p.eval b ≠ 0) (hqb : q.eval b ≠ 0) :
    2 * (cauchyIndex (algebraMap _ _ q / algebraMap _ _ p) a b +
      cauchyIndex (algebraMap _ _ p / algebraMap _ _ q) a b) =
      sign ((p * q).eval b) - sign ((p * q).eval a) := by
  have hp0 : p ≠ 0 := by rintro rfl; simp at hpa
  set f := algebraMap ℝ[X] ℝ⟮X⟯ q / algebraMap _ _ p with hf
  have key : f.num * p = q * f.denom := (num_mul_eq_mul_denom_iff hp0).2 rfl
  -- `f.denom` divides `p`, and `f.num * p = q * f.denom`, so neither vanishes at `a` or `b`
  have hd {x : ℝ} (hpx : p.eval x ≠ 0) : f.denom.eval x ≠ 0 := fun h =>
    hpx (eval_eq_zero_of_dvd_of_eval_eq_zero (denom_div_dvd q p) h)
  have hn {x : ℝ} (hpx : p.eval x ≠ 0) (hqx : q.eval x ≠ 0) : f.num.eval x ≠ 0 := fun h => by
    have := congrArg (eval x) key
    simp [h, hqx, hd hpx] at this
  rw [← inv_div (algebraMap ℝ[X] ℝ⟮X⟯ q), ← hf, ← sign_eval_num_mul_denom_div q hpa,
    ← sign_eval_num_mul_denom_div q hpb]
  exact two_mul_cauchyIndex_add_cauchyIndex_inv hab (hn hpa hqa) (hd hpa) (hn hpb hqb) (hd hpb)

end RatFunc
