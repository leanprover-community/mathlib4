/-
Copyright (c) 2025 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
module

public import Mathlib.RingTheory.Polynomial.GaussNorm
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Algebra.Order.Hom.Basic


/-!
# Sup Norm of Polynomials

In this file we define the sup norm on `Polynomial`s based on their coefficients as well as several
basic results about this norm. We note that this is often called the _(naive) height_ of the
polynomial in the literature.

The sup norm is related to the Mahler measure of the polynomial. See
`Mathlib/Analysis/Polynomial/MahlerMeasure.lean`.

## Main definitions

- `Polynomial.supNorm p`: the sup norm of the coefficients of the polynomial, equal to the
  maximum of the norm of its coefficients (or zero for the zero polynomial)

## A Note on Naming

In the literature, the sup norm is often called the _(naive) height_ of a polynomial and the
`l^1` norm is often called the _length_ of the polynomial. Unfortunately, these terms are
extremely overloaded and Mathlib defines _height_ differently.

### TODOs

All other `l^p` norms can be defined on Polynomials as well. In the literature, the `l^1` norm is
sometimes called the polynomial's _length_. The `l^2` norm sometimes arises due to Parseval's
theorem implying that the squared `l^2` norm of a complex polynomial is the integral of the norm of
the polynomial's value on the unit circle.
-/


@[expose] public section supnorm_seminorm

variable {A : Type*} [SeminormedRing A] (p : Polynomial A)

namespace Polynomial

/-- The sup norm of a polynomial on a semi-normed space, defined as the maximum of its coefficients
(or `0` when `q = 0`). Often called the _(naive) height_ of the polynomial. -/
noncomputable def supNorm : ℝ := p.gaussNorm (SeminormedRing.toRingSeminorm A) 1

/-- The direct definition of the supNorm -/
lemma supNorm_def' : p.supNorm =
    if hp : p.support.Nonempty then p.support.sup' hp (norm ∘ p.coeff) else 0 := by
  split_ifs with h
  · simp only [supNorm, gaussNorm, h, ↓reduceDIte, one_pow, mul_one, Function.comp_apply]
    have : (fun x => SeminormedRing.toRingSeminorm A (p.coeff x)) = fun x => ‖p.coeff x‖ := by rfl
    rw [this]
  · simp [supNorm, gaussNorm, h]

@[simp]
lemma supNorm_zero : (0 : A[X]).supNorm = 0 := gaussNorm_zero _ _

lemma supNorm_nonneg : 0 ≤ p.supNorm := by
  apply gaussNorm_nonneg
  norm_num

@[simp]
lemma supNorm_C {a : A} : (C a).supNorm = ‖a‖ := by
  apply gaussNorm_C

@[simp]
lemma supNorm_monomial (n : ℕ) {a : A} : (monomial n a).supNorm = ‖a‖ := by
  by_cases ha : a = 0
  · simp [ha]
  · simp [supNorm, gaussNorm, support_monomial n ha]
    norm_cast

@[simp]
lemma supNorm_X [NormOneClass A] : (X : A[X]).supNorm = 1 := by
  rw [show (X : A[X]) = monomial 1 1 from rfl, supNorm_monomial, norm_one]

lemma le_supNorm (i : ℕ) : ‖p.coeff i‖ ≤ p.supNorm := by
  have := le_gaussNorm (SeminormedRing.toRingSeminorm A) p (by norm_num : (0 : ℝ) ≤ 1) i
  simpa using this

lemma exists_eq_supNorm : ∃ i : ℕ, p.supNorm = ‖p.coeff i‖ := by
  obtain ⟨i, hi⟩ := p.exists_eq_gaussNorm (SeminormedRing.toRingSeminorm A) 1
  use i
  simpa using hi

/-- The supNorm can also be defined with an iSup. Note that this uses the fact that `norm` is both
a `ZeroHom` and `NonnegHom` so is not _a priori_ true from the `gaussNorm` definition. -/
lemma supNorm_eq_iSup : p.supNorm = ⨆ i, ‖p.coeff i‖ := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := exists_eq_supNorm p
    calc p.supNorm
      _ = ‖p.coeff i‖ := hi
      _ ≤ ⨆ j, ‖p.coeff j‖ := le_ciSup ⟨p.supNorm, by
          intro x hx
          obtain ⟨j, rfl⟩ := hx
          exact le_supNorm p j⟩ i
  · apply ciSup_le
    intro i
    exact le_supNorm p i

end Polynomial
end supnorm_seminorm

@[expose] public section supnorm_norm

namespace Polynomial

variable {A : Type*} [NormedRing A] (p : Polynomial A)

lemma supNorm_eq_zero_iff : p.supNorm = 0 ↔ p = 0 := by
  unfold supNorm
  apply gaussNorm_eq_zero_iff
  · intro x hx
    rw [show SeminormedRing.toRingSeminorm A x = ‖x‖ by rfl] at hx
    exact norm_eq_zero.mp hx
  · norm_num

end Polynomial

end supnorm_norm
