/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.EraseLead

/-!
# Denominators of evaluation of polynomials at ratios

Let `i : R → K` be a homomorphism of semirings.  Assume that `K` is commutative.  If `a` and
`b` are elements of `R` such that `i b ∈ K` is invertible, then for any polynomial
`f ∈ R[X]` the "mathematical" expression `b ^ f.natDegree * f (a / b) ∈ K` is in
the image of the homomorphism `i`.
-/


open Polynomial Finset

open Polynomial

section DenomsClearable

variable {R K : Type*} [Semiring R] [CommSemiring K] {i : R →+* K}
variable {a b : R} {bi : K}

-- TODO: use hypothesis (ub : IsUnit (i b)) to work with localizations.
/-- `denomsClearable` formalizes the property that `b ^ N * f (a / b)`
does not have denominators, if the inequality `f.natDegree ≤ N` holds.

The definition asserts the existence of an element `D` of `R` and an
element `bi = 1 / i b` of `K` such that clearing the denominators of
the fraction equals `i D`.
-/
def DenomsClearable (a b : R) (N : ℕ) (f : R[X]) (i : R →+* K) : Prop :=
  ∃ (D : R) (bi : K), bi * i b = 1 ∧ i D = i b ^ N * eval (i a * bi) (f.map i)

theorem denomsClearable_zero (N : ℕ) (a : R) (bu : bi * i b = 1) : DenomsClearable a b N 0 i :=
  ⟨0, bi, bu, by
    simp only [eval_zero, RingHom.map_zero, mul_zero, Polynomial.map_zero]⟩

theorem denomsClearable_C_mul_X_pow {N : ℕ} (a : R) (bu : bi * i b = 1) {n : ℕ} (r : R)
    (nN : n ≤ N) : DenomsClearable a b N (C r * X ^ n) i := by
  refine ⟨r * a ^ n * b ^ (N - n), bi, bu, ?_⟩
  rw [C_mul_X_pow_eq_monomial, map_monomial, ← C_mul_X_pow_eq_monomial, eval_mul, eval_pow, eval_C]
  rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_pow, RingHom.map_pow, eval_X, mul_comm]
  rw [← tsub_add_cancel_of_le nN]
  conv_lhs => rw [← mul_one (i a), ← bu]
  simp [mul_assoc, mul_comm, mul_left_comm, pow_add, mul_pow]

theorem DenomsClearable.add {N : ℕ} {f g : R[X]} :
    DenomsClearable a b N f i → DenomsClearable a b N g i → DenomsClearable a b N (f + g) i :=
  fun ⟨Df, bf, bfu, Hf⟩ ⟨Dg, bg, bgu, Hg⟩ =>
  ⟨Df + Dg, bf, bfu, by
    rw [RingHom.map_add, Polynomial.map_add, eval_add, mul_add, Hf, Hg]
    congr
    refine @inv_unique K _ (i b) bg bf ?_ ?_ <;> rwa [mul_comm]⟩

theorem denomsClearable_of_natDegree_le (N : ℕ) (a : R) (bu : bi * i b = 1) :
    ∀ f : R[X], f.natDegree ≤ N → DenomsClearable a b N f i :=
  induction_with_natDegree_le _ N (denomsClearable_zero N a bu)
    (fun _ r _ => denomsClearable_C_mul_X_pow a bu r) fun _ _ _ _ df dg => df.add dg

/-- If `i : R → K` is a ring homomorphism, `f` is a polynomial with coefficients in `R`,
`a, b` are elements of `R`, with `i b` invertible, then there is a `D ∈ R` such that
`b ^ f.natDegree * f (a / b)` equals `i D`. -/
theorem denomsClearable_natDegree (i : R →+* K) (f : R[X]) (a : R) (bu : bi * i b = 1) :
    DenomsClearable a b f.natDegree f i :=
  denomsClearable_of_natDegree_le f.natDegree a bu f le_rfl

end DenomsClearable

open RingHom

/-- Evaluating a polynomial with integer coefficients at a rational number and clearing
denominators, yields a number greater than or equal to one.  The target can be any
`LinearOrderedField K`.
The assumption on `K` could be weakened to `LinearOrderedCommRing` assuming that the
image of the denominator is invertible in `K`. -/
theorem one_le_pow_mul_abs_eval_div {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {f : ℤ[X]} {a b : ℤ}
    (b0 : 0 < b) (fab : eval ((a : K) / b) (f.map (algebraMap ℤ K)) ≠ 0) :
    (1 : K) ≤ (b : K) ^ f.natDegree * |eval ((a : K) / b) (f.map (algebraMap ℤ K))| := by
  obtain ⟨ev, bi, bu, hF⟩ :=
    denomsClearable_natDegree (b := b) (algebraMap ℤ K) f a
      (by
        rw [eq_intCast, one_div_mul_cancel]
        rw [Int.cast_ne_zero]
        exact b0.ne.symm)
  obtain Fa := congr_arg abs hF
  rw [eq_one_div_of_mul_eq_one_left bu, eq_intCast, eq_intCast, abs_mul] at Fa
  rw [abs_of_pos (pow_pos (Int.cast_pos.mpr b0) _ : 0 < (b : K) ^ _), one_div, eq_intCast] at Fa
  rw [div_eq_mul_inv, ← Fa, ← Int.cast_abs, ← Int.cast_one, Int.cast_le]
  refine Int.le_of_lt_add_one ((lt_add_iff_pos_left 1).mpr (abs_pos.mpr fun F0 => fab ?_))
  rw [eq_one_div_of_mul_eq_one_left bu, F0, one_div, eq_intCast, Int.cast_zero, zero_eq_mul] at hF
  rcases hF with hF | hF
  · exact (not_le.mpr b0 (le_of_eq (Int.cast_eq_zero.mp (eq_zero_of_pow_eq_zero hF)))).elim
  · rwa [div_eq_mul_inv]
