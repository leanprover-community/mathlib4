/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/

import Mathlib.Algebra.CharP.Defs
import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.PowerSeries.Basic

/-! # Formal power series (in one variable) - Order

The `PowerSeries.order` of a formal power series `φ` is the multiplicity of the variable `X` in `φ`.

If the coefficients form an integral domain, then `PowerSeries.order` is an
additive valuation (`PowerSeries.order_mul`, `PowerSeries.min_order_le_order_add`).

We prove that if the commutative ring `R` of coefficients is an integral domain,
then the ring `R⟦X⟧` of formal power series in one variable over `R`
is an integral domain.

Given a non-zero power series `f`, `divided_by_X_pow_order f` is the power series obtained by
dividing out the largest power of X that divides `f`, that is its order. This is useful when
proving that `R⟦X⟧` is a normalization monoid, which is done in `PowerSeries.Inverse`.

-/
noncomputable section

open Polynomial

open Finset (antidiagonal mem_antidiagonal)

namespace PowerSeries

open Finsupp (single)

variable {R : Type*}

section OrderBasic

open multiplicity

variable [Semiring R] {φ : R⟦X⟧}

theorem exists_coeff_ne_zero_iff_ne_zero : (∃ n : ℕ, coeff R n φ ≠ 0) ↔ φ ≠ 0 := by
  refine not_iff_not.mp ?_
  push_neg
  simp [(coeff R _).map_zero]

/-- The order of a formal power series `φ` is the greatest `n : PartENat`
such that `X^n` divides `φ`. The order is `⊤` if and only if `φ = 0`. -/
def order (φ : R⟦X⟧) : ℕ∞ :=
  letI := Classical.decEq R
  letI := Classical.decEq R⟦X⟧
  if h : φ = 0 then ⊤ else Nat.find (exists_coeff_ne_zero_iff_ne_zero.mpr h)

/-- The order of the `0` power series is infinite. -/
@[simp]
theorem order_zero : order (0 : R⟦X⟧) = ⊤ :=
  dif_pos rfl

theorem order_finite_iff_ne_zero : (order φ < ⊤) ↔ φ ≠ 0 := by
  simp only [order]
  constructor
  · split_ifs with h <;> intro H
    · simp at H
    · exact h
  · intro h
    simp [h]

/-- If the order of a formal power series is finite,
then the coefficient indexed by the order is nonzero. -/
theorem coeff_order (h : order φ < ⊤) : coeff R (φ.order.lift h) φ ≠ 0 := by
  classical
  simp only [order, order_finite_iff_ne_zero.mp h, not_false_iff, dif_neg]
  generalize_proofs h
  exact Nat.find_spec h

/-- If the `n`th coefficient of a formal power series is nonzero,
then the order of the power series is less than or equal to `n`. -/
theorem order_le (n : ℕ) (h : coeff R n φ ≠ 0) : order φ ≤ n := by
  classical
  rw [order, dif_neg]
  · simpa using ⟨n, le_rfl, h⟩
  · exact exists_coeff_ne_zero_iff_ne_zero.mp ⟨n, h⟩

/-- The `n`th coefficient of a formal power series is `0` if `n` is strictly
smaller than the order of the power series. -/
theorem coeff_of_lt_order (n : ℕ) (h : ↑n < order φ) : coeff R n φ = 0 := by
  contrapose! h
  exact order_le _ h

/-- The `0` power series is the unique power series with infinite order. -/
@[simp]
theorem order_eq_top {φ : R⟦X⟧} : φ.order = ⊤ ↔ φ = 0 := by
  simpa using order_finite_iff_ne_zero.not_left

/-- The order of a formal power series is at least `n` if
the `i`th coefficient is `0` for all `i < n`. -/
theorem nat_le_order (φ : R⟦X⟧) (n : ℕ) (h : ∀ i < n, coeff R i φ = 0) : ↑n ≤ order φ := by
  by_contra H; rw [not_le] at H
  have lt_top : order φ < ⊤ := lt_top_of_lt H
  replace H : (order φ).lift lt_top < n := by simpa
  exact coeff_order lt_top (h _ H)

/-- The order of a formal power series is at least `n` if
the `i`th coefficient is `0` for all `i < n`. -/
theorem le_order (φ : R⟦X⟧) (n : ℕ∞) (h : ∀ i : ℕ, ↑i < n → coeff R i φ = 0) :
    n ≤ order φ := by
  cases n with
  | top => simpa using ext (by simpa using h)
  | coe n =>
    convert nat_le_order φ n _
    simpa using h

/-- The order of a formal power series is exactly `n` if the `n`th coefficient is nonzero,
and the `i`th coefficient is `0` for all `i < n`. -/
theorem order_eq_nat {φ : R⟦X⟧} {n : ℕ} :
    order φ = n ↔ coeff R n φ ≠ 0 ∧ ∀ i, i < n → coeff R i φ = 0 := by
  classical
  rcases eq_or_ne φ 0 with (rfl | hφ)
  · simp
  simp [order, dif_neg hφ, Nat.find_eq_iff]

/-- The order of a formal power series is exactly `n` if the `n`th coefficient is nonzero,
and the `i`th coefficient is `0` for all `i < n`. -/
theorem order_eq {φ : R⟦X⟧} {n : ℕ∞} :
    order φ = n ↔ (∀ i : ℕ, ↑i = n → coeff R i φ ≠ 0) ∧ ∀ i : ℕ, ↑i < n → coeff R i φ = 0 := by
  cases n with
  | top => simp [ext_iff]
  | coe n => simp [order_eq_nat]


/-- The order of the sum of two formal power series
 is at least the minimum of their orders. -/
theorem min_order_le_order_add (φ ψ : R⟦X⟧) : min (order φ) (order ψ) ≤ order (φ + ψ) := by
  refine le_order _ _ ?_
  simp +contextual [coeff_of_lt_order]

@[deprecated (since := "2024-11-12")] alias le_order_add := min_order_le_order_add

private theorem order_add_of_order_eq.aux (φ ψ : R⟦X⟧) (_h : order φ ≠ order ψ)
    (H : order φ < order ψ) : order (φ + ψ) ≤ order φ ⊓ order ψ := by
  suffices order (φ + ψ) = order φ by
    rw [le_inf_iff, this]
    exact ⟨le_rfl, le_of_lt H⟩
  rw [order_eq]
  constructor
  · intro i hi
    rw [← hi] at H
    rw [(coeff _ _).map_add, coeff_of_lt_order i H, add_zero]
    exact (order_eq_nat.1 hi.symm).1
  · intro i hi
    rw [(coeff _ _).map_add, coeff_of_lt_order i hi, coeff_of_lt_order i (lt_trans hi H),
      zero_add]

/-- The order of the sum of two formal power series
 is the minimum of their orders if their orders differ. -/
theorem order_add_of_order_eq (φ ψ : R⟦X⟧) (h : order φ ≠ order ψ) :
    order (φ + ψ) = order φ ⊓ order ψ := by
  refine le_antisymm ?_ (min_order_le_order_add _ _)
  by_cases H₁ : order φ < order ψ
  · apply order_add_of_order_eq.aux _ _ h H₁
  by_cases H₂ : order ψ < order φ
  · simpa only [add_comm, inf_comm] using order_add_of_order_eq.aux _ _ h.symm H₂
  exfalso; exact h (le_antisymm (not_lt.1 H₂) (not_lt.1 H₁))

/-- The order of the product of two formal power series
 is at least the sum of their orders. -/
theorem le_order_mul (φ ψ : R⟦X⟧) : order φ + order ψ ≤ order (φ * ψ) := by
  apply le_order
  intro n hn; rw [coeff_mul, Finset.sum_eq_zero]
  rintro ⟨i, j⟩ hij
  by_cases hi : ↑i < order φ
  · rw [coeff_of_lt_order i hi, zero_mul]
  by_cases hj : ↑j < order ψ
  · rw [coeff_of_lt_order j hj, mul_zero]
  rw [not_lt] at hi hj; rw [mem_antidiagonal] at hij
  exfalso
  apply ne_of_lt (lt_of_lt_of_le hn <| add_le_add hi hj)
  rw [← Nat.cast_add, hij]

alias order_mul_ge := le_order_mul

/-- The order of the monomial `a*X^n` is infinite if `a = 0` and `n` otherwise. -/
theorem order_monomial (n : ℕ) (a : R) [Decidable (a = 0)] :
    order (monomial R n a) = if a = 0 then (⊤ : ℕ∞) else n := by
  split_ifs with h
  · rw [h, order_eq_top, LinearMap.map_zero]
  · rw [order_eq]
    constructor <;> intro i hi
    · simp only [Nat.cast_inj] at hi
      rwa [hi, coeff_monomial_same]
    · simp only [Nat.cast_lt] at hi
      rw [coeff_monomial, if_neg]
      exact ne_of_lt hi

/-- The order of the monomial `a*X^n` is `n` if `a ≠ 0`. -/
theorem order_monomial_of_ne_zero (n : ℕ) (a : R) (h : a ≠ 0) : order (monomial R n a) = n := by
  classical
  rw [order_monomial, if_neg h]

/-- If `n` is strictly smaller than the order of `ψ`, then the `n`th coefficient of its product
with any other power series is `0`. -/
theorem coeff_mul_of_lt_order {φ ψ : R⟦X⟧} {n : ℕ} (h : ↑n < ψ.order) :
    coeff R n (φ * ψ) = 0 := by
  suffices coeff R n (φ * ψ) = ∑ p ∈ antidiagonal n, 0 by rw [this, Finset.sum_const_zero]
  rw [coeff_mul]
  apply Finset.sum_congr rfl
  intro x hx
  refine mul_eq_zero_of_right (coeff R x.fst φ) (coeff_of_lt_order x.snd (lt_of_le_of_lt ?_ h))
  rw [mem_antidiagonal] at hx
  norm_cast
  omega

theorem coeff_mul_one_sub_of_lt_order {R : Type*} [CommRing R] {φ ψ : R⟦X⟧} (n : ℕ)
    (h : ↑n < ψ.order) : coeff R n (φ * (1 - ψ)) = coeff R n φ := by
  simp [coeff_mul_of_lt_order h, mul_sub]

theorem coeff_mul_prod_one_sub_of_lt_order {R ι : Type*} [CommRing R] (k : ℕ) (s : Finset ι)
    (φ : R⟦X⟧) (f : ι → R⟦X⟧) :
    (∀ i ∈ s, ↑k < (f i).order) → coeff R k (φ * ∏ i ∈ s, (1 - f i)) = coeff R k φ := by
  classical
  induction' s using Finset.induction_on with a s ha ih t
  · simp
  · intro t
    simp only [Finset.mem_insert, forall_eq_or_imp] at t
    rw [Finset.prod_insert ha, ← mul_assoc, mul_right_comm, coeff_mul_one_sub_of_lt_order _ t.1]
    exact ih t.2

-- TODO: link with `X_pow_dvd_iff`
theorem X_pow_order_dvd (h : order φ < ⊤) : X ^ (order φ).lift h ∣ φ := by
  refine ⟨PowerSeries.mk fun n => coeff R (n + (order φ).lift h) φ, ?_⟩
  ext n
  simp only [coeff_mul, coeff_X_pow, coeff_mk, boole_mul, Finset.sum_ite,
    Finset.sum_const_zero, add_zero]
  rw [Finset.filter_fst_eq_antidiagonal n ((order φ).lift h)]
  split_ifs with hn
  · simp [tsub_add_cancel_of_le hn]
  · simp only [Finset.sum_empty]
    refine coeff_of_lt_order _ ?_
    simpa using hn

theorem order_eq_emultiplicity_X {R : Type*} [Semiring R] (φ : R⟦X⟧) :
    order φ = emultiplicity X φ := by
  classical
  rcases eq_or_ne φ 0 with (rfl | hφ)
  · simp
  cases ho : order φ with
  | top => simp [hφ] at ho
  | coe n =>
    have hn : φ.order.lift (order_finite_iff_ne_zero.mpr hφ) = n := by simp [ho]
    rw [← hn, eq_comm]
    apply le_antisymm _
    · apply le_emultiplicity_of_pow_dvd
      apply X_pow_order_dvd
    · apply Order.le_of_lt_add_one
      rw [← not_le, ← Nat.cast_one, ← Nat.cast_add, ← pow_dvd_iff_le_emultiplicity]
      rintro ⟨ψ, H⟩
      have := congr_arg (coeff R n) H
      rw [← (ψ.commute_X.pow_right _).eq, coeff_mul_of_lt_order, ← hn] at this
      · exact coeff_order _ this
      · rw [X_pow_eq, order_monomial]
        split_ifs
        · simp
        · rw [← hn, ENat.coe_lt_coe]
          simp

/-- Given a non-zero power series `f`, `divided_by_X_pow_order f` is the power series obtained by
  dividing out the largest power of X that divides `f`, that is its order -/
def divided_by_X_pow_order {f : PowerSeries R} (hf : f ≠ 0) : R⟦X⟧ :=
  (exists_eq_mul_right_of_dvd (X_pow_order_dvd (order_finite_iff_ne_zero.2 hf))).choose

theorem self_eq_X_pow_order_mul_divided_by_X_pow_order {f : R⟦X⟧} (hf : f ≠ 0) :
    X ^ f.order.lift (order_finite_iff_ne_zero.mpr hf) * divided_by_X_pow_order hf = f :=
  haveI dvd := X_pow_order_dvd (order_finite_iff_ne_zero.mpr hf)
  (exists_eq_mul_right_of_dvd dvd).choose_spec.symm

end OrderBasic

section OrderZeroNeOne

variable [Semiring R] [Nontrivial R]

/-- The order of the formal power series `1` is `0`. -/
@[simp]
theorem order_one : order (1 : R⟦X⟧) = 0 := by
  simpa using order_monomial_of_ne_zero 0 (1 : R) one_ne_zero

/-- The order of an invertible power series is `0`. -/
theorem order_zero_of_unit {f : PowerSeries R} : IsUnit f → f.order = 0 := by
  rintro ⟨⟨u, v, hu, hv⟩, hf⟩
  apply And.left
  rw [← add_eq_zero, ← hf, ← nonpos_iff_eq_zero, ← @order_one R _ _, ← hu]
  exact order_mul_ge _ _

/-- The order of the formal power series `X` is `1`. -/
@[simp]
theorem order_X : order (X : R⟦X⟧) = 1 := by
  simpa only [Nat.cast_one] using order_monomial_of_ne_zero 1 (1 : R) one_ne_zero

/-- The order of the formal power series `X^n` is `n`. -/
@[simp]
theorem order_X_pow (n : ℕ) : order ((X : R⟦X⟧) ^ n) = n := by
  rw [X_pow_eq, order_monomial_of_ne_zero]
  exact one_ne_zero

end OrderZeroNeOne

section OrderIsDomain

-- TODO: generalize to `[Semiring R] [NoZeroDivisors R]`
variable [CommRing R] [IsDomain R]

/-- The order of the product of two formal power series over an integral domain
 is the sum of their orders. -/
theorem order_mul (φ ψ : R⟦X⟧) : order (φ * ψ) = order φ + order ψ := by
  classical
  simp only [order_eq_emultiplicity_X]
  rw [emultiplicity_mul X_prime]

-- Dividing `X` by the maximal power of `X` dividing it leaves `1`.
@[simp]
theorem divided_by_X_pow_order_of_X_eq_one : divided_by_X_pow_order X_ne_zero = (1 : R⟦X⟧) := by
  rw [← mul_eq_left₀ X_ne_zero]
  simpa using self_eq_X_pow_order_mul_divided_by_X_pow_order (@X_ne_zero R _ _)

-- Dividing a power series by the maximal power of `X` dividing it, respects multiplication.
theorem divided_by_X_pow_orderMul {f g : R⟦X⟧} (hf : f ≠ 0) (hg : g ≠ 0) :
    divided_by_X_pow_order hf * divided_by_X_pow_order hg =
      divided_by_X_pow_order (mul_ne_zero hf hg) := by
  set df := f.order.lift (order_finite_iff_ne_zero.mpr hf)
  set dg := g.order.lift (order_finite_iff_ne_zero.mpr hg)
  set dfg := (f * g).order.lift (order_finite_iff_ne_zero.mpr (mul_ne_zero hf hg)) with hdfg
  have H_add_d : df + dg = dfg := by
    simp_all [order_mul f g]
  have H := self_eq_X_pow_order_mul_divided_by_X_pow_order (mul_ne_zero hf hg)
  have : f * g = X ^ dfg * (divided_by_X_pow_order hf * divided_by_X_pow_order hg) := by
    calc
      f * g = X ^ df * divided_by_X_pow_order hf * (X ^ dg * divided_by_X_pow_order hg) := by
        rw [self_eq_X_pow_order_mul_divided_by_X_pow_order,
          self_eq_X_pow_order_mul_divided_by_X_pow_order]
      _ = X ^ df * X ^ dg * divided_by_X_pow_order hf * divided_by_X_pow_order hg := by ring
      _ = X ^ (df + dg) * divided_by_X_pow_order hf * divided_by_X_pow_order hg := by rw [pow_add]
      _ = X ^ dfg * divided_by_X_pow_order hf * divided_by_X_pow_order hg := by rw [H_add_d]
      _ = X ^ dfg * (divided_by_X_pow_order hf * divided_by_X_pow_order hg) := by rw [mul_assoc]
  refine (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (pow_ne_zero dfg X_ne_zero) ?_).symm
  simp only [this] at H
  convert H

end OrderIsDomain

end PowerSeries

end
