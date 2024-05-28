/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/

import Mathlib.Algebra.CharP.Defs
import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.PowerSeries.Basic

#align_import ring_theory.power_series.basic from "leanprover-community/mathlib"@"2d5739b61641ee4e7e53eca5688a08f66f2e6a60"

/-! # Formal power series (in one variable) - Order

The `PowerSeries.order` of a formal power series `φ` is the multiplicity of the variable `X` in `φ`.

If the coefficients form an integral domain, then `PowerSeries.order` is an
additive valuation (`PowerSeries.order_mul`, `PowerSeries.le_order_add`).

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
  -- FIXME: the `FunLike.coe` doesn't seem to be picked up in the expression after #8386?
  simp [PowerSeries.ext_iff, (coeff R _).map_zero]
#align power_series.exists_coeff_ne_zero_iff_ne_zero PowerSeries.exists_coeff_ne_zero_iff_ne_zero

/-- The order of a formal power series `φ` is the greatest `n : PartENat`
such that `X^n` divides `φ`. The order is `⊤` if and only if `φ = 0`. -/
def order (φ : R⟦X⟧) : PartENat :=
  letI := Classical.decEq R
  letI := Classical.decEq R⟦X⟧
  if h : φ = 0 then ⊤ else Nat.find (exists_coeff_ne_zero_iff_ne_zero.mpr h)
#align power_series.order PowerSeries.order

/-- The order of the `0` power series is infinite. -/
@[simp]
theorem order_zero : order (0 : R⟦X⟧) = ⊤ :=
  dif_pos rfl
#align power_series.order_zero PowerSeries.order_zero

theorem order_finite_iff_ne_zero : (order φ).Dom ↔ φ ≠ 0 := by
  simp only [order]
  constructor
  · split_ifs with h <;> intro H
    · simp only [PartENat.top_eq_none, Part.not_none_dom] at H
    · exact h
  · intro h
    simp [h]
#align power_series.order_finite_iff_ne_zero PowerSeries.order_finite_iff_ne_zero

/-- If the order of a formal power series is finite,
then the coefficient indexed by the order is nonzero. -/
theorem coeff_order (h : (order φ).Dom) : coeff R (φ.order.get h) φ ≠ 0 := by
  classical
  simp only [order, order_finite_iff_ne_zero.mp h, not_false_iff, dif_neg, PartENat.get_natCast']
  generalize_proofs h
  exact Nat.find_spec h
#align power_series.coeff_order PowerSeries.coeff_order

/-- If the `n`th coefficient of a formal power series is nonzero,
then the order of the power series is less than or equal to `n`. -/
theorem order_le (n : ℕ) (h : coeff R n φ ≠ 0) : order φ ≤ n := by
  classical
  rw [order, dif_neg]
  · simp only [PartENat.coe_le_coe]
    exact Nat.find_le h
  · exact exists_coeff_ne_zero_iff_ne_zero.mp ⟨n, h⟩
#align power_series.order_le PowerSeries.order_le

/-- The `n`th coefficient of a formal power series is `0` if `n` is strictly
smaller than the order of the power series. -/
theorem coeff_of_lt_order (n : ℕ) (h : ↑n < order φ) : coeff R n φ = 0 := by
  contrapose! h
  exact order_le _ h
#align power_series.coeff_of_lt_order PowerSeries.coeff_of_lt_order

/-- The `0` power series is the unique power series with infinite order. -/
@[simp]
theorem order_eq_top {φ : R⟦X⟧} : φ.order = ⊤ ↔ φ = 0 :=
  PartENat.not_dom_iff_eq_top.symm.trans order_finite_iff_ne_zero.not_left
#align power_series.order_eq_top PowerSeries.order_eq_top

/-- The order of a formal power series is at least `n` if
the `i`th coefficient is `0` for all `i < n`. -/
theorem nat_le_order (φ : R⟦X⟧) (n : ℕ) (h : ∀ i < n, coeff R i φ = 0) : ↑n ≤ order φ := by
  by_contra H; rw [not_le] at H
  have : (order φ).Dom := PartENat.dom_of_le_natCast H.le
  rw [← PartENat.natCast_get this, PartENat.coe_lt_coe] at H
  exact coeff_order this (h _ H)
#align power_series.nat_le_order PowerSeries.nat_le_order

/-- The order of a formal power series is at least `n` if
the `i`th coefficient is `0` for all `i < n`. -/
theorem le_order (φ : R⟦X⟧) (n : PartENat) (h : ∀ i : ℕ, ↑i < n → coeff R i φ = 0) :
    n ≤ order φ := by
  induction n using PartENat.casesOn
  · show _ ≤ _
    rw [top_le_iff, order_eq_top]
    ext i
    exact h _ (PartENat.natCast_lt_top i)
  · apply nat_le_order
    simpa only [PartENat.coe_lt_coe] using h
#align power_series.le_order PowerSeries.le_order

/-- The order of a formal power series is exactly `n` if the `n`th coefficient is nonzero,
and the `i`th coefficient is `0` for all `i < n`. -/
theorem order_eq_nat {φ : R⟦X⟧} {n : ℕ} :
    order φ = n ↔ coeff R n φ ≠ 0 ∧ ∀ i, i < n → coeff R i φ = 0 := by
  classical
  rcases eq_or_ne φ 0 with (rfl | hφ)
  · simpa [(coeff R _).map_zero] using (PartENat.natCast_ne_top _).symm
  simp [order, dif_neg hφ, Nat.find_eq_iff]
#align power_series.order_eq_nat PowerSeries.order_eq_nat

/-- The order of a formal power series is exactly `n` if the `n`th coefficient is nonzero,
and the `i`th coefficient is `0` for all `i < n`. -/
theorem order_eq {φ : R⟦X⟧} {n : PartENat} :
    order φ = n ↔ (∀ i : ℕ, ↑i = n → coeff R i φ ≠ 0) ∧ ∀ i : ℕ, ↑i < n → coeff R i φ = 0 := by
  induction n using PartENat.casesOn
  · rw [order_eq_top]
    constructor
    · rintro rfl
      constructor <;> intros
      · exfalso
        exact PartENat.natCast_ne_top ‹_› ‹_›
      · exact (coeff _ _).map_zero
    · rintro ⟨_h₁, h₂⟩
      ext i
      exact h₂ i (PartENat.natCast_lt_top i)
  · simpa [PartENat.natCast_inj] using order_eq_nat
#align power_series.order_eq PowerSeries.order_eq

/-- The order of the sum of two formal power series
 is at least the minimum of their orders. -/
theorem le_order_add (φ ψ : R⟦X⟧) : min (order φ) (order ψ) ≤ order (φ + ψ) := by
  refine le_order _ _ ?_
  simp (config := { contextual := true }) [coeff_of_lt_order]
#align power_series.le_order_add PowerSeries.le_order_add

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
-- #align power_series.order_add_of_order_eq.aux power_series.order_add_of_order_eq.aux

/-- The order of the sum of two formal power series
 is the minimum of their orders if their orders differ. -/
theorem order_add_of_order_eq (φ ψ : R⟦X⟧) (h : order φ ≠ order ψ) :
    order (φ + ψ) = order φ ⊓ order ψ := by
  refine le_antisymm ?_ (le_order_add _ _)
  by_cases H₁ : order φ < order ψ
  · apply order_add_of_order_eq.aux _ _ h H₁
  by_cases H₂ : order ψ < order φ
  · simpa only [add_comm, inf_comm] using order_add_of_order_eq.aux _ _ h.symm H₂
  exfalso; exact h (le_antisymm (not_lt.1 H₂) (not_lt.1 H₁))
#align power_series.order_add_of_order_eq PowerSeries.order_add_of_order_eq

/-- The order of the product of two formal power series
 is at least the sum of their orders. -/
theorem order_mul_ge (φ ψ : R⟦X⟧) : order φ + order ψ ≤ order (φ * ψ) := by
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
#align power_series.order_mul_ge PowerSeries.order_mul_ge

/-- The order of the monomial `a*X^n` is infinite if `a = 0` and `n` otherwise. -/
theorem order_monomial (n : ℕ) (a : R) [Decidable (a = 0)] :
    order (monomial R n a) = if a = 0 then (⊤ : PartENat) else n := by
  split_ifs with h
  · rw [h, order_eq_top, LinearMap.map_zero]
  · rw [order_eq]
    constructor <;> intro i hi
    · rw [PartENat.natCast_inj] at hi
      rwa [hi, coeff_monomial_same]
    · rw [PartENat.coe_lt_coe] at hi
      rw [coeff_monomial, if_neg]
      exact ne_of_lt hi
#align power_series.order_monomial PowerSeries.order_monomial

/-- The order of the monomial `a*X^n` is `n` if `a ≠ 0`. -/
theorem order_monomial_of_ne_zero (n : ℕ) (a : R) (h : a ≠ 0) : order (monomial R n a) = n := by
  classical
  rw [order_monomial, if_neg h]
#align power_series.order_monomial_of_ne_zero PowerSeries.order_monomial_of_ne_zero

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
#align power_series.coeff_mul_of_lt_order PowerSeries.coeff_mul_of_lt_order

theorem coeff_mul_one_sub_of_lt_order {R : Type*} [CommRing R] {φ ψ : R⟦X⟧} (n : ℕ)
    (h : ↑n < ψ.order) : coeff R n (φ * (1 - ψ)) = coeff R n φ := by
  simp [coeff_mul_of_lt_order h, mul_sub]
#align power_series.coeff_mul_one_sub_of_lt_order PowerSeries.coeff_mul_one_sub_of_lt_order

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
#align power_series.coeff_mul_prod_one_sub_of_lt_order PowerSeries.coeff_mul_prod_one_sub_of_lt_order

-- TODO: link with `X_pow_dvd_iff`
theorem X_pow_order_dvd (h : (order φ).Dom) : X ^ (order φ).get h ∣ φ := by
  refine ⟨PowerSeries.mk fun n => coeff R (n + (order φ).get h) φ, ?_⟩
  ext n
  simp only [coeff_mul, coeff_X_pow, coeff_mk, boole_mul, Finset.sum_ite,
    Finset.sum_const_zero, add_zero]
  rw [Finset.filter_fst_eq_antidiagonal n (Part.get (order φ) h)]
  split_ifs with hn
  · simp [tsub_add_cancel_of_le hn]
  · simp only [Finset.sum_empty]
    refine coeff_of_lt_order _ ?_
    simpa [PartENat.coe_lt_iff] using fun _ => hn
set_option linter.uppercaseLean3 false in
#align power_series.X_pow_order_dvd PowerSeries.X_pow_order_dvd

theorem order_eq_multiplicity_X {R : Type*} [Semiring R] [@DecidableRel R⟦X⟧ (· ∣ ·)] (φ : R⟦X⟧) :
    order φ = multiplicity X φ := by
  classical
  rcases eq_or_ne φ 0 with (rfl | hφ)
  · simp
  induction' ho : order φ using PartENat.casesOn with n
  · simp [hφ] at ho
  have hn : φ.order.get (order_finite_iff_ne_zero.mpr hφ) = n := by simp [ho]
  rw [← hn]
  refine
    le_antisymm (le_multiplicity_of_pow_dvd <| X_pow_order_dvd (order_finite_iff_ne_zero.mpr hφ))
      (PartENat.find_le _ _ ?_)
  rintro ⟨ψ, H⟩
  have := congr_arg (coeff R n) H
  rw [← (ψ.commute_X.pow_right _).eq, coeff_mul_of_lt_order, ← hn] at this
  · exact coeff_order _ this
  · rw [X_pow_eq, order_monomial]
    split_ifs
    · exact PartENat.natCast_lt_top _
    · rw [← hn, PartENat.coe_lt_coe]
      exact Nat.lt_succ_self _
set_option linter.uppercaseLean3 false in
#align power_series.order_eq_multiplicity_X PowerSeries.order_eq_multiplicity_X

/-- Given a non-zero power series `f`, `divided_by_X_pow_order f` is the power series obtained by
  dividing out the largest power of X that divides `f`, that is its order-/
def divided_by_X_pow_order {f : PowerSeries R} (hf : f ≠ 0) : R⟦X⟧ :=
  (exists_eq_mul_right_of_dvd (X_pow_order_dvd (order_finite_iff_ne_zero.2 hf))).choose

theorem self_eq_X_pow_order_mul_divided_by_X_pow_order {f : R⟦X⟧} (hf : f ≠ 0) :
    X ^ f.order.get (order_finite_iff_ne_zero.mpr hf) * divided_by_X_pow_order hf = f :=
  haveI dvd := X_pow_order_dvd (order_finite_iff_ne_zero.mpr hf)
  (exists_eq_mul_right_of_dvd dvd).choose_spec.symm

end OrderBasic

section OrderZeroNeOne

variable [Semiring R] [Nontrivial R]

/-- The order of the formal power series `1` is `0`. -/
@[simp]
theorem order_one : order (1 : R⟦X⟧) = 0 := by
  simpa using order_monomial_of_ne_zero 0 (1 : R) one_ne_zero
#align power_series.order_one PowerSeries.order_one

/-- The order of an invertible power series is `0`. -/
theorem order_zero_of_unit {f : PowerSeries R} : IsUnit f → f.order = 0 := by
  rintro ⟨⟨u, v, hu, hv⟩, hf⟩
  apply And.left
  rw [← add_eq_zero_iff, ← hf, ← nonpos_iff_eq_zero, ← @order_one R _ _, ← hu]
  exact order_mul_ge _ _

/-- The order of the formal power series `X` is `1`. -/
@[simp]
theorem order_X : order (X : R⟦X⟧) = 1 := by
  simpa only [Nat.cast_one] using order_monomial_of_ne_zero 1 (1 : R) one_ne_zero
set_option linter.uppercaseLean3 false in
#align power_series.order_X PowerSeries.order_X

/-- The order of the formal power series `X^n` is `n`. -/
@[simp]
theorem order_X_pow (n : ℕ) : order ((X : R⟦X⟧) ^ n) = n := by
  rw [X_pow_eq, order_monomial_of_ne_zero]
  exact one_ne_zero
set_option linter.uppercaseLean3 false in
#align power_series.order_X_pow PowerSeries.order_X_pow

end OrderZeroNeOne

section OrderIsDomain

-- TODO: generalize to `[Semiring R] [NoZeroDivisors R]`
variable [CommRing R] [IsDomain R]

/-- The order of the product of two formal power series over an integral domain
 is the sum of their orders. -/
theorem order_mul (φ ψ : R⟦X⟧) : order (φ * ψ) = order φ + order ψ := by
  classical
  simp_rw [order_eq_multiplicity_X]
  exact multiplicity.mul X_prime
#align power_series.order_mul PowerSeries.order_mul

-- Dividing `X` by the maximal power of `X` dividing it leaves `1`.
@[simp]
theorem divided_by_X_pow_order_of_X_eq_one : divided_by_X_pow_order X_ne_zero = (1 : R⟦X⟧) := by
  rw [← mul_eq_left₀ X_ne_zero]
  simpa only [order_X, X_ne_zero, PartENat.get_one, pow_one, Ne, not_false_iff] using
    self_eq_X_pow_order_mul_divided_by_X_pow_order (@X_ne_zero R _ _)

-- Dividing a power series by the maximal power of `X` dividing it, respects multiplication.
theorem divided_by_X_pow_orderMul {f g : R⟦X⟧} (hf : f ≠ 0) (hg : g ≠ 0) :
    divided_by_X_pow_order hf * divided_by_X_pow_order hg =
      divided_by_X_pow_order (mul_ne_zero hf hg) := by
  set df := f.order.get (order_finite_iff_ne_zero.mpr hf)
  set dg := g.order.get (order_finite_iff_ne_zero.mpr hg)
  set dfg := (f * g).order.get (order_finite_iff_ne_zero.mpr (mul_ne_zero hf hg)) with hdfg
  have H_add_d : df + dg = dfg := by simp_all only [PartENat.get_add, order_mul f g]
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
  simp [← hdfg, this] at H
  refine (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (pow_ne_zero dfg X_ne_zero) ?_).symm
  convert H

end OrderIsDomain

end PowerSeries

end
