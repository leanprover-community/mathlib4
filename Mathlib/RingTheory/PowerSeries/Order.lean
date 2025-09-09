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

variable [Semiring R] {φ : R⟦X⟧}

theorem exists_coeff_ne_zero_iff_ne_zero : (∃ n : ℕ, coeff n φ ≠ 0) ↔ φ ≠ 0 := by
  refine not_iff_not.mp ?_
  push_neg
  simp

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
  split_ifs with h <;> simpa

/-- The `0` power series is the unique power series with infinite order. -/
@[simp]
theorem order_eq_top {φ : R⟦X⟧} : φ.order = ⊤ ↔ φ = 0 := by
  simpa using order_finite_iff_ne_zero.not_left

theorem coe_toNat_order {φ : R⟦X⟧} (hf : φ ≠ 0) : φ.order.toNat = φ.order := by
  rw [ENat.coe_toNat_eq_self.mpr (order_eq_top.not.mpr hf)]

/-- If the order of a formal power series is finite,
then the coefficient indexed by the order is nonzero. -/
theorem coeff_order (h : φ ≠ 0) : coeff φ.order.toNat φ ≠ 0 := by
  classical
  simp only [order, h, not_false_iff, dif_neg]
  generalize_proofs h
  exact Nat.find_spec h

/-- If the `n`th coefficient of a formal power series is nonzero,
then the order of the power series is less than or equal to `n`. -/
theorem order_le (n : ℕ) (h : coeff n φ ≠ 0) : order φ ≤ n := by
  classical
  rw [order, dif_neg]
  · simpa using ⟨n, le_rfl, h⟩
  · exact exists_coeff_ne_zero_iff_ne_zero.mp ⟨n, h⟩

/-- The `n`th coefficient of a formal power series is `0` if `n` is strictly
smaller than the order of the power series. -/
theorem coeff_of_lt_order (n : ℕ) (h : ↑n < order φ) : coeff n φ = 0 := by
  contrapose! h
  exact order_le _ h

theorem coeff_of_lt_order_toNat (n : ℕ) (h : n < φ.order.toNat) : coeff n φ = 0 := by
  by_cases h' : φ = 0
  · simp [h']
  · refine coeff_of_lt_order _ ?_
    rwa [← coe_toNat_order h', ENat.coe_lt_coe]

/-- The order of a formal power series is at least `n` if
the `i`th coefficient is `0` for all `i < n`. -/
theorem nat_le_order (φ : R⟦X⟧) (n : ℕ) (h : ∀ i < n, coeff i φ = 0) : ↑n ≤ order φ := by
  classical
  simp only [order]
  split_ifs
  · simp
  · simpa [Nat.le_find_iff]

/-- The order of a formal power series is at least `n` if
the `i`th coefficient is `0` for all `i < n`. -/
theorem le_order (φ : R⟦X⟧) (n : ℕ∞) (h : ∀ i : ℕ, ↑i < n → coeff i φ = 0) :
    n ≤ order φ := by
  cases n with
  | top => simpa using ext (by simpa using h)
  | coe n =>
    convert nat_le_order φ n _
    simpa using h

/-- The order of a formal power series is exactly `n` if the `n`th coefficient is nonzero,
and the `i`th coefficient is `0` for all `i < n`. -/
theorem order_eq_nat {φ : R⟦X⟧} {n : ℕ} :
    order φ = n ↔ coeff n φ ≠ 0 ∧ ∀ i, i < n → coeff i φ = 0 := by
  classical
  rcases eq_or_ne φ 0 with (rfl | hφ)
  · simp
  simp [order, dif_neg hφ, Nat.find_eq_iff]

/-- The order of a formal power series is exactly `n` if the `n`th coefficient is nonzero,
and the `i`th coefficient is `0` for all `i < n`. -/
theorem order_eq {φ : R⟦X⟧} {n : ℕ∞} :
    order φ = n ↔ (∀ i : ℕ, ↑i = n → coeff i φ ≠ 0) ∧ ∀ i : ℕ, ↑i < n → coeff i φ = 0 := by
  cases n with
  | top => simp
  | coe n => simp [order_eq_nat]


/-- The order of the sum of two formal power series
is at least the minimum of their orders. -/
theorem min_order_le_order_add (φ ψ : R⟦X⟧) : min (order φ) (order ψ) ≤ order (φ + ψ) := by
  refine le_order _ _ ?_
  simp +contextual [coeff_of_lt_order]

private theorem order_add_of_order_eq.aux (φ ψ : R⟦X⟧)
    (H : order φ < order ψ) : order (φ + ψ) ≤ order φ ⊓ order ψ := by
  suffices order (φ + ψ) = order φ by
    rw [le_inf_iff, this]
    exact ⟨le_rfl, le_of_lt H⟩
  rw [order_eq]
  constructor
  · intro i hi
    rw [← hi] at H
    rw [(coeff _).map_add, coeff_of_lt_order i H, add_zero]
    exact (order_eq_nat.1 hi.symm).1
  · intro i hi
    rw [(coeff _).map_add, coeff_of_lt_order i hi, coeff_of_lt_order i (lt_trans hi H),
      zero_add]

/-- The order of the sum of two formal power series
is the minimum of their orders if their orders differ. -/
theorem order_add_of_order_eq (φ ψ : R⟦X⟧) (h : order φ ≠ order ψ) :
    order (φ + ψ) = order φ ⊓ order ψ := by
  refine le_antisymm ?_ (min_order_le_order_add _ _)
  rcases h.lt_or_gt with (φ_lt_ψ | ψ_lt_φ)
  · apply order_add_of_order_eq.aux _ _ φ_lt_ψ
  · simpa only [add_comm, inf_comm] using order_add_of_order_eq.aux _ _ ψ_lt_φ

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

theorem le_order_pow (φ : R⟦X⟧) (n : ℕ) : n • order φ ≤ order (φ ^ n) := by
  induction n with
  | zero => simp
  | succ n hn =>
    simp only [add_smul, one_smul, pow_succ]
    apply le_trans _ (le_order_mul _ _)
    exact add_le_add_right hn φ.order

alias order_mul_ge := le_order_mul

/-- The order of the monomial `a*X^n` is infinite if `a = 0` and `n` otherwise. -/
theorem order_monomial (n : ℕ) (a : R) [Decidable (a = 0)] :
    order (monomial n a) = if a = 0 then (⊤ : ℕ∞) else n := by
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
theorem order_monomial_of_ne_zero (n : ℕ) (a : R) (h : a ≠ 0) : order (monomial n a) = n := by
  classical
  rw [order_monomial, if_neg h]

/-- If `n` is strictly smaller than the order of `ψ`, then the `n`th coefficient of its product
with any other power series is `0`. -/
theorem coeff_mul_of_lt_order {φ ψ : R⟦X⟧} {n : ℕ} (h : ↑n < ψ.order) :
    coeff n (φ * ψ) = 0 := by
  suffices coeff n (φ * ψ) = ∑ p ∈ antidiagonal n, 0 by rw [this, Finset.sum_const_zero]
  rw [coeff_mul]
  apply Finset.sum_congr rfl
  intro x hx
  refine mul_eq_zero_of_right (coeff x.fst φ) (coeff_of_lt_order x.snd (lt_of_le_of_lt ?_ h))
  rw [mem_antidiagonal] at hx
  norm_cast
  grind

theorem coeff_mul_one_sub_of_lt_order {R : Type*} [Ring R] {φ ψ : R⟦X⟧} (n : ℕ)
    (h : ↑n < ψ.order) : coeff n (φ * (1 - ψ)) = coeff n φ := by
  simp [coeff_mul_of_lt_order h, mul_sub]

theorem coeff_mul_prod_one_sub_of_lt_order {R ι : Type*} [CommRing R] (k : ℕ) (s : Finset ι)
    (φ : R⟦X⟧) (f : ι → R⟦X⟧) :
    (∀ i ∈ s, ↑k < (f i).order) → coeff k (φ * ∏ i ∈ s, (1 - f i)) = coeff k φ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    intro t
    simp only [Finset.mem_insert, forall_eq_or_imp] at t
    rw [Finset.prod_insert ha, ← mul_assoc, mul_right_comm, coeff_mul_one_sub_of_lt_order _ t.1]
    exact ih t.2

/-- Given a non-zero power series `f`, `divXPowOrder f` is the power series obtained by
dividing out the largest power of X that divides `f`, that is its order -/
def divXPowOrder (f : R⟦X⟧) : R⟦X⟧ :=
  .mk fun n ↦ coeff (n + f.order.toNat) f

@[deprecated (since := "2025-04-15")]
noncomputable alias divided_by_X_pow_order := divXPowOrder

@[simp]
lemma coeff_divXPowOrder {f : R⟦X⟧} {n : ℕ} :
    coeff n (divXPowOrder f) = coeff (n + f.order.toNat) f :=
  coeff_mk _ _

@[simp]
lemma divXPowOrder_zero :
    divXPowOrder (0 : R⟦X⟧) = 0 := by
  ext
  simp

lemma constantCoeff_divXPowOrder {f : R⟦X⟧} :
    constantCoeff (divXPowOrder f) = coeff f.order.toNat f := by
  simp [← coeff_zero_eq_constantCoeff]

lemma constantCoeff_divXPowOrder_eq_zero_iff {f : R⟦X⟧} :
    constantCoeff (divXPowOrder f) = 0 ↔ f = 0 := by
  by_cases h : f = 0
  · simp [h]
  · simp [constantCoeff_divXPowOrder, coeff_order h, h]

theorem X_pow_order_mul_divXPowOrder {f : R⟦X⟧} :
    X ^ f.order.toNat * divXPowOrder f = f := by
  ext n
  rw [coeff_X_pow_mul']
  split_ifs with h
  · simp [h]
  · push_neg at h
    rw [coeff_of_lt_order_toNat _ h]

@[deprecated (since := "2025-04-15")]
alias self_eq_X_pow_order_mul_divided_by_X_pow_order := X_pow_order_mul_divXPowOrder

theorem X_pow_order_dvd : X ^ φ.order.toNat ∣ φ := by
  simpa only [X_pow_dvd_iff] using coeff_of_lt_order_toNat

theorem order_eq_emultiplicity_X {R : Type*} [Semiring R] (φ : R⟦X⟧) :
    order φ = emultiplicity X φ := by
  classical
  rcases eq_or_ne φ 0 with (rfl | hφ)
  · simp
  cases ho : order φ with
  | top => simp [hφ] at ho
  | coe n =>
    have hn : φ.order.toNat = n := by simp [ho]
    rw [← hn, eq_comm]
    apply le_antisymm _
    · apply le_emultiplicity_of_pow_dvd
      apply X_pow_order_dvd
    · apply Order.le_of_lt_add_one
      rw [← not_le, ← Nat.cast_one, ← Nat.cast_add, ← pow_dvd_iff_le_emultiplicity]
      rintro ⟨ψ, H⟩
      have := congr_arg (coeff n) H
      rw [X_pow_mul, coeff_mul_of_lt_order, ← hn] at this
      · exact coeff_order hφ this
      · rw [X_pow_eq, order_monomial]
        split_ifs
        · simp
        · rw [← hn, ENat.coe_lt_coe]
          simp

end OrderBasic

section OrderZeroNeOne

variable [Semiring R] [Nontrivial R]

/-- The order of the formal power series `1` is `0`. -/
@[simp]
theorem order_one : order (1 : R⟦X⟧) = 0 := by
  simpa using order_monomial_of_ne_zero 0 (1 : R) one_ne_zero

/-- The order of an invertible power series is `0`. -/
theorem order_zero_of_unit {f : R⟦X⟧} : IsUnit f → f.order = 0 := by
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

/-- Dividing `X` by the maximal power of `X` dividing it leaves `1`. -/
@[simp]
theorem divXPowOrder_X :
    divXPowOrder X = (1 : R⟦X⟧) := by
  ext n
  simp [coeff_X]

@[deprecated (since := "2025-04-15")] alias divided_by_X_pow_order_of_X_eq_one := divXPowOrder_X

end OrderZeroNeOne

section NoZeroDivisors

variable [Semiring R] [NoZeroDivisors R]

/-- The order of the product of two formal power series over an integral domain
is the sum of their orders. -/
theorem order_mul (φ ψ : R⟦X⟧) : order (φ * ψ) = order φ + order ψ := by
  apply le_antisymm _ (le_order_mul _ _)
  by_cases h : φ = 0 ∨ ψ = 0
  · rcases h with h | h <;> simp [h]
  · push_neg at h
    rw [← coe_toNat_order h.1, ← coe_toNat_order h.2, ← ENat.coe_add]
    apply order_le
    rw [coeff_mul, Finset.sum_eq_single_of_mem ⟨φ.order.toNat, ψ.order.toNat⟩ (by simp)]
    · exact mul_ne_zero (coeff_order h.1) (coeff_order h.2)
    · intro ij hij h
      rcases trichotomy_of_add_eq_add (mem_antidiagonal.mp hij) with h' | h' | h'
      · exact False.elim (h (by simp [Prod.ext_iff, h'.1, h'.2]))
      · rw [coeff_of_lt_order_toNat ij.1 h', zero_mul]
      · rw [coeff_of_lt_order_toNat ij.2 h', mul_zero]

theorem order_pow [Nontrivial R] (φ : R⟦X⟧) (n : ℕ) :
    order (φ ^ n) = n • order φ := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · simp only [Subsingleton.eq_zero φ, order_zero, nsmul_eq_mul]
    by_cases hn : n = 0
    · simp [hn, pow_zero]
    · simp [zero_pow hn, ENat.mul_top', if_neg hn]
  induction n with
  | zero => simp
  | succ n hn =>
    simp only [add_smul, one_smul, pow_succ, order_mul, hn]

/-- The operation of dividing a power series by the largest possible power of `X`
preserves multiplication. -/
theorem divXPowOrder_mul_divXPowOrder {f g : R⟦X⟧} :
    divXPowOrder f * divXPowOrder g = divXPowOrder (f * g) := by
  by_cases h : f = 0 ∨ g = 0
  · rcases h with (h | h) <;> simp [h]
  push_neg at h
  apply X_pow_mul_cancel (k := f.order.toNat + g.order.toNat)
  calc
    X ^ (f.order.toNat + g.order.toNat) * (f.divXPowOrder * g.divXPowOrder)
    _ = (X ^ f.order.toNat * f.divXPowOrder) * (X ^ g.order.toNat * g.divXPowOrder) := by
        conv_rhs =>
          rw [mul_assoc, X_pow_mul, X_pow_mul, ← mul_assoc, mul_assoc, ← pow_add]
        rw [X_pow_mul, add_comm]
    _ = f * g := by
        simp [X_pow_order_mul_divXPowOrder]
    _ = X ^ ((f * g).order.toNat) * (f * g).divXPowOrder := by
        simp [X_pow_order_mul_divXPowOrder]
    _ = X ^ (f.order.toNat + g.order.toNat) * (f * g).divXPowOrder := by
        rw [order_mul, ENat.toNat_add (order_eq_top.not.mpr h.1) (order_eq_top.not.mpr h.2)]

@[deprecated (since := "2025-04-15")] alias divided_by_X_pow_orderMul :=
  divXPowOrder_mul_divXPowOrder

end NoZeroDivisors

end PowerSeries

end
