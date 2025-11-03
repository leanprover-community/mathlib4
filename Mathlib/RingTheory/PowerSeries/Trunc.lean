/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.RingTheory.PowerSeries.Basic

/-!

# Formal power series in one variable - Truncation

`PowerSeries.trunc n φ` truncates a (univariate) formal power series
to the polynomial that has the same coefficients as `φ`, for all `m < n`,
and `0` otherwise.

-/

noncomputable section

open Polynomial

open Finset (antidiagonal mem_antidiagonal)

namespace PowerSeries

open Finsupp (single)

variable {R : Type*}

section Trunc
variable [Semiring R]
open Finset Nat

/-- The `n`th truncation of a formal power series to a polynomial -/
def trunc (n : ℕ) (φ : R⟦X⟧) : R[X] :=
  ∑ m ∈ Ico 0 n, Polynomial.monomial m (coeff m φ)

theorem coeff_trunc (m) (n) (φ : R⟦X⟧) :
    (trunc n φ).coeff m = if m < n then coeff m φ else 0 := by
  simp [trunc, Polynomial.coeff_monomial]

@[simp]
theorem trunc_zero (n) : trunc n (0 : R⟦X⟧) = 0 :=
  Polynomial.ext fun m => by
    rw [coeff_trunc, LinearMap.map_zero, Polynomial.coeff_zero]
    split_ifs <;> rfl

@[simp]
theorem trunc_one (n) : trunc (n + 1) (1 : R⟦X⟧) = 1 :=
  Polynomial.ext fun m => by
    grind [PowerSeries.coeff_trunc, PowerSeries.coeff_one, Polynomial.coeff_one]

@[simp]
theorem trunc_C (n) (a : R) : trunc (n + 1) (C a) = Polynomial.C a :=
  Polynomial.ext fun m => by
    rw [coeff_trunc, coeff_C, Polynomial.coeff_C]
    split_ifs with H <;> first | rfl | try simp_all

@[simp]
theorem trunc_add (n) (φ ψ : R⟦X⟧) : trunc n (φ + ψ) = trunc n φ + trunc n ψ :=
  Polynomial.ext fun m => by
    simp only [coeff_trunc, Polynomial.coeff_add]
    split_ifs with H
    · rfl
    · rw [zero_add]

theorem trunc_succ (f : R⟦X⟧) (n : ℕ) :
    trunc n.succ f = trunc n f + Polynomial.monomial n (coeff n f) := by
  rw [trunc, Ico_zero_eq_range, sum_range_succ, trunc, Ico_zero_eq_range]

theorem natDegree_trunc_lt (f : R⟦X⟧) (n) : (trunc (n + 1) f).natDegree < n + 1 := by
  rw [Nat.lt_succ_iff, natDegree_le_iff_coeff_eq_zero]
  intros
  rw [coeff_trunc]
  split_ifs with h
  · rw [Nat.lt_succ_iff, ← not_lt] at h
    contradiction
  · rfl

@[simp] lemma trunc_zero' {f : R⟦X⟧} : trunc 0 f = 0 := rfl

theorem degree_trunc_lt (f : R⟦X⟧) (n) : (trunc n f).degree < n := by
  rw [degree_lt_iff_coeff_zero]
  intros
  rw [coeff_trunc]
  split_ifs with h
  · rw [← not_le] at h
    contradiction
  · rfl

theorem eval₂_trunc_eq_sum_range {S : Type*} [Semiring S] (s : S) (G : R →+* S) (n) (f : R⟦X⟧) :
    (trunc n f).eval₂ G s = ∑ i ∈ range n, G (coeff i f) * s ^ i := by
  cases n with
  | zero =>
    rw [trunc_zero', range_zero, sum_empty, eval₂_zero]
  | succ n =>
    have := natDegree_trunc_lt f n
    rw [eval₂_eq_sum_range' (hn := this)]
    apply sum_congr rfl
    intro _ h
    rw [mem_range] at h
    congr
    rw [coeff_trunc, if_pos h]

@[simp] theorem trunc_X (n) : trunc (n + 2) X = (Polynomial.X : R[X]) := by
  ext d
  rw [coeff_trunc, coeff_X]
  split_ifs with h₁ h₂
  · rw [h₂, coeff_X_one]
  · rw [coeff_X_of_ne_one h₂]
  · rw [coeff_X_of_ne_one]
    intro hd
    apply h₁
    rw [hd]
    exact n.one_lt_succ_succ

lemma trunc_X_of {n : ℕ} (hn : 2 ≤ n) : trunc n X = (Polynomial.X : R[X]) := by
  cases n with
  | zero => contradiction
  | succ n =>
    cases n with
    | zero => contradiction
    | succ n => exact trunc_X n

@[simp]
lemma trunc_one_left (p : R⟦X⟧) : trunc (R := R) 1 p = .C (coeff 0 p) := by
  ext i; simp +contextual [coeff_trunc, Polynomial.coeff_C]

lemma trunc_one_X : trunc (R := R) 1 X = 0 := by simp

@[simp]
lemma trunc_C_mul (n : ℕ) (r : R) (f : R⟦X⟧) : trunc n (C r * f) = .C r * trunc n f := by
  ext i; simp [coeff_trunc]

@[simp]
lemma trunc_mul_C (n : ℕ) (f : R⟦X⟧) (r : R) : trunc n (f * C r) = trunc n f * .C r := by
  ext i; simp [coeff_trunc]

/-- Split off the first `n` coefficients. -/
lemma eq_shift_mul_X_pow_add_trunc (n : ℕ) (f : R⟦X⟧) :
    f = (mk fun i ↦ coeff (i + n) f) * X ^ n + (f.trunc n : R⟦X⟧) := by
  ext j
  rw [map_add, Polynomial.coeff_coe, coeff_mul_X_pow', coeff_trunc]
  simp_rw [← not_le]
  split_ifs with h <;> simp [h]

/-- Split off the first `n` coefficients. -/
lemma eq_X_pow_mul_shift_add_trunc (n : ℕ) (f : R⟦X⟧) :
    f = X ^ n * (mk fun i ↦ coeff (i + n) f) + (f.trunc n : R⟦X⟧) := by
  rw [← (commute_X_pow _ n).eq, ← eq_shift_mul_X_pow_add_trunc]

end Trunc

section Trunc
/-
Lemmas in this section involve the coercion `R[X] → R⟦X⟧`, so they may only be stated in the case
`R` is commutative. This is because the coercion is an `R`-algebra map.
-/
variable {R : Type*} [CommSemiring R]

open Nat hiding pow_succ pow_zero
open Finset Finset.Nat

theorem trunc_trunc_of_le {n m} (f : R⟦X⟧) (hnm : n ≤ m := by rfl) :
    trunc n ↑(trunc m f) = trunc n f := by
  ext d
  rw [coeff_trunc, coeff_trunc, coeff_coe]
  split_ifs with h
  · rw [coeff_trunc, if_pos <| lt_of_lt_of_le h hnm]
  · rfl

@[simp] theorem trunc_trunc {n} (f : R⟦X⟧) : trunc n ↑(trunc n f) = trunc n f :=
  trunc_trunc_of_le f

@[simp] theorem trunc_trunc_mul {n} (f g : R⟦X⟧) :
    trunc n ((trunc n f) * g : R⟦X⟧) = trunc n (f * g) := by
  ext m
  rw [coeff_trunc, coeff_trunc]
  split_ifs with h
  · rw [coeff_mul, coeff_mul, sum_congr rfl]
    intro _ hab
    have ha := lt_of_le_of_lt (antidiagonal.fst_le hab) h
    rw [coeff_coe, coeff_trunc, if_pos ha]
  · rfl

@[simp] theorem trunc_mul_trunc {n} (f g : R⟦X⟧) :
    trunc n (f * (trunc n g) : R⟦X⟧) = trunc n (f * g) := by
  rw [mul_comm, trunc_trunc_mul, mul_comm]

theorem trunc_trunc_mul_trunc {n} (f g : R⟦X⟧) :
    trunc n (trunc n f * trunc n g : R⟦X⟧) = trunc n (f * g) := by
  rw [trunc_trunc_mul, trunc_mul_trunc]

@[simp] theorem trunc_trunc_pow (f : R⟦X⟧) (n a : ℕ) :
    trunc n ((trunc n f : R⟦X⟧) ^ a) = trunc n (f ^ a) := by
  induction a with
  | zero =>
    rw [pow_zero, pow_zero]
  | succ a ih =>
    rw [_root_.pow_succ', _root_.pow_succ', trunc_trunc_mul,
      ← trunc_trunc_mul_trunc, ih, trunc_trunc_mul_trunc]

theorem trunc_coe_eq_self {n} {f : R[X]} (hn : natDegree f < n) : trunc n (f : R⟦X⟧) = f := by
  rw [← Polynomial.coe_inj]
  ext m
  rw [coeff_coe, coeff_trunc]
  split
  case isTrue h => rfl
  case isFalse h =>
    rw [not_lt] at h
    rw [coeff_coe]; symm
    exact coeff_eq_zero_of_natDegree_lt <| lt_of_lt_of_le hn h

/-- The function `coeff n : R⟦X⟧ → R` is continuous. I.e. `coeff n f` depends only on a sufficiently
long truncation of the power series `f`. -/
theorem coeff_coe_trunc_of_lt {n m} {f : R⟦X⟧} (h : n < m) :
    coeff n (trunc m f) = coeff n f := by
  rwa [coeff_coe, coeff_trunc, if_pos]

/-- The `n`-th coefficient of `f*g` may be calculated
from the truncations of `f` and `g`. -/
theorem coeff_mul_eq_coeff_trunc_mul_trunc₂ {n a b} (f g : R⟦X⟧) (ha : n < a) (hb : n < b) :
    coeff n (f * g) = coeff n ((trunc a f : R⟦X⟧) * (trunc b g : R⟦X⟧)) := by
  symm
  rw [← coeff_coe_trunc_of_lt n.lt_succ_self, ← trunc_trunc_mul_trunc, trunc_trunc_of_le f ha,
    trunc_trunc_of_le g hb, trunc_trunc_mul_trunc, coeff_coe_trunc_of_lt n.lt_succ_self]

theorem coeff_mul_eq_coeff_trunc_mul_trunc {d n} (f g) (h : d < n) :
    coeff d (f * g) = coeff d ((trunc n f : R⟦X⟧) * (trunc n g : R⟦X⟧)) :=
  coeff_mul_eq_coeff_trunc_mul_trunc₂ f g h h

end Trunc

section Map
variable {S : Type*} [Semiring R] [Semiring S] (f : R →+* S)

lemma trunc_map (p : R⟦X⟧) (n : ℕ) : (p.map f).trunc n = (p.trunc n).map f := by
  ext m; simp [coeff_trunc, apply_ite f]

end Map

end PowerSeries

end
