/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Order.CauSeq.BigOperators
import Mathlib.Analysis.Normed.Ring.Basic

/-! # Cauchy divided powers

We introduce a class for making an abstract exponential function.

-/

open Finset Nat
open CauSeq Finset IsAbsoluteValue

variable {A : Type*} [NormedRing A]

/-- A class that allows us to define exponential functions without division. -/
class CauchyDividedPower (A) [NormedRing A] where
  /-- The divided power function -/
  dpow : ℕ → A → A
  /-- The submonoid where we define exp. -/
  support : AddSubmonoid A
  dpow_null : ∀ {n x} (_ : x ∉ support), dpow n x = 0
  dpow_zero : ∀ {x} (_ : x ∈ support), dpow 0 x = 1
  dpow_one : ∀ {x} (_ : x ∈ support), dpow 1 x = x
--  dpow_mem : ∀ {n x} (_ : n ≠ 0) (_ : x ∈ support), dpow n x ∈ support
  dpow_add : ∀ {n} {x y} (_ : x ∈ support) (_ : y ∈ support) (_ : x * y = y * x),
    dpow n (x + y) = Finset.sum (range (n + 1)) fun k ↦ dpow k x * dpow (n - k) y
  mul_dpow : ∀ {m n} {x} (_ : x ∈ support),
    dpow m x * dpow n x = choose (m + n) m • dpow (m + n) x
  cauchy : ∀ x, IsCauSeq (‖·‖) fun n => ∑ m ∈ range n, ‖dpow m x‖

namespace CauchyDividedPower

/-- The Cauchy sequence defining the exponential. -/
@[pp_nodot]
def exp' [IsAbsoluteValue (R := A) (‖·‖)] [CauchyDividedPower A] (x : A) : CauSeq A (‖·‖) :=
  ⟨fun n => ∑ m ∈ range n, dpow m x, (cauchy x).of_abv⟩

/-- The exponential function. -/
noncomputable def exp [IsAbsoluteValue (R := A) (‖·‖)] [CauSeq.IsComplete A (‖·‖)]
    [CauchyDividedPower A] (x : A) : A :=
  CauSeq.lim (exp' x)

theorem dpow_pos_zero [NoZeroSMulDivisors ℕ A] [CauchyDividedPower A] {n : ℕ} (hn : n ≠ 0) :
    dpow n (0 : A) = 0 := by
  induction n with
  | zero => exact (hn rfl).elim
  | succ n ih =>
    have : dpow n (0 : A) * dpow 1 0 = choose (n + 1) n • dpow (n + 1) 0 :=
      mul_dpow (AddSubmonoid.zero_mem support)
    rw [dpow_one (AddSubmonoid.zero_mem support), mul_zero, choose_symm_add,
      choose_one_right] at this
    exact (smul_eq_zero_iff_right hn).mp this.symm

theorem exp_zero [IsAbsoluteValue (R := A) (‖·‖)] [CauSeq.IsComplete A (‖·‖)]
    [CauchyDividedPower A] [NoZeroSMulDivisors ℕ A] :
    exp (0 : A) = 1 := by
  have (n : ℕ) : ∑ m ∈ range n, dpow m (0 : A) = if n = 0 then 0 else 1 := by
    by_cases h : n = 0
    · simp [h]
    · simp only [h, ↓reduceIte, ← dpow_zero (AddSubmonoid.zero_mem support)]
      exact Finset.sum_eq_single_of_mem 0 (mem_range.mpr <| zero_lt_of_ne_zero h)
        fun k _ hk ↦ dpow_pos_zero hk
  simp_rw [exp, exp', this]
  exact lim_eq_of_equiv_const fun ε ε0 => ⟨1, fun j hj => by simp [ε0, Nat.ne_zero_of_lt hj]⟩

theorem exp_add [IsAbsoluteValue (R := A) (‖·‖)] [CauSeq.IsComplete A (‖·‖)]
    [CauchyDividedPower A] {x y : A} (hx : x ∈ CauchyDividedPower.support)
    (hy : y ∈ CauchyDividedPower.support) (hxy : x * y = y * x):
    exp (x + y) = exp x * exp y := by
  simp_rw [exp, exp', lim_mul_lim]
  apply (lim_eq_lim_of_equiv _).symm
  simp_rw [CauchyDividedPower.dpow_add hx hy hxy]
  exact cauchy_product (CauchyDividedPower.cauchy x) (CauchyDividedPower.cauchy y).of_abv

end CauchyDividedPower
