/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Batteries.Data.Rat.Float

/-!
# Chudnovsky's formula for π

This file defines the infinite sum in Chudnovsky's formula for computing `π⁻¹`.
It does not (yet!) contain a proof; anyone is welcome to adopt this problem,
but at present we are a long way off.

## Main definitions

* `chudnovskySum`: The infinite sum in Chudnovsky's formula

## Future work

* Use this formula to give approximations for `π`.
* Prove the sum equals `π⁻¹`, as stated using `proof_wanted` below.
* Show that each imaginary quadratic field of class number 1 (corresponding to Heegner numbers)
  gives a Ramanujan type formula, and that this is the formula coming from 163,
  with $$j(\frac{1+\sqrt{-163}}{2}) = -640320^3$$, and the other magic constants coming from
  Eisenstein series.

## References
* [Milla, *A detailed proof of the Chudnovsky formula*][Milla_2018]
* [Chen and Glebov, *On Chudnovsky--Ramanujan type formulae*][Chen_Glebov_2018]

-/

open scoped Real BigOperators
open Nat

/-- The numerator of the nth term in Chudnovsky's series -/
def chudnovskyNum (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ n * (6 * n)! * (545140134 * n + 13591409)

/-- The denominator of the nth term in Chudnovsky's series -/
def chudnovskyDenom (n : ℕ) : ℕ :=
  (3 * n)! * (n)! ^ 3 * 640320 ^ (3 * n)

/-- The term at index `n` in Chudnovsky's series for `π⁻¹` -/
def chudnovskyTerm (n : ℕ) : ℚ :=
  chudnovskyNum n / chudnovskyDenom n

-- Sanity check that when calculated in `Float` we get the right answer:
/-- info: 3.141593 -/
#guard_msgs in
#eval 1 / (12 / (640320 : Float) ^ (3 / 2) *
  (List.ofFn fun n : Fin 37 => (chudnovskyTerm n).toFloat).sum)

/-- The infinite sum in Chudnovsky's formula for `π⁻¹` -/
noncomputable def chudnovskySum : ℝ :=
  12 / (640320 : ℝ) ^ (3 / 2 : ℝ) * ∑' n : ℕ, (chudnovskyTerm n : ℝ)

/-- **Chudnovsky's formula**: The sum equals `π⁻¹` -/
proof_wanted chudnovskySum_eq_pi_inv : chudnovskySum = π⁻¹

namespace Summable

open Filter Finset
open Topology

theorem alternating {f : ℕ → ℝ} (hf : Summable f) :
    Summable (fun n => (-1) ^ n * f n) :=
  Summable.of_abs (by simpa [summable_abs_iff])

theorem tendsto_alternating_series_tsum {f : ℕ → ℝ} (hfs : Summable f) :
    Tendsto (fun n => (∑ i ∈ range n, (-1) ^ i * f i)) atTop (𝓝 (∑' i : ℕ, (-1) ^ i * f i)) :=
  Summable.tendsto_sum_tsum_nat hfs.alternating

theorem alternating_series_error_bound
    (f : ℕ → ℝ) (hfa : Antitone f) (hfs : Summable f) (n : ℕ) :
    |(∑' i : ℕ, (-1) ^ i * f i) - (∑ i ∈ range n, (-1) ^ i * f i)| ≤ f n := by
  obtain h := hfs.tendsto_alternating_series_tsum
  have upper := hfa.alternating_series_le_tendsto h
  have lower := hfa.tendsto_le_alternating_series h
  obtain (h | h) := even_or_odd n
  · obtain ⟨n, rfl⟩ := even_iff_exists_two_mul.mp h
    specialize upper n
    specialize lower n
    simp [Finset.sum_range_succ] at lower
    rw [abs_sub_le_iff]
    constructor <;> linarith
  · obtain ⟨n, rfl⟩ := odd_iff_exists_bit1.mp h
    specialize upper (n + 1)
    specialize lower n
    rw [Nat.mul_add, Finset.sum_range_succ,
      show (-1 : ℝ) ^ (2 * n + 1) = -1 by simp [pow_add]] at upper
    rw [abs_sub_le_iff]
    constructor <;> linarith
