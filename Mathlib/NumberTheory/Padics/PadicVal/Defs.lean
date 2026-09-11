/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Matthew Robert Ballard
-/
module

public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.Data.Nat.Factors

/-!
# `p`-adic Valuation

This file defines the `p`-adic valuation on `ℕ`, `ℤ`, and `ℚ`.

The `p`-adic valuation on `ℚ` is the difference of the multiplicities of `p` in the numerator and
denominator of `q`. This function obeys the standard properties of a valuation, with the appropriate
assumptions on `p`. The `p`-adic valuations on `ℕ` and `ℤ` agree with that on `ℚ`.

The valuation induces a norm on `ℚ`. This norm is defined in
`Mathlib/NumberTheory/Padics/PadicNorm.lean`.
-/

public section

assert_not_exists Field

universe u

open Nat

variable {p : ℕ}

theorem multiplicity_eq_emultiplicity_of_ne_one (hp : p ≠ 1) {n : ℕ} (hn : n ≠ 0) :
    multiplicity p n = emultiplicity p n := by
  rw [eq_comm, emultiplicity_eq_coe, pow_dvd_iff_le_multiplicity hp hn,
    pow_dvd_iff_le_multiplicity hp hn]
  simp

@[deprecated (since := "2026-09-11")] alias padicValNat_eq_emultiplicity_of_ne_one :=
  multiplicity_eq_emultiplicity_of_ne_one

@[simp]
theorem Nat.toNat_emultiplicity (p n : ℕ) : (emultiplicity p n).toNat = multiplicity p n := by
  rcases eq_or_ne p 1 with rfl | hp
  · simp
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [← multiplicity_eq_emultiplicity_of_ne_one, *]

@[deprecated (since := "2026-09-08")] alias padicValNat_def' := padicValNat_def

/-- A simplification of `multiplicity` when one input is prime, by analogy with
`padicValRat_def`. -/
theorem multiplicity_eq_emultiplicity [hp : Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    multiplicity p n = emultiplicity p n :=
  multiplicity_eq_emultiplicity_of_ne_one hp.out.ne_one hn

namespace padicValNat

@[deprecated (since := "2026-03-15")]
alias maxPowDiv_eq_emultiplicity := multiplicity_eq_emultiplicity

@[deprecated (since := "2026-03-15")]
alias maxPowDiv_eq_multiplicity := padicValNat_def'

@[deprecated multiplicity_zero_right (since := "2026-03-15")]
protected theorem zero : multiplicity p 0 = 0 := multiplicity_zero_right p

@[deprecated multiplicity_one_right (since := "2026-03-15")]
protected theorem one : multiplicity p 1 = 0 := multiplicity_one_right

end padicValNat

@[simp]
theorem Nat.multiplicity_eq_zero_iff {n : ℕ} : multiplicity p n = 0 ↔ p = 1 ∨ n = 0 ∨ ¬p ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn₀; · simp
  rcases eq_or_ne p 1 with rfl | hp₁; · simp
  simpa [*] using pow_dvd_iff_le_multiplicity (k := 1) hp₁ hn₀ |>.symm |>.not

@[deprecated (since := "2026-09-11")] alias padicValNat.eq_zero_iff :=
  Nat.multiplicity_eq_zero_iff

open List

theorem le_emultiplicity_iff_replicate_subperm_primeFactorsList {a b : ℕ} {n : ℕ} (ha : a.Prime)
    (hb : b ≠ 0) :
    ↑n ≤ emultiplicity a b ↔ replicate n a <+~ b.primeFactorsList :=
  (replicate_subperm_primeFactorsList_iff ha hb).trans
    pow_dvd_iff_le_emultiplicity |>.symm

theorem le_multiplicity_iff_replicate_subperm_primeFactorsList {a b : ℕ} {n : ℕ} (ha : a.Prime)
    (hb : b ≠ 0) :
    n ≤ multiplicity a b ↔ replicate n a <+~ b.primeFactorsList := by
  rw [← le_emultiplicity_iff_replicate_subperm_primeFactorsList ha hb,
    Nat.finiteMultiplicity_iff.2 ⟨ha.ne_one, Nat.pos_of_ne_zero hb⟩
      |>.emultiplicity_eq_multiplicity, ← padicValNat_def,
    ENat.natCast_le_natCast]

@[deprecated (since := "2026-09-11")] alias le_padicValNat_iff_replicate_subperm_primeFactorsList :=
le_multiplicity_iff_replicate_subperm_primeFactorsList

/-- A weak upper bound on `multiplicity p n`. -/
theorem mul_multiplicity_le {p n : ℕ} : p * multiplicity p n ≤ n := by
  obtain rfl | hp := eq_or_ne p 1
  · simp
  obtain rfl | hn := eq_or_ne n 0
  · simp
  grw [Nat.mul_le_pow hp, Nat.le_of_dvd hn.bot_lt (pow_multiplicity_dvd p n)]

@[deprecated (since := "2026-09-11")] alias mul_padicValNat_le := mul_multiplicity_le
