/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Matthew Robert Ballard
-/
module

public import Mathlib.Data.Nat.MaxPowDiv
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

@[expose] public section

assert_not_exists Field

universe u

open Nat

variable {p : ℕ}

theorem padicValNat_eq_emultiplicity_of_ne_one (hp : p ≠ 1) {n : ℕ} (hn : n ≠ 0) :
    padicValNat p n = emultiplicity p n := by
  rw [eq_comm, emultiplicity_eq_coe, pow_dvd_iff_le_padicValNat hp hn,
    pow_dvd_iff_le_padicValNat hp hn]
  simp

@[simp]
theorem Nat.toNat_emultiplicity (p n : ℕ) : (emultiplicity p n).toNat = padicValNat p n := by
  rcases eq_or_ne p 1 with rfl | hp
  · simp
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [← padicValNat_eq_emultiplicity_of_ne_one, *]

theorem padicValNat_def' {n : ℕ} (hp : p ≠ 1) (hn : n ≠ 0) :
    padicValNat p n = multiplicity p n :=
  .symm <| multiplicity_eq_of_emultiplicity_eq_some <| .symm <|
    padicValNat_eq_emultiplicity_of_ne_one hp hn

/-- A simplification of `padicValNat` when one input is prime, by analogy with
`padicValRat_def`. -/
theorem padicValNat_def [hp : Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    padicValNat p n = multiplicity p n :=
  padicValNat_def' hp.out.ne_one hn

/-- A simplification of `padicValNat` when one input is prime, by analogy with
`padicValRat_def`. -/
theorem padicValNat_eq_emultiplicity [hp : Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    padicValNat p n = emultiplicity p n :=
  padicValNat_eq_emultiplicity_of_ne_one hp.out.ne_one hn

namespace padicValNat

@[deprecated (since := "2026-03-15")]
alias maxPowDiv_eq_emultiplicity := padicValNat_eq_emultiplicity

@[deprecated (since := "2026-03-15")]
alias maxPowDiv_eq_multiplicity := padicValNat_def'

@[deprecated padicValNat_zero_right (since := "2026-03-15")]
protected theorem zero : padicValNat p 0 = 0 := padicValNat_zero_right p

@[deprecated padicValNat_one_right (since := "2026-03-15")]
protected theorem one : padicValNat p 1 = 0 := padicValNat_one_right p

@[simp]
theorem eq_zero_iff {n : ℕ} : padicValNat p n = 0 ↔ p = 1 ∨ n = 0 ∨ ¬p ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn₀; · simp
  rcases eq_or_ne p 1 with rfl | hp₁; · simp
  simpa [*] using pow_dvd_iff_le_padicValNat (k := 1) hp₁ hn₀ |>.symm |>.not

end padicValNat

open List

theorem le_emultiplicity_iff_replicate_subperm_primeFactorsList {a b : ℕ} {n : ℕ} (ha : a.Prime)
    (hb : b ≠ 0) :
    ↑n ≤ emultiplicity a b ↔ replicate n a <+~ b.primeFactorsList :=
  (replicate_subperm_primeFactorsList_iff ha hb).trans
    pow_dvd_iff_le_emultiplicity |>.symm

theorem le_padicValNat_iff_replicate_subperm_primeFactorsList {a b : ℕ} {n : ℕ} (ha : a.Prime)
    (hb : b ≠ 0) :
    n ≤ padicValNat a b ↔ replicate n a <+~ b.primeFactorsList := by
  rw [← le_emultiplicity_iff_replicate_subperm_primeFactorsList ha hb,
    Nat.finiteMultiplicity_iff.2 ⟨ha.ne_one, Nat.pos_of_ne_zero hb⟩
      |>.emultiplicity_eq_multiplicity, ← padicValNat_def' ha.ne_one hb,
    Nat.cast_le]
