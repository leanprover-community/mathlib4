/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Matthew Robert Ballard
-/
import Mathlib.RingTheory.Multiplicity
import Mathlib.Data.Nat.Factors

/-!
# `p`-adic Valuation

This file defines the `p`-adic valuation on `ℕ`, `ℤ`, and `ℚ`.

The `p`-adic valuation on `ℚ` is the difference of the multiplicities of `p` in the numerator and
denominator of `q`. This function obeys the standard properties of a valuation, with the appropriate
assumptions on `p`. The `p`-adic valuations on `ℕ` and `ℤ` agree with that on `ℚ`.

The valuation induces a norm on `ℚ`. This norm is defined in padicNorm.lean.
-/

universe u

open Nat

open multiplicity

variable {p : ℕ}

/-- For `p ≠ 1`, the `p`-adic valuation of a natural `n ≠ 0` is the largest natural number `k` such
that `p^k` divides `n`. If `n = 0` or `p = 1`, then `padicValNat p q` defaults to `0`. -/
noncomputable def padicValNat (p : ℕ) (n : ℕ) : ℕ :=
  if p ≠ 1 ∧ 0 < n then multiplicity p n else 0

/-- A simplification of `padicValNat` when one input is prime, by analogy with
`padicValRat_def`. -/
theorem padicValNat_def [hp : Fact p.Prime] {n : ℕ} (hn : 0 < n) :
    padicValNat p n = multiplicity p n :=
  dif_pos ⟨hp.out.ne_one, hn⟩

theorem padicValNat_def' {n : ℕ} (hp : p ≠ 1) (hn : 0 < n) :
    ↑(padicValNat p n) = multiplicity p n := by simp [padicValNat, hp, hn]

namespace padicValNat

open multiplicity

open List

/-- `padicValNat p 0` is `0` for any `p`. -/
@[simp]
protected theorem zero : padicValNat p 0 = 0 := by simp [padicValNat]

/-- `padicValNat p 1` is `0` for any `p`. -/
@[simp]
protected theorem one : padicValNat p 1 = 0 := by
  unfold padicValNat
  split_ifs with h
  · simp [Nat.multiplicity_finite_iff.2 h]
  · rfl

@[simp]
theorem eq_zero_iff {n : ℕ} : padicValNat p n = 0 ↔ p = 1 ∨ n = 0 ∨ ¬p ∣ n := by
  simp only [padicValNat, ne_eq, pos_iff_ne_zero, ite_eq_else, multiplicity_eq_zero, and_imp, ←
    or_iff_not_imp_left]

end padicValNat

open List

theorem le_emultiplicity_iff_replicate_subperm_primeFactorsList {a b : ℕ} {n : ℕ} (ha : a.Prime)
    (hb : b ≠ 0) :
    ↑n ≤ emultiplicity a b ↔ replicate n a <+~ b.primeFactorsList :=
  (replicate_subperm_primeFactorsList_iff ha hb).trans
    pow_dvd_iff_le_emultiplicity |>.symm

@[deprecated (since := "2024-07-17")]
alias le_multiplicity_iff_replicate_subperm_factors :=
  le_emultiplicity_iff_replicate_subperm_primeFactorsList

theorem le_padicValNat_iff_replicate_subperm_primeFactorsList {a b : ℕ} {n : ℕ} (ha : a.Prime)
    (hb : b ≠ 0) :
    n ≤ padicValNat a b ↔ replicate n a <+~ b.primeFactorsList := by
  rw [← le_emultiplicity_iff_replicate_subperm_primeFactorsList ha hb,
    Nat.multiplicity_finite_iff.2 ⟨ha.ne_one, Nat.pos_of_ne_zero hb⟩
      |>.emultiplicity_eq_multiplicity,     ← padicValNat_def' ha.ne_one (Nat.pos_of_ne_zero hb),
      Nat.cast_le]

@[deprecated (since := "2024-07-17")]
alias le_padicValNat_iff_replicate_subperm_factors :=
  le_padicValNat_iff_replicate_subperm_primeFactorsList
