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

assert_not_exists Field

universe u

open Nat

variable {p : ℕ}

/-- For `p ≠ 1`, the `p`-adic valuation of a natural `n ≠ 0` is the largest natural number `k` such
that `p^k` divides `n`. If `n = 0` or `p = 1`, then `padicValNat p q` defaults to `0`. -/
def padicValNat (p : ℕ) (n : ℕ) : ℕ :=
  if h : p ≠ 1 ∧ 0 < n then Nat.find (finiteMultiplicity_iff.2 h) else 0

theorem padicValNat_def' {n : ℕ} (hp : p ≠ 1) (hn : n ≠ 0) :
    padicValNat p n = multiplicity p n := by
  simp only [padicValNat, ne_eq, hp, not_false_eq_true, Nat.pos_iff_ne_zero.mpr hn, and_self,
    ↓reduceDIte, multiplicity, emultiplicity,
    finiteMultiplicity_iff.mpr ⟨hp, Nat.pos_iff_ne_zero.mpr hn⟩]
  convert (WithTop.untopD_coe ..).symm

/-- A simplification of `padicValNat` when one input is prime, by analogy with
`padicValRat_def`. -/
theorem padicValNat_def [hp : Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    padicValNat p n = multiplicity p n :=
  padicValNat_def' hp.out.ne_one hn

/-- A simplification of `padicValNat` when one input is prime, by analogy with
`padicValRat_def`. -/
theorem padicValNat_eq_emultiplicity [hp : Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    padicValNat p n = emultiplicity p n := by
  rw [(finiteMultiplicity_iff.2
    ⟨hp.out.ne_one, Nat.pos_iff_ne_zero.mpr hn⟩).emultiplicity_eq_multiplicity]
  exact_mod_cast padicValNat_def hn

namespace padicValNat

open List

/-- `padicValNat p 0` is `0` for any `p`. -/
@[simp]
protected theorem zero : padicValNat p 0 = 0 := by simp [padicValNat]

/-- `padicValNat p 1` is `0` for any `p`. -/
@[simp]
protected theorem one : padicValNat p 1 = 0 := by simp [padicValNat]

@[simp]
theorem eq_zero_iff {n : ℕ} : padicValNat p n = 0 ↔ p = 1 ∨ n = 0 ∨ ¬p ∣ n := by
  simp only [padicValNat, ne_eq, pos_iff_ne_zero, dite_eq_right_iff, find_eq_zero, zero_add,
    pow_one, and_imp, ← or_iff_not_imp_left]

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
