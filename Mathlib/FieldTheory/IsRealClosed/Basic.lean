/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Ring.Semireal.Defs
public import Mathlib.Tactic.LinearCombination

/-!
# Real Closed Field

A field `R` is real closed if all of the following hold:
1. `R` is real (that is, `-1` is not a sum of squares in `R`).
2. for every `x` in `R`, one of `x` or `-x` is a square.
3. every odd-degree polynomial over `R` has a root in `R`.

A real closed field is an algebraic generalisation of the real numbers.

In this file we define real closed fields and prove some of their properties.

TODO (Artie Khovanov) : equivalent conditions for a real field to be real closed
TODO (Artie Khovanov) : real numbers, real algebraic numbers, hyperreals form a real closed field

## Main Definitions

- `IsRealClosed R` is the typeclass saying `R` is a real closed field.

## Tags

real closed, rcf

-/

@[expose] public section

open Polynomial

/--
A field `R` is real closed if all of the following hold:
1. `R` is real (that is, `-1` is not a sum of squares in `R`).
2. for every `x` in `R`, one of `x` or `-x` is a square.
3. every odd-degree polynomial over `R` has a root in `R`.
-/
class IsRealClosed (R : Type*) [Field R] : Prop extends IsSemireal R where
  isSquare_or_isSquare_neg (x : R) : IsSquare x ∨ IsSquare (-x)
  exists_isRoot_of_odd_natDegree {f : R[X]} (hf : Odd f.natDegree) : ∃ x, f.IsRoot x

attribute [aesop 90% forward] IsRealClosed.isSquare_or_isSquare_neg

namespace IsRealClosed

universe u

variable {R : Type u} [Field R]

theorem of_linearOrderedField [LinearOrder R] [IsStrictOrderedRing R]
    (isSquare_of_nonneg : ∀ {x : R}, 0 ≤ x → IsSquare x)
    (exists_isRoot_of_odd_natDegree : ∀ {f : R[X]}, Odd f.natDegree → ∃ x, f.IsRoot x) :
    IsRealClosed R where
  isSquare_or_isSquare_neg {x} := by
    rcases le_total x 0 with (neg | pos)
    · exact .inr <| isSquare_of_nonneg (neg_nonneg_of_nonpos neg)
    · exact .inl <| isSquare_of_nonneg pos
  exists_isRoot_of_odd_natDegree := exists_isRoot_of_odd_natDegree

variable [IsRealClosed R]

@[aesop 50%]
theorem _root_.IsSquare.of_not_isSquare_neg {x : R} (hx : ¬ IsSquare (-x)) : IsSquare x := by aesop

@[aesop 80%]
theorem isSquare_neg_of_not_isSquare {x : R} (hx : ¬ IsSquare x) : IsSquare (-x) := by aesop

theorem exists_eq_pow_of_odd (x : R) {n : ℕ} (hn : Odd n) : ∃ r, x = r ^ n := by
  rcases exists_isRoot_of_odd_natDegree (f := X ^ n - C x) (by simp [hn]) with ⟨r, hr⟩
  exact ⟨r, by linear_combination - (by simpa using hr : r ^ n - x = 0)⟩

theorem exists_eq_zpow_of_odd (x : R) {k : ℤ} (hk : Odd k) : ∃ r, x = r ^ k := by
  rcases k.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · simpa using exists_eq_pow_of_odd x (by simpa using hk)
  · rcases exists_eq_pow_of_odd x (by simpa using hk) with ⟨r, hr⟩
    exact ⟨r⁻¹, by simpa using hr⟩

theorem exists_eq_pow_of_isSquare {x : R} (hx : IsSquare x) {n : ℕ} (hn : n ≠ 0) :
    ∃ r, x = r ^ n := by
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    rcases Nat.even_or_odd n with (even | odd)
    · rcases even with ⟨m, hm⟩
      rcases hx with ⟨s, hs⟩
      rcases isSquare_or_isSquare_neg s with (h | h) <;>
        rcases ih m (by lia) h (by lia) with ⟨r, hr⟩ <;>
        exact ⟨r, by simp [hm, pow_add, ← hr, hs]⟩
    · exact exists_eq_pow_of_odd x odd

theorem exists_eq_zpow_of_isSquare {x : R} (hx : IsSquare x) {k : ℤ} (hk : k ≠ 0) :
    ∃ r, x = r ^ k := by
  rcases k.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · simpa using exists_eq_pow_of_isSquare hx (by simpa using hk)
  · rcases exists_eq_pow_of_isSquare hx (by simpa using hk) with ⟨r, hr⟩
    exact ⟨r⁻¹, by simpa using hr⟩

section LinearOrderedField

variable [LinearOrder R] [IsStrictOrderedRing R]

theorem nonneg_iff_isSquare {x : R} : 0 ≤ x ↔ IsSquare x where
  mp h := by
    suffices IsSquare (-x) → x = 0 by aesop
    exact fun hc ↦ le_antisymm (nonpos_of_neg_nonneg (IsSquare.nonneg hc)) h
  mpr := IsSquare.nonneg

alias ⟨_root_.IsSquare.of_nonneg, _⟩ := nonneg_iff_isSquare

theorem exists_eq_pow_of_nonneg {x : R} (hx : 0 ≤ x) {n : ℕ} (hn : n ≠ 0) : ∃ r, x = r ^ n :=
  exists_eq_pow_of_isSquare (.of_nonneg hx) hn

theorem exists_eq_zpow_of_nonneg {x : R} (hx : 0 ≤ x) {k : ℤ} (hk : k ≠ 0) : ∃ r, x = r ^ k :=
  exists_eq_zpow_of_isSquare (.of_nonneg hx) hk

end LinearOrderedField

end IsRealClosed
