/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module examples.mersenne_primes
! leanprover-community/mathlib commit 58581d0fe523063f5651df0619be2bf65012a94a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.NumberTheory.LucasLehmer

/-!
# Explicit Mersenne primes

We run some Lucas-Lehmer tests to prove the first Mersenne primes are prime.

See the discussion at the end of [Mathlib/NumberTheory/LucasLehmer.lean]
for ideas about extending this to larger Mersenne primes.
-/

set_option profiler true

-- The Lucas-Lehmer test does not apply to `mersenne 2`
example : ¬ LucasLehmerTest 2 := by norm_num

example : (mersenne 2).Prime := by decide

example : (mersenne 3).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

example : (mersenne 5).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

example : (mersenne 7).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

example : (mersenne 13).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

example : (mersenne 17).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

example : (mersenne 19).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

/-- 2147483647.Prime, Euler (1772) -/
example : (mersenne 31).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

/-- Pervushin (1883), Seelhoff (1886) -/
example : (mersenne 61).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

example : (mersenne 89).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

example : (mersenne 107).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

/-- Édouard Lucas (1876) -/
example : (mersenne 127).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

/-- Robinson and Lehmer using SWAC computer, (1952) -/
example : (mersenne 521).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

example : (mersenne 607).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

example : (mersenne 1279).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

example : (mersenne 2203).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

example : (mersenne 2281).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

/-- Riesel (1957) -/
example : (mersenne 3217).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

/-- Hurwitz (1961) -/
example : (mersenne 4253).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

example : (mersenne 4423).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

/-- Gillies (1963) -/
example : (mersenne 9689).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

example : (mersenne 9941).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

example : (mersenne 11213).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

/-- Tuckerman (1971) -/
example : (mersenne 19937).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

/-- Noll and Nickel (1978) -/
example : (mersenne 21701).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

/-- Noll (1979) -/
example : (mersenne 23209).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

-- First failing example ("deep recursion detected")
-- /-- Nelson and Slowinski (1979)) -/
-- example : (mersenne 44497).Prime :=
--   lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)
