/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.NumberTheory.LucasLehmer

#align_import examples.mersenne_primes from "leanprover-community/mathlib"@"58581d0fe523063f5651df0619be2bf65012a94a"

/-!
# Explicit Mersenne primes

We run some Lucas-Lehmer tests to prove the first Mersenne primes are prime.

See the discussion at the end of [Mathlib/NumberTheory/LucasLehmer.lean]
for ideas about extending this to larger Mersenne primes.
-/

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

/-- Lehmer and Robinson using SWAC computer, (1952) -/
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

example : (mersenne 3217).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

example : (mersenne 4253).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

example : (mersenne 4423).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

-- First failure ("deep recursion detected")
/-
example : (mersenne 9689).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)
-/
