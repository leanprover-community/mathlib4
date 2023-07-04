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

We run some Lucas-Lehmer tests to prove some Mersenne primes are prime.

See the discussion at the end of [Mathlib/NumberTheory/LucasLehmer.lean]
for ideas about extending this to larger Mersenne primes.
-/


example : (mersenne 13).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by lucas_lehmer_test)

example : (mersenne 17).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by lucas_lehmer_test)

example : (mersenne 19).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by lucas_lehmer_test)

/-- 2147483647.Prime, Euler (1772) -/
example : (mersenne 31).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by lucas_lehmer_test)

/-!
The next four primality tests are too slow to run interactively with -T100000,
but work fine on the command line.
-/


-- /-- 2305843009213693951.Prime, Pervouchine (1883), Seelhoff (1886) -/
-- example : (mersenne 61).Prime :=
--   lucas_lehmer_sufficiency _ (by norm_num) (by LucasLehmer.run_test).
-- /-- 618970019642690137449562111.Prime, Powers (1911) -/
-- -- takes ~100s
-- example : (mersenne 89).Prime :=
--   lucas_lehmer_sufficiency _ (by norm_num) (by LucasLehmer.run_test).
-- /-- 162259276829213363391578010288127.Prime, Power (1914) -/
-- -- takes ~190s
-- example : (mersenne 107).Prime :=
--   lucas_lehmer_sufficiency _ (by norm_num) (by LucasLehmer.run_test).
-- /-- 170141183460469231731687303715884105727.Prime, Lucas (1876) -/
-- -- takes ~370s
-- example : (mersenne 127).Prime :=
--   lucas_lehmer_sufficiency _ (by norm_num) (by LucasLehmer.run_test).
-- This still doesn't get us over the big gap and into the computer era, unfortunately.
-- /-- (2^521 - 1).Prime, Robinson (1954) -/
-- -- This has not been run successfully!
-- example : (mersenne 521).Prime :=
--   lucas_lehmer_sufficiency _ (by norm_num) (by LucasLehmer.run_test).
