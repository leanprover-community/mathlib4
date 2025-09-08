/-
Copyright (c) 2025 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
import Mathlib.NumberTheory.FLT.Basic

/-!
# Euler's sum of powers conjecture

Euler's sum of powers conjecture says that at least n nth powers of positive integers
are required to sum to an nth power of a positive integer.

This was an attempt to generalize Fermat's Last Theorem,
which is the special case of summing 2 nth powers.

https://en.wikipedia.org/wiki/Euler%27s_sum_of_powers_conjecture
http://euler.free.fr/
-/


namespace Counterexample

/-- Euler's sum of powers conjecture over a given semiring with a specific exponent. -/
abbrev SumOfPowersConjectureWith (R : Type*) [Semiring R] (n : ℕ) : Prop :=
  ∀ (a : List R) (b : R), 2 ≤ a.length → 0 ∉ a → b ≠ 0 →
  (a.map (· ^ n)).sum = b ^ n → n ≤ a.length

/-- Euler's sum of powers conjecture over the naturals for a given exponent. -/
abbrev SumOfPowersConjectureFor (n : ℕ) : Prop := SumOfPowersConjectureWith ℕ n

/-- Euler's sum of powers conjecture over the naturals. -/
abbrev SumOfPowersConjecture : Prop := ∀ n, SumOfPowersConjectureFor n

/-- Euler's sum of powers conjecture over the integers for a given exponent. -/
abbrev SumOfPowersConjectureIntFor (n : ℕ) : Prop := SumOfPowersConjectureWith ℤ n

/-- Euler's sum of powers conjecture over the integers. -/
abbrev SumOfPowersConjectureInt : Prop := ∀ n, SumOfPowersConjectureIntFor n

/-- Euler's sum of powers conjecture over a given semiring with a specific exponent implies FLT. -/
theorem fermatLastTheoremWith_of_sumOfPowersConjectureWith (R : Type*) [Semiring R] :
    ∀ n ≥ 3, SumOfPowersConjectureWith R n → FermatLastTheoremWith R n := by
  intro n hn conj a b c ha hb hc hsum
  have : n ≤ 2 := conj [a, b] c (by simp) (by simp [ha.symm, hb.symm]) hc (by simpa)
  omega

/-- Euler's sum of powers conjecture over the naturals implies FLT. -/
theorem fermatLastTheorem_of_sumOfPowersConjecture : SumOfPowersConjecture → FermatLastTheorem :=
  fun conj n hn ↦ fermatLastTheoremWith_of_sumOfPowersConjectureWith ℕ n hn (conj n)

/--
The first counterexample was found by L. J. Lander and T. R. Parkin in 1966
through a computer search, disproving the conjecture.
https://www.ams.org/journals/bull/1966-72-06/S0002-9904-1966-11654-3/S0002-9904-1966-11654-3.pdf
-/
theorem sum_of_powers_conjecture_false₀ : ¬SumOfPowersConjectureFor 5 := by
  intro conj
  let n := 5
  let a := [27, 84, 110, 133]
  let b := 144
  have : 5 ≤ 4 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega

/--
Noam D. Elkies, October 1988
https://www.ams.org/journals/mcom/1988-51-184/S0025-5718-1988-0930224-9/S0025-5718-1988-0930224-9.pdf
-/
theorem sum_of_powers_conjecture_false₁ : ¬SumOfPowersConjectureFor 4 := by
  intro conj
  let n := 4
  let a := [2_682_440, 15_365_639, 18_796_760]
  let b := 20_615_673
  have : 4 ≤ 3 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega

/--
Roger E. Frye, November 1988
https://ieeexplore.ieee.org/document/74138
-/
theorem sum_of_powers_conjecture_false₂ : ¬SumOfPowersConjectureFor 4 := by
  intro conj
  let n := 4
  let a := [95_800, 217_519, 414_560]
  let b := 422_481
  have : 4 ≤ 3 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega

/--
Bob Scher, Ed Seidl, 1996
This counterexample uses a negative number,
so it does not disprove the conjecture over ℕ, but rather over ℤ.
-/
theorem sum_of_powers_conjecture_int_false₀ : ¬SumOfPowersConjectureIntFor 5 := by
  intro conj
  let n := 5
  let a := [-220, 5_027, 6_237, 14_068]
  let b := 14_132
  have : 5 ≤ 4 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega

/-- Allan MacLeod, 1997 -/
theorem sum_of_powers_conjecture_false₃ : ¬SumOfPowersConjectureFor 4 := by
  intro conj
  let n := 4
  let a := [673_865, 1_390_400, 2_767_624]
  let b := 2_813_001
  have : 4 ≤ 3 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega

/-- Allan MacLeod, 1998 -/
theorem sum_of_powers_conjecture_false₄ : ¬SumOfPowersConjectureFor 4 := by
  intro conj
  let n := 4
  let a := [219_076_465, 275_156_240, 630_662_624]
  let b := 638_523_249
  have : 4 ≤ 3 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega

/--
Daniel J. Bernstein, 2000-06-12
https://www.ams.org/journals/mcom/2001-70-233/S0025-5718-00-01219-9/S0025-5718-00-01219-9.pdf
-/
theorem sum_of_powers_conjecture_false₅ : ¬SumOfPowersConjectureFor 4 := by
  intro conj
  let n := 4
  let a := [1_705_575, 5_507_880, 8_332_208]
  let b := 8_707_481
  have : 4 ≤ 3 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega

/-- Daniel J. Bernstein, 2000-06-12 -/
theorem sum_of_powers_conjecture_false₆ : ¬SumOfPowersConjectureFor 4 := by
  intro conj
  let n := 4
  let a := [5_870_000, 8_282_543, 11_289_040]
  let b := 12_197_457
  have : 4 ≤ 3 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega

/-- Daniel J. Bernstein, 2000-06-12 -/
theorem sum_of_powers_conjecture_false₇ : ¬SumOfPowersConjectureFor 4 := by
  intro conj
  let n := 4
  let a := [4_479_031, 12_552_200, 14_173_720]
  let b := 16_003_017
  have : 4 ≤ 3 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega

/-- Daniel J. Bernstein, 2000-06-12 -/
theorem sum_of_powers_conjecture_false₈ : ¬SumOfPowersConjectureFor 4 := by
  intro conj
  let n := 4
  let a := [3_642_840, 7_028_600, 16_281_009]
  let b := 16_430_513
  have : 4 ≤ 3 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega

/-- Jim Frye, 2004-08-27 -/
theorem sum_of_powers_conjecture_false₉ : ¬SumOfPowersConjectureFor 5 := by
  intro conj
  let n := 5
  let a := [55, 3_183, 28_969, 85_282]
  let b := 85_359
  have : 5 ≤ 4 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega

/-- Seiji Tomita, 2006-03-13 -/
theorem sum_of_powers_conjecture_false₁₀ : ¬SumOfPowersConjectureFor 4 := by
  intro conj
  let n := 4
  let a := [186_668_000, 260_052_385, 582_665_296]
  let b := 589_845_921
  have : 4 ≤ 3 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega

/-- Seiji Tomita, 2006-03-13 -/
theorem sum_of_powers_conjecture_false₁₁ : ¬SumOfPowersConjectureFor 4 := by
  intro conj
  let n := 4
  let a := [50_237_800, 632_671_960, 1_670_617_271]
  let b := 1_679_142_729
  have : 4 ≤ 3 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega

/-- Seiji Tomita, 2006-03-13 -/
theorem sum_of_powers_conjecture_false₁₂ : ¬SumOfPowersConjectureFor 4 := by
  intro conj
  let n := 4
  let a := [7_592_431_981_391, 22_495_595_284_040, 27_239_791_692_640]
  let b := 29_999_857_938_609
  have : 4 ≤ 3 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega

/-- Seiji Tomita, 2006-03-13 -/
theorem sum_of_powers_conjecture_false₁₃ : ¬SumOfPowersConjectureFor 4 := by
  intro conj
  let n := 4
  let a := [
    169_218_021_322_170_204_480_680_305,
    1_288_056_982_586_427_591_062_203_384,
    1_507_524_066_882_038_472_584_786_800,
  ]
  let b := 1_677_479_490_238_223_823_661_446_513
  have : 4 ≤ 3 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega

/-- Robert Gerbicz, 2006-11-02 -/
theorem sum_of_powers_conjecture_false₁₄ : ¬SumOfPowersConjectureFor 4 := by
  intro conj
  let n := 4
  let a := [34_918_520, 87_865_617, 106_161_120]
  let b := 117_112_081
  have : 4 ≤ 3 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega

/-- Robert Gerbicz, 2006-11-08 -/
theorem sum_of_powers_conjecture_false₁₅ : ¬SumOfPowersConjectureFor 4 := by
  intro conj
  let n := 4
  let a := [2_164_632, 31_669_120, 41_084_175]
  let b := 44_310_257
  have : 4 ≤ 3 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega

/-- Robert Gerbicz, 2006-11-08 -/
theorem sum_of_powers_conjecture_false₁₆ : ¬SumOfPowersConjectureFor 4 := by
  intro conj
  let n := 4
  let a := [10_409_096, 42_878_560, 65_932_985]
  let b := 68_711_097
  have : 4 ≤ 3 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega

/-- Seiji Tomita, 2007-01-28 -/
theorem sum_of_powers_conjecture_false₁₇ : ¬SumOfPowersConjectureFor 4 := by
  intro conj
  let n := 4
  let a := [664_793_200, 2_448_718_655, 3_134_081_336]
  let b := 3_393_603_777
  have : 4 ≤ 3 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega

/-- Juergen Rathmann, 2007-05-31 -/
theorem sum_of_powers_conjecture_false₁₈ : ¬SumOfPowersConjectureFor 4 := by
  intro conj
  let n := 4
  let a := [1_841_160, 121_952_168, 122_055_375]
  let b := 145_087_793
  have : 4 ≤ 3 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega

/-- Juergen Rathmann, 2007-06-01 -/
theorem sum_of_powers_conjecture_false₁₉ : ¬SumOfPowersConjectureFor 4 := by
  intro conj
  let n := 4
  let a := [27_450_160, 108_644_015, 146_627_384]
  let b := 156_646_737
  have : 4 ≤ 3 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega

/-- Seiji Tomita, 2007-10-24 -/
theorem sum_of_powers_conjecture_false₂₀ : ¬SumOfPowersConjectureFor 4 := by
  intro conj
  let n := 4
  let a := [140_976_551, 5_821_981_400, 15_355_831_360]
  let b := 15_434_547_801
  have : 4 ≤ 3 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega

/--
Robert Gerbicz, Leonid Durman, Yuri Radaev, Alexey Zubkov, 2007-10-31
https://euler413.narod.ru/
-/
theorem sum_of_powers_conjecture_false₂₁ : ¬SumOfPowersConjectureFor 4 := by
  intro conj
  let n := 4
  let a := [92_622_401, 1_553_556_440, 1_593_513_080]
  let b := 1_871_713_857
  have : 4 ≤ 3 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega

/-- Robert Gerbicz, Leonid Durman, Yuri Radaev, Alexey Zubkov, 2007-11-02 -/
theorem sum_of_powers_conjecture_false₂₂ : ¬SumOfPowersConjectureFor 4 := by
  intro conj
  let n := 4
  let a := [558_424_440, 606_710_871, 769_321_280]
  let b := 873_822_121
  have : 4 ≤ 3 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega

/-- Robert Gerbicz, Leonid Durman, Yuri Radaev, Alexey Zubkov, 2007-11-02 -/
theorem sum_of_powers_conjecture_false₂₃ : ¬SumOfPowersConjectureFor 4 := by
  intro conj
  let n := 4
  let a := [686_398_000, 1_237_796_960, 1_662_997_663]
  let b := 1_787_882_337
  have : 4 ≤ 3 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega

/-- Robert Gerbicz, Leonid Durman, Yuri Radaev, Alexey Zubkov, 2008-01-25 -/
theorem sum_of_powers_conjecture_false₂₄ : ¬SumOfPowersConjectureFor 4 := by
  intro conj
  let n := 4
  let a := [588_903_336, 859_396_455, 1_166_705_840]
  let b := 1_259_768_473
  have : 4 ≤ 3 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega


/-- Seiji Tomita, 2008-05-15 -/
theorem sum_of_powers_conjecture_false₂₅ : ¬SumOfPowersConjectureFor 4 := by
  intro conj
  let n := 4
  let a := [502_038_853_976, 2_480_452_675_600, 4_987_588_419_655]
  let b := 5_062_297_699_257
  have : 4 ≤ 3 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega

/-- Seiji Tomita, 2008-08-13 -/
theorem sum_of_powers_conjecture_false₂₆ : ¬SumOfPowersConjectureFor 4 := by
  intro conj
  let n := 4
  let a := [3_579_087_147_375_440, 14_890_026_433_468_471, 18_565_945_114_216_720]
  let b := 20_249_506_709_579_721
  have : 4 ≤ 3 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega

/-- Seiji Tomita, 2008-08-13 -/
theorem sum_of_powers_conjecture_false₂₇ : ¬SumOfPowersConjectureFor 4 := by
  intro conj
  let n := 4
  let a := [8_813_425_670_440_240, 47_886_740_272_114_976, 56_827_813_308_111_785]
  let b := 62_940_516_903_410_601
  have : 4 ≤ 3 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega

/-- Seiji Tomita, 2008-09-15 -/
theorem sum_of_powers_conjecture_false₂₈ : ¬SumOfPowersConjectureFor 4 := by
  intro conj
  let n := 4
  let a := [130_064_300_991_400, 440_804_942_580_160, 514_818_101_299_289]
  let b := 573_646_321_871_961
  have : 4 ≤ 3 := conj a b (by simp [a]) (by simp [a]) (by simp) (by decide)
  omega

end Counterexample
