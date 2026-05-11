/-
Copyright (c) 2026 Meta Platforms, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/
module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.NumberTheory.PrimeCounting

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.NumberTheory.SylvesterSchur.ResidualFinite

/-!
# Finite certificates for the large residual Sylvester-Schur estimates

This file contains the explicit prime-counting and endpoint power certificates used for the
mid residual range in `Mathlib.NumberTheory.SylvesterSchur.ResidualLarge`.

## Main statements

* `second_residual_mid_primeCounting_lt_start_pow`: the finite prime-counting estimate for
  `38 ≤ n < 945` and `1291 ≤ k`.

## Implementation notes

The prime-counting certificates avoid one large computation by sieving with the primes up to
`29`, covering the remaining candidate set by private interval chunks, and exposing only the
resulting prime-counting bounds.  The endpoint power certificates are similarly hidden behind
mathematical inequalities for the relevant segments.  The numerical constants in this file are
certificate data for those interval and endpoint checks, not downstream API.
-/

@[expose] public section

namespace Nat.SylvesterSchur
namespace Internal

open Finset Nat

private def smallSievePrimes : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29}

private def smallSieveProduct : ℕ := 2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 * 29

private def factorialSieveCandidates (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun m => m ≠ 1 ∧ Nat.Coprime smallSieveProduct m)

private lemma prime_mem_smallSievePrimes_of_le_twenty_nine {p : ℕ}
    (hp : p.Prime) (hp29 : p ≤ 29) :
    p ∈ smallSievePrimes := by
  have hp2 : 2 ≤ p := hp.two_le
  interval_cases p <;> try norm_num [Nat.Prime] at hp <;> norm_num [smallSievePrimes]

private lemma prime_coprime_smallSieveProduct_of_twenty_nine_lt {p : ℕ}
    (hp : p.Prime) (hp29 : 29 < p) :
    Nat.Coprime smallSieveProduct p := by
  have hfac : Nat.Coprime (Nat.factorial 29) p := (hp.coprime_factorial_of_lt hp29).symm
  have hdiv : smallSieveProduct ∣ Nat.factorial 29 := by
    norm_num [smallSieveProduct, Nat.factorial]
  exact hfac.of_dvd_left hdiv

private lemma primeCounting_le_small_sieve (n : ℕ) :
    Nat.primeCounting n ≤ smallSievePrimes.card + (factorialSieveCandidates n).card := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  let counted := (Finset.range (n + 1)).filter Nat.Prime
  have hsubset : counted ⊆ smallSievePrimes ∪ factorialSieveCandidates n := by
    intro p hp
    have hp_mem_range : p ∈ Finset.range (n + 1) := (Finset.mem_filter.mp hp).1
    have hpr : p.Prime := (Finset.mem_filter.mp hp).2
    by_cases hp29 : p ≤ 29
    · exact Finset.mem_union_left _
        (prime_mem_smallSievePrimes_of_le_twenty_nine hpr hp29)
    · exact Finset.mem_union_right _ <| Finset.mem_filter.mpr ⟨hp_mem_range, hpr.ne_one,
        prime_coprime_smallSieveProduct_of_twenty_nine_lt hpr (by omega)⟩
  exact (Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)

private lemma primeCounting_le_of_factorial_sieve_card {n c B : ℕ}
    (hcard : (factorialSieveCandidates n).card = c)
    (hbound : smallSievePrimes.card + c ≤ B) :
    Nat.primeCounting n ≤ B := by
  exact (primeCounting_le_small_sieve n).trans (by rwa [hcard])

private def sieveChunk (lo hi : ℕ) : Finset ℕ :=
  (Finset.Icc lo hi).filter (fun m => m ≠ 1 ∧ Nat.Coprime smallSieveProduct m)

private def finsetUnionList : List (Finset ℕ) → Finset ℕ
  | [] => ∅
  | s :: ss => s ∪ finsetUnionList ss

private def finsetCardSum : List (Finset ℕ) → ℕ
  | [] => 0
  | s :: ss => s.card + finsetCardSum ss

private lemma card_finsetUnionList_le_cardSum (l : List (Finset ℕ)) :
    (finsetUnionList l).card ≤ finsetCardSum l := by
  induction l with
  | nil => simp [finsetUnionList, finsetCardSum]
  | cons s ss ih =>
      exact (Finset.card_union_le s (finsetUnionList ss)).trans
        (Nat.add_le_add_left ih s.card)

private lemma factorialSieveCandidates_card_le_of_chunks {n B : ℕ}
    {chunks : List (Finset ℕ)} (hcover : factorialSieveCandidates n ⊆ finsetUnionList chunks)
    (hcard : finsetCardSum chunks ≤ B) :
    (factorialSieveCandidates n).card ≤ B :=
  (Finset.card_le_card hcover).trans ((card_finsetUnionList_le_cardSum chunks).trans hcard)

private def sieveChunksOfBounds (bounds : List (ℕ × ℕ)) : List (Finset ℕ) :=
  bounds.map fun b => sieveChunk b.1 b.2

private lemma mem_finsetUnionList_sieveChunksOfBounds {bounds : List (ℕ × ℕ)}
    {b : ℕ × ℕ} {m : ℕ} (hb : b ∈ bounds)
    (hmprop : m ≠ 1 ∧ Nat.Coprime smallSieveProduct m) (hlo : b.1 ≤ m)
    (hhi : m ≤ b.2) :
    m ∈ finsetUnionList (sieveChunksOfBounds bounds) := by
  induction bounds with
  | nil => simp at hb
  | cons c cs ih =>
      rw [List.mem_cons] at hb
      change m ∈ sieveChunk c.1 c.2 ∪ finsetUnionList (sieveChunksOfBounds cs)
      rw [Finset.mem_union]
      rcases hb with hbc | hb
      · subst c
        left
        rw [sieveChunk, Finset.mem_filter]
        exact ⟨Finset.mem_Icc.mpr ⟨hlo, hhi⟩, hmprop⟩
      · right
        exact ih hb

private lemma factorialSieveCandidates_subset_sieveChunksOfBounds {n : ℕ}
    {bounds : List (ℕ × ℕ)}
    (hcover : ∀ {m : ℕ}, m ≤ n → ∃ b ∈ bounds, b.1 ≤ m ∧ m ≤ b.2) :
    factorialSieveCandidates n ⊆ finsetUnionList (sieveChunksOfBounds bounds) := by
  intro m hm
  have hm_range : m ∈ Finset.range (n + 1) := (Finset.mem_filter.mp hm).1
  have hmle : m ≤ n := by
    simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hm_range)
  have hmprop : m ≠ 1 ∧ Nat.Coprime smallSieveProduct m := (Finset.mem_filter.mp hm).2
  rcases hcover hmle with ⟨b, hb, hblo, hbhi⟩
  exact mem_finsetUnionList_sieveChunksOfBounds hb hmprop hblo hbhi

private lemma sieveChunk_card_le_0_99 : (sieveChunk 0 99).card ≤ 15 := by decide

private lemma sieveChunk_card_le_100_199 : (sieveChunk 100 199).card ≤ 21 := by decide

private lemma sieveChunk_card_le_200_299 : (sieveChunk 200 299).card ≤ 16 := by decide

private lemma sieveChunk_card_le_300_399 : (sieveChunk 300 399).card ≤ 16 := by decide

private lemma sieveChunk_card_le_400_499 : (sieveChunk 400 499).card ≤ 17 := by decide

private lemma sieveChunk_card_le_500_509 : (sieveChunk 500 509).card ≤ 2 := by decide

private lemma sieveChunk_card_le_500_599 : (sieveChunk 500 599).card ≤ 14 := by decide

private lemma sieveChunk_card_le_600_699 : (sieveChunk 600 699).card ≤ 16 := by decide

private lemma sieveChunk_card_le_700_715 : (sieveChunk 700 715).card ≤ 2 := by decide

private lemma sieveChunk_card_le_700_799 : (sieveChunk 700 799).card ≤ 14 := by decide

private lemma sieveChunk_card_le_800_855 : (sieveChunk 800 855).card ≤ 8 := by decide

private lemma sieveChunk_card_le_800_899 : (sieveChunk 800 899).card ≤ 15 := by decide

private lemma sieveChunk_card_le_900_917 : (sieveChunk 900 917).card ≤ 2 := by decide

private lemma sieveChunk_card_le_900_940 : (sieveChunk 900 940).card ≤ 5 := by decide

private lemma sieveChunk_card_le_900_944 : (sieveChunk 900 944).card ≤ 6 := by decide

/-! ### Prime-counting endpoint certificates -/

/- These private rows are certificate data for the mid residual range. The public statement
below packages the table as a single mathematical estimate. -/
private lemma primeCounting_le_75 : Nat.primeCounting 75 ≤ 21 :=
  primeCounting_le_of_factorial_sieve_card (c := 11) (by decide) (by decide)

private lemma primeCounting_le_157 : Nat.primeCounting 157 ≤ 37 :=
  primeCounting_le_of_factorial_sieve_card (c := 27) (by decide) (by decide)

private lemma primeCounting_le_309 : Nat.primeCounting 309 ≤ 63 :=
  primeCounting_le_of_factorial_sieve_card (c := 53) (by decide) (by decide)

private def sieveBounds509 : List (ℕ × ℕ) :=
  [(0, 99), (100, 199), (200, 299), (300, 399), (400, 499), (500, 509)]

private def sieveChunks509 : List (Finset ℕ) :=
  sieveChunksOfBounds sieveBounds509

private lemma factorialSieveCandidates_subset_sieveChunks509 :
    factorialSieveCandidates 509 ⊆ finsetUnionList sieveChunks509 := by
  exact factorialSieveCandidates_subset_sieveChunksOfBounds (bounds := sieveBounds509) <| by
    intro m hm
    simp [sieveBounds509]
    omega

private lemma factorialSieveCandidates_card_le_509 :
    (factorialSieveCandidates 509).card ≤ 87 :=
  factorialSieveCandidates_card_le_of_chunks factorialSieveCandidates_subset_sieveChunks509 <| by
    have h0 := sieveChunk_card_le_0_99
    have h1 := sieveChunk_card_le_100_199
    have h2 := sieveChunk_card_le_200_299
    have h3 := sieveChunk_card_le_300_399
    have h4 := sieveChunk_card_le_400_499
    have h5 := sieveChunk_card_le_500_509
    simp [sieveChunks509, sieveChunksOfBounds, sieveBounds509, finsetCardSum]
    omega

private lemma primeCounting_le_509 : Nat.primeCounting 509 ≤ 97 :=
  (primeCounting_le_small_sieve 509).trans <| by
    have hsmall : smallSievePrimes.card = 10 := by decide
    have hcard := factorialSieveCandidates_card_le_509
    omega

private def sieveBounds715 : List (ℕ × ℕ) :=
  [(0, 99), (100, 199), (200, 299), (300, 399), (400, 499), (500, 599),
    (600, 699), (700, 715)]

private def sieveChunks715 : List (Finset ℕ) :=
  sieveChunksOfBounds sieveBounds715

private lemma factorialSieveCandidates_subset_sieveChunks715 :
    factorialSieveCandidates 715 ⊆ finsetUnionList sieveChunks715 := by
  exact factorialSieveCandidates_subset_sieveChunksOfBounds (bounds := sieveBounds715) <| by
    intro m hm
    simp [sieveBounds715]
    omega

private lemma factorialSieveCandidates_card_le_715 :
    (factorialSieveCandidates 715).card ≤ 117 :=
  factorialSieveCandidates_card_le_of_chunks factorialSieveCandidates_subset_sieveChunks715 <| by
    have h0 := sieveChunk_card_le_0_99
    have h1 := sieveChunk_card_le_100_199
    have h2 := sieveChunk_card_le_200_299
    have h3 := sieveChunk_card_le_300_399
    have h4 := sieveChunk_card_le_400_499
    have h5 := sieveChunk_card_le_500_599
    have h6 := sieveChunk_card_le_600_699
    have h7 := sieveChunk_card_le_700_715
    simp [sieveChunks715, sieveChunksOfBounds, sieveBounds715, finsetCardSum]
    omega

private lemma primeCounting_le_715 : Nat.primeCounting 715 ≤ 127 :=
  (primeCounting_le_small_sieve 715).trans <| by
    have hsmall : smallSievePrimes.card = 10 := by decide
    have hcard := factorialSieveCandidates_card_le_715
    omega

private def sieveBounds855 : List (ℕ × ℕ) :=
  [(0, 99), (100, 199), (200, 299), (300, 399), (400, 499), (500, 599),
    (600, 699), (700, 799), (800, 855)]

private def sieveChunks855 : List (Finset ℕ) :=
  sieveChunksOfBounds sieveBounds855

private lemma factorialSieveCandidates_subset_sieveChunks855 :
    factorialSieveCandidates 855 ⊆ finsetUnionList sieveChunks855 := by
  exact factorialSieveCandidates_subset_sieveChunksOfBounds (bounds := sieveBounds855) <| by
    intro m hm
    simp [sieveBounds855]
    omega

private lemma factorialSieveCandidates_card_le_855 :
    (factorialSieveCandidates 855).card ≤ 137 :=
  factorialSieveCandidates_card_le_of_chunks factorialSieveCandidates_subset_sieveChunks855 <| by
    have h0 := sieveChunk_card_le_0_99
    have h1 := sieveChunk_card_le_100_199
    have h2 := sieveChunk_card_le_200_299
    have h3 := sieveChunk_card_le_300_399
    have h4 := sieveChunk_card_le_400_499
    have h5 := sieveChunk_card_le_500_599
    have h6 := sieveChunk_card_le_600_699
    have h7 := sieveChunk_card_le_700_799
    have h8 := sieveChunk_card_le_800_855
    simp [sieveChunks855, sieveChunksOfBounds, sieveBounds855, finsetCardSum]
    omega

private lemma primeCounting_le_855 : Nat.primeCounting 855 ≤ 147 :=
  (primeCounting_le_small_sieve 855).trans <| by
    have hsmall : smallSievePrimes.card = 10 := by decide
    have hcard := factorialSieveCandidates_card_le_855
    omega

private def sieveBounds917 : List (ℕ × ℕ) :=
  [(0, 99), (100, 199), (200, 299), (300, 399), (400, 499), (500, 599),
    (600, 699), (700, 799), (800, 899), (900, 917)]

private def sieveChunks917 : List (Finset ℕ) :=
  sieveChunksOfBounds sieveBounds917

private lemma factorialSieveCandidates_subset_sieveChunks917 :
    factorialSieveCandidates 917 ⊆ finsetUnionList sieveChunks917 := by
  exact factorialSieveCandidates_subset_sieveChunksOfBounds (bounds := sieveBounds917) <| by
    intro m hm
    simp [sieveBounds917]
    omega

private lemma factorialSieveCandidates_card_le_917 :
    (factorialSieveCandidates 917).card ≤ 146 :=
  factorialSieveCandidates_card_le_of_chunks factorialSieveCandidates_subset_sieveChunks917 <| by
    have h0 := sieveChunk_card_le_0_99
    have h1 := sieveChunk_card_le_100_199
    have h2 := sieveChunk_card_le_200_299
    have h3 := sieveChunk_card_le_300_399
    have h4 := sieveChunk_card_le_400_499
    have h5 := sieveChunk_card_le_500_599
    have h6 := sieveChunk_card_le_600_699
    have h7 := sieveChunk_card_le_700_799
    have h8 := sieveChunk_card_le_800_899
    have h9 := sieveChunk_card_le_900_917
    simp [sieveChunks917, sieveChunksOfBounds, sieveBounds917, finsetCardSum]
    omega

private lemma primeCounting_le_917 : Nat.primeCounting 917 ≤ 156 :=
  (primeCounting_le_small_sieve 917).trans <| by
    have hsmall : smallSievePrimes.card = 10 := by decide
    have hcard := factorialSieveCandidates_card_le_917
    omega

private def sieveBounds940 : List (ℕ × ℕ) :=
  [(0, 99), (100, 199), (200, 299), (300, 399), (400, 499), (500, 599),
    (600, 699), (700, 799), (800, 899), (900, 940)]

private def sieveChunks940 : List (Finset ℕ) :=
  sieveChunksOfBounds sieveBounds940

private lemma factorialSieveCandidates_subset_sieveChunks940 :
    factorialSieveCandidates 940 ⊆ finsetUnionList sieveChunks940 := by
  exact factorialSieveCandidates_subset_sieveChunksOfBounds (bounds := sieveBounds940) <| by
    intro m hm
    simp [sieveBounds940]
    omega

private lemma factorialSieveCandidates_card_le_940 :
    (factorialSieveCandidates 940).card ≤ 149 :=
  factorialSieveCandidates_card_le_of_chunks factorialSieveCandidates_subset_sieveChunks940 <| by
    have h0 := sieveChunk_card_le_0_99
    have h1 := sieveChunk_card_le_100_199
    have h2 := sieveChunk_card_le_200_299
    have h3 := sieveChunk_card_le_300_399
    have h4 := sieveChunk_card_le_400_499
    have h5 := sieveChunk_card_le_500_599
    have h6 := sieveChunk_card_le_600_699
    have h7 := sieveChunk_card_le_700_799
    have h8 := sieveChunk_card_le_800_899
    have h9 := sieveChunk_card_le_900_940
    simp [sieveChunks940, sieveChunksOfBounds, sieveBounds940, finsetCardSum]
    omega

private lemma primeCounting_le_940 : Nat.primeCounting 940 ≤ 159 :=
  (primeCounting_le_small_sieve 940).trans <| by
    have hsmall : smallSievePrimes.card = 10 := by decide
    have hcard := factorialSieveCandidates_card_le_940
    omega

private def sieveBounds944 : List (ℕ × ℕ) :=
  [(0, 99), (100, 199), (200, 299), (300, 399), (400, 499), (500, 599),
    (600, 699), (700, 799), (800, 899), (900, 944)]

private def sieveChunks944 : List (Finset ℕ) :=
  sieveChunksOfBounds sieveBounds944

private lemma factorialSieveCandidates_subset_sieveChunks944 :
    factorialSieveCandidates 944 ⊆ finsetUnionList sieveChunks944 := by
  exact factorialSieveCandidates_subset_sieveChunksOfBounds (bounds := sieveBounds944) <| by
    intro m hm
    simp [sieveBounds944]
    omega

private lemma factorialSieveCandidates_card_le_944 :
    (factorialSieveCandidates 944).card ≤ 150 :=
  factorialSieveCandidates_card_le_of_chunks factorialSieveCandidates_subset_sieveChunks944 <| by
    have h0 := sieveChunk_card_le_0_99
    have h1 := sieveChunk_card_le_100_199
    have h2 := sieveChunk_card_le_200_299
    have h3 := sieveChunk_card_le_300_399
    have h4 := sieveChunk_card_le_400_499
    have h5 := sieveChunk_card_le_500_599
    have h6 := sieveChunk_card_le_600_699
    have h7 := sieveChunk_card_le_700_799
    have h8 := sieveChunk_card_le_800_899
    have h9 := sieveChunk_card_le_900_944
    simp [sieveChunks944, sieveChunksOfBounds, sieveBounds944, finsetCardSum]
    omega

private lemma primeCounting_le_944 : Nat.primeCounting 944 ≤ 160 :=
  (primeCounting_le_small_sieve 944).trans <| by
    have hsmall : smallSievePrimes.card = 10 := by decide
    have hcard := factorialSieveCandidates_card_le_944
    omega

/-! ### Power endpoint certificates -/

/- A small binary-power certificate keeps the following endpoint checks from relying on a
raised exponentiation evaluator threshold. -/
private def pow1291_1 : ℕ := 1291
private def pow1291_2 : ℕ := pow1291_1 * pow1291_1
private def pow1291_4 : ℕ := pow1291_2 * pow1291_2
private def pow1291_8 : ℕ := pow1291_4 * pow1291_4
private def pow1291_16 : ℕ := pow1291_8 * pow1291_8
private def pow1291_32 : ℕ := pow1291_16 * pow1291_16
private def pow1291_64 : ℕ := pow1291_32 * pow1291_32
private def pow1291_128 : ℕ := pow1291_64 * pow1291_64
private def pow1291_256 : ℕ := pow1291_128 * pow1291_128
private def pow1291_512 : ℕ := pow1291_256 * pow1291_256

private lemma pow1291_1_eq : 1291 ^ 1 = pow1291_1 := by
  norm_num [pow1291_1]

private lemma pow1291_2_eq : 1291 ^ 2 = pow1291_2 := by
  norm_num [pow1291_2, pow1291_1]

private lemma pow1291_4_eq : 1291 ^ 4 = pow1291_4 := by
  rw [show 4 = 2 * 2 by norm_num, pow_mul, pow1291_2_eq, pow_two, pow1291_4]

private lemma pow1291_8_eq : 1291 ^ 8 = pow1291_8 := by
  rw [show 8 = 4 * 2 by norm_num, pow_mul, pow1291_4_eq, pow_two, pow1291_8]

private lemma pow1291_16_eq : 1291 ^ 16 = pow1291_16 := by
  rw [show 16 = 8 * 2 by norm_num, pow_mul, pow1291_8_eq, pow_two, pow1291_16]

private lemma pow1291_32_eq : 1291 ^ 32 = pow1291_32 := by
  rw [show 32 = 16 * 2 by norm_num, pow_mul, pow1291_16_eq, pow_two,
    pow1291_32]

private lemma pow1291_64_eq : 1291 ^ 64 = pow1291_64 := by
  rw [show 64 = 32 * 2 by norm_num, pow_mul, pow1291_32_eq, pow_two,
    pow1291_64]

private lemma pow1291_128_eq : 1291 ^ 128 = pow1291_128 := by
  rw [show 128 = 64 * 2 by norm_num, pow_mul, pow1291_64_eq, pow_two,
    pow1291_128]

private lemma pow1291_256_eq : 1291 ^ 256 = pow1291_256 := by
  rw [show 256 = 128 * 2 by norm_num, pow_mul, pow1291_128_eq, pow_two,
    pow1291_256]

private lemma pow1291_512_eq : 1291 ^ 512 = pow1291_512 := by
  rw [show 512 = 256 * 2 by norm_num, pow_mul, pow1291_256_eq, pow_two,
    pow1291_512]

private lemma pow1291_17_eq : 1291 ^ 17 = pow1291_16 * pow1291_1 := by
  rw [show 17 = 16 + 1 by norm_num]
  rw [pow_add]
  rw [pow1291_16_eq, pow1291_1_eq]

private lemma pow1291_39_eq :
    1291 ^ 39 = pow1291_32 * pow1291_4 * pow1291_2 * pow1291_1 := by
  rw [show 39 = 32 + 4 + 2 + 1 by norm_num]
  rw [pow_add, pow_add, pow_add]
  rw [pow1291_32_eq, pow1291_4_eq, pow1291_2_eq, pow1291_1_eq]

private lemma pow1291_95_eq :
    1291 ^ 95 = pow1291_64 * pow1291_16 * pow1291_8 * pow1291_4 *
      pow1291_2 * pow1291_1 := by
  rw [show 95 = 64 + 16 + 8 + 4 + 2 + 1 by norm_num]
  rw [pow_add, pow_add, pow_add, pow_add, pow_add]
  rw [pow1291_64_eq, pow1291_16_eq, pow1291_8_eq, pow1291_4_eq,
    pow1291_2_eq, pow1291_1_eq]

private lemma pow1291_213_eq :
    1291 ^ 213 = pow1291_128 * pow1291_64 * pow1291_16 * pow1291_4 *
      pow1291_1 := by
  rw [show 213 = 128 + 64 + 16 + 4 + 1 by norm_num]
  rw [pow_add, pow_add, pow_add, pow_add]
  rw [pow1291_128_eq, pow1291_64_eq, pow1291_16_eq, pow1291_4_eq,
    pow1291_1_eq]

private lemma pow1291_383_eq :
    1291 ^ 383 = pow1291_256 * pow1291_64 * pow1291_32 * pow1291_16 *
      pow1291_8 * pow1291_4 * pow1291_2 * pow1291_1 := by
  rw [show 383 = 256 + 64 + 32 + 16 + 8 + 4 + 2 + 1 by norm_num]
  rw [pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add]
  rw [pow1291_256_eq, pow1291_64_eq, pow1291_32_eq, pow1291_16_eq,
    pow1291_8_eq, pow1291_4_eq, pow1291_2_eq, pow1291_1_eq]

private lemma pow1291_569_eq :
    1291 ^ 569 = pow1291_512 * pow1291_32 * pow1291_16 * pow1291_8 *
      pow1291_1 := by
  rw [show 569 = 512 + 32 + 16 + 8 + 1 by norm_num]
  rw [pow_add, pow_add, pow_add, pow_add]
  rw [pow1291_512_eq, pow1291_32_eq, pow1291_16_eq, pow1291_8_eq,
    pow1291_1_eq]

private lemma pow1291_700_eq :
    1291 ^ 700 = pow1291_512 * pow1291_128 * pow1291_32 * pow1291_16 *
      pow1291_8 * pow1291_4 := by
  rw [show 700 = 512 + 128 + 32 + 16 + 8 + 4 by norm_num]
  rw [pow_add, pow_add, pow_add, pow_add, pow_add]
  rw [pow1291_512_eq, pow1291_128_eq, pow1291_32_eq, pow1291_16_eq,
    pow1291_8_eq, pow1291_4_eq]

private lemma pow1291_759_eq :
    1291 ^ 759 = pow1291_512 * pow1291_128 * pow1291_64 * pow1291_32 *
      pow1291_16 * pow1291_4 * pow1291_2 * pow1291_1 := by
  rw [show 759 = 512 + 128 + 64 + 32 + 16 + 4 + 2 + 1 by norm_num]
  rw [pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add]
  rw [pow1291_512_eq, pow1291_128_eq, pow1291_64_eq, pow1291_32_eq,
    pow1291_16_eq, pow1291_4_eq, pow1291_2_eq, pow1291_1_eq]

private lemma pow1291_781_eq :
    1291 ^ 781 = pow1291_512 * pow1291_256 * pow1291_8 * pow1291_4 *
      pow1291_1 := by
  rw [show 781 = 512 + 256 + 8 + 4 + 1 by norm_num]
  rw [pow_add, pow_add, pow_add, pow_add]
  rw [pow1291_512_eq, pow1291_256_eq, pow1291_8_eq, pow1291_4_eq,
    pow1291_1_eq]

private lemma second_residual_mid_base_38 :
    Nat.factorial 38 * 26 ^ 21 < 15 ^ 21 * 1291 ^ (38 - 21) := by
  rw [show 38 - 21 = 17 by norm_num, pow1291_17_eq]
  norm_num [Nat.factorial_eq_factorialBinarySplitting, Nat.factorialBinarySplitting,
    pow1291_512, pow1291_256, pow1291_128, pow1291_64, pow1291_32, pow1291_16,
    pow1291_8, pow1291_4, pow1291_2, pow1291_1]

private lemma second_residual_mid_base_76 :
    Nat.factorial 76 * 26 ^ 37 < 15 ^ 37 * 1291 ^ (76 - 37) := by
  rw [show 76 - 37 = 39 by norm_num, pow1291_39_eq]
  norm_num [Nat.factorial_eq_factorialBinarySplitting, Nat.factorialBinarySplitting,
    pow1291_512, pow1291_256, pow1291_128, pow1291_64, pow1291_32, pow1291_16,
    pow1291_8, pow1291_4, pow1291_2, pow1291_1]

private lemma second_residual_mid_base_158 :
    Nat.factorial 158 * 26 ^ 63 < 15 ^ 63 * 1291 ^ (158 - 63) := by
  rw [show 158 - 63 = 95 by norm_num, pow1291_95_eq]
  norm_num [Nat.factorial_eq_factorialBinarySplitting, Nat.factorialBinarySplitting,
    pow1291_512, pow1291_256, pow1291_128, pow1291_64, pow1291_32, pow1291_16,
    pow1291_8, pow1291_4, pow1291_2, pow1291_1]

private lemma second_residual_mid_base_310 :
    Nat.factorial 310 * 26 ^ 97 < 15 ^ 97 * 1291 ^ (310 - 97) := by
  rw [show 310 - 97 = 213 by norm_num, pow1291_213_eq]
  norm_num [Nat.factorial_eq_factorialBinarySplitting, Nat.factorialBinarySplitting,
    pow1291_512, pow1291_256, pow1291_128, pow1291_64, pow1291_32, pow1291_16,
    pow1291_8, pow1291_4, pow1291_2, pow1291_1]

private lemma second_residual_mid_base_510 :
    Nat.factorial 510 * 26 ^ 127 < 15 ^ 127 * 1291 ^ (510 - 127) := by
  rw [show 510 - 127 = 383 by norm_num, pow1291_383_eq]
  norm_num [Nat.factorial_eq_factorialBinarySplitting, Nat.factorialBinarySplitting,
    pow1291_512, pow1291_256, pow1291_128, pow1291_64, pow1291_32, pow1291_16,
    pow1291_8, pow1291_4, pow1291_2, pow1291_1]

private lemma second_residual_mid_base_716 :
    Nat.factorial 716 * 26 ^ 147 < 15 ^ 147 * 1291 ^ (716 - 147) := by
  rw [show 716 - 147 = 569 by norm_num, pow1291_569_eq]
  norm_num [Nat.factorial_eq_factorialBinarySplitting, Nat.factorialBinarySplitting,
    pow1291_512, pow1291_256, pow1291_128, pow1291_64, pow1291_32, pow1291_16,
    pow1291_8, pow1291_4, pow1291_2, pow1291_1]

private lemma second_residual_mid_base_856 :
    Nat.factorial 856 * 26 ^ 156 < 15 ^ 156 * 1291 ^ (856 - 156) := by
  rw [show 856 - 156 = 700 by norm_num, pow1291_700_eq]
  norm_num [Nat.factorial_eq_factorialBinarySplitting, Nat.factorialBinarySplitting,
    pow1291_512, pow1291_256, pow1291_128, pow1291_64, pow1291_32, pow1291_16,
    pow1291_8, pow1291_4, pow1291_2, pow1291_1]

private lemma second_residual_mid_base_918 :
    Nat.factorial 918 * 26 ^ 159 < 15 ^ 159 * 1291 ^ (918 - 159) := by
  rw [show 918 - 159 = 759 by norm_num, pow1291_759_eq]
  norm_num [Nat.factorial_eq_factorialBinarySplitting, Nat.factorialBinarySplitting,
    pow1291_512, pow1291_256, pow1291_128, pow1291_64, pow1291_32, pow1291_16,
    pow1291_8, pow1291_4, pow1291_2, pow1291_1]

private lemma second_residual_mid_base_941 :
    Nat.factorial 941 * 26 ^ 160 < 15 ^ 160 * 1291 ^ (941 - 160) := by
  rw [show 941 - 160 = 781 by norm_num, pow1291_781_eq]
  norm_num [Nat.factorial_eq_factorialBinarySplitting, Nat.factorialBinarySplitting,
    pow1291_512, pow1291_256, pow1291_128, pow1291_64, pow1291_32, pow1291_16,
    pow1291_8, pow1291_4, pow1291_2, pow1291_1]

/-! ### Mid residual estimate -/

private lemma mul_top_pow_lt_start_pow_of_scaled_top_le_start
    {F N k e n a b : ℕ} (he : e ≤ n) (hkpos : 0 < k)
    (htop : b * N ≤ a * k)
    (hconst : F * a ^ e < b ^ e * k ^ (n - e)) :
    F * N ^ e < k ^ n := by
  have htop_pow : b ^ e * N ^ e ≤ a ^ e * k ^ e := by
    simpa [Nat.mul_pow] using Nat.pow_le_pow_left htop e
  have hscaled_le : b ^ e * (F * N ^ e) ≤ F * (a ^ e * k ^ e) := by
    calc
      b ^ e * (F * N ^ e) = F * (b ^ e * N ^ e) := by ring
      _ ≤ F * (a ^ e * k ^ e) := Nat.mul_le_mul_left F htop_pow
  have hscaled_lt : F * (a ^ e * k ^ e) < b ^ e * k ^ n := by
    calc
      F * (a ^ e * k ^ e) = (F * a ^ e) * k ^ e := by ring
      _ < (b ^ e * k ^ (n - e)) * k ^ e :=
        Nat.mul_lt_mul_of_pos_right hconst (pow_pos hkpos e)
      _ = b ^ e * (k ^ (n - e) * k ^ e) := by ring
      _ = b ^ e * k ^ ((n - e) + e) := by rw [pow_add]
      _ = b ^ e * k ^ n := by rw [Nat.sub_add_cancel he]
  exact Nat.lt_of_mul_lt_mul_left (hscaled_le.trans_lt hscaled_lt)

private lemma primeCounting_le_self (n : ℕ) : Nat.primeCounting n ≤ n := by
  rw [Nat.primeCounting, Nat.primeCounting']
  refine (Nat.count_mono_left (n := n + 1) (p := Nat.Prime)
    (q := fun m : ℕ => m ≠ 0) ?_).trans_eq ?_
  · intro k _ hk
    exact hk.ne_zero
  rw [add_comm n 1, Nat.count_add]
  simp [Nat.count_succ]

private lemma factorial_scaled_bound_step {m P : ℕ} (hP : P ≤ m) (hm : m + 1 < 1291)
    (h : Nat.factorial m * 26 ^ P < 15 ^ P * 1291 ^ (m - P)) :
    Nat.factorial (m + 1) * 26 ^ P < 15 ^ P * 1291 ^ (m + 1 - P) := by
  have hmul :
      (m + 1) * (Nat.factorial m * 26 ^ P) <
        1291 * (15 ^ P * 1291 ^ (m - P)) :=
    Nat.mul_lt_mul_of_lt_of_le hm h.le (by positivity)
  calc
    Nat.factorial (m + 1) * 26 ^ P = (m + 1) * (Nat.factorial m * 26 ^ P) := by
      rw [Nat.factorial_succ]
      ring
    _ < 1291 * (15 ^ P * 1291 ^ (m - P)) := hmul
    _ = 15 ^ P * 1291 ^ (m + 1 - P) := by
      have hsub : m + 1 - P = (m - P) + 1 := by omega
      rw [hsub, pow_add]
      ring

private lemma factorial_scaled_bound_of_le {lo n P : ℕ} (hlo : lo ≤ n) (hn : n < 1291)
    (hP : P ≤ lo)
    (hbase : Nat.factorial lo * 26 ^ P < 15 ^ P * 1291 ^ (lo - P)) :
    Nat.factorial n * 26 ^ P < 15 ^ P * 1291 ^ (n - P) := by
  induction n, hlo using Nat.le_induction with
  | base => exact hbase
  | succ m hm ih =>
      exact factorial_scaled_bound_step (hP.trans hm) (by omega) (ih (by omega))

private lemma scaled_pow_le_of_le {e P n k : ℕ} (heP : e ≤ P) (hPn : P ≤ n)
    (hk15 : 15 ≤ k) :
    15 ^ P * k ^ (n - P) ≤ 15 ^ e * k ^ (n - e) := by
  have hpow : 15 ^ (P - e) ≤ k ^ (P - e) := Nat.pow_le_pow_left hk15 _
  calc
    15 ^ P * k ^ (n - P) = 15 ^ e * (15 ^ (P - e) * k ^ (n - P)) := by
      nth_rewrite 1 [show P = e + (P - e) by omega]
      rw [pow_add]
      ring
    _ ≤ 15 ^ e * (k ^ (P - e) * k ^ (n - P)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hpow)
    _ = 15 ^ e * k ^ ((P - e) + (n - P)) := by rw [pow_add]
    _ = 15 ^ e * k ^ (n - e) := by
      congr 2
      omega

private lemma factorial_mul_scaled_primeCounting_lt_of_segment {lo n P k : ℕ}
    (hlo : lo ≤ n) (hn : n < 1291) (hPlo : P ≤ lo) (hpi : Nat.primeCounting n ≤ P)
    (hbase : Nat.factorial lo * 26 ^ P < 15 ^ P * 1291 ^ (lo - P))
    (hk : 1291 ≤ k) :
    Nat.factorial n * 26 ^ Nat.primeCounting n <
      15 ^ Nat.primeCounting n * k ^ (n - Nat.primeCounting n) := by
  have hfixed1291 := factorial_scaled_bound_of_le hlo hn hPlo hbase
  have hfixedk :
      Nat.factorial n * 26 ^ P < 15 ^ P * k ^ (n - P) :=
    hfixed1291.trans_le (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hk _))
  have hlhs :
      Nat.factorial n * 26 ^ Nat.primeCounting n ≤ Nat.factorial n * 26 ^ P :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num : 0 < 26) hpi)
  have hrhs :
      15 ^ P * k ^ (n - P) ≤
        15 ^ Nat.primeCounting n * k ^ (n - Nat.primeCounting n) :=
    scaled_pow_le_of_le hpi (hPlo.trans hlo) (by omega)
  exact hlhs.trans_lt (hfixedk.trans_le hrhs)

/-- The mid residual range `38 ≤ n < 945` satisfies the prime-counting conditional
estimate once `1291 ≤ k`, using the finite certificates in this file. -/
lemma second_residual_mid_primeCounting_lt_start_pow {n k : ℕ}
    (hn38 : 38 ≤ n) (hnlt945 : n < 945) (hk1291 : 1291 ≤ k) :
    Nat.factorial n * (k + n - 1) ^ Nat.primeCounting n < k ^ n := by
  have hkpos : 0 < k := by omega
  have htop : 15 * (k + n - 1) ≤ 26 * k := by omega
  apply mul_top_pow_lt_start_pow_of_scaled_top_le_start (a := 26) (b := 15)
  · exact primeCounting_le_self _
  · exact hkpos
  · exact htop
  · by_cases hn75 : n ≤ 75
    · have hpi := (Nat.monotone_primeCounting hn75).trans primeCounting_le_75
      exact factorial_mul_scaled_primeCounting_lt_of_segment hn38 (by omega) (by norm_num)
        hpi second_residual_mid_base_38 hk1291
    by_cases hn157 : n ≤ 157
    · have hpi := (Nat.monotone_primeCounting hn157).trans primeCounting_le_157
      exact factorial_mul_scaled_primeCounting_lt_of_segment (by omega : 76 ≤ n)
        (by omega) (by norm_num) hpi second_residual_mid_base_76 hk1291
    by_cases hn309 : n ≤ 309
    · have hpi := (Nat.monotone_primeCounting hn309).trans primeCounting_le_309
      exact factorial_mul_scaled_primeCounting_lt_of_segment (by omega : 158 ≤ n)
        (by omega) (by norm_num) hpi second_residual_mid_base_158 hk1291
    by_cases hn509 : n ≤ 509
    · have hpi := (Nat.monotone_primeCounting hn509).trans primeCounting_le_509
      exact factorial_mul_scaled_primeCounting_lt_of_segment (by omega : 310 ≤ n)
        (by omega) (by norm_num) hpi second_residual_mid_base_310 hk1291
    by_cases hn715 : n ≤ 715
    · have hpi := (Nat.monotone_primeCounting hn715).trans primeCounting_le_715
      exact factorial_mul_scaled_primeCounting_lt_of_segment (by omega : 510 ≤ n)
        (by omega) (by norm_num) hpi second_residual_mid_base_510 hk1291
    by_cases hn855 : n ≤ 855
    · have hpi := (Nat.monotone_primeCounting hn855).trans primeCounting_le_855
      exact factorial_mul_scaled_primeCounting_lt_of_segment (by omega : 716 ≤ n)
        (by omega) (by norm_num) hpi second_residual_mid_base_716 hk1291
    by_cases hn917 : n ≤ 917
    · have hpi := (Nat.monotone_primeCounting hn917).trans primeCounting_le_917
      exact factorial_mul_scaled_primeCounting_lt_of_segment (by omega : 856 ≤ n)
        (by omega) (by norm_num) hpi second_residual_mid_base_856 hk1291
    by_cases hn940 : n ≤ 940
    · have hpi := (Nat.monotone_primeCounting hn940).trans primeCounting_le_940
      exact factorial_mul_scaled_primeCounting_lt_of_segment (by omega : 918 ≤ n)
        (by omega) (by norm_num) hpi second_residual_mid_base_918 hk1291
    have hn944 : n ≤ 944 := by omega
    have hpi := (Nat.monotone_primeCounting hn944).trans primeCounting_le_944
    exact factorial_mul_scaled_primeCounting_lt_of_segment (by omega : 941 ≤ n)
      (by omega) (by norm_num) hpi second_residual_mid_base_941 hk1291

end Internal
end Nat.SylvesterSchur
