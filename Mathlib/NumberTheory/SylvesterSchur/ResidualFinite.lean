/-
Copyright (c) 2026 Meta Platforms, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.NumberTheory.SylvesterSchur.BlockReductions

/-!
# Finite residual checks for the Sylvester-Schur theorem

This file contains the finite residual checks used by the Sylvester-Schur proof.
-/

@[expose] public section

namespace Nat.SylvesterSchur
namespace Internal

open Finset Nat

private lemma three_mul_choose_two_mul_add_le_two_mul_choose_succ
    {n i : ℕ} (hi : i + 1 ≤ n) :
    3 * Nat.choose (2 * n + i) n ≤ 2 * Nat.choose (2 * n + i + 1) n := by
  have hchoose :
      Nat.choose (2 * n + i + 1) n * (n + i + 1) =
        Nat.choose (2 * n + i) n * (2 * n + i + 1) := by
    have h := (Nat.choose_mul_succ_eq (2 * n + i) n).symm
    have h1 : 2 * n + i + 1 - n = n + i + 1 := by omega
    simpa [h1] using h
  apply Nat.le_of_mul_le_mul_right _ (by omega : 0 < n + i + 1)
  calc
    (3 * Nat.choose (2 * n + i) n) * (n + i + 1)
        = Nat.choose (2 * n + i) n * (3 * (n + i + 1)) := by ring
    _ ≤ Nat.choose (2 * n + i) n * (2 * (2 * n + i + 1)) := by
        apply Nat.mul_le_mul_left
        omega
    _ = 2 * (Nat.choose (2 * n + i) n * (2 * n + i + 1)) := by ring
    _ = 2 * (Nat.choose (2 * n + i + 1) n * (n + i + 1)) := by
        rw [← hchoose]
    _ = (2 * Nat.choose (2 * n + i + 1) n) * (n + i + 1) := by ring

private lemma three_pow_mul_centralBinom_le_two_pow_mul_choose_two_mul_add
    {n i : ℕ} (hi : i ≤ n) :
    3 ^ i * Nat.centralBinom n ≤ 2 ^ i * Nat.choose (2 * n + i) n := by
  induction i with
  | zero =>
      simp [Nat.centralBinom, two_mul]
  | succ i ih =>
      have hi' : i ≤ n := by omega
      have hstep := ih hi'
      have hratio :
          3 * Nat.choose (2 * n + i) n ≤
            2 * Nat.choose (2 * n + i + 1) n :=
        three_mul_choose_two_mul_add_le_two_mul_choose_succ hi
      calc
        3 ^ (i + 1) * Nat.centralBinom n
            = 3 * (3 ^ i * Nat.centralBinom n) := by ring
        _ ≤ 3 * (2 ^ i * Nat.choose (2 * n + i) n) :=
          Nat.mul_le_mul_left 3 hstep
        _ = 2 ^ i * (3 * Nat.choose (2 * n + i) n) := by ring
        _ ≤ 2 ^ i * (2 * Nat.choose (2 * n + i + 1) n) :=
          Nat.mul_le_mul_left _ hratio
        _ = 2 ^ (i + 1) * Nat.choose (2 * n + (i + 1)) n := by ring_nf

private lemma three_pow_mul_centralBinom_le_two_pow_mul_choose_three_mul (n : ℕ) :
    3 ^ n * Nat.centralBinom n ≤ 2 ^ n * Nat.choose (3 * n) n := by
  convert
    three_pow_mul_centralBinom_le_two_pow_mul_choose_two_mul_add (n := n) (i := n) le_rfl
    using 1
  · ring_nf

private lemma three_pow_mul_four_pow_lt_mul_two_pow_mul_choose_three_mul
    {n : ℕ} (hn : 4 ≤ n) :
    3 ^ n * 4 ^ n < n * (2 ^ n * Nat.choose (3 * n) n) := by
  have hcentral : 4 ^ n < n * Nat.centralBinom n :=
    Nat.four_pow_lt_mul_centralBinom n hn
  have hmul : 3 ^ n * 4 ^ n < 3 ^ n * (n * Nat.centralBinom n) :=
    (Nat.mul_lt_mul_left (pow_pos (by norm_num : 0 < 3) n)).mpr hcentral
  have hupper :
      3 ^ n * (n * Nat.centralBinom n) ≤ n * (2 ^ n * Nat.choose (3 * n) n) := by
    calc
      3 ^ n * (n * Nat.centralBinom n)
          = n * (3 ^ n * Nat.centralBinom n) := by ring
      _ ≤ n * (2 ^ n * Nat.choose (3 * n) n) :=
        Nat.mul_le_mul_left n (three_pow_mul_centralBinom_le_two_pow_mul_choose_three_mul n)
  exact hmul.trans_le hupper

/-- In the first residual range, the scaled ternary lower bound contradicts the
three-layer Erdős upper bound unless `Nat.choose N r` has a prime divisor above `r`. -/
lemma exists_prime_dvd_choose_of_scaled_ternary_erdos_layers_bound {N r : ℕ}
    (hr : 4 ≤ r) (hrN : 3 * r ≤ N)
    (hbound :
      r * (2 ^ r * ((3 * r) ^ r *
        4 ^ (r + Nat.sqrt N + Nat.nthRoot 3 N * Nat.log 2 N))) <
        3 ^ r * 4 ^ r * N ^ r) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  apply exists_large_prime_dvd_choose_of_not_forall_prime_dvd_le
  intro hsmall
  have hchoose_upper :
      Nat.choose N r ≤
        4 ^ (r + Nat.sqrt N + Nat.nthRoot 3 N * Nat.log 2 N) := by
    exact (choose_le_prod_erdos_layers_of_no_large (by omega) (by omega) hsmall).trans
      (erdos_layers_le_four_pow_three_layers N r)
  have hchoose_scaled :
      N ^ r * Nat.choose (3 * r) r ≤ (3 * r) ^ r * Nat.choose N r :=
    pow_mul_choose_le_pow_mul_choose (M := 3 * r) (N := N) (r := r)
      (by omega) hrN
  have hcentral :
      3 ^ r * 4 ^ r < r * (2 ^ r * Nat.choose (3 * r) r) :=
    three_pow_mul_four_pow_lt_mul_two_pow_mul_choose_three_mul hr
  have hcentral_scaled :
      3 ^ r * 4 ^ r * N ^ r <
        r * (2 ^ r * (N ^ r * Nat.choose (3 * r) r)) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      Nat.mul_lt_mul_of_pos_right hcentral (pow_pos (by omega : 0 < N) r)
  have hupper_scaled :
      r * (2 ^ r * (N ^ r * Nat.choose (3 * r) r)) ≤
        r * (2 ^ r * ((3 * r) ^ r *
          4 ^ (r + Nat.sqrt N + Nat.nthRoot 3 N * Nat.log 2 N))) := by
    exact Nat.mul_le_mul_left r <| Nat.mul_le_mul_left (2 ^ r) <|
      hchoose_scaled.trans <| Nat.mul_le_mul_left ((3 * r) ^ r) hchoose_upper
  exact (not_lt_of_ge (le_of_lt (hcentral_scaled.trans_le hupper_scaled))) hbound

/-- In the central residual range, the offset central-binomial lower bound contradicts
the `N / 3` first-layer estimate unless a large prime divides `Nat.choose N r`. -/
lemma exists_prime_dvd_choose_of_central_offset_erdos_div_three_layers_bound
    {N r i : ℕ} (hr : 4 ≤ r) (hi : i ≤ r) (hN : N = 2 * r + i) (hN6 : 6 ≤ N)
    (hbound :
      r * (2 ^ i *
        (∏ j ∈ Finset.range (Nat.log 2 N),
          if j = 0 then primorial (N / 3) else primorial (Nat.nthRoot (j + 1) N))) <
        3 ^ i * 4 ^ r) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  apply exists_large_prime_dvd_choose_of_not_forall_prime_dvd_le
  intro hsmall
  have hchoose_upper :
      Nat.choose N r ≤
        ∏ j ∈ Finset.range (Nat.log 2 N),
          if j = 0 then primorial (N / 3) else primorial (Nat.nthRoot (j + 1) N) := by
    exact choose_le_prod_erdos_div_three_layers_of_no_large (by omega) (by omega)
      (by omega) hN6 hsmall
  have hcentral : 4 ^ r < r * Nat.centralBinom r :=
    Nat.four_pow_lt_mul_centralBinom r hr
  have hoffset :
      3 ^ i * Nat.centralBinom r ≤ 2 ^ i * Nat.choose N r := by
    have h :=
      three_pow_mul_centralBinom_le_two_pow_mul_choose_two_mul_add (n := r) (i := i) hi
    simpa [hN] using h
  have hlower :
      3 ^ i * 4 ^ r < r * (2 ^ i * Nat.choose N r) := by
    calc
      3 ^ i * 4 ^ r
          < 3 ^ i * (r * Nat.centralBinom r) :=
            (Nat.mul_lt_mul_left (pow_pos (by norm_num : 0 < 3) i)).mpr hcentral
      _ = r * (3 ^ i * Nat.centralBinom r) := by ring
      _ ≤ r * (2 ^ i * Nat.choose N r) :=
            Nat.mul_le_mul_left r hoffset
  have hupper_mul :
      r * (2 ^ i * Nat.choose N r) ≤
        r * (2 ^ i *
          (∏ j ∈ Finset.range (Nat.log 2 N),
            if j = 0 then primorial (N / 3) else primorial (Nat.nthRoot (j + 1) N))) :=
    Nat.mul_le_mul_left r (Nat.mul_le_mul_left (2 ^ i) hchoose_upper)
  exact (not_lt_of_ge (le_of_lt (hlower.trans_le hupper_mul))) hbound

/-- Small central-offset cases for `Nat.choose (2 * n + 2) n`, handled by an
explicit short prime-gap certificate. -/
lemma exists_prime_dvd_choose_two_mul_add_two_small {n : ℕ} (hn7 : 7 ≤ n)
    (hnlt : n < 512) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (2 * n + 2) n := by
  have hchoose : ∀ p : ℕ, p.Prime → n + 3 ≤ p → p ≤ 2 * n + 2 →
      p ∣ Nat.choose (2 * n + 2) n := by
    intro p hp hp_low hp_high
    have hd : p ∣ Nat.choose (n + (n + 2)) n :=
      hp.dvd_choose_add (by omega) (by omega) (by omega)
    rwa [show n + (n + 2) = 2 * n + 2 by omega] at hd
  by_cases hn11 : n < 11
  · exact ⟨13, by norm_num, by omega, hchoose 13 (by norm_num) (by omega) (by omega)⟩
  by_cases hn21 : n < 21
  · exact ⟨23, by norm_num, by omega, hchoose 23 (by norm_num) (by omega) (by omega)⟩
  by_cases hn35 : n < 35
  · exact ⟨37, by norm_num, by omega, hchoose 37 (by norm_num) (by omega) (by omega)⟩
  by_cases hn69 : n < 69
  · exact ⟨71, by norm_num, by omega, hchoose 71 (by norm_num) (by omega) (by omega)⟩
  by_cases hn135 : n < 135
  · exact ⟨137, by norm_num, by omega, hchoose 137 (by norm_num) (by omega) (by omega)⟩
  by_cases hn261 : n < 261
  · exact ⟨263, by norm_num, by omega, hchoose 263 (by norm_num) (by omega) (by omega)⟩
  exact ⟨521, by norm_num, by omega, hchoose 521 (by norm_num) (by omega) (by omega)⟩

private lemma exists_large_prime_factor_in_block_of_prime_near {n k p g : ℕ}
    (hg : g < n) (hklo : n + 3 ≤ k) (hp : p.Prime) (hkp : k ≤ p)
    (hp_le : p ≤ k + g) :
    ∃ i < n, ∃ q : ℕ, q.Prime ∧ n < q ∧ q ∣ k + i := by
  refine ⟨p - k, by omega, p, hp, by omega, ?_⟩
  have hsum : k + (p - k) = p := by omega
  rw [hsum]

private lemma exists_prime_near_seven_of_ge_ten_lt_100 {k : ℕ}
    (hk10 : 10 ≤ k) (hklt : k < 100) :
    ∃ p : ℕ, p.Prime ∧ k ≤ p ∧ p ≤ k + 7 := by
  by_cases hk17 : k ≤ 17
  · exact ⟨17, by norm_num, by omega, by omega⟩
  by_cases hk23 : k ≤ 23
  · exact ⟨23, by norm_num, by omega, by omega⟩
  by_cases hk31 : k ≤ 31
  · exact ⟨31, by norm_num, by omega, by omega⟩
  by_cases hk37 : k ≤ 37
  · exact ⟨37, by norm_num, by omega, by omega⟩
  by_cases hk43 : k ≤ 43
  · exact ⟨43, by norm_num, by omega, by omega⟩
  by_cases hk47 : k ≤ 47
  · exact ⟨47, by norm_num, by omega, by omega⟩
  by_cases hk53 : k ≤ 53
  · exact ⟨53, by norm_num, by omega, by omega⟩
  by_cases hk61 : k ≤ 61
  · exact ⟨61, by norm_num, by omega, by omega⟩
  by_cases hk67 : k ≤ 67
  · exact ⟨67, by norm_num, by omega, by omega⟩
  by_cases hk73 : k ≤ 73
  · exact ⟨73, by norm_num, by omega, by omega⟩
  by_cases hk79 : k ≤ 79
  · exact ⟨79, by norm_num, by omega, by omega⟩
  by_cases hk83 : k ≤ 83
  · exact ⟨83, by norm_num, by omega, by omega⟩
  by_cases hk89 : k ≤ 89
  · exact ⟨89, by norm_num, by omega, by omega⟩
  by_cases hk97 : k ≤ 97
  · exact ⟨97, by norm_num, by omega, by omega⟩
  exact ⟨103, by norm_num, by omega, by omega⟩

private lemma exists_prime_near_six_low {k : ℕ} (hk10 : 10 ≤ k) (hk53 : k ≤ 53) :
    ∃ p : ℕ, p.Prime ∧ k ≤ p ∧ p ≤ k + 6 := by
  by_cases hk13 : k ≤ 13
  · exact ⟨13, by norm_num, by omega, by omega⟩
  by_cases hk19 : k ≤ 19
  · exact ⟨19, by norm_num, by omega, by omega⟩
  by_cases hk23 : k ≤ 23
  · exact ⟨23, by norm_num, by omega, by omega⟩
  by_cases hk29 : k ≤ 29
  · exact ⟨29, by norm_num, by omega, by omega⟩
  by_cases hk31 : k ≤ 31
  · exact ⟨31, by norm_num, by omega, by omega⟩
  by_cases hk37 : k ≤ 37
  · exact ⟨37, by norm_num, by omega, by omega⟩
  by_cases hk43 : k ≤ 43
  · exact ⟨43, by norm_num, by omega, by omega⟩
  by_cases hk47 : k ≤ 47
  · exact ⟨47, by norm_num, by omega, by omega⟩
  by_cases hk53 : k ≤ 53
  · exact ⟨53, by norm_num, by omega, by omega⟩
  omega

private lemma exists_prime_near_six_high {k : ℕ}
    (hk54 : 54 ≤ k) (hklt : k < 100) (hk90 : k ≠ 90) :
    ∃ p : ℕ, p.Prime ∧ k ≤ p ∧ p ≤ k + 6 := by
  by_cases hk59 : k ≤ 59
  · exact ⟨59, by norm_num, by omega, by omega⟩
  by_cases hk61 : k ≤ 61
  · exact ⟨61, by norm_num, by omega, by omega⟩
  by_cases hk67 : k ≤ 67
  · exact ⟨67, by norm_num, by omega, by omega⟩
  by_cases hk73 : k ≤ 73
  · exact ⟨73, by norm_num, by omega, by omega⟩
  by_cases hk79 : k ≤ 79
  · exact ⟨79, by norm_num, by omega, by omega⟩
  by_cases hk83 : k ≤ 83
  · exact ⟨83, by norm_num, by omega, by omega⟩
  by_cases hk89 : k ≤ 89
  · exact ⟨89, by norm_num, by omega, by omega⟩
  by_cases hk97 : k ≤ 97
  · exact ⟨97, by norm_num, by omega, by omega⟩
  exact ⟨101, by norm_num, by omega, by omega⟩

private lemma exists_prime_near_six_of_ge_ten_lt_100_ne_ninety {k : ℕ}
    (hk10 : 10 ≤ k) (hklt : k < 100) (hk90 : k ≠ 90) :
    ∃ p : ℕ, p.Prime ∧ k ≤ p ∧ p ≤ k + 6 := by
  by_cases hk53 : k ≤ 53
  · exact exists_prime_near_six_low hk10 hk53
  exact exists_prime_near_six_high (by omega) hklt hk90

private lemma exists_prime_near_mid_range_low {k : ℕ}
    (hk41 : 41 ≤ k) (hk331 : k ≤ 331) :
    ∃ p : ℕ, p.Prime ∧ k ≤ p ∧ p ≤ k + 21 := by
  by_cases hk61 : k ≤ 61
  · exact ⟨61, by norm_num, by omega, by omega⟩
  by_cases hk83 : k ≤ 83
  · exact ⟨83, by norm_num, by omega, by omega⟩
  by_cases hk103 : k ≤ 103
  · exact ⟨103, by norm_num, by omega, by omega⟩
  by_cases hk113 : k ≤ 113
  · exact ⟨113, by norm_num, by omega, by omega⟩
  by_cases hk131 : k ≤ 131
  · exact ⟨131, by norm_num, by omega, by omega⟩
  by_cases hk151 : k ≤ 151
  · exact ⟨151, by norm_num, by omega, by omega⟩
  by_cases hk173 : k ≤ 173
  · exact ⟨173, by norm_num, by omega, by omega⟩
  by_cases hk193 : k ≤ 193
  · exact ⟨193, by norm_num, by omega, by omega⟩
  by_cases hk211 : k ≤ 211
  · exact ⟨211, by norm_num, by omega, by omega⟩
  by_cases hk233 : k ≤ 233
  · exact ⟨233, by norm_num, by omega, by omega⟩
  by_cases hk251 : k ≤ 251
  · exact ⟨251, by norm_num, by omega, by omega⟩
  by_cases hk271 : k ≤ 271
  · exact ⟨271, by norm_num, by omega, by omega⟩
  by_cases hk293 : k ≤ 293
  · exact ⟨293, by norm_num, by omega, by omega⟩
  by_cases hk313 : k ≤ 313
  · exact ⟨313, by norm_num, by omega, by omega⟩
  exact ⟨331, by norm_num, by omega, by omega⟩

private lemma exists_prime_near_mid_range_middle {k : ℕ}
    (hk332 : 332 ≤ k) (hk641 : k ≤ 641) :
    ∃ p : ℕ, p.Prime ∧ k ≤ p ∧ p ≤ k + 21 := by
  by_cases hk353 : k ≤ 353
  · exact ⟨353, by norm_num, by omega, by omega⟩
  by_cases hk373 : k ≤ 373
  · exact ⟨373, by norm_num, by omega, by omega⟩
  by_cases hk389 : k ≤ 389
  · exact ⟨389, by norm_num, by omega, by omega⟩
  by_cases hk409 : k ≤ 409
  · exact ⟨409, by norm_num, by omega, by omega⟩
  by_cases hk431 : k ≤ 431
  · exact ⟨431, by norm_num, by omega, by omega⟩
  by_cases hk449 : k ≤ 449
  · exact ⟨449, by norm_num, by omega, by omega⟩
  by_cases hk467 : k ≤ 467
  · exact ⟨467, by norm_num, by omega, by omega⟩
  by_cases hk487 : k ≤ 487
  · exact ⟨487, by norm_num, by omega, by omega⟩
  by_cases hk509 : k ≤ 509
  · exact ⟨509, by norm_num, by omega, by omega⟩
  by_cases hk523 : k ≤ 523
  · exact ⟨523, by norm_num, by omega, by omega⟩
  by_cases hk541 : k ≤ 541
  · exact ⟨541, by norm_num, by omega, by omega⟩
  by_cases hk563 : k ≤ 563
  · exact ⟨563, by norm_num, by omega, by omega⟩
  by_cases hk577 : k ≤ 577
  · exact ⟨577, by norm_num, by omega, by omega⟩
  by_cases hk599 : k ≤ 599
  · exact ⟨599, by norm_num, by omega, by omega⟩
  by_cases hk619 : k ≤ 619
  · exact ⟨619, by norm_num, by omega, by omega⟩
  exact ⟨641, by norm_num, by omega, by omega⟩

private lemma exists_prime_near_mid_range_high_low {k : ℕ}
    (hk642 : 642 ≤ k) (hk809 : k ≤ 809) :
    ∃ p : ℕ, p.Prime ∧ k ≤ p ∧ p ≤ k + 21 := by
  by_cases hk661 : k ≤ 661
  · exact ⟨661, by norm_num, by omega, by omega⟩
  by_cases hk683 : k ≤ 683
  · exact ⟨683, by norm_num, by omega, by omega⟩
  by_cases hk701 : k ≤ 701
  · exact ⟨701, by norm_num, by omega, by omega⟩
  by_cases hk719 : k ≤ 719
  · exact ⟨719, by norm_num, by omega, by omega⟩
  by_cases hk739 : k ≤ 739
  · exact ⟨739, by norm_num, by omega, by omega⟩
  by_cases hk761 : k ≤ 761
  · exact ⟨761, by norm_num, by omega, by omega⟩
  by_cases hk773 : k ≤ 773
  · exact ⟨773, by norm_num, by omega, by omega⟩
  by_cases hk787 : k ≤ 787
  · exact ⟨787, by norm_num, by omega, by omega⟩
  by_cases hk809 : k ≤ 809
  · exact ⟨809, by norm_num, by omega, by omega⟩
  omega

private lemma exists_prime_near_mid_range_high_top {k : ℕ}
    (hk810 : 810 ≤ k) (hk997 : k ≤ 997) :
    ∃ p : ℕ, p.Prime ∧ k ≤ p ∧ p ≤ k + 21 := by
  by_cases hk829 : k ≤ 829
  · exact ⟨829, by norm_num, by omega, by omega⟩
  by_cases hk839 : k ≤ 839
  · exact ⟨839, by norm_num, by omega, by omega⟩
  by_cases hk859 : k ≤ 859
  · exact ⟨859, by norm_num, by omega, by omega⟩
  by_cases hk881 : k ≤ 881
  · exact ⟨881, by norm_num, by omega, by omega⟩
  by_cases hk887 : k ≤ 887
  · exact ⟨887, by norm_num, by omega, by omega⟩
  by_cases hk907 : k ≤ 907
  · exact ⟨907, by norm_num, by omega, by omega⟩
  by_cases hk929 : k ≤ 929
  · exact ⟨929, by norm_num, by omega, by omega⟩
  by_cases hk947 : k ≤ 947
  · exact ⟨947, by norm_num, by omega, by omega⟩
  by_cases hk967 : k ≤ 967
  · exact ⟨967, by norm_num, by omega, by omega⟩
  by_cases hk983 : k ≤ 983
  · exact ⟨983, by norm_num, by omega, by omega⟩
  exact ⟨997, by norm_num, by omega, by omega⟩

private lemma exists_prime_near_mid_range_high {k : ℕ}
    (hk642 : 642 ≤ k) (hk997 : k ≤ 997) :
    ∃ p : ℕ, p.Prime ∧ k ≤ p ∧ p ≤ k + 21 := by
  by_cases hk809 : k ≤ 809
  · exact exists_prime_near_mid_range_high_low hk642 hk809
  exact exists_prime_near_mid_range_high_top (by omega) hk997

private lemma exists_prime_near_mid_range_top {k : ℕ}
    (hk998 : 998 ≤ k) (hklt : k < 1291) :
    ∃ p : ℕ, p.Prime ∧ k ≤ p ∧ p ≤ k + 21 := by
  by_cases hk1019 : k ≤ 1019
  · exact ⟨1019, by norm_num, by omega, by omega⟩
  by_cases hk1039 : k ≤ 1039
  · exact ⟨1039, by norm_num, by omega, by omega⟩
  by_cases hk1061 : k ≤ 1061
  · exact ⟨1061, by norm_num, by omega, by omega⟩
  by_cases hk1069 : k ≤ 1069
  · exact ⟨1069, by norm_num, by omega, by omega⟩
  by_cases hk1091 : k ≤ 1091
  · exact ⟨1091, by norm_num, by omega, by omega⟩
  by_cases hk1109 : k ≤ 1109
  · exact ⟨1109, by norm_num, by omega, by omega⟩
  by_cases hk1129 : k ≤ 1129
  · exact ⟨1129, by norm_num, by omega, by omega⟩
  by_cases hk1151 : k ≤ 1151
  · exact ⟨1151, by norm_num, by omega, by omega⟩
  by_cases hk1171 : k ≤ 1171
  · exact ⟨1171, by norm_num, by omega, by omega⟩
  by_cases hk1193 : k ≤ 1193
  · exact ⟨1193, by norm_num, by omega, by omega⟩
  by_cases hk1213 : k ≤ 1213
  · exact ⟨1213, by norm_num, by omega, by omega⟩
  by_cases hk1231 : k ≤ 1231
  · exact ⟨1231, by norm_num, by omega, by omega⟩
  by_cases hk1249 : k ≤ 1249
  · exact ⟨1249, by norm_num, by omega, by omega⟩
  by_cases hk1259 : k ≤ 1259
  · exact ⟨1259, by norm_num, by omega, by omega⟩
  by_cases hk1279 : k ≤ 1279
  · exact ⟨1279, by norm_num, by omega, by omega⟩
  exact ⟨1301, by norm_num, by omega, by omega⟩

/- A prime-gap certificate for the mid residual range.

For every `41 ≤ k < 1291`, one of the displayed primes lies in `[k, k + 21]`.
Since the mid residual has block length at least `38`, this prime is one of the
  terms in the block. -/
private lemma exists_prime_near_of_ge_forty_one_lt_1291 {k : ℕ}
    (hk41 : 41 ≤ k) (hklt : k < 1291) :
    ∃ p : ℕ, p.Prime ∧ k ≤ p ∧ p ≤ k + 21 := by
  by_cases hk331 : k ≤ 331
  · exact exists_prime_near_mid_range_low hk41 hk331
  by_cases hk641 : k ≤ 641
  · exact exists_prime_near_mid_range_middle (by omega) hk641
  by_cases hk997 : k ≤ 997
  · exact exists_prime_near_mid_range_high (by omega) hk997
  exact exists_prime_near_mid_range_top (by omega) hklt

/-- For `7 ≤ n < 38` and `k < 100`, a small prime-gap table supplies a block term
with a prime divisor greater than `n`. -/
lemma second_residual_tiny_has_large_prime_factor {n k : ℕ}
    (hn7 : 7 ≤ n) (hnlt : n < 38) (hklo : n + 3 ≤ k) (hklt : k < 100) :
    ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i := by
  by_cases hn8 : 8 ≤ n
  · obtain ⟨p, hp, hkp, hp_le⟩ :=
      exists_prime_near_seven_of_ge_ten_lt_100 (by omega) hklt
    exact exists_large_prime_factor_in_block_of_prime_near (by omega) hklo hp hkp hp_le
  have hn_eq : n = 7 := by omega
  subst n
  by_cases hk90 : k = 90
  · subst k
    exact ⟨4, by norm_num, 47, by norm_num, by norm_num, by norm_num⟩
  obtain ⟨p, hp, hkp, hp_le⟩ :=
    exists_prime_near_six_of_ge_ten_lt_100_ne_ninety (by omega) hklt hk90
  exact exists_large_prime_factor_in_block_of_prime_near (by omega) hklo hp hkp hp_le

/-- For `38 ≤ n < 945` and `k < 1291`, a prime-gap table supplies a block term
with a prime divisor greater than `n`. -/
lemma second_residual_mid_has_large_prime_factor {n k : ℕ}
    (hn38 : 38 ≤ n) (hnlt : n < 945) (hklo : n + 3 ≤ k) (hklt : k < 1291) :
    ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i := by
  obtain ⟨p, hp, hkp, hp_le⟩ :=
    exists_prime_near_of_ge_forty_one_lt_1291 (by omega) hklt
  exact exists_large_prime_factor_in_block_of_prime_near (by omega) hklo hp hkp hp_le


end Internal
end Nat.SylvesterSchur
