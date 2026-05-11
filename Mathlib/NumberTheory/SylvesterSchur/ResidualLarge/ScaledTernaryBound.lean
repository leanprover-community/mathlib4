/-
Copyright (c) 2026 Meta Platforms, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/
module

public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.NumberTheory.SylvesterSchur.ResidualLarge.PowerBounds

import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scaled ternary bound for the Sylvester-Schur large residual estimate

This file dispatches the range `3 * n ≤ N ≤ n ^ 2 + n` from root-log estimates and
base-exponent bounds.

## Main statements

* `first_residual_large_scaled_ternary_bound`: the large residual estimate used when
  `3 * n ≤ N ≤ n ^ 2 + n`.
* `sqrt_le_div_fifteen_of_le_four_mul` and
  `nthRoot_three_mul_log_le_one_fifth_of_le_four_mul`: reusable estimates for the central
  range `N ≤ 4 * n`.

## Implementation notes

The proof follows the same large/small split pattern as Mathlib's proof of Bertrand's postulate:
first reduce the product estimate to an exponent inequality, then cover the remaining range by
explicit monotone estimates.  The interval split
`[3, 4]`, `(4, 8]`, `(8, 16]`, `(16, 64]`, `(64, 512]`, and `(512, n + 1]`
controls the size of `N / n`.  The apparently arbitrary numerical cutoffs in the private
`Nat.nthRoot 3` lemmas are local certificates for bounding
`Nat.nthRoot 3 N * Nat.log 2 N`; they are kept private because they are proof data, not public
API.
-/

@[expose] public section

namespace Nat.SylvesterSchur
namespace Internal

/-! ### Algebraic reductions -/

private lemma four_pow_eq_two_pow_two_mul (n : ℕ) : 4 ^ n = 2 ^ (2 * n) := by
  rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul]

private lemma scaled_ternary_bound_of_cancelled {n N A : ℕ}
    (h : n * (2 ^ n * (n ^ n * 4 ^ A)) < N ^ n) :
    n * (2 ^ n * ((3 * n) ^ n * 4 ^ (n + A))) <
      3 ^ n * 4 ^ n * N ^ n := by
  have hpos : 0 < 3 ^ n * 4 ^ n := by positivity
  calc
    n * (2 ^ n * ((3 * n) ^ n * 4 ^ (n + A)))
        = 3 ^ n * 4 ^ n * (n * (2 ^ n * (n ^ n * 4 ^ A))) := by
          rw [Nat.mul_pow, pow_add]
          ring
    _ < 3 ^ n * 4 ^ n * N ^ n := Nat.mul_lt_mul_of_pos_left h hpos

private lemma cancelled_bound_of_base_pow_exponent_cap {n N B A E : ℕ}
    (hnpos : 0 < n) (hNlo : B * n < N) (hA : A ≤ E)
    (hbase : n * (2 ^ n * 4 ^ E) < B ^ n) :
    n * (2 ^ n * (n ^ n * 4 ^ A)) < N ^ n := by
  have hA4 : 4 ^ A ≤ 4 ^ E := Nat.pow_le_pow_right (by norm_num : 0 < 4) hA
  have hleft_le :
      n * (2 ^ n * (n ^ n * 4 ^ A)) ≤ (n * (2 ^ n * 4 ^ E)) * n ^ n := by
    calc
      n * (2 ^ n * (n ^ n * 4 ^ A)) = (n * (2 ^ n * 4 ^ A)) * n ^ n := by
        ring
      _ ≤ (n * (2 ^ n * 4 ^ E)) * n ^ n := by
        exact Nat.mul_le_mul_right _
          (Nat.mul_le_mul_left n (Nat.mul_le_mul_left (2 ^ n) hA4))
  have hright_lt : (n * (2 ^ n * 4 ^ E)) * n ^ n < B ^ n * n ^ n :=
    Nat.mul_lt_mul_of_pos_right hbase (pow_pos hnpos n)
  have hBN_le : (B * n) ^ n ≤ N ^ n := Nat.pow_le_pow_left hNlo.le n
  have hBN : (B * n) ^ n = B ^ n * n ^ n := by rw [Nat.mul_pow]
  exact hleft_le.trans_lt (hright_lt.trans_le (by simpa [hBN] using hBN_le))

private lemma cancelled_bound_of_base_pow_exponent_cap_le {n N B A E : ℕ}
    (hnpos : 0 < n) (hNlo : B * n ≤ N) (hA : A ≤ E)
    (hbase : n * (2 ^ n * 4 ^ E) < B ^ n) :
    n * (2 ^ n * (n ^ n * 4 ^ A)) < N ^ n := by
  have hA4 : 4 ^ A ≤ 4 ^ E := Nat.pow_le_pow_right (by norm_num : 0 < 4) hA
  have hleft_le :
      n * (2 ^ n * (n ^ n * 4 ^ A)) ≤ (n * (2 ^ n * 4 ^ E)) * n ^ n := by
    calc
      n * (2 ^ n * (n ^ n * 4 ^ A)) = (n * (2 ^ n * 4 ^ A)) * n ^ n := by
        ring
      _ ≤ (n * (2 ^ n * 4 ^ E)) * n ^ n := by
        exact Nat.mul_le_mul_right _
          (Nat.mul_le_mul_left n (Nat.mul_le_mul_left (2 ^ n) hA4))
  have hright_lt : (n * (2 ^ n * 4 ^ E)) * n ^ n < B ^ n * n ^ n :=
    Nat.mul_lt_mul_of_pos_right hbase (pow_pos hnpos n)
  have hBN_le : (B * n) ^ n ≤ N ^ n := Nat.pow_le_pow_left hNlo n
  have hBN : (B * n) ^ n = B ^ n * n ^ n := by rw [Nat.mul_pow]
  exact hleft_le.trans_lt (hright_lt.trans_le (by simpa [hBN] using hBN_le))

private lemma base_two_pow_exp {b D E n : ℕ} (hn_self : n ≤ 2 ^ D)
    (hExp : D + n + 2 * E < b * n) :
    n * (2 ^ n * 4 ^ E) < (2 ^ b) ^ n := by
  have hleft :
      n * (2 ^ n * 4 ^ E) ≤ 2 ^ D * (2 ^ n * 4 ^ E) :=
    Nat.mul_le_mul_right _ hn_self
  have hpow : 2 ^ D * (2 ^ n * 4 ^ E) = 2 ^ (D + n + 2 * E) := by
    rw [four_pow_eq_two_pow_two_mul E]
    rw [← pow_add, ← pow_add]
    congr 1
    ring
  have hlt : 2 ^ (D + n + 2 * E) < 2 ^ (b * n) :=
    Nat.pow_lt_pow_right (by norm_num : 1 < 2) hExp
  have hrhs : 2 ^ (b * n) = (2 ^ b) ^ n := by rw [pow_mul]
  exact hleft.trans_lt (by simpa [hpow, hrhs] using hlt)

private lemma self_le_two_pow_two_mul_div_one_twenty_eight_add_one {n : ℕ}
    (hn : 512 ≤ n) :
    n ≤ 2 ^ (2 * (n / 128 + 1)) := by
  have hself := self_le_four_pow_div_one_twenty_eight_add_one hn
  have hpow : 4 ^ (n / 128 + 1) = 2 ^ (2 * (n / 128 + 1)) :=
    four_pow_eq_two_pow_two_mul (n / 128 + 1)
  rwa [hpow] at hself

private lemma range_3_base_exp {n : ℕ} (hn : 945 ≤ n) :
    n * (2 ^ n * 4 ^ (4 * n / 15)) < 3 ^ n := by
  let D := 2 * (n / 128 + 1)
  have hn_self : n ≤ 2 ^ D := by
    dsimp [D]
    exact self_le_two_pow_two_mul_div_one_twenty_eight_add_one (by omega : 512 ≤ n)
  have hleft :
      n * (2 ^ n * 4 ^ (4 * n / 15)) ≤ 2 ^ D * (2 ^ n * 4 ^ (4 * n / 15)) :=
    Nat.mul_le_mul_right _ hn_self
  have hpow : 2 ^ D * (2 ^ n * 4 ^ (4 * n / 15)) =
      2 ^ (D + n + 2 * (4 * n / 15)) := by
    rw [four_pow_eq_two_pow_two_mul (4 * n / 15)]
    rw [← pow_add, ← pow_add]
    congr 1
    ring
  have hexp : D + n + 2 * (4 * n / 15) < 19 * (n / 12) := by
    dsimp [D]
    omega
  have hlt : 2 ^ (D + n + 2 * (4 * n / 15)) < 2 ^ (19 * (n / 12)) :=
    Nat.pow_lt_pow_right (by norm_num : 1 < 2) hexp
  exact hleft.trans_lt (by
    rw [hpow]
    exact hlt.trans_le (two_pow_nineteen_mul_div_twelve_le_three_pow n))

private lemma range_4_base_exp {n : ℕ} (hn : 945 ≤ n) :
    n * (2 ^ n * 4 ^ (2 * n / 5)) < 4 ^ n := by
  simpa using
    base_two_pow_exp (b := 2) (D := 2 * (n / 128 + 1)) (E := 2 * n / 5)
      (self_le_two_pow_two_mul_div_one_twenty_eight_add_one (by omega : 512 ≤ n))
      (by omega)

private lemma range_8_base_exp {n : ℕ} (hn : 945 ≤ n) :
    n * (2 ^ n * 4 ^ (3 * n / 4)) < 8 ^ n := by
  simpa using
    base_two_pow_exp (b := 3) (D := 2 * (n / 128 + 1)) (E := 3 * n / 4)
      (self_le_two_pow_two_mul_div_one_twenty_eight_add_one (by omega : 512 ≤ n))
      (by omega)

private lemma range_16_base_exp {n : ℕ} (hn : 945 ≤ n) :
    n * (2 ^ n * 4 ^ n) < 16 ^ n := by
  simpa using
    base_two_pow_exp (b := 4) (D := 2 * (n / 128 + 1)) (E := n)
      (self_le_two_pow_two_mul_div_one_twenty_eight_add_one (by omega : 512 ≤ n))
      (by omega)

private lemma range_64_base_exp {n : ℕ} (hn : 945 ≤ n) :
    n * (2 ^ n * 4 ^ (9 * n / 4)) < 64 ^ n := by
  simpa using
    base_two_pow_exp (b := 6) (D := 2 * (n / 128 + 1)) (E := 9 * n / 4)
      (self_le_two_pow_two_mul_div_one_twenty_eight_add_one (by omega : 512 ≤ n))
      (by omega)

private lemma range_512_base_exp (n : ℕ) :
    n * (2 ^ n * 4 ^ (3 * n)) < 512 ^ n := by
  have hn4 : n < 4 ^ n :=
    Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left (by norm_num : 2 ≤ 4) n)
  have h4 : 4 ^ n = 2 ^ (2 * n) :=
    four_pow_eq_two_pow_two_mul n
  have h43 : 4 ^ (3 * n) = 2 ^ (2 * (3 * n)) :=
    four_pow_eq_two_pow_two_mul (3 * n)
  have h512 : 512 ^ n = 2 ^ (9 * n) := by
    rw [show 512 = 2 ^ 9 by norm_num, ← pow_mul]
  calc
    n * (2 ^ n * 4 ^ (3 * n))
        < 4 ^ n * (2 ^ n * 4 ^ (3 * n)) :=
          Nat.mul_lt_mul_of_pos_right hn4 (by positivity)
    _ = 512 ^ n := by
          rw [h4, h43, h512]
          rw [← pow_add, ← pow_add]
          congr 1
          ring


private lemma sqrt_le_self_of_le_sq_add_self {n N : ℕ} (hNhi : N ≤ n ^ 2 + n) :
    Nat.sqrt N ≤ n := by
  calc
    Nat.sqrt N ≤ Nat.sqrt (n ^ 2 + n) := Nat.sqrt_le_sqrt hNhi
    _ = n := Nat.sqrt_add_eq' n (by omega)

private lemma pow_six_step_of_ten_le {s : ℕ} (hs : 10 ≤ s) :
    (s + 2) ^ 6 ≤ 4 * (s + 1) ^ 6 := by
  have hcube : (s + 2) ^ 3 ≤ 2 * (s + 1) ^ 3 := by
    nlinarith [hs, sq_nonneg (s : ℤ)]
  have hsquare := Nat.pow_le_pow_left hcube 2
  calc
    (s + 2) ^ 6 = ((s + 2) ^ 3) ^ 2 := by ring
    _ ≤ (2 * (s + 1) ^ 3) ^ 2 := hsquare
    _ = 4 * (s + 1) ^ 6 := by ring

private lemma sqrt_succ_pow_six_le_two_pow_two_mul_add_one {s : ℕ} (hs : 10 ≤ s) :
    (s + 1) ^ 6 ≤ 2 ^ (2 * s + 1) := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
      calc
        (s + 1 + 1) ^ 6 = (s + 2) ^ 6 := by ring
        _ ≤ 4 * (s + 1) ^ 6 := pow_six_step_of_ten_le hs
        _ ≤ 4 * 2 ^ (2 * s + 1) := Nat.mul_le_mul_left 4 ih
        _ = 2 ^ (2 * (s + 1) + 1) := by
          rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]
          congr 1
          ring

private lemma log_two_le_two_mul_sqrt_nthRoot_three {N : ℕ}
    (hc : 100 ≤ Nat.nthRoot 3 N) :
    Nat.log 2 N ≤ 2 * Nat.sqrt (Nat.nthRoot 3 N) := by
  let c := Nat.nthRoot 3 N
  let s := Nat.sqrt c
  have hs10 : 10 ≤ s := by
    dsimp [s]
    rw [Nat.le_sqrt]
    omega
  have hNlt : N < (c + 1) ^ 3 := by
    dsimp [c]
    exact (Nat.nthRoot_lt_iff (by norm_num : 3 ≠ 0)).mp (Nat.lt_succ_self _)
  have hc_succ : c + 1 ≤ (s + 1) ^ 2 := by
    dsimp [s]
    exact Nat.succ_le_succ_sqrt' c
  have hcube : (c + 1) ^ 3 ≤ (s + 1) ^ 6 := by
    calc
      (c + 1) ^ 3 ≤ ((s + 1) ^ 2) ^ 3 := Nat.pow_le_pow_left hc_succ 3
      _ = (s + 1) ^ 6 := by ring
  have hpow : (c + 1) ^ 3 ≤ 2 ^ (2 * s + 1) :=
    hcube.trans (sqrt_succ_pow_six_le_two_pow_two_mul_add_one hs10)
  have hloglt : Nat.log 2 N < 2 * s + 1 :=
    Nat.log_lt_of_lt_pow' (by omega) (hNlt.trans_le hpow)
  dsimp [c, s] at hloglt ⊢
  omega

private lemma nthRoot_three_mul_log_le_of_nthRoot_lt {N A e M : ℕ}
    (hroot : Nat.nthRoot 3 N < A) (hpow : A ^ 3 ≤ 2 ^ e) (he : e ≠ 0)
    (hbound : (A - 1) * (e - 1) ≤ M) :
    Nat.nthRoot 3 N * Nat.log 2 N ≤ M := by
  have hNlt : N < A ^ 3 := by
    exact (Nat.nthRoot_lt_iff (by norm_num : 3 ≠ 0)).mp hroot
  have hloglt : Nat.log 2 N < e :=
    Nat.log_lt_of_lt_pow' he (hNlt.trans_le hpow)
  have hroot_le : Nat.nthRoot 3 N ≤ A - 1 := by omega
  have hlog_le : Nat.log 2 N ≤ e - 1 := by omega
  exact (Nat.mul_le_mul hroot_le hlog_le).trans hbound

private lemma nthRoot_three_mul_log_le_mul_pred_of_nthRoot_lt {N A e : ℕ}
    (hroot : Nat.nthRoot 3 N < A) (hpow : A ^ 3 ≤ 2 ^ e) (he : e ≠ 0) :
    Nat.nthRoot 3 N * Nat.log 2 N ≤ Nat.nthRoot 3 N * (e - 1) := by
  have hNlt : N < A ^ 3 := by
    exact (Nat.nthRoot_lt_iff (by norm_num : 3 ≠ 0)).mp hroot
  have hloglt : Nat.log 2 N < e :=
    Nat.log_lt_of_lt_pow' he (hNlt.trans_le hpow)
  exact Nat.mul_le_mul_left _ (by omega)

private lemma nthRoot_three_pow_le_of_le {N M : ℕ} (hNM : N ≤ M) :
    (Nat.nthRoot 3 N) ^ 3 ≤ M :=
  (Nat.pow_nthRoot_le (Or.inl (by norm_num : 3 ≠ 0))).trans hNM

private lemma first_residual_large_root_log_le_two_mul_self {n N : ℕ}
    (hn : 945 ≤ n) (hNhi : N ≤ n ^ 2 + n) :
    Nat.nthRoot 3 N * Nat.log 2 N ≤ 2 * n := by
  let c := Nat.nthRoot 3 N
  let s := Nat.sqrt c
  have hc3n : c ^ 3 ≤ n ^ 2 + n := by
    simpa [c] using nthRoot_three_pow_le_of_le hNhi
  by_cases hc100lt : c < 100
  · simpa [c] using
      nthRoot_three_mul_log_le_of_nthRoot_lt
        (N := N) (A := 100) (e := 20) (M := 2 * n)
        (by simpa [c] using hc100lt) (by norm_num) (by norm_num) (by omega)
  · have hc100 : 100 ≤ c := by omega
    have hlog : Nat.log 2 N ≤ 2 * s := by
      dsimp [s, c]
      exact log_two_le_two_mul_sqrt_nthRoot_three (N := N) (by simpa [c] using hc100)
    have hs2 : s ^ 2 ≤ c := by
      dsimp [s]
      exact Nat.sqrt_le' c
    have hcs_sq : (c * s) ^ 2 ≤ n ^ 2 + n := by
      calc
        (c * s) ^ 2 = c ^ 2 * s ^ 2 := by ring
        _ ≤ c ^ 2 * c := Nat.mul_le_mul_left (c ^ 2) hs2
        _ = c ^ 3 := by ring
        _ ≤ n ^ 2 + n := hc3n
    have hcsn : c * s ≤ n := by
      simpa [Nat.sqrt_eq'] using
        sqrt_le_self_of_le_sq_add_self (n := n) (N := (c * s) ^ 2) hcs_sq
    calc
      c * Nat.log 2 N ≤ c * (2 * s) := Nat.mul_le_mul_left c hlog
      _ = 2 * (c * s) := by ring
      _ ≤ 2 * n := Nat.mul_le_mul_left 2 hcsn

private lemma first_residual_large_exponent_le_three_mul_self {n N : ℕ}
    (hn : 945 ≤ n) (hNhi : N ≤ n ^ 2 + n) :
    Nat.sqrt N + Nat.nthRoot 3 N * Nat.log 2 N ≤ 3 * n := by
  have hsqrt : Nat.sqrt N ≤ n := sqrt_le_self_of_le_sq_add_self hNhi
  have hroot_log : Nat.nthRoot 3 N * Nat.log 2 N ≤ 2 * n :=
    first_residual_large_root_log_le_two_mul_self hn hNhi
  omega

private lemma sqrt_le_div_of_sq_mul_le {a B n N : ℕ} (ha : 0 < a)
    (hpoly : a ^ 2 * (B * n) ≤ n ^ 2) (hNhi : N ≤ B * n) :
    Nat.sqrt N ≤ n / a := by
  let s := Nat.sqrt N
  have hs2 : s ^ 2 ≤ N := by
    dsimp [s]
    simpa [pow_two] using Nat.sqrt_le N
  have hsq : (a * s) ^ 2 ≤ n ^ 2 := by
    calc
      (a * s) ^ 2 = a ^ 2 * s ^ 2 := by ring
      _ ≤ a ^ 2 * N := Nat.mul_le_mul_left (a ^ 2) hs2
      _ ≤ a ^ 2 * (B * n) := Nat.mul_le_mul_left (a ^ 2) hNhi
      _ ≤ n ^ 2 := hpoly
  have hle : a * s ≤ n :=
    (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).mp hsq
  rw [Nat.le_div_iff_mul_le ha]
  simpa [s, Nat.mul_comm] using hle

/-- If `N ≤ 4 * n` and `n` is large enough, then `sqrt N` is at most `n / 15`. -/
lemma sqrt_le_div_fifteen_of_le_four_mul {n N : ℕ} (hn : 900 ≤ n)
    (hNhi : N ≤ 4 * n) :
    Nat.sqrt N ≤ n / 15 := by
  exact sqrt_le_div_of_sq_mul_le (a := 15) (B := 4) (by norm_num)
    (by nlinarith [hn]) hNhi

private lemma const_log_product_le_one_fifth_of_le_four_mul {c n m : ℕ}
    (hquad : 20 * m ≤ c ^ 2) (hc3n : c ^ 3 ≤ 4 * n) :
    c * m ≤ n / 5 := by
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 5)]
  apply Nat.le_of_mul_le_mul_left (c := 4)
  · have hcubic : (20 * m) * c ≤ c ^ 3 := by
      calc
        (20 * m) * c ≤ c ^ 2 * c := Nat.mul_le_mul_right c hquad
        _ = c ^ 3 := by ring
    calc
      4 * (c * m * 5) = (20 * m) * c := by ring
      _ ≤ c ^ 3 := hcubic
      _ ≤ 4 * n := hc3n
  · norm_num

private lemma nthRoot_three_mul_log_le_one_fifth_of_lt {n N A e m : ℕ}
    (hroot : Nat.nthRoot 3 N < A) (hpow : A ^ 3 ≤ 2 ^ e) (he : e ≠ 0)
    (hpred : e - 1 ≤ m)
    (hquad : 20 * m ≤ (Nat.nthRoot 3 N) ^ 2)
    (hc3n : (Nat.nthRoot 3 N) ^ 3 ≤ 4 * n) :
    Nat.nthRoot 3 N * Nat.log 2 N ≤ n / 5 := by
  have hlog :=
    nthRoot_three_mul_log_le_mul_pred_of_nthRoot_lt hroot hpow he
  exact hlog.trans <| (Nat.mul_le_mul_left _ hpred).trans <|
    const_log_product_le_one_fifth_of_le_four_mul hquad hc3n

private lemma nthRoot_three_mul_log_le_one_fifth_of_nthRoot_ge
    {n N : ℕ} (hroot : 100 ≤ Nat.nthRoot 3 N)
    (hc3n : (Nat.nthRoot 3 N) ^ 3 ≤ 4 * n) :
    Nat.nthRoot 3 N * Nat.log 2 N ≤ n / 5 := by
  let c := Nat.nthRoot 3 N
  let s := Nat.sqrt c
  have hlog : Nat.log 2 N ≤ 2 * s := by
    dsimp [s, c]
    exact log_two_le_two_mul_sqrt_nthRoot_three (N := N) (by simpa [c] using hroot)
  have hs_le_c : s ≤ c := by
    dsimp [s]
    exact Nat.sqrt_le_self c
  have h40 : 40 * s ≤ c ^ 2 := by
    calc
      40 * s ≤ c * s := Nat.mul_le_mul_right s (by omega)
      _ ≤ c * c := Nat.mul_le_mul_left c hs_le_c
      _ = c ^ 2 := by ring
  have h10cs : 10 * (c * s) ≤ n := by
    apply Nat.le_of_mul_le_mul_left (c := 4)
    · calc
        4 * (10 * (c * s)) = (40 * s) * c := by ring
        _ ≤ c ^ 2 * c := Nat.mul_le_mul_right c h40
        _ = c ^ 3 := by ring
        _ ≤ 4 * n := by simpa [c] using hc3n
    · norm_num
  have htarget : c * (2 * s) ≤ n / 5 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 5)]
    calc
      c * (2 * s) * 5 = 10 * (c * s) := by ring
      _ ≤ n := h10cs
  calc
    c * Nat.log 2 N ≤ c * (2 * s) := Nat.mul_le_mul_left c hlog
    _ ≤ n / 5 := htarget

private lemma nthRoot_three_mul_log_le_one_fifth_of_ge_sixteen
    {n N : ℕ} (hroot16 : 16 ≤ Nat.nthRoot 3 N)
    (hc3n : (Nat.nthRoot 3 N) ^ 3 ≤ 4 * n) :
    Nat.nthRoot 3 N * Nat.log 2 N ≤ n / 5 := by
  let c := Nat.nthRoot 3 N
  have hc16 : 16 ≤ c := by simpa [c] using hroot16
  by_cases hc20lt : c < 20
  · simpa [c] using
      nthRoot_three_mul_log_le_one_fifth_of_lt
        (N := N) (A := 20) (e := 13) (m := 12)
        (by simpa [c] using hc20lt) (by norm_num) (by norm_num) (by omega)
        (by nlinarith [hc16]) (by simpa [c] using hc3n)
  by_cases hc32lt : c < 32
  · simpa [c] using
      nthRoot_three_mul_log_le_one_fifth_of_lt
        (N := N) (A := 32) (e := 15) (m := 14)
        (by simpa [c] using hc32lt) (by norm_num) (by norm_num) (by omega)
        (by nlinarith [Nat.le_of_not_gt hc20lt]) (by simpa [c] using hc3n)
  by_cases hc64lt : c < 64
  · simpa [c] using
      nthRoot_three_mul_log_le_one_fifth_of_lt
        (N := N) (A := 64) (e := 18) (m := 17)
        (by simpa [c] using hc64lt) (by norm_num) (by norm_num) (by omega)
        (by nlinarith [Nat.le_of_not_gt hc32lt]) (by simpa [c] using hc3n)
  by_cases hc100lt : c < 100
  · simpa [c] using
      nthRoot_three_mul_log_le_one_fifth_of_lt
        (N := N) (A := 100) (e := 20) (m := 19)
        (by simpa [c] using hc100lt) (by norm_num) (by norm_num) (by omega)
        (by nlinarith [Nat.le_of_not_gt hc64lt]) (by simpa [c] using hc3n)
  have hc100 : 100 ≤ c := by omega
  simpa [c] using
    nthRoot_three_mul_log_le_one_fifth_of_nthRoot_ge
      (N := N) (n := n) (by simpa [c] using hc100) (by simpa [c] using hc3n)

/-- In the range `N ≤ 4 * n`, the `Nat.nthRoot 3 N * Nat.log 2 N` contribution is at
most `n / 5`. -/
lemma nthRoot_three_mul_log_le_one_fifth_of_le_four_mul {n N : ℕ}
    (hn : 945 ≤ n) (hNhi : N ≤ 4 * n) :
    Nat.nthRoot 3 N * Nat.log 2 N ≤ n / 5 := by
  let c := Nat.nthRoot 3 N
  have hc3n : c ^ 3 ≤ 4 * n := by
    simpa [c] using nthRoot_three_pow_le_of_le hNhi
  by_cases hc16lt : c < 16
  · simpa [c] using
      nthRoot_three_mul_log_le_of_nthRoot_lt
        (N := N) (A := 16) (e := 12) (M := n / 5)
        (by simpa [c] using hc16lt) (by norm_num) (by norm_num) (by omega)
  exact nthRoot_three_mul_log_le_one_fifth_of_ge_sixteen
    (by simpa [c] using Nat.le_of_not_gt hc16lt) (by simpa [c] using hc3n)

private lemma first_residual_large_exponent_le_four_fifteenths {n N : ℕ}
    (hn : 945 ≤ n) (hNhi : N ≤ 4 * n) :
    Nat.sqrt N + Nat.nthRoot 3 N * Nat.log 2 N ≤ 4 * n / 15 := by
  have hsqrt : Nat.sqrt N ≤ n / 15 :=
    sqrt_le_div_fifteen_of_le_four_mul (by omega : 900 ≤ n) hNhi
  have hroot_log : Nat.nthRoot 3 N * Nat.log 2 N ≤ n / 5 :=
    nthRoot_three_mul_log_le_one_fifth_of_le_four_mul hn hNhi
  omega


private lemma sqrt_le_div_ten_of_le_eight_mul {n N : ℕ} (hn : 800 ≤ n)
    (hNhi : N ≤ 8 * n) :
    Nat.sqrt N ≤ n / 10 := by
  exact sqrt_le_div_of_sq_mul_le (a := 10) (B := 8) (by norm_num)
    (by nlinarith [hn]) hNhi

private lemma cube_succ_le_two_pow_three_mul_div_four_add_one {c : ℕ} (hc : 15 ≤ c) :
    (c + 1) ^ 3 ≤ 2 ^ (3 * c / 4 + 1) := by
  induction c using Nat.strong_induction_on with
  | h c ih =>
    by_cases hsmall : c < 19
    · interval_cases c <;> norm_num
    · have hc19 : 19 ≤ c := by omega
      have hprev15 : 15 ≤ c - 4 := by omega
      have hprev := ih (c - 4) (by omega) hprev15
      have hpoly : (c + 1) ^ 3 ≤ 8 * ((c - 4) + 1) ^ 3 := by
        have hsub : (c - 4) + 1 = c - 3 := by omega
        calc
          (c + 1) ^ 3 ≤ (2 * (c - 3)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
          _ = 8 * (c - 3) ^ 3 := by ring
          _ = 8 * ((c - 4) + 1) ^ 3 := by rw [hsub]
      have hpow : 8 * 2 ^ (3 * (c - 4) / 4 + 1) = 2 ^ (3 * c / 4 + 1) := by
        have hdiv : 3 * c / 4 = 3 * (c - 4) / 4 + 3 := by omega
        rw [hdiv, show 8 = 2 ^ 3 by norm_num, ← pow_add]
        congr 1
        ring
      exact hpoly.trans (by simpa [hpow] using Nat.mul_le_mul_left 8 hprev)

private lemma log_two_le_three_mul_nthRoot_three_div_four {N : ℕ}
    (hc : 15 ≤ Nat.nthRoot 3 N) :
    Nat.log 2 N ≤ 3 * Nat.nthRoot 3 N / 4 := by
  let c := Nat.nthRoot 3 N
  have hNlt : N < (c + 1) ^ 3 := by
    dsimp [c]
    exact (Nat.nthRoot_lt_iff (by norm_num : 3 ≠ 0)).mp (Nat.lt_succ_self _)
  have hcube : (c + 1) ^ 3 ≤ 2 ^ (3 * c / 4 + 1) :=
    cube_succ_le_two_pow_three_mul_div_four_add_one (by simpa [c] using hc)
  have hloglt : Nat.log 2 N < 3 * c / 4 + 1 :=
    Nat.log_lt_of_lt_pow' (by omega) (hNlt.trans_le hcube)
  dsimp [c] at hloglt ⊢
  omega

private lemma mul_three_mul_div_four_le_mul_div_of_scaled_sq {a b c n : ℕ}
    (hb : 0 < b) (hsq : 3 * b * c ^ 2 ≤ 4 * (a * n)) :
    c * (3 * c / 4) ≤ a * n / b := by
  have hdivmul : 4 * (3 * c / 4) ≤ 3 * c := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.div_mul_le_self (3 * c) 4
  rw [Nat.le_div_iff_mul_le hb]
  apply Nat.le_of_mul_le_mul_left (c := 4)
  · calc
      4 * (c * (3 * c / 4) * b) = b * c * (4 * (3 * c / 4)) := by ring
      _ ≤ b * c * (3 * c) := Nat.mul_le_mul_left (b * c) hdivmul
      _ = 3 * b * c ^ 2 := by ring
      _ ≤ 4 * (a * n) := hsq
  · norm_num

private lemma nthRoot_three_mul_log_le_mul_div_of_scaled_sq {a b n N : ℕ}
    (hroot : 15 ≤ Nat.nthRoot 3 N) (hb : 0 < b)
    (hsq : 3 * b * (Nat.nthRoot 3 N) ^ 2 ≤ 4 * (a * n)) :
    Nat.nthRoot 3 N * Nat.log 2 N ≤ a * n / b := by
  let c := Nat.nthRoot 3 N
  have hlog : Nat.log 2 N ≤ 3 * c / 4 := by
    dsimp [c]
    exact log_two_le_three_mul_nthRoot_three_div_four (N := N) (by simpa [c] using hroot)
  calc
    c * Nat.log 2 N ≤ c * (3 * c / 4) := Nat.mul_le_mul_left c hlog
    _ ≤ a * n / b := mul_three_mul_div_four_le_mul_div_of_scaled_sq
      (a := a) (b := b) hb (by simpa [c] using hsq)

private lemma first_residual_large_root_log_le_three_tenths_of_le_eight_mul {n N : ℕ}
    (hn : 945 ≤ n) (hNhi : N ≤ 8 * n) :
    Nat.nthRoot 3 N * Nat.log 2 N ≤ 3 * n / 10 := by
  let c := Nat.nthRoot 3 N
  by_cases hc20 : c < 20
  · simpa [c] using
      nthRoot_three_mul_log_le_of_nthRoot_lt
        (N := N) (A := 20) (e := 13) (M := 3 * n / 10)
        (by simpa [c] using hc20) (by norm_num) (by norm_num) (by omega)
  · have hc20le : 20 ≤ c := by omega
    have hc15 : 15 ≤ c := by omega
    have hc3n : c ^ 3 ≤ 8 * n := by
      simpa [c] using nthRoot_three_pow_le_of_le hNhi
    have h5 : 5 * c ^ 2 ≤ 2 * n := by
      nlinarith [hc20le, hc3n]
    simpa [c] using
      nthRoot_three_mul_log_le_mul_div_of_scaled_sq (a := 3) (b := 10) (n := n)
        (N := N) (by simpa [c] using hc15) (by norm_num) (by nlinarith [h5])

private lemma first_residual_large_exponent_le_two_fifths {n N : ℕ}
    (hn : 945 ≤ n) (hNhi : N ≤ 8 * n) :
    Nat.sqrt N + Nat.nthRoot 3 N * Nat.log 2 N ≤ 2 * n / 5 := by
  have hsqrt : Nat.sqrt N ≤ n / 10 :=
    sqrt_le_div_ten_of_le_eight_mul (by omega : 800 ≤ n) hNhi
  have hroot_log : Nat.nthRoot 3 N * Nat.log 2 N ≤ 3 * n / 10 :=
    first_residual_large_root_log_le_three_tenths_of_le_eight_mul hn hNhi
  omega


private lemma sqrt_le_div_seven_of_le_sixteen_mul {n N : ℕ} (hn : 784 ≤ n)
    (hNhi : N ≤ 16 * n) :
    Nat.sqrt N ≤ n / 7 := by
  exact sqrt_le_div_of_sq_mul_le (a := 7) (B := 16) (by norm_num)
    (by nlinarith [hn]) hNhi

private lemma first_residual_large_root_log_le_three_fifths_of_le_sixteen_mul {n N : ℕ}
    (hn : 945 ≤ n) (hNhi : N ≤ 16 * n) :
    Nat.nthRoot 3 N * Nat.log 2 N ≤ 3 * n / 5 := by
  let c := Nat.nthRoot 3 N
  by_cases hc20 : c < 20
  · simpa [c] using
      nthRoot_three_mul_log_le_of_nthRoot_lt
        (N := N) (A := 20) (e := 13) (M := 3 * n / 5)
        (by simpa [c] using hc20) (by norm_num) (by norm_num) (by omega)
  · have hc20le : 20 ≤ c := by omega
    have hc15 : 15 ≤ c := by omega
    have hc3n : c ^ 3 ≤ 16 * n := by
      simpa [c] using nthRoot_three_pow_le_of_le hNhi
    have h5 : 5 * c ^ 2 ≤ 4 * n := by
      nlinarith [hc20le, hc3n]
    simpa [c] using
      nthRoot_three_mul_log_le_mul_div_of_scaled_sq (a := 3) (b := 5) (n := n)
        (N := N) (by simpa [c] using hc15) (by norm_num) (by nlinarith [h5])

private lemma first_residual_large_exponent_le_three_fourths {n N : ℕ}
    (hn : 945 ≤ n) (hNhi : N ≤ 16 * n) :
    Nat.sqrt N + Nat.nthRoot 3 N * Nat.log 2 N ≤ 3 * n / 4 := by
  have hsqrt : Nat.sqrt N ≤ n / 7 :=
    sqrt_le_div_seven_of_le_sixteen_mul (by omega : 784 ≤ n) hNhi
  have hroot_log : Nat.nthRoot 3 N * Nat.log 2 N ≤ 3 * n / 5 :=
    first_residual_large_root_log_le_three_fifths_of_le_sixteen_mul hn hNhi
  omega


private lemma sqrt_le_div_three_of_le_sixty_four_mul {n N : ℕ} (hn : 576 ≤ n)
    (hNhi : N ≤ 64 * n) :
    Nat.sqrt N ≤ n / 3 := by
  exact sqrt_le_div_of_sq_mul_le (a := 3) (B := 64) (by norm_num)
    (by nlinarith [hn]) hNhi

private lemma const_log_product_le_two_thirds_of_le_sixty_four_mul {c n m : ℕ}
    (hquad : 96 * m ≤ c ^ 2) (hc3n : c ^ 3 ≤ 64 * n) :
    c * m ≤ 2 * n / 3 := by
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 3)]
  apply Nat.le_of_mul_le_mul_left (c := 32)
  · have hcubic : (96 * m) * c ≤ c ^ 3 := by
      calc
        (96 * m) * c ≤ c ^ 2 * c := Nat.mul_le_mul_right c hquad
        _ = c ^ 3 := by ring
    calc
      32 * (c * m * 3) = (96 * m) * c := by ring
      _ ≤ c ^ 3 := hcubic
      _ ≤ 64 * n := hc3n
      _ = 32 * (2 * n) := by ring
  · norm_num

private lemma nthRoot_three_mul_log_le_two_thirds_of_lt {n N A e m : ℕ}
    (hroot : Nat.nthRoot 3 N < A) (hpow : A ^ 3 ≤ 2 ^ e) (he : e ≠ 0)
    (hpred : e - 1 ≤ m)
    (hquad : 96 * m ≤ (Nat.nthRoot 3 N) ^ 2)
    (hc3n : (Nat.nthRoot 3 N) ^ 3 ≤ 64 * n) :
    Nat.nthRoot 3 N * Nat.log 2 N ≤ 2 * n / 3 := by
  have hlog :=
    nthRoot_three_mul_log_le_mul_pred_of_nthRoot_lt hroot hpow he
  exact hlog.trans <| (Nat.mul_le_mul_left _ hpred).trans <|
    const_log_product_le_two_thirds_of_le_sixty_four_mul hquad hc3n

private lemma nthRoot_three_mul_log_le_two_thirds_of_nthRoot_ge
    {n N : ℕ} (hroot : 72 ≤ Nat.nthRoot 3 N)
    (hc3n : (Nat.nthRoot 3 N) ^ 3 ≤ 64 * n) :
    Nat.nthRoot 3 N * Nat.log 2 N ≤ 2 * n / 3 := by
  let c := Nat.nthRoot 3 N
  have hroot_c : 72 ≤ c := by
    dsimp [c]
    exact hroot
  have hc15 : 15 ≤ c := by omega
  have hsquare : 9 * c ^ 2 ≤ 8 * n := by
    apply Nat.le_of_mul_le_mul_left (c := 8)
    · have hc_sq : 72 * c ^ 2 ≤ c ^ 3 := by
        calc
          72 * c ^ 2 ≤ c * c ^ 2 :=
            Nat.mul_le_mul_right (c ^ 2) hroot_c
          _ = c ^ 3 := by ring
      calc
        8 * (9 * c ^ 2) = 72 * c ^ 2 := by ring
        _ ≤ c ^ 3 := hc_sq
        _ ≤ 64 * n := by simpa [c] using hc3n
        _ = 8 * (8 * n) := by ring
    · norm_num
  simpa [c] using
    nthRoot_three_mul_log_le_mul_div_of_scaled_sq (a := 2) (b := 3) (n := n)
      (N := N) (by simpa [c] using hc15) (by norm_num) (by nlinarith [hsquare])

private lemma first_residual_large_root_log_le_two_thirds_of_le_sixty_four_mul {n N : ℕ}
    (hn : 945 ≤ n) (hNhi : N ≤ 64 * n) :
    Nat.nthRoot 3 N * Nat.log 2 N ≤ 2 * n / 3 := by
  let c := Nat.nthRoot 3 N
  have hc3n : c ^ 3 ≤ 64 * n := by
    simpa [c] using nthRoot_three_pow_le_of_le hNhi
  by_cases hc40lt : c < 40
  · simpa [c] using
      nthRoot_three_mul_log_le_of_nthRoot_lt
        (N := N) (A := 40) (e := 16) (M := 2 * n / 3)
        (by simpa [c] using hc40lt) (by norm_num) (by norm_num) (by omega)
  by_cases hc42lt : c < 42
  · simpa [c] using
      nthRoot_three_mul_log_le_two_thirds_of_lt
        (N := N) (A := 42) (e := 17) (m := 16)
        (by simpa [c] using hc42lt) (by norm_num) (by norm_num) (by omega)
        (by nlinarith [Nat.le_of_not_gt hc40lt]) (by simpa [c] using hc3n)
  by_cases hc72lt : c < 72
  · simpa [c] using
      nthRoot_three_mul_log_le_two_thirds_of_lt
        (N := N) (A := 72) (e := 19) (m := 18)
        (by simpa [c] using hc72lt) (by norm_num) (by norm_num) (by omega)
        (by nlinarith [Nat.le_of_not_gt hc42lt]) (by simpa [c] using hc3n)
  · have hc72 : 72 ≤ c := by omega
    simpa [c] using
      nthRoot_three_mul_log_le_two_thirds_of_nthRoot_ge
        (N := N) (n := n) (by simpa [c] using hc72) (by simpa [c] using hc3n)

private lemma first_residual_large_exponent_le_self {n N : ℕ}
    (hn : 945 ≤ n) (hNhi : N ≤ 64 * n) :
    Nat.sqrt N + Nat.nthRoot 3 N * Nat.log 2 N ≤ n := by
  have hsqrt : Nat.sqrt N ≤ n / 3 :=
    sqrt_le_div_three_of_le_sixty_four_mul (by omega : 576 ≤ n) hNhi
  have hroot_log : Nat.nthRoot 3 N * Nat.log 2 N ≤ 2 * n / 3 :=
    first_residual_large_root_log_le_two_thirds_of_le_sixty_four_mul hn hNhi
  omega


private lemma sqrt_le_three_mul_div_four_of_le_five_twelve_mul {n N : ℕ} (hn : 911 ≤ n)
    (hNhi : N ≤ 512 * n) :
    Nat.sqrt N ≤ 3 * n / 4 := by
  let s := Nat.sqrt N
  have hs2 : s ^ 2 ≤ N := by
    dsimp [s]
    simpa [pow_two] using Nat.sqrt_le N
  have hpoly : 16 * (512 * n) ≤ (3 * n) ^ 2 := by nlinarith [hn]
  have hsq : (4 * s) ^ 2 ≤ (3 * n) ^ 2 := by
    calc
      (4 * s) ^ 2 = 16 * s ^ 2 := by ring
      _ ≤ 16 * N := Nat.mul_le_mul_left 16 hs2
      _ ≤ 16 * (512 * n) := Nat.mul_le_mul_left 16 hNhi
      _ ≤ (3 * n) ^ 2 := hpoly
  have h4 : 4 * s ≤ 3 * n := by
    exact (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).mp hsq
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 4)]
  simpa [s, Nat.mul_comm] using h4

private lemma const_log_product_le_three_halves {c n m : ℕ}
    (hquad : 1024 * m ≤ 3 * c ^ 2) (hc3n : c ^ 3 ≤ 512 * n) :
    c * m ≤ 3 * n / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
  apply Nat.le_of_mul_le_mul_left (c := 512)
  · have hcubic : (1024 * m) * c ≤ 3 * c ^ 3 := by
      calc
        (1024 * m) * c ≤ (3 * c ^ 2) * c := Nat.mul_le_mul_right c hquad
        _ = 3 * c ^ 3 := by ring
    calc
      512 * (c * m * 2) = (1024 * m) * c := by ring
      _ ≤ 3 * c ^ 3 := hcubic
      _ ≤ 3 * (512 * n) := Nat.mul_le_mul_left 3 hc3n
      _ = 512 * (3 * n) := by ring
  · norm_num

private lemma nthRoot_three_mul_log_le_three_halves_of_lt {n N A e m : ℕ}
    (hroot : Nat.nthRoot 3 N < A) (hpow : A ^ 3 ≤ 2 ^ e) (he : e ≠ 0)
    (hpred : e - 1 ≤ m)
    (hquad : 1024 * m ≤ 3 * (Nat.nthRoot 3 N) ^ 2)
    (hc3n : (Nat.nthRoot 3 N) ^ 3 ≤ 512 * n) :
    Nat.nthRoot 3 N * Nat.log 2 N ≤ 3 * n / 2 := by
  have hlog :=
    nthRoot_three_mul_log_le_mul_pred_of_nthRoot_lt hroot hpow he
  exact hlog.trans <| (Nat.mul_le_mul_left _ hpred).trans <|
    const_log_product_le_three_halves hquad hc3n

private lemma nthRoot_three_sq_le_two_mul_of_ge_two_fifty_six
    {n N : ℕ} (hroot : 256 ≤ Nat.nthRoot 3 N)
    (hc3n : (Nat.nthRoot 3 N) ^ 3 ≤ 512 * n) :
    (Nat.nthRoot 3 N) ^ 2 ≤ 2 * n := by
  let c := Nat.nthRoot 3 N
  apply Nat.le_of_mul_le_mul_left (c := 256)
  · have hc_sq : 256 * c ^ 2 ≤ c ^ 3 := by
      calc
        256 * c ^ 2 ≤ c * c ^ 2 := Nat.mul_le_mul_right (c ^ 2) (by simpa [c] using hroot)
        _ = c ^ 3 := by ring
    calc
      256 * c ^ 2 ≤ c ^ 3 := hc_sq
      _ ≤ 512 * n := by simpa [c] using hc3n
      _ = 256 * (2 * n) := by ring
  · norm_num

private lemma nthRoot_three_mul_log_le_three_halves_of_sq_le
    {n N : ℕ} (hroot : 15 ≤ Nat.nthRoot 3 N)
    (hsq : (Nat.nthRoot 3 N) ^ 2 ≤ 2 * n) :
    Nat.nthRoot 3 N * Nat.log 2 N ≤ 3 * n / 2 := by
  exact nthRoot_three_mul_log_le_mul_div_of_scaled_sq (a := 3) (b := 2) (n := n)
    (N := N) hroot (by norm_num) (by nlinarith [hsq])

private lemma nthRoot_three_mul_log_le_three_halves_of_lt_eighty_one
    {n N : ℕ} (hroot79 : 79 ≤ Nat.nthRoot 3 N)
    (hroot81 : Nat.nthRoot 3 N < 81)
    (hc3n : (Nat.nthRoot 3 N) ^ 3 ≤ 512 * n) (hNhi : N ≤ 512 * n) :
    Nat.nthRoot 3 N * Nat.log 2 N ≤ 3 * n / 2 := by
  let c := Nat.nthRoot 3 N
  by_cases hNpow19 : N < 2 ^ 19
  · have hloglt : Nat.log 2 N < 19 := Nat.log_lt_of_lt_pow' (by norm_num) hNpow19
    have hLle : Nat.log 2 N ≤ 18 := by omega
    have hprod : c * Nat.log 2 N ≤ c * 18 := Nat.mul_le_mul_left c hLle
    have hc_bound : c * 18 ≤ 3 * n / 2 :=
      const_log_product_le_three_halves (c := c) (n := n) (m := 18)
        (by nlinarith [hroot79]) (by simpa [c] using hc3n)
    dsimp [c] at hprod ⊢
    exact hprod.trans hc_bound
  · have hn1024 : 1024 ≤ n := by nlinarith [Nat.le_of_not_gt hNpow19, hNhi]
    simpa [c] using
      nthRoot_three_mul_log_le_of_nthRoot_lt
        (N := N) (A := 81) (e := 20) (M := 3 * n / 2)
        (by simpa [c] using hroot81) (by norm_num) (by norm_num) (by omega)

private lemma nthRoot_three_mul_log_le_three_halves_of_ge_seventy_nine
    {n N : ℕ} (hroot79 : 79 ≤ Nat.nthRoot 3 N)
    (hc3n : (Nat.nthRoot 3 N) ^ 3 ≤ 512 * n) (hNhi : N ≤ 512 * n) :
    Nat.nthRoot 3 N * Nat.log 2 N ≤ 3 * n / 2 := by
  let c := Nat.nthRoot 3 N
  have hc79 : 79 ≤ c := by simpa [c] using hroot79
  by_cases hc81lt : c < 81
  · simpa [c] using
      nthRoot_three_mul_log_le_three_halves_of_lt_eighty_one
        (N := N) (n := n) (by simpa [c] using hc79)
        (by simpa [c] using hc81lt) (by simpa [c] using hc3n) hNhi
  by_cases hc91lt : c < 91
  · simpa [c] using
      nthRoot_three_mul_log_le_three_halves_of_lt
        (N := N) (A := 91) (e := 20) (m := 19)
        (by simpa [c] using hc91lt) (by norm_num) (by norm_num) (by omega)
        (by nlinarith [Nat.le_of_not_gt hc81lt]) (by simpa [c] using hc3n)
  by_cases hc128lt : c < 128
  · simpa [c] using
      nthRoot_three_mul_log_le_three_halves_of_lt
        (N := N) (A := 128) (e := 21) (m := 20)
        (by simpa [c] using hc128lt) (by norm_num) (by norm_num) (by omega)
        (by nlinarith [Nat.le_of_not_gt hc91lt]) (by simpa [c] using hc3n)
  by_cases hc256lt : c < 256
  · simpa [c] using
      nthRoot_three_mul_log_le_three_halves_of_lt
        (N := N) (A := 256) (e := 24) (m := 23)
        (by simpa [c] using hc256lt) (by norm_num) (by norm_num) (by omega)
        (by nlinarith [Nat.le_of_not_gt hc128lt]) (by simpa [c] using hc3n)
  have hc256 : 256 ≤ c := by omega
  simpa [c] using
    nthRoot_three_mul_log_le_three_halves_of_sq_le
      (N := N) (n := n) (by simpa [c] using (by omega : 15 ≤ c))
      (nthRoot_three_sq_le_two_mul_of_ge_two_fifty_six
        (N := N) (n := n) (by simpa [c] using hc256) (by simpa [c] using hc3n))

private lemma first_residual_large_root_log_le_three_halves_of_le_five_twelve_mul
    {n N : ℕ} (hn : 945 ≤ n) (hNhi : N ≤ 512 * n) :
    Nat.nthRoot 3 N * Nat.log 2 N ≤ 3 * n / 2 := by
  let c := Nat.nthRoot 3 N
  have hc3n : c ^ 3 ≤ 512 * n := by
    simpa [c] using nthRoot_three_pow_le_of_le hNhi
  by_cases hc79lt : c < 79
  · simpa [c] using
      nthRoot_three_mul_log_le_of_nthRoot_lt
        (N := N) (A := 79) (e := 19) (M := 3 * n / 2)
        (by simpa [c] using hc79lt) (by norm_num) (by norm_num) (by omega)
  exact nthRoot_three_mul_log_le_three_halves_of_ge_seventy_nine
    (by simpa [c] using Nat.le_of_not_gt hc79lt) (by simpa [c] using hc3n) hNhi

private lemma first_residual_large_exponent_le_nine_fourths {n N : ℕ}
    (hn : 945 ≤ n) (hNhi : N ≤ 512 * n) :
    Nat.sqrt N + Nat.nthRoot 3 N * Nat.log 2 N ≤ 9 * n / 4 := by
  have hsqrt : Nat.sqrt N ≤ 3 * n / 4 :=
    sqrt_le_three_mul_div_four_of_le_five_twelve_mul (by omega : 911 ≤ n) hNhi
  have hroot_log : Nat.nthRoot 3 N * Nat.log 2 N ≤ 3 * n / 2 :=
    first_residual_large_root_log_le_three_halves_of_le_five_twelve_mul hn hNhi
  omega

/-! ### Range dispatch -/

private lemma first_residual_large_cancelled_bound_range_3_4 {n N : ℕ}
    (hn : 945 ≤ n) (hNlo : 3 * n ≤ N) (hNhi : N ≤ 4 * n) :
    n * (2 ^ n * (n ^ n *
      4 ^ (Nat.sqrt N + Nat.nthRoot 3 N * Nat.log 2 N))) < N ^ n := by
  exact cancelled_bound_of_base_pow_exponent_cap_le (B := 3) (E := 4 * n / 15)
    (by omega) hNlo (first_residual_large_exponent_le_four_fifteenths hn hNhi)
    (range_3_base_exp hn)

private lemma first_residual_large_cancelled_bound_range_4_8 {n N : ℕ}
    (hn : 945 ≤ n) (hNlo : 4 * n < N) (hNhi : N ≤ 8 * n) :
    n * (2 ^ n * (n ^ n *
      4 ^ (Nat.sqrt N + Nat.nthRoot 3 N * Nat.log 2 N))) < N ^ n := by
  exact cancelled_bound_of_base_pow_exponent_cap (B := 4) (E := 2 * n / 5) (by omega)
    hNlo (first_residual_large_exponent_le_two_fifths hn hNhi) (range_4_base_exp hn)

private lemma first_residual_large_cancelled_bound_range_8_16 {n N : ℕ}
    (hn : 945 ≤ n) (hNlo : 8 * n < N) (hNhi : N ≤ 16 * n) :
    n * (2 ^ n * (n ^ n *
      4 ^ (Nat.sqrt N + Nat.nthRoot 3 N * Nat.log 2 N))) < N ^ n := by
  exact cancelled_bound_of_base_pow_exponent_cap (B := 8) (E := 3 * n / 4) (by omega)
    hNlo (first_residual_large_exponent_le_three_fourths hn hNhi) (range_8_base_exp hn)

private lemma first_residual_large_cancelled_bound_range_16_64 {n N : ℕ}
    (hn : 945 ≤ n) (hNlo : 16 * n < N) (hNhi : N ≤ 64 * n) :
    n * (2 ^ n * (n ^ n *
      4 ^ (Nat.sqrt N + Nat.nthRoot 3 N * Nat.log 2 N))) < N ^ n := by
  exact cancelled_bound_of_base_pow_exponent_cap (B := 16) (E := n) (by omega)
    hNlo (first_residual_large_exponent_le_self hn hNhi) (range_16_base_exp hn)

private lemma first_residual_large_cancelled_bound_range_64_512 {n N : ℕ}
    (hn : 945 ≤ n) (hNlo : 64 * n < N) (hNhi : N ≤ 512 * n) :
    n * (2 ^ n * (n ^ n *
      4 ^ (Nat.sqrt N + Nat.nthRoot 3 N * Nat.log 2 N))) < N ^ n := by
  exact cancelled_bound_of_base_pow_exponent_cap (B := 64) (E := 9 * n / 4) (by omega)
    hNlo (first_residual_large_exponent_le_nine_fourths hn hNhi) (range_64_base_exp hn)

private lemma first_residual_large_cancelled_bound_range_512 {n N : ℕ}
    (hn : 945 ≤ n) (hNlo : 512 * n < N) (hNhi : N ≤ n ^ 2 + n) :
    n * (2 ^ n * (n ^ n *
      4 ^ (Nat.sqrt N + Nat.nthRoot 3 N * Nat.log 2 N))) < N ^ n := by
  exact cancelled_bound_of_base_pow_exponent_cap (B := 512) (E := 3 * n) (by omega)
    hNlo (first_residual_large_exponent_le_three_mul_self hn hNhi) (range_512_base_exp n)

private lemma first_residual_large_cancelled_bound {n N : ℕ}
    (hn : 945 ≤ n) (hNlo : 3 * n ≤ N) (hNhi : N ≤ n ^ 2 + n) :
    n * (2 ^ n * (n ^ n *
      4 ^ (Nat.sqrt N + Nat.nthRoot 3 N * Nat.log 2 N))) < N ^ n := by
  by_cases hN4 : N ≤ 4 * n
  · exact first_residual_large_cancelled_bound_range_3_4 hn hNlo hN4
  by_cases hN8 : N ≤ 8 * n
  · exact first_residual_large_cancelled_bound_range_4_8 hn (by omega) hN8
  by_cases hN16 : N ≤ 16 * n
  · exact first_residual_large_cancelled_bound_range_8_16 hn (by omega) hN16
  by_cases hN64 : N ≤ 64 * n
  · exact first_residual_large_cancelled_bound_range_16_64 hn (by omega) hN64
  by_cases hN512 : N ≤ 512 * n
  · exact first_residual_large_cancelled_bound_range_64_512 hn (by omega) hN512
  exact first_residual_large_cancelled_bound_range_512 hn (by omega) hNhi

/-- Large-`n` first residual estimate: after scaling to the ternary lower bound,
the Erdős three-layer upper bound is too small throughout `3 * n ≤ N ≤ n ^ 2 + n`. -/
lemma first_residual_large_scaled_ternary_bound {n N : ℕ}
    (hn : 945 ≤ n) (hNlo : 3 * n ≤ N) (hNhi : N ≤ n ^ 2 + n) :
    n * (2 ^ n * ((3 * n) ^ n *
      4 ^ (n + Nat.sqrt N + Nat.nthRoot 3 N * Nat.log 2 N))) <
      3 ^ n * 4 ^ n * N ^ n := by
  simpa [Nat.add_assoc] using
    scaled_ternary_bound_of_cancelled (n := n) (N := N)
      (A := Nat.sqrt N + Nat.nthRoot 3 N * Nat.log 2 N)
      (first_residual_large_cancelled_bound hn hNlo hNhi)

end Internal
end Nat.SylvesterSchur
