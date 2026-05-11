/-
Copyright (c) 2026 Meta Platforms, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.Primorial
public import Mathlib.NumberTheory.SylvesterSchur.PrimeCounting

/-!
# Binomial factorization bounds for Sylvester-Schur

This file bounds binomial coefficients under the hypothesis that all prime
divisors are small, using factorization and primorial estimates.
-/

@[expose] public section

namespace Nat.SylvesterSchur

open scoped BigOperators

open Finset Nat

/-! ### Binomial factorization bounds -/

/-- If every prime divisor of `Nat.choose N r` is at most `r`, then the product formula for
`Nat.choose N r` can be truncated from primes up to `N` to candidates up to `r`. -/
theorem choose_eq_prod_small_prime_powers_of_no_large {N r : ℕ} (hrN : r ≤ N)
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ Nat.choose N r → p ≤ r) :
    (∏ p ∈ Finset.range (r + 1), p ^ (Nat.choose N r).factorization p) =
      Nat.choose N r := by
  calc
    (∏ p ∈ Finset.range (r + 1), p ^ (Nat.choose N r).factorization p)
        = ∏ p ∈ Finset.range (N + 1), p ^ (Nat.choose N r).factorization p := by
          apply Finset.prod_subset
          · intro p hp
            exact Finset.mem_range.mpr <| (Finset.mem_range.mp hp).trans_le
              (Nat.succ_le_succ hrN)
          · intro p hpN hp_not_small
            rw [Finset.mem_range] at hpN hp_not_small
            have hpr : r < p := by omega
            by_cases hp : p.Prime
            · by_cases hdvd : p ∣ Nat.choose N r
              · exact (hpr.not_ge (hsmall p hp hdvd)).elim
              · rw [Nat.factorization_eq_zero_of_not_dvd hdvd, pow_zero]
            · rw [Nat.factorization_eq_zero_of_not_prime _ hp, pow_zero]
    _ = Nat.choose N r := Nat.prod_pow_factorization_choose N r hrN

/- A first crude consequence of the previous lemma: under the same no-large-prime hypothesis,
`Nat.choose N r` is at most `N ^ (r + 1)`.  This bound is too weak for the final theorem, but it is
a useful checkpoint for the factorization part of the proof. -/
private lemma choose_le_top_pow_succ_of_no_large {N r : ℕ} (hN : 0 < N) (hrN : r ≤ N)
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ Nat.choose N r → p ≤ r) :
    Nat.choose N r ≤ N ^ (r + 1) := by
  rw [← choose_eq_prod_small_prime_powers_of_no_large hrN hsmall]
  calc
    (∏ p ∈ Finset.range (r + 1), p ^ (Nat.choose N r).factorization p)
        ≤ ∏ _p ∈ Finset.range (r + 1), N := by
          apply Finset.prod_le_prod'
          intro p hp_mem
          by_cases hp : p.Prime
          · exact Nat.pow_factorization_choose_le hN
          · rw [Nat.factorization_eq_zero_of_not_prime _ hp, pow_zero]
            exact hN
    _ = N ^ (r + 1) := by simp

/-- The same no-large-prime hypothesis gives the sharper Erdős factorization bound with exponent
`Nat.primeCounting r`. The remaining hard part of the classical proof is to contradict this bound
using lower estimates for the relevant binomial coefficient. -/
theorem choose_le_top_pow_primeCounting_of_no_large {N r : ℕ} (hN : 0 < N) (hrN : r ≤ N)
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ Nat.choose N r → p ≤ r) :
    Nat.choose N r ≤ N ^ Nat.primeCounting r := by
  rw [← choose_eq_prod_small_prime_powers_of_no_large hrN hsmall]
  calc
    (∏ p ∈ Finset.range (r + 1), p ^ (Nat.choose N r).factorization p)
        = ∏ p ∈ (Finset.range (r + 1)).filter Nat.Prime,
            p ^ (Nat.choose N r).factorization p := by
          rw [Finset.prod_filter_of_ne]
          intro p _ hp_ne_one
          by_contra hp_not_prime
          simp [Nat.factorization_eq_zero_of_not_prime _ hp_not_prime] at hp_ne_one
    _ ≤ ∏ _p ∈ (Finset.range (r + 1)).filter Nat.Prime, N := by
          exact Finset.prod_le_prod' fun p hp_mem => Nat.pow_factorization_choose_le hN
    _ = N ^ Nat.primeCounting r := by
          rw [Finset.prod_const]
          congr
          rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting' (r + 1),
            Nat.primesBelow]

/-- Replacing `Nat.primeCounting r` by the elementary bound `r - 1` gives a slightly coarser
version of the preceding no-large-prime estimate. -/
theorem choose_le_top_pow_sub_one_of_no_large {N r : ℕ} (hN : 0 < N) (hr : 2 ≤ r)
    (hrN : r ≤ N) (hsmall : ∀ p : ℕ, p.Prime → p ∣ Nat.choose N r → p ≤ r) :
    Nat.choose N r ≤ N ^ (r - 1) := by
  exact (choose_le_top_pow_primeCounting_of_no_large hN hrN hsmall).trans
    (Nat.pow_le_pow_right hN (primeCounting_le_sub_one hr))

/-- Using the already-formalized prime-counting bound `π(r) ≤ r / 2 + 1` gives a sharper
no-large-prime estimate. -/
theorem choose_le_top_pow_half_add_one_of_no_large {N r : ℕ} (hN : 0 < N) (hrN : r ≤ N)
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ Nat.choose N r → p ≤ r) :
    Nat.choose N r ≤ N ^ (r / 2 + 1) := by
  exact (choose_le_top_pow_primeCounting_of_no_large hN hrN hsmall).trans
    (Nat.pow_le_pow_right hN (primeCounting_le_half_add_one r))

/-- Using the project `π(r) ≤ 3r/8` estimate gives the corresponding no-large-prime bound. -/
theorem choose_le_top_pow_three_mul_div_eight_of_no_large {N r : ℕ} (hN : 0 < N)
    (hr : 38 ≤ r) (hrN : r ≤ N)
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ Nat.choose N r → p ≤ r) :
    Nat.choose N r ≤ N ^ (3 * r / 8) := by
  exact (choose_le_top_pow_primeCounting_of_no_large hN hrN hsmall).trans
    (Nat.pow_le_pow_right hN (primeCounting_le_three_mul_div_eight hr))

/- Fixed-layer form of the Erdős prime-power estimate.  For a fixed exponent `j`, primes whose
exponent in `Nat.choose N r` is at least `j` all lie below the `j`th root of `N`; hence their
product is bounded by the corresponding primorial. -/
private lemma layer_prime_product_le_primorial_nthRoot {N r j : ℕ} (hN : 0 < N) (hj : j ≠ 0) :
    (∏ p ∈ (Finset.range (r + 1)).filter
        (fun p => p.Prime ∧ j ≤ (Nat.choose N r).factorization p), p) ≤
      primorial (Nat.nthRoot j N) := by
  dsimp [primorial]
  apply Finset.prod_le_prod_of_subset_of_one_le'
  · intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_filter]
    have hp_prime : p.Prime := hp.2.1
    have hpow_le :
        p ^ j ≤ p ^ (Nat.choose N r).factorization p :=
      Nat.pow_le_pow_right hp_prime.one_le hp.2.2
    have hpow_top :
        p ^ (Nat.choose N r).factorization p ≤ N :=
      Nat.pow_factorization_choose_le hN
    have hp_root : p ≤ Nat.nthRoot j N :=
      (Nat.le_nthRoot_iff hj).mpr (hpow_le.trans hpow_top)
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hp_root), hp_prime⟩
  · intro p hp _hp_not
    exact (Finset.mem_filter.mp hp).2.one_le

/- Zero-based layer form: primes whose exponent is greater than `j` are controlled by the
`(j+1)`st root of `N`. -/
private lemma layer_prime_product_lt_factorization_le_primorial_nthRoot {N r j : ℕ}
    (hN : 0 < N) :
    (∏ p ∈ (Finset.range (r + 1)).filter
        (fun p => p.Prime ∧ j < (Nat.choose N r).factorization p), p) ≤
      primorial (Nat.nthRoot (j + 1) N) := by
  simpa [Nat.succ_le_iff] using
    (layer_prime_product_le_primorial_nthRoot (N := N) (r := r) (j := j + 1) hN
      (by omega))

/- The first Erdős layer: primes that occur at least once are bounded by the primorial of `r`
under the no-large-prime truncation. -/
private lemma first_layer_prime_product_le_primorial {N r : ℕ} :
    (∏ p ∈ (Finset.range (r + 1)).filter
        (fun p => p.Prime ∧ 0 < (Nat.choose N r).factorization p), p) ≤ primorial r := by
  dsimp [primorial]
  apply Finset.prod_le_prod_of_subset_of_one_le'
  · intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_filter]
    exact ⟨hp.1, hp.2.1⟩
  · intro p hp _hp_not
    exact (Finset.mem_filter.mp hp).2.one_le

private lemma first_layer_prime_product_le_primorial_div_three_aux {N r : ℕ}
    (h2rN : 2 * r ≤ N) (hN6 : 6 ≤ N) :
    (∏ p ∈ (Finset.range (r + 1)).filter
        (fun p => p.Prime ∧ 0 < (Nat.choose N r).factorization p), p) ≤
      primorial (N / 3) := by
  dsimp [primorial]
  apply Finset.prod_le_prod_of_subset_of_one_le'
  · intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_filter]
    have hp_prime : p.Prime := hp.2.1
    have hp_le_r : p ≤ r := by
      rw [Finset.mem_range] at hp
      omega
    have hp_le_sub : p ≤ N - r := by omega
    have hp_le_div : p ≤ N / 3 := by
      by_cases hp2 : p = 2
      · subst hp2
        omega
      · have hnot : ¬ N < 3 * p := by
          intro hlt
          have hzero :
              (Nat.choose N r).factorization p = 0 :=
            Nat.factorization_choose_of_lt_three_mul hp2 hp_le_r hp_le_sub hlt
          omega
        have hle : 3 * p ≤ N := by omega
        omega
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hp_le_div), hp_prime⟩
  · intro p hp _hp_not
    exact (Finset.mem_filter.mp hp).2.one_le

/- Central-range first layer.  If `2 * r ≤ N < 3 * r`, then every prime `p ≤ r`
that divides `Nat.choose N r` is at most `N / 3`.  This is the formal version of
Erdős's observation in the `2r < N < 3r` case, using Mathlib's
`Nat.factorization_choose_of_lt_three_mul`. -/
private lemma first_layer_central_prime_product_le_primorial_div_three {N r : ℕ}
    (h2rN : 2 * r ≤ N) (_hNlt3r : N < 3 * r) (hN6 : 6 ≤ N) :
    (∏ p ∈ (Finset.range (r + 1)).filter
        (fun p => p.Prime ∧ 0 < (Nat.choose N r).factorization p), p) ≤
      primorial (N / 3) := by
  exact first_layer_prime_product_le_primorial_div_three_aux h2rN hN6

/- First-layer `N / 3` bound without a central-range assumption.  If `2 * r ≤ N`, then
every prime `p ≤ r` in the first layer of `Nat.choose N r` is at most `N / 3` (apart from
`p = 2`, which is also at most `N / 3` once `6 ≤ N`). -/
private lemma first_layer_prime_product_le_primorial_div_three {N r : ℕ}
    (h2rN : 2 * r ≤ N) (hN6 : 6 ≤ N) :
    (∏ p ∈ (Finset.range (r + 1)).filter
        (fun p => p.Prime ∧ 0 < (Nat.choose N r).factorization p), p) ≤
      primorial (N / 3) := by
  exact first_layer_prime_product_le_primorial_div_three_aux h2rN hN6

/- Product over the first `L` layers with membership `j < e` is exactly `p ^ e`, provided
`e ≤ L`. -/
private lemma prod_range_ite_lt_eq_pow (p e L : ℕ) (heL : e ≤ L) :
    (∏ j ∈ Finset.range L, if j < e then p else 1) = p ^ e := by
  rw [← Finset.prod_filter (s := Finset.range L) (p := fun j => j < e) (f := fun _ => p)]
  have hfilter : (Finset.range L).filter (fun j => j < e) = Finset.range e := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfilter, Finset.prod_const, Finset.card_range]

private lemma choose_eq_prod_prime_factorization_layers {N r : ℕ} (hrN : r ≤ N)
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ Nat.choose N r → p ≤ r) :
    Nat.choose N r =
      ∏ j ∈ Finset.range (Nat.log 2 N),
        ∏ p ∈ ((Finset.range (r + 1)).filter Nat.Prime).filter
          (fun p => j < (Nat.choose N r).factorization p), p := by
  classical
  conv_lhs => rw [← choose_eq_prod_small_prime_powers_of_no_large hrN hsmall]
  let S : Finset ℕ := (Finset.range (r + 1)).filter Nat.Prime
  calc
    (∏ p ∈ Finset.range (r + 1), p ^ (Nat.choose N r).factorization p)
        = ∏ p ∈ S, p ^ (Nat.choose N r).factorization p := by
          dsimp [S]
          exact (Finset.prod_filter_of_ne
            (s := Finset.range (r + 1)) (p := Nat.Prime)
            (f := fun p => p ^ (Nat.choose N r).factorization p)
            (by
              intro p _ hp_ne_one
              change p ^ (Nat.choose N r).factorization p ≠ 1 at hp_ne_one
              by_contra hp_not_prime
              simp [Nat.factorization_eq_zero_of_not_prime _ hp_not_prime] at hp_ne_one)).symm
    _ = ∏ p ∈ S, ∏ j ∈ Finset.range (Nat.log 2 N),
          if j < (Nat.choose N r).factorization p then p else 1 := by
          apply Finset.prod_congr rfl
          intro p hp
          dsimp [S] at hp
          rw [Finset.mem_filter] at hp
          exact (prod_range_ite_lt_eq_pow p ((Nat.choose N r).factorization p)
            (Nat.log 2 N)
            (Nat.factorization_choose_le_log.trans
              (Nat.log_anti_left Nat.one_lt_two hp.2.two_le))).symm
    _ = ∏ j ∈ Finset.range (Nat.log 2 N), ∏ p ∈ S,
          if j < (Nat.choose N r).factorization p then p else 1 := by
          exact Finset.prod_comm
    _ = ∏ j ∈ Finset.range (Nat.log 2 N),
          ∏ p ∈ S.filter (fun p => j < (Nat.choose N r).factorization p), p := by
          apply Finset.prod_congr rfl
          intro j hj
          exact (Finset.prod_filter
            (s := S) (p := fun p => j < (Nat.choose N r).factorization p)
            (f := fun p => p)).symm

/-- Full Erdős prime-power layer bound. Under the no-large-prime hypothesis, the binomial
coefficient is bounded by the product of primorials at successive roots of `N`. -/
theorem choose_le_prod_primorial_nthRoot_of_no_large {N r : ℕ} (hN : 0 < N)
    (hrN : r ≤ N) (hsmall : ∀ p : ℕ, p.Prime → p ∣ Nat.choose N r → p ≤ r) :
    Nat.choose N r ≤
      ∏ j ∈ Finset.range (Nat.log 2 N), primorial (Nat.nthRoot (j + 1) N) := by
  classical
  rw [choose_eq_prod_prime_factorization_layers hrN hsmall]
  exact Finset.prod_le_prod' fun j hj => by
    have hlayer := layer_prime_product_lt_factorization_le_primorial_nthRoot
      (N := N) (r := r) (j := j) hN
    simpa [Finset.filter_filter, and_assoc, and_left_comm, and_comm] using hlayer

/-- Sharpened full Erdős layer bound.  The first layer uses the no-large-prime cutoff `r`;
subsequent layers use the root bounds.  This matches the product estimate in Erdős's proof. -/
theorem choose_le_prod_erdos_layers_of_no_large {N r : ℕ} (hN : 0 < N)
    (hrN : r ≤ N) (hsmall : ∀ p : ℕ, p.Prime → p ∣ Nat.choose N r → p ≤ r) :
    Nat.choose N r ≤
      ∏ j ∈ Finset.range (Nat.log 2 N),
        if j = 0 then primorial r else primorial (Nat.nthRoot (j + 1) N) := by
  classical
  rw [choose_eq_prod_prime_factorization_layers hrN hsmall]
  exact Finset.prod_le_prod' fun j hj => by
    by_cases hj0 : j = 0
    · subst hj0
      have hlayer := first_layer_prime_product_le_primorial (N := N) (r := r)
      simpa [Finset.filter_filter, and_assoc, and_left_comm, and_comm] using hlayer
    · have hlayer := layer_prime_product_lt_factorization_le_primorial_nthRoot
        (N := N) (r := r) (j := j) hN
      simpa [hj0, Finset.filter_filter, and_assoc, and_left_comm, and_comm] using hlayer

/-- Sharpened Erdős layer bound in the central range `2 * r ≤ N < 3 * r`.  The first
layer is bounded by `primorial (N / 3)` rather than `primorial r`. -/
theorem choose_le_prod_erdos_central_layers_of_no_large {N r : ℕ} (hN : 0 < N)
    (hrN : r ≤ N) (h2rN : 2 * r ≤ N) (hNlt3r : N < 3 * r) (hN6 : 6 ≤ N)
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ Nat.choose N r → p ≤ r) :
    Nat.choose N r ≤
      ∏ j ∈ Finset.range (Nat.log 2 N),
        if j = 0 then primorial (N / 3) else primorial (Nat.nthRoot (j + 1) N) := by
  classical
  rw [choose_eq_prod_prime_factorization_layers hrN hsmall]
  exact Finset.prod_le_prod' fun j hj => by
    by_cases hj0 : j = 0
    · subst hj0
      have hlayer :=
        first_layer_central_prime_product_le_primorial_div_three
          (N := N) (r := r) h2rN hNlt3r hN6
      simpa [Finset.filter_filter, and_assoc, and_left_comm, and_comm] using hlayer
    · have hlayer := layer_prime_product_lt_factorization_le_primorial_nthRoot
        (N := N) (r := r) (j := j) hN
      simpa [hj0, Finset.filter_filter, and_assoc, and_left_comm, and_comm] using hlayer

/-- Sharpened Erdős layer bound with the `N / 3` first layer.  Unlike
`choose_le_prod_erdos_central_layers_of_no_large`, this form does not assume `N < 3 * r`;
the first-layer cutoff follows from `Nat.factorization_choose_of_lt_three_mul`. -/
theorem choose_le_prod_erdos_div_three_layers_of_no_large {N r : ℕ} (hN : 0 < N)
    (hrN : r ≤ N) (h2rN : 2 * r ≤ N) (hN6 : 6 ≤ N)
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ Nat.choose N r → p ≤ r) :
    Nat.choose N r ≤
      ∏ j ∈ Finset.range (Nat.log 2 N),
        if j = 0 then primorial (N / 3) else primorial (Nat.nthRoot (j + 1) N) := by
  classical
  rw [choose_eq_prod_prime_factorization_layers hrN hsmall]
  exact Finset.prod_le_prod' fun j hj => by
    by_cases hj0 : j = 0
    · subst hj0
      have hlayer :=
        first_layer_prime_product_le_primorial_div_three (N := N) (r := r) h2rN hN6
      simpa [Finset.filter_filter, and_assoc, and_left_comm, and_comm] using hlayer
    · have hlayer := layer_prime_product_lt_factorization_le_primorial_nthRoot
        (N := N) (r := r) (j := j) hN
      simpa [hj0, Finset.filter_filter, and_assoc, and_left_comm, and_comm] using hlayer

end Nat.SylvesterSchur
