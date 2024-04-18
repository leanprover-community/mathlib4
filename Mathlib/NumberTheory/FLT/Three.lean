/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.NumberTheory.FLT.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Int.Basic

/-!
# Fermat Last Theorem in the case `n = 3`
The goal of this file is to prove Fermat Last theorem in the case `n = 3`.

## Main results
* `fermatLastTheoremThree_case1`: the first case of Fermat Last Theorem when `n = 3`:
  if `a b c : ℤ` are such that `¬ 3 ∣ a * b * c`, then `a ^ 3 + b ^ 3 ≠ c ^ 3`.

## TODO
Prove case 2.
-/

section case1

open ZMod

private lemma cube_of_castHom_ne_zero {n : ZMod 9} :
    castHom (show 3 ∣ 9 by norm_num) (ZMod 3) n ≠ 0 → n ^ 3 = 1 ∨ n ^ 3 = 8 := by
  revert n; decide

private lemma cube_of_not_dvd {n : ℤ} (h : ¬ 3 ∣ n) :
    (n : ZMod 9) ^ 3 = 1 ∨ (n : ZMod 9) ^ 3 = 8 := by
  apply cube_of_castHom_ne_zero
  rwa [map_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- If `a b c : ℤ` are such that `¬ 3 ∣ a * b * c`, then `a ^ 3 + b ^ 3 ≠ c ^ 3`. -/
theorem fermatLastTheoremThree_case_1 {a b c : ℤ} (hdvd : ¬ 3 ∣ a * b * c) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  simp_rw [Int.prime_three.dvd_mul, not_or] at hdvd
  apply mt (congrArg (Int.cast : ℤ → ZMod 9))
  simp_rw [Int.cast_add, Int.cast_pow]
  rcases cube_of_not_dvd hdvd.1.1 with ha | ha <;>
  rcases cube_of_not_dvd hdvd.1.2 with hb | hb <;>
  rcases cube_of_not_dvd hdvd.2 with hc | hc <;>
  rw [ha, hb, hc] <;> decide

end case1

section case2

private lemma three_dvd_b_of_dvd_a_of_gcd_eq_one_of_case2 {a b c : ℤ} (ha : a ≠ 0)
    (Hgcd: Finset.gcd {a, b, c} id = 1) (h3a : 3 ∣ a) (HF : a ^ 3 + b ^ 3 + c ^ 3 = 0)
    (H : ∀ a b c : ℤ, c ≠ 0 → ¬ 3 ∣ a → ¬ 3 ∣ b  → 3 ∣ c → IsCoprime a b → a ^ 3 + b ^ 3 ≠ c ^ 3) :
    3 ∣ b := by
  have hbc : IsCoprime (-b) (-c) := by
    refine IsCoprime.neg_neg ?_
    rw [add_comm (a ^ 3), add_assoc, add_comm (a ^ 3), ← add_assoc] at HF
    refine isCoprime_of_gcd_eq_one_of_FLT ?_ HF
    convert Hgcd using 2
    rw [Finset.pair_comm, Finset.Insert.comm]
  by_contra! h3b
  by_cases h3c : 3 ∣ c
  · apply h3b
    rw [add_assoc, add_comm (b ^ 3), ← add_assoc] at HF
    exact dvd_c_of_prime_of_dvd_a_of_dvd_b_of_FLT Int.prime_three h3a h3c HF
  · refine H (-b) (-c) a ha (by simp [h3b]) (by simp [h3c]) h3a hbc ?_
    rw [add_eq_zero_iff_eq_neg, ← (show Odd 3 by decide).neg_pow] at HF
    rw [← HF]
    ring

open Finset in
private lemma fermatLastTheoremThree_of_dvd_a_of_gcd_eq_one_of_case2 {a b c : ℤ} (ha : a ≠ 0)
    (h3a : 3 ∣ a) (Hgcd: Finset.gcd {a, b, c} id = 1)
    (H : ∀ a b c : ℤ, c ≠ 0 → ¬ 3 ∣ a → ¬ 3 ∣ b  → 3 ∣ c → IsCoprime a b → a ^ 3 + b ^ 3 ≠ c ^ 3) :
    a ^ 3 + b ^ 3 + c ^ 3 ≠ 0 := by
  intro HF
  apply (show ¬(3 ∣ (1 : ℤ)) by decide)
  rw [← Hgcd]
  refine dvd_gcd (fun x hx ↦ ?_)
  simp only [mem_insert, mem_singleton] at hx
  have h3b : 3 ∣ b := by
    refine three_dvd_b_of_dvd_a_of_gcd_eq_one_of_case2 ha ?_ h3a HF H
    simp only [← Hgcd, gcd_insert, gcd_singleton, id_eq, ← Int.abs_eq_normalize, abs_neg]
  rcases hx with (hx | hx | hx)
  · exact hx ▸ h3a
  · exact hx ▸ h3b
  · simpa [hx] using dvd_c_of_prime_of_dvd_a_of_dvd_b_of_FLT Int.prime_three h3a h3b HF

open Finset Int in
/--
  To prove Fermat's Last Theorem for `n = 3`, it is enough to show that that for all `a`, `b`, `c`
  in `ℤ` such that `c ≠ 0`, `¬ 3 ∣ a`, `¬ 3 ∣ b`, `a` and `b` are coprime and `3 ∣ c`, we have
  `a ^ 3 + b ^ 3 ≠ c ^ 3`.
-/
theorem fermatLastTheoremThree_of_three_dvd_only_c
    (H : ∀ a b c : ℤ, c ≠ 0 → ¬ 3 ∣ a → ¬ 3 ∣ b  → 3 ∣ c → IsCoprime a b → a ^ 3 + b ^ 3 ≠ c ^ 3) :
    FermatLastTheoremFor 3 := by
  rw [fermatLastTheoremFor_iff_int]
  refine fermatLastTheoremWith_of_fermatLastTheoremWith_coprime (fun a b c ha hb hc Hgcd hF ↦?_)
  by_cases h1 : 3 ∣ a * b * c
  swap; exact fermatLastTheoremThree_case_1 h1 hF
  rw [(prime_three).dvd_mul, (prime_three).dvd_mul] at h1
  rw [← sub_eq_zero, sub_eq_add_neg, ← (show Odd 3 by decide).neg_pow] at hF
  rcases h1 with ((h3a | h3b) | h3c)
  · refine fermatLastTheoremThree_of_dvd_a_of_gcd_eq_one_of_case2 ha h3a ?_ H hF
    simp only [← Hgcd, Insert.comm, gcd_insert, gcd_singleton, id_eq, ← abs_eq_normalize, abs_neg]
  · rw [add_comm (a ^ 3)] at hF
    refine fermatLastTheoremThree_of_dvd_a_of_gcd_eq_one_of_case2 hb h3b ?_ H hF
    simp only [← Hgcd, Insert.comm, gcd_insert, gcd_singleton, id_eq, ← abs_eq_normalize, abs_neg]
  · rw [add_comm _ ((-c) ^ 3), ← add_assoc] at hF
    refine fermatLastTheoremThree_of_dvd_a_of_gcd_eq_one_of_case2 (neg_ne_zero.2 hc) (by simp [h3c])
      ?_ H hF
    rw [Finset.Insert.comm (-c), Finset.pair_comm (-c) b]
    simp only [← Hgcd, Insert.comm, gcd_insert, gcd_singleton, id_eq, ← abs_eq_normalize, abs_neg]

end case2
