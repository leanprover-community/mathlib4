/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
import Mathlib.NumberTheory.FermatPsp
import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
import Mathlib.Data.Nat.Squarefree
import Mathlib.GroupTheory.Exponent

/-!
# Korselt's Criterion for Carmichael Numbers

This module formalizes and machine-checks Korselt's Criterion (1899) for Carmichael numbers
in Lean 4, leveraging Mathlib's pre-existing Carmichael lambda function
(`Mathlib.NumberTheory.ArithmeticFunction.Carmichael`).

## Mathematical Strategy: The Tripartite Equivalence

For any composite integer `n > 1`, we establish:
`Nat.Carmichael n 鈫?ArithmeticFunction.carmichael n 鈭?n - 1 鈫?Korselt Condition`.

## Main Results

- `Nat.carmichael_iff_carmichael_dvd`: Step 1 bridging `Nat.Carmichael` with `carmichael n 鈭?n - 1`.
- `Nat.carmichael_dvd_iff_korselt`: Step 2 bridging `carmichael n 鈭?n - 1` with Korselt's condition.
- `Nat.carmichael_iff_korselt`: Step 3 (Main Theorem: Korselt's Criterion).

## References

* A. Korselt, *Probl猫me chinois*, L'Interm茅diaire des Math茅maticiens 6 (1899), 142鈥?43.
-/

open ArithmeticFunction

namespace Nat

/-- **Step 1**: A composite natural number `n > 1` is a Carmichael number if and only if
the Carmichael function `carmichael n` divides `n - 1`. -/
theorem carmichael_iff_carmichael_dvd (n : 鈩? (hn : 1 < n) (hcomp : 卢 n.Prime) :
    Nat.Carmichael n 鈫?ArithmeticFunction.carmichael n 鈭?n - 1 := by
  have hn0 : n 鈮?0 := by lia
  have : NeZero n := 鉄╤n0鉄?
  have h_exp : ArithmeticFunction.carmichael n = Monoid.exponent (ZMod n)耍 :=
    carmichael_eq_exponent hn0
  rw [h_exp, Monoid.exponent_dvd_iff_forall_pow_eq_one]
  constructor
  路 intro hc g
    have hcop := ZMod.val_coe_unit_coprime g
    have hpp := hc.probablePrime hcop
    dsimp [ProbablePrime] at hpp
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    rw [鈫?ZMod.natCast_zmod_val (g : ZMod n)]
    rw [鈫?Nat.cast_pow]
    have hb_pos : 1 鈮?(g : ZMod n).val := by
      by_contra! h0
      have hz : (g : ZMod n).val = 0 := by lia
      rw [hz, Nat.Coprime, Nat.gcd_zero_left] at hcop
      subst hcop
      lia
    have hpow_ge : 1 鈮?(g : ZMod n).val ^ (n - 1) :=
      Nat.one_le_pow (n - 1) _ hb_pos
    have hmodeq : 1 鈮?(g : ZMod n).val ^ (n - 1) [MOD n] :=
      Nat.modEq_of_dvd' hpow_ge hpp
    rw [鈫?Nat.cast_one (R := ZMod n)]
    exact ((ZMod.natCast_eq_natCast_iff 1 ((g : ZMod n).val ^ (n - 1)) n).mpr hmodeq).symm
  路 intro hg
    refine 鉄╤comp, hn, fun b hb 鈫??_鉄?
    dsimp [ProbablePrime]
    let u : (ZMod n)耍 := ZMod.unitOfCoprime b hb
    have hu := hg u
    have hu_val : ((u ^ (n - 1) : (ZMod n)耍) : ZMod n) = (1 : ZMod n) := by
      rw [hu, Units.val_one]
    rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime b hb, 鈫?Nat.cast_pow,
      鈫?Nat.cast_one (R := ZMod n)] at hu_val
    have hmodeq : (b ^ (n - 1) : 鈩? 鈮?1 [MOD n] :=
      (ZMod.natCast_eq_natCast_iff (b ^ (n - 1)) 1 n).mp hu_val
    exact hmodeq.symm.dvd'

/-- The Carmichael function of a prime `p` is `p - 1`. -/
lemma carmichael_prime {p : 鈩晑 (hp : p.Prime) : ArithmeticFunction.carmichael p = p - 1 := by
  by_cases hp2 : p = 2
  路 subst hp2
    have h2 : (2 : 鈩? = 2 ^ 1 := by rfl
    rw [h2, carmichael_two_pow_of_le_two (by decide)]
    rfl
  路 have hp1 : (p : 鈩? = p ^ 1 := by rw [pow_one]
    rw [hp1, carmichael_pow_of_prime_ne_two 1 hp hp2, pow_one, Nat.totient_prime hp]

/-- For any prime `p` and power `k 鈮?1`, `p - 1` divides `carmichael (p ^ k)`. -/
lemma prime_sub_one_dvd_carmichael_pow {p : 鈩晑 (hp : p.Prime) {k : 鈩晑 (hk : 1 鈮?k) :
    p - 1 鈭?ArithmeticFunction.carmichael (p ^ k) := by
  by_cases hp2 : p = 2
  路 subst hp2
    have : 2 - 1 = 1 := rfl
    rw [this]
    exact one_dvd _
  路 rw [carmichael_pow_of_prime_ne_two k hp hp2, totient_prime_pow hp hk]
    exact 鉄╬ ^ (k - 1), mul_comm _ _鉄?

/-- For any prime `p` and power `k 鈮?2`, `p` divides `carmichael (p ^ k)`. -/
lemma prime_dvd_carmichael_pow_of_two_le {p : 鈩晑 (hp : p.Prime) {k : 鈩晑 (hk : 2 鈮?k) :
    p 鈭?ArithmeticFunction.carmichael (p ^ k) := by
  by_cases hp2 : p = 2
  路 subst hp2
    by_cases hk2 : k = 2
    路 subst hk2
      rw [carmichael_two_pow_of_le_two (by decide)]
      exact dvd_rfl
    路 rw [carmichael_two_pow_of_ne_two hk2]
      exact dvd_pow_self 2 (by lia)
  路 rw [carmichael_pow_of_prime_ne_two k hp hp2, totient_prime_pow hp (by lia)]
    have hdvd : p 鈭?p ^ (k - 1) := dvd_pow_self p (by lia)
    exact dvd_mul_of_dvd_left hdvd (p - 1)

/-- If `p 鈭?n` and `p 鈭?n - 1` with `1 鈮?n`, then `p 鈭?1`. -/
lemma dvd_one_of_dvd_and_dvd_sub_one {p n : 鈩晑 (hpn : p 鈭?n) (hpn1 : p 鈭?n - 1) (hn : 1 鈮?n) :
    p 鈭?1 := by
  have h_add : (n - 1) + 1 = n := Nat.sub_add_cancel hn
  have hp_add : p 鈭?(n - 1) + 1 := h_add.symm 鈻?hpn
  exact (Nat.dvd_add_right hpn1).mp hp_add

/-- **Step 2**: The Carmichael function divides `n - 1` if and only if `n` is square-free
and `p - 1 鈭?n - 1` for all prime divisors `p 鈭?n`. -/
theorem carmichael_dvd_iff_korselt (n : 鈩? (hn : 1 < n) :
    ArithmeticFunction.carmichael n 鈭?n - 1 鈫?
    Squarefree n 鈭?鈭� p : 鈩? p.Prime 鈫?p 鈭?n 鈫?(p - 1) 鈭?(n - 1) := by
  have hn0 : n 鈮?0 := by lia
  have : NeZero n := 鉄╤n0鉄?
  rw [carmichael_factorization n]
  constructor
  路 intro h_div
    have h_korselt : 鈭� p : 鈩? p.Prime 鈫?p 鈭?n 鈫?(p - 1) 鈭?(n - 1) := by
      intro p hp hpn
      have hp_mem : p 鈭?n.primeFactors := by
        rw [Nat.mem_primeFactors]
        exact 鉄╤p, hpn, hn0鉄?
      have hdvd_lcm : carmichael (p ^ n.factorization p) 鈭?
          n.primeFactors.lcm fun q 鈫?carmichael (q ^ n.factorization q) :=
        Finset.dvd_lcm hp_mem
      have hdvd_total : carmichael (p ^ n.factorization p) 鈭?n - 1 :=
        hdvd_lcm.trans h_div
      have h1le : 1 鈮?n.factorization p :=
        (hp.dvd_iff_one_le_factorization hn0).mp hpn
      have hp_sub : p - 1 鈭?carmichael (p ^ n.factorization p) :=
        prime_sub_one_dvd_carmichael_pow hp h1le
      exact hp_sub.trans hdvd_total
    refine 鉄?_, h_korselt鉄?
    rw [squarefree_iff_factorization_le_one hn0]
    intro p
    by_cases hp : p.Prime
    路 by_contra! h2le
      have hpn : p 鈭?n := by
        rw [hp.dvd_iff_one_le_factorization hn0]
        lia
      have hp_mem : p 鈭?n.primeFactors := by
        rw [Nat.mem_primeFactors]
        exact 鉄╤p, hpn, hn0鉄?
      have hdvd_lcm : carmichael (p ^ n.factorization p) 鈭?
          n.primeFactors.lcm fun q 鈫?carmichael (q ^ n.factorization q) :=
        Finset.dvd_lcm hp_mem
      have hdvd_total : carmichael (p ^ n.factorization p) 鈭?n - 1 :=
        hdvd_lcm.trans h_div
      have hp_dvd : p 鈭?carmichael (p ^ n.factorization p) :=
        prime_dvd_carmichael_pow_of_two_le hp h2le
      have hp_dvd_n1 : p 鈭?n - 1 := hp_dvd.trans hdvd_total
      have hp_dvd_one : p 鈭?1 := dvd_one_of_dvd_and_dvd_sub_one hpn hp_dvd_n1 (by lia)
      exact hp.not_dvd_one hp_dvd_one
    路 rw [factorization_eq_zero_of_not_prime _ hp]
      exact zero_le_one
  路 rintro 鉄╤_sq, h_korselt鉄?
    rw [Finset.lcm_dvd_iff]
    intro p hp_mem
    rw [Nat.mem_primeFactors] at hp_mem
    rcases hp_mem with 鉄╤p, hpn, -鉄?
    have h_fac : n.factorization p = 1 :=
      factorization_eq_one_of_squarefree h_sq hp hpn
    rw [h_fac, pow_one, carmichael_prime hp]
    exact h_korselt p hp hpn

/-- **Korselt's Criterion (1899)**: A composite positive integer `n > 1` is a Carmichael number
if and only if `n` is square-free and `p - 1 鈭?n - 1` for all prime divisors `p 鈭?n`. -/
theorem carmichael_iff_korselt (n : 鈩? (hn : 1 < n) (hcomp : 卢 n.Prime) :
    Nat.Carmichael n 鈫?Squarefree n 鈭?鈭� p : 鈩? p.Prime 鈫?p 鈭?n 鈫?(p - 1) 鈭?(n - 1) :=
  (carmichael_iff_carmichael_dvd n hn hcomp).trans (carmichael_dvd_iff_korselt n hn)

end Nat

export Nat (carmichael_iff_carmichael_dvd carmichael_dvd_iff_korselt carmichael_iff_korselt)
