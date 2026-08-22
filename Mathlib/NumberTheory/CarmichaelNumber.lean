/-
Copyright (c) 2026 Felix Pernegger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Pernegger
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
public import Mathlib.NumberTheory.FermatPsp
public import Mathlib.Tactic.Simproc.Factors

/-!
# Carmichael numbers

This file defines Carmichael numbers and proves Korselt's criterion about them.

## Main definitions

* `Nat.IsCarmichael`: a predicate for Carmicheal numbers

## Main results

* `Nat.IsCarmichael_iff_korselt`: Korselt's criterion for Carmichael numbers
* `Nat.isCarmichael_561`: `561` is a Carmichael number

## TODO

* Prove (in computationally efficient manner) that there are no Carmichael numbers less than `561`.

## References

https://en.wikipedia.org/wiki/Carmichael_number

-/

public section

namespace Nat

open ArithmeticFunction

/-- We say a natural number `n` is a Carmichael number if it is greater than 2, composite and
for all natural number `b` coprime to `n` we have `n ∣ b ^ (n - 1) - 1`. -/
@[expose]
def IsCarmichael (n : ℕ) : Prop :=
  2 < n ∧ ¬ n.Prime ∧ ∀ b, b.Coprime n → ProbablePrime n b

variable {n : ℕ}

theorem IsCarmichael.two_lt (h : n.IsCarmichael) : 2 < n := h.1

theorem IsCarmichael.not_prime (h : n.IsCarmichael) : ¬ n.Prime := h.2.1

theorem IsCarmichael.probablePrime_of_coprime {b : ℕ} (h : n.IsCarmichael) (hb : b.Coprime n) :
    ProbablePrime n b := h.2.2 b hb

theorem Prime.not_isCarmichael (hn : n.Prime) : ¬ n.IsCarmichael := by
  contrapose hn
  exact hn.not_prime

@[simp]
theorem not_isCarmichael_zero : ¬ IsCarmichael 0 := by
  intro h
  simpa using h.two_lt

@[simp]
theorem not_isCarmichael_one : ¬ IsCarmichael 1 := by
  intro h
  simpa using h.two_lt

-- TODO: move this to a more appropriate file
lemma sub_one_pow_mod {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    (n - 1) ^ k % n = if Odd k then n - 1 else 1 := by
  induction k with
  | zero => simp [mod_eq_of_lt hn]
  | succ k ih =>
    simp only [pow_succ, mul_mod, ih, self_sub_mod, ite_mul, one_mul]
    by_cases hk : Odd k
    · simp only [hk, ↓reduceIte, not_odd_iff_even.mpr hk.add_one, mod_eq_iff]
      refine Or.inr ⟨lt_of_succ_le hn, n - 2, ?_⟩
      rw [Nat.mul_sub, Nat.mul_sub, mul_one, Nat.sub_mul, one_mul, Nat.sub_sub,
        self_add_sub_one n, mul_comm 2, tsub_tsub_assoc (by gcongr)]
      lia
    · simp [hk, not_even_iff_odd.mpr (not_odd_iff_even.mp hk).add_one]

-- TODO: move this to a more appropriate file
lemma pow_mod_succ {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    n ^ k % (n + 1) = if Odd k then n else 1 :=
  sub_one_pow_mod (n := n + 1) (by lia) k

/-- A Carmichael number is odd. -/
theorem IsCarmichael.odd (h : n.IsCarmichael) : Odd n := by
  have : n.ProbablePrime (n - 1) := h.probablePrime_of_coprime (b := n - 1)
    <| (coprime_self_sub_left (by grind [h.two_lt])).mpr (by simp)
  rw [ProbablePrime, dvd_iff_mod_eq_zero, ← mod_sub_of_le] at this
  · rw [sub_one_pow_mod h.two_lt.le] at this
    contrapose! this
    simp_rw [(odd_sub' (m := n) (n := 1) (by grind [h.two_lt.le])).mpr (by simp_all)]
    exact Nat.sub_ne_zero_iff_lt.mpr <| lt_sub_of_add_lt h.two_lt
  · rw [sub_one_pow_mod h.two_lt.le]
    by_cases h0 : Odd (n - 1)
    · simp [h0]
      grind [h.two_lt]
    · simp [h0]

lemma IsCarmichael.zmod_unit_pow_sub_one (s : (ZMod n)ˣ) (hn : n.IsCarmichael) :
  s ^ (n - 1) = 1 := by
  have _ : NeZero n := ⟨by grind [hn.two_lt]⟩
  have suf : (↑s : ZMod n).val ^ (n - 1) ≡ 1 [MOD n] := by
    apply (probablePrime_iff_modEq n ?_).mp <|
      hn.probablePrime_of_coprime (ZMod.val_coe_unit_coprime s)
    rw [one_le_iff_ne_zero]
    intro hs0
    have h_coprime := ZMod.val_coe_unit_coprime s
    rw [hs0, coprime_zero_left] at h_coprime
    grind [hn.two_lt]
  ext
  simp [← cast_one (R := ZMod n), ← (ZMod.natCast_eq_natCast_iff ..).mpr suf]

/-- A Carmichael number is squarefree. -/
theorem IsCarmichael.squarefree (h : n.IsCarmichael) : Squarefree n := by
  intro k hk
  rw [isUnit_iff_eq_one]
  contrapose! hk
  intro hn
  obtain ⟨p, hp, pk⟩ := ne_one_iff_exists_prime_dvd.mp hk
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have : NeZero n := ⟨by grind [h.two_lt]⟩
  have p_dvd : p * p ∣ n := dvd_trans (by gcongr) hn
  have p_odd : Odd p := h.odd.of_dvd_nat <| dvd_trans (p.dvd_mul_left p) p_dvd
  have h_cyclic : IsCyclic (ZMod (p ^ 2))ˣ :=
    (ZMod.isCyclic_units_iff_of_odd p_odd.pow).mpr ⟨p, 2, hp, p_odd, rfl⟩
  obtain ⟨r, hr⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp h_cyclic
  rw [card_eq_fintype_card, ZMod.card_units_eq_totient] at hr
  have p_sq_dvd : p ^ 2 ∣ n := by simpa [pow_two] using p_dvd
  obtain ⟨s, hs⟩ := ZMod.unitsMap_surjective p_sq_dvd r
  have r_pow : r ^ (n - 1) = 1 := by rw [← hs, ← map_pow, h.zmod_unit_pow_sub_one, map_one]
  have phi_dvd : φ (p ^ 2) ∣ n - 1 := by
    rw [← hr]
    exact orderOf_dvd_of_pow_eq_one r_pow
  have p_dvd_sub : p ∣ n - 1 := dvd_trans (by simp [totient_prime_pow_succ hp 1]) phi_dvd
  apply hp.ne_one
  exact eq_one_of_dvd_coprimes ((coprime_self_sub_left (by grind [h.two_lt])).mpr (by simp))
    p_dvd_sub (dvd_trans (p.dvd_mul_right p) p_dvd)

theorem IsCarmichael.carmichael_dvd_pred (h : n.IsCarmichael) : carmichael n ∣ n - 1 := by
  have : NeZero n := ⟨by grind [h.two_lt]⟩
  rw [carmichael_eq_exponent']
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro s
  exact h.zmod_unit_pow_sub_one s

theorem IsCarmichael.prime_sub_one_dvd {p : ℕ} (h : n.IsCarmichael) (hp : p.Prime) (hpn : p ∣ n) :
    p - 1 ∣ n - 1 := by
  refine dvd_trans ?_ h.carmichael_dvd_pred
  rw [← carmichael_of_prime hp]
  exact carmichael_dvd (by simpa using hpn)

/-- **Korselt's criterion** for Carmichael numbers:
`n` is a Carmichael number if and only if it is greater than two, composite, sqaurefree and for all
of for each prime divisor `p`, we have `p - 1 ∣ n - 1`. -/
theorem isCarmichael_iff_korselt :
    n.IsCarmichael ↔ 2 < n ∧ ¬n.Prime ∧ Squarefree n ∧ ∀ p, p.Prime → p ∣ n → p - 1 ∣ n - 1 := by
  refine ⟨fun h ↦ ⟨h.two_lt, h.not_prime, h.squarefree, fun _ ↦ h.prime_sub_one_dvd⟩, ?_⟩
  intro ⟨hn, hn_prime, hn_squarefree, h_dvd⟩
  have : NeZero n := ⟨by lia⟩
  refine ⟨hn, hn_prime, fun b hb ↦ ?_⟩
  rw [probablePrime_iff_modEq n (show 1 ≤ b by grind)]
  have carmichael_dvd : carmichael n ∣ n - 1 := by
    rw [carmichael_factorization]
    apply Finset.lcm_dvd
    intro p hp_mem
    rw [mem_primeFactors] at hp_mem
    rw [factorization_eq_one_of_squarefree hn_squarefree hp_mem.1 hp_mem.2.1, pow_one,
      carmichael_of_prime hp_mem.1]
    exact h_dvd p hp_mem.1 hp_mem.2.1
  obtain ⟨d, hd⟩ := carmichael_dvd
  have hb_pow : (ZMod.unitOfCoprime b hb) ^ (n - 1) = 1 := by
    rw [hd, pow_mul, pow_carmichael, one_pow]
  have h_cast : (b : ZMod n) ^ (n - 1) = 1 := by
    simpa using congrArg Units.val hb_pow
  apply (ZMod.natCast_eq_natCast_iff ..).mp
  simp [h_cast]

/-- **Korselt's criterion** stated in a form suitable for concrete calculations. -/
theorem isCarmichael_iff_korselt_primeFactorsList :
    n.IsCarmichael ↔
      2 < n ∧ ¬n.Prime ∧ n.primeFactorsList.Nodup ∧ ∀ p ∈ n.primeFactorsList, p - 1 ∣ n - 1 := by
  simp only [isCarmichael_iff_korselt, mem_primeFactorsList', ne_eq, and_imp, and_congr_right_iff]
  intro hn
  rw [squarefree_iff_nodup_primeFactorsList] <;> grind

/-- 561 is a Carmichael number. -/
theorem isCarmichael_561 : IsCarmichael 561 := by
  simp [isCarmichael_iff_korselt_primeFactorsList]
  norm_num

/-- 1105 is a Carmichael number. -/
theorem isCarmichael_1105 : IsCarmichael 1105 := by
  simp [isCarmichael_iff_korselt_primeFactorsList]
  norm_num

end Nat
