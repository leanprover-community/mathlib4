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

* Prove (in a computationally efficient manner) that there are no Carmichael numbers
  less than `561`.

## References

https://en.wikipedia.org/wiki/Carmichael_number

-/

public section

namespace Nat

open ArithmeticFunction

/-- We say a natural number `n` is a Carmichael number if it is greater than 2, composite and
for all natural numbers `b` coprime to `n` we have `n ∣ b ^ (n - 1) - 1`. -/
@[expose]
def IsCarmichael (n : ℕ) : Prop :=
  2 < n ∧ ¬ n.Prime ∧ ∀ b, b.Coprime n → ProbablePrime n b

variable {n : ℕ}

theorem IsCarmichael.two_lt (h : n.IsCarmichael) : 2 < n := h.1

theorem IsCarmichael.neZero (h : n.IsCarmichael) : NeZero n :=
  ⟨by grind [h.two_lt]⟩

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

lemma IsCarmichael.zmod_unit_pow_sub_one (s : (ZMod n)ˣ) (hn : n.IsCarmichael) :
  s ^ (n - 1) = 1 := by
  have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by grind [hn.two_lt])
  ext
  have : NeZero n := hn.neZero
  rw [Units.val_one, Units.val_pow_eq_pow_val, ← ZMod.natCast_zmod_val s.val,
    ← probablePrime_iff_zmod_one n (by simp [Units.ne_zero s])]
  exact hn.probablePrime_of_coprime <| ZMod.val_coe_unit_coprime s

/-- A Carmichael number is odd. -/
theorem IsCarmichael.odd (h : n.IsCarmichael) : Odd n := by
  match n with
  | 0 => exact (not_isCarmichael_zero h).elim
  | n + 1 =>
    have H := h.zmod_unit_pow_sub_one (-1)
    rw [Nat.add_one_sub_one, neg_one_pow_eq_ite] at H
    contrapose! H
    rw [ite_eq_right (by grind), ne_eq, Units.ext_iff, Units.val_one, Units.coe_neg_one,
      ZMod.neg_one_eq_one_iff]
    grind [h.two_lt]

/-- A Carmichael number is squarefree. -/
theorem IsCarmichael.squarefree (h : n.IsCarmichael) : Squarefree n := by
  refine squarefree_iff_prime_squarefree.mpr fun p hp p_dvd ↦ ?_
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have p_odd : Odd p := h.odd.of_dvd_nat <| dvd_trans (p.dvd_mul_left p) p_dvd
  obtain ⟨r, hr⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp <|
    (ZMod.isCyclic_units_iff_of_odd p_odd.pow).mpr ⟨p, 2, hp, p_odd, rfl⟩
  rw [card_eq_fintype_card, ZMod.card_units_eq_totient] at hr
  have : NeZero n := h.neZero
  obtain ⟨s, hs⟩ := ZMod.unitsMap_surjective (pow_two p ▸ p_dvd) r
  have phi_dvd : φ (p ^ 2) ∣ n - 1 := by
    rw [← hr, ← hs]
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, h.zmod_unit_pow_sub_one, map_one]
  have p_dvd_n : p ∣ n := dvd_trans (dvd_mul_left p p) p_dvd
  refine hp.not_dvd_one <| dvd_sub_iff_right (by grind [h.two_lt]) p_dvd_n |>.mp ?_
  exact dvd_trans (by simp [totient_prime_pow_succ hp 1]) phi_dvd

theorem IsCarmichael.carmichael_dvd_sub_one (h : n.IsCarmichael) : carmichael n ∣ n - 1 := by
  rw [@carmichael_eq_exponent' n h.neZero]
  exact Monoid.exponent_dvd_of_forall_pow_eq_one h.zmod_unit_pow_sub_one

theorem IsCarmichael.prime_sub_one_dvd {p : ℕ} (h : n.IsCarmichael) (hp : p.Prime) (hpn : p ∣ n) :
    p - 1 ∣ n - 1 := by
  refine dvd_trans ?_ h.carmichael_dvd_sub_one
  rw [← carmichael_of_prime hp]
  exact carmichael_dvd (by simpa using hpn)

/-- **Korselt's criterion** for Carmichael numbers:
`n` is a Carmichael number if and only if it is greater than two, composite, squarefree, and for
each prime divisor `p` of `n`, we have `p - 1 ∣ n - 1`. -/
theorem isCarmichael_iff_korselt :
    n.IsCarmichael ↔ 2 < n ∧ ¬n.Prime ∧ Squarefree n ∧ ∀ p, p.Prime → p ∣ n → p - 1 ∣ n - 1 := by
  refine ⟨fun h ↦ ⟨h.two_lt, h.not_prime, h.squarefree, fun _ ↦ h.prime_sub_one_dvd⟩, ?_⟩
  intro ⟨hn, hn_prime, hn_squarefree, h_dvd⟩
  refine ⟨hn, hn_prime, fun b hb ↦ ?_⟩
  obtain ⟨d, hd⟩ : carmichael n ∣ n - 1 := by
    rw [@carmichael_factorization n ⟨by lia⟩]
    refine Finset.lcm_dvd fun p hp_mem ↦ ?_
    rw [mem_primeFactors] at hp_mem
    rw [factorization_eq_one_of_squarefree hn_squarefree hp_mem.1 hp_mem.2.1, pow_one,
      carmichael_of_prime hp_mem.1]
    exact h_dvd p hp_mem.1 hp_mem.2.1
  rw [probablePrime_iff_zmod_one n (by grind), ← ZMod.coe_unitOfCoprime b hb,
    ← Units.val_pow_eq_pow_val, hd, pow_mul, pow_carmichael, one_pow, Units.val_one]

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
