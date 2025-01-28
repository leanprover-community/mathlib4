/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.GroupTheory.Index

/-! # Subgroups of small index are normal

* `Subgroup.normal_of_index_eq_smallest_prime_factor`: in a finite group `G`,
a subgroup of index equal to the smallest prime factor of `Nat.card G` is normal.

* `Subgroup.normal_of_index_two`: in a group `G`, a subgroup of index 2 is normal
(This does not require `G` to be finite.)

-/

variable {G : Type*} [Group G] {H : Subgroup G} {p : ℕ}

namespace Subgroup

open MulAction MonoidHom Nat

private theorem dvd_prime {r p : ℕ} (hp : p.Prime) (h : r ∣ p !)
    (hr : ∀ {l : ℕ} (_ : l.Prime) (_ : l ∣ r), p ≤ l) : r ∣ p := by
  rw [← Coprime.dvd_mul_right (n := (p-1)!) _]
  · rw [mul_factorial_pred hp.pos]; exact h
  · rw [coprime_iff_gcd_eq_one]
    by_contra h
    obtain ⟨l, hl, hl'⟩ := exists_prime_and_dvd h
    rw [dvd_gcd_iff, hl.dvd_factorial] at hl'
    apply (lt_iff_not_ge p.pred p).mp (Nat.pred_lt hp.ne_zero)
    rw [pred_eq_sub_one, ge_iff_le]
    exact le_trans (hr hl hl'.left) hl'.right

/-- A subgroup of a finite group whose index is the smallest prime factor is normal -/
theorem normal_of_index_eq_smallest_prime_factor [Finite G]
    (hHp : H.index = (Nat.card G).minFac) :
    H.Normal := by
  by_cases hG : Nat.card G = 1
  · rw [hG, minFac_one, index_eq_one] at hHp
    rw [hHp]
    infer_instance
  have hp : (Nat.card G).minFac.Prime := minFac_prime hG
  have hp' {l : ℕ} (h1 : l.Prime) (h2 : l ∣ Nat.card G) : (Nat.card G).minFac ≤ l :=
    minFac_le_of_dvd h1.two_le h2
  set f := toPermHom G (G ⧸ H) with hf
  convert MonoidHom.normal_ker f
  suffices H.normalCore.relindex H = 1 by
    rw [← normalCore_eq_ker]
    rw [relindex_eq_one] at this
    exact le_antisymm this (normalCore_le H)
  have index_ne_zero : H.index ≠ 0 := hHp ▸ Nat.Prime.ne_zero hp
  apply mul_left_injective₀ index_ne_zero
  dsimp only
  rw [relindex_mul_index H.normalCore_le, one_mul, normalCore_eq_ker, hHp, ← hf]
  apply Or.resolve_left (hp.eq_one_or_self_of_dvd f.ker.index _)
  · -- f.ker.index ≠ 1
    intro hf_one
    apply hp.ne_one
    rw [← hHp, index_eq_one, eq_top_iff]
    apply le_trans _ H.normalCore_le
    rw [← eq_top_iff, ← index_eq_one, normalCore_eq_ker, hf_one]
  · --  f.ker.index ∣ p,
    apply dvd_prime hp
    · -- f.ker.index ∣ p.factorial : Lagrange on range
      classical
      haveI _ : Fintype f.range := Fintype.ofFinite ↥f.range
      haveI _ : Fintype (G ⧸ H) := fintypeOfIndexNeZero index_ne_zero
      rw [index_ker f, ← hHp]
      simp only [index, card_eq_fintype_card, ← Fintype.card_perm]
      simp only [← card_eq_fintype_card]
      exact f.range.card_subgroup_dvd_card
    · -- Condition on prime factors of f.ker.index : hypothesis on G
      intro l hl hl'
      exact hp' hl (dvd_trans hl' f.ker.index_dvd_card)

/-- A subgroup of index 1 is normal (does not require finiteness of G) -/ 
theorem normal_of_index_eq_one (hH : H.index = 1) : H.Normal := by 
  rw [index_eq_one] at hH 
  rw [hH] 
  infer_instance

/-- A subgroup of index 2 is normal (does not require finiteness of G) -/
theorem normal_of_index_eq_two (hH : H.index = 2) :
    H.Normal := by
  obtain ⟨a, ha⟩ := index_eq_two_iff.mp hH
  have ha1 : ∀ b, b * a ∈ H ↔ ¬ b ∈ H := by simpa only [xor_iff_iff_not] using ha
  have ha2 : ∀ b, ¬ b * a ∈ H ↔ b ∈ H := by simpa only [xor_iff_not_iff'] using ha
  refine ⟨fun b hb c ↦ ?_⟩
  by_cases hc : c ∈ H
  · exact H.mul_mem (H.mul_mem hc hb) (H.inv_mem hc)
  rw [← ha1, ← H.inv_mem_iff] at hc
  rw [← H.inv_mem_iff, ← ha2, ← H.inv_mem_iff, ← ha1] at hb
  simpa [mul_assoc] using H.mul_mem (H.inv_mem hc) (H.mul_mem hb hc)

end Subgroup
