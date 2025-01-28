/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.GroupTheory.Index
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Prime.Factorial

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
    (hp : p.Prime) (hHp : H.index = p) (hp' : ∀ {l : ℕ} (_ : l.Prime) (_: l ∣ Nat.card G), p ≤ l) :
    H.Normal := by
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

/-- A subgroup of index 2 is normal (does not require finiteness of G) -/
theorem normal_of_index_eq_two (hH : H.index = 2) :
    H.Normal := by
  classical
  set f := MulAction.toPermHom G (G ⧸ H) with hf
  convert MonoidHom.normal_ker f
  suffices H.normalCore.relindex H = 1 by
    rw [← Subgroup.normalCore_eq_ker]
    rw [Subgroup.relindex_eq_one] at this
    exact le_antisymm this (normalCore_le H)
  have index_ne_zero : H.index ≠ 0 := by rw [hH]; exact two_ne_zero
  apply mul_left_injective₀ index_ne_zero; dsimp only
  rw [relindex_mul_index H.normalCore_le, one_mul, normalCore_eq_ker, hH]
  have _ : Fintype (G ⧸ H) := by apply fintypeOfIndexNeZero index_ne_zero
  apply Nat.eq_of_lt_succ_of_not_lt
  · rw [index_ker f, card_eq_fintype_card, Nat.lt_succ_iff]
    apply le_of_dvd two_pos
    rw [← card_eq_fintype_card]
    apply dvd_trans f.range.card_subgroup_dvd_card
    rw [card_eq_fintype_card, Fintype.card_perm, ← card_eq_fintype_card]
    unfold index at hH ; rw [hH]; norm_num
  · -- ¬(f.ker.index < 2)
    intro h
    apply not_le.mpr Nat.one_lt_two
    rw [Nat.lt_succ_iff] at h
    apply le_trans _ h
    rw [← hH, ← H.normalCore_eq_ker]
    apply Nat.le_of_dvd _ (index_dvd_of_le H.normalCore_le)
    rw [zero_lt_iff, H.normalCore_eq_ker, index_ker f, card_eq_fintype_card]
    exact Fintype.card_ne_zero

end Subgroup
