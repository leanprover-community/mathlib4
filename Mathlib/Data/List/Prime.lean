/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Anne Baanen
-/
import Mathlib.Algebra.Associated
import Mathlib.Data.List.BigOperators.Lemmas
import Mathlib.Data.List.Perm

#align_import data.list.prime from "leanprover-community/mathlib"@"ccad6d5093bd2f5c6ca621fc74674cce51355af6"

/-!
# Products of lists of prime elements.

This file contains some theorems relating `Prime` and products of `List`s.

-/


open List

section CommMonoidWithZero

variable {M : Type*} [CommMonoidWithZero M]

/-- Prime `p` divides the product of a list `L` iff it divides some `a ∈ L` -/
theorem Prime.dvd_prod_iff {p : M} {L : List M} (pp : Prime p) : p ∣ L.prod ↔ ∃ a ∈ L, p ∣ a := by
  constructor
  -- ⊢ p ∣ prod L → ∃ a, a ∈ L ∧ p ∣ a
  · intro h
    -- ⊢ ∃ a, a ∈ L ∧ p ∣ a
    induction' L with L_hd L_tl L_ih
    -- ⊢ ∃ a, a ∈ [] ∧ p ∣ a
    · rw [prod_nil] at h
      -- ⊢ ∃ a, a ∈ [] ∧ p ∣ a
      exact absurd h pp.not_dvd_one
      -- 🎉 no goals
    · rw [prod_cons] at h
      -- ⊢ ∃ a, a ∈ L_hd :: L_tl ∧ p ∣ a
      cases' pp.dvd_or_dvd h with hd hd
      -- ⊢ ∃ a, a ∈ L_hd :: L_tl ∧ p ∣ a
      · exact ⟨L_hd, mem_cons_self L_hd L_tl, hd⟩
        -- 🎉 no goals
      · obtain ⟨x, hx1, hx2⟩ := L_ih hd
        -- ⊢ ∃ a, a ∈ L_hd :: L_tl ∧ p ∣ a
        exact ⟨x, mem_cons_of_mem L_hd hx1, hx2⟩
        -- 🎉 no goals
  · exact fun ⟨a, ha1, ha2⟩ => dvd_trans ha2 (dvd_prod ha1)
    -- 🎉 no goals
#align prime.dvd_prod_iff Prime.dvd_prod_iff

theorem Prime.not_dvd_prod {p : M} {L : List M} (pp : Prime p) (hL : ∀ a ∈ L, ¬p ∣ a) :
    ¬p ∣ L.prod :=
  mt (Prime.dvd_prod_iff pp).1 <| not_exists.2 <| fun a => not_and.2 (hL a)
#align prime.not_dvd_prod Prime.not_dvd_prod

end CommMonoidWithZero

section CancelCommMonoidWithZero

variable {M : Type*} [CancelCommMonoidWithZero M] [Unique (Units M)]

theorem mem_list_primes_of_dvd_prod {p : M} (hp : Prime p) {L : List M} (hL : ∀ q ∈ L, Prime q)
    (hpL : p ∣ L.prod) : p ∈ L := by
  obtain ⟨x, hx1, hx2⟩ := hp.dvd_prod_iff.mp hpL
  -- ⊢ p ∈ L
  rwa [(prime_dvd_prime_iff_eq hp (hL x hx1)).mp hx2]
  -- 🎉 no goals
#align mem_list_primes_of_dvd_prod mem_list_primes_of_dvd_prod

theorem perm_of_prod_eq_prod :
    ∀ {l₁ l₂ : List M}, l₁.prod = l₂.prod → (∀ p ∈ l₁, Prime p) → (∀ p ∈ l₂, Prime p) → Perm l₁ l₂
  | [], [], _, _, _ => Perm.nil
  | [], a :: l, h₁, _, h₃ =>
    have ha : a ∣ 1 := @prod_nil M _ ▸ h₁.symm ▸ (@prod_cons _ _ l a).symm ▸ dvd_mul_right _ _
    absurd ha (Prime.not_dvd_one (h₃ a (mem_cons_self _ _)))
  | a :: l, [], h₁, h₂, _ =>
    have ha : a ∣ 1 := @prod_nil M _ ▸ h₁ ▸ (@prod_cons _ _ l a).symm ▸ dvd_mul_right _ _
    absurd ha (Prime.not_dvd_one (h₂ a (mem_cons_self _ _)))
  | a :: l₁, b :: l₂, h, hl₁, hl₂ => by
    classical
      have hl₁' : ∀ p ∈ l₁, Prime p := fun p hp => hl₁ p (mem_cons_of_mem _ hp)
      have hl₂' : ∀ p ∈ (b :: l₂).erase a, Prime p := fun p hp => hl₂ p (mem_of_mem_erase hp)
      have ha : a ∈ b :: l₂ :=
        mem_list_primes_of_dvd_prod (hl₁ a (mem_cons_self _ _)) hl₂
          (h ▸ by rw [prod_cons]; exact dvd_mul_right _ _)
      have hb : b :: l₂ ~ a :: (b :: l₂).erase a := perm_cons_erase ha
      have hl : prod l₁ = prod ((b :: l₂).erase a) :=
        (mul_right_inj' (hl₁ a (mem_cons_self _ _)).ne_zero).1 <| by
          rwa [← prod_cons, ← prod_cons, ← hb.prod_eq]
      exact Perm.trans ((perm_of_prod_eq_prod hl hl₁' hl₂').cons _) hb.symm
#align perm_of_prod_eq_prod perm_of_prod_eq_prod

end CancelCommMonoidWithZero
