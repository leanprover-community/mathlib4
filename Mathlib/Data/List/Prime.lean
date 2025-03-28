/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Anne Baanen
-/
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Algebra.GroupWithZero.Associated

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
  · intro h
    induction' L with L_hd L_tl L_ih
    · rw [prod_nil] at h
      exact absurd h pp.not_dvd_one
    · rw [prod_cons] at h
      rcases pp.dvd_or_dvd h with hd | hd
      · exact ⟨L_hd, mem_cons_self, hd⟩
      · obtain ⟨x, hx1, hx2⟩ := L_ih hd
        exact ⟨x, mem_cons_of_mem L_hd hx1, hx2⟩
  · exact fun ⟨a, ha1, ha2⟩ => dvd_trans ha2 (dvd_prod ha1)

theorem Prime.not_dvd_prod {p : M} {L : List M} (pp : Prime p) (hL : ∀ a ∈ L, ¬p ∣ a) :
    ¬p ∣ L.prod :=
  mt (Prime.dvd_prod_iff pp).1 <| not_exists.2 fun a => not_and.2 (hL a)

end CommMonoidWithZero

section CancelCommMonoidWithZero

variable {M : Type*} [CancelCommMonoidWithZero M] [Subsingleton Mˣ]

theorem mem_list_primes_of_dvd_prod {p : M} (hp : Prime p) {L : List M} (hL : ∀ q ∈ L, Prime q)
    (hpL : p ∣ L.prod) : p ∈ L := by
  obtain ⟨x, hx1, hx2⟩ := hp.dvd_prod_iff.mp hpL
  rwa [(prime_dvd_prime_iff_eq hp (hL x hx1)).mp hx2]

theorem perm_of_prod_eq_prod :
    ∀ {l₁ l₂ : List M}, l₁.prod = l₂.prod → (∀ p ∈ l₁, Prime p) → (∀ p ∈ l₂, Prime p) → Perm l₁ l₂
  | [], [], _, _, _ => Perm.nil
  | [], a :: l, h₁, _, h₃ =>
    have ha : a ∣ 1 := prod_nil (M := M) ▸ h₁.symm ▸ (prod_cons (l := l)).symm ▸ dvd_mul_right _ _
    absurd ha (Prime.not_dvd_one (h₃ a mem_cons_self))
  | a :: l, [], h₁, h₂, _ =>
    have ha : a ∣ 1 := prod_nil (M := M) ▸ h₁ ▸ (prod_cons (l := l)).symm ▸ dvd_mul_right _ _
    absurd ha (Prime.not_dvd_one (h₂ a mem_cons_self))
  | a :: l₁, b :: l₂, h, hl₁, hl₂ => by
    classical
      have hl₁' : ∀ p ∈ l₁, Prime p := fun p hp => hl₁ p (mem_cons_of_mem _ hp)
      have hl₂' : ∀ p ∈ (b :: l₂).erase a, Prime p := fun p hp => hl₂ p (mem_of_mem_erase hp)
      have ha : a ∈ b :: l₂ :=
        mem_list_primes_of_dvd_prod (hl₁ a mem_cons_self) hl₂
          (h ▸ by rw [prod_cons]; exact dvd_mul_right _ _)
      have hb : b :: l₂ ~ a :: (b :: l₂).erase a := perm_cons_erase ha
      have hl : prod l₁ = prod ((b :: l₂).erase a) :=
        (mul_right_inj' (hl₁ a mem_cons_self).ne_zero).1 <| by
          rwa [← prod_cons, ← prod_cons, ← hb.prod_eq]
      exact Perm.trans ((perm_of_prod_eq_prod hl hl₁' hl₂').cons _) hb.symm

end CancelCommMonoidWithZero
