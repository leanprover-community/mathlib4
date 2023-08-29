/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Data.List.Cycle
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.List

#align_import group_theory.perm.cycle.concrete from "leanprover-community/mathlib"@"00638177efd1b2534fc5269363ebf42a7871df9a"

/-!

# Properties of cyclic permutations constructed from lists/cycles

In the following, `{α : Type*} [Fintype α] [DecidableEq α]`.

## Main definitions

* `Cycle.formPerm`: the cyclic permutation created by looping over a `Cycle α`
* `Equiv.Perm.toList`: the list formed by iterating application of a permutation
* `Equiv.Perm.toCycle`: the cycle formed by iterating application of a permutation
* `Equiv.Perm.isoCycle`: the equivalence between cyclic permutations `f : Perm α`
  and the terms of `Cycle α` that correspond to them
* `Equiv.Perm.isoCycle'`: the same equivalence as `Equiv.Perm.isoCycle`
  but with evaluation via choosing over fintypes
* The notation `c[1, 2, 3]` to emulate notation of cyclic permutations `(1 2 3)`
* A `Repr` instance for any `Perm α`, by representing the `Finset` of
  `Cycle α` that correspond to the cycle factors.

## Main results

* `List.isCycle_formPerm`: a nontrivial list without duplicates, when interpreted as
  a permutation, is cyclic
* `Equiv.Perm.IsCycle.existsUnique_cycle`: there is only one nontrivial `Cycle α`
  corresponding to each cyclic `f : Perm α`

## Implementation details

The forward direction of `Equiv.Perm.isoCycle'` uses `Fintype.choose` of the uniqueness
result, relying on the `Fintype` instance of a `Cycle.nodup` subtype.
It is unclear if this works faster than the `Equiv.Perm.toCycle`, which relies
on recursion over `Finset.univ`.
Running `#eval` on even a simple noncyclic permutation `c[(1 : Fin 7), 2, 3] * c[0, 5]`
to show it takes a long time. TODO: is this because computing the cycle factors is slow?

-/


open Equiv Equiv.Perm List

variable {α : Type*}

namespace List

variable [DecidableEq α] {l l' : List α}

theorem formPerm_disjoint_iff (hl : Nodup l) (hl' : Nodup l') (hn : 2 ≤ l.length)
    (hn' : 2 ≤ l'.length) : Perm.Disjoint (formPerm l) (formPerm l') ↔ l.Disjoint l' := by
  rw [disjoint_iff_eq_or_eq, List.Disjoint]
  -- ⊢ (∀ (x : α), ↑(formPerm l) x = x ∨ ↑(formPerm l') x = x) ↔ ∀ ⦃a : α⦄, a ∈ l → …
  constructor
  -- ⊢ (∀ (x : α), ↑(formPerm l) x = x ∨ ↑(formPerm l') x = x) → ∀ ⦃a : α⦄, a ∈ l → …
  · rintro h x hx hx'
    -- ⊢ False
    specialize h x
    -- ⊢ False
    rw [formPerm_apply_mem_eq_self_iff _ hl _ hx, formPerm_apply_mem_eq_self_iff _ hl' _ hx'] at h
    -- ⊢ False
    rcases h with (hl | hl') <;> linarith
    -- ⊢ False
                                 -- 🎉 no goals
                                 -- 🎉 no goals
  · intro h x
    -- ⊢ ↑(formPerm l) x = x ∨ ↑(formPerm l') x = x
    by_cases hx : x ∈ l
    -- ⊢ ↑(formPerm l) x = x ∨ ↑(formPerm l') x = x
    by_cases hx' : x ∈ l'
    · exact (h hx hx').elim
      -- 🎉 no goals
    all_goals have := formPerm_eq_self_of_not_mem _ _ ‹_›; tauto
    -- 🎉 no goals
#align list.form_perm_disjoint_iff List.formPerm_disjoint_iff

set_option linter.deprecated false in
theorem isCycle_formPerm (hl : Nodup l) (hn : 2 ≤ l.length) : IsCycle (formPerm l) := by
  cases' l with x l
  -- ⊢ IsCycle (formPerm [])
  · norm_num at hn
    -- 🎉 no goals
  induction' l with y l generalizing x
  -- ⊢ IsCycle (formPerm [x])
  · norm_num at hn
    -- 🎉 no goals
  · use x
    -- ⊢ ↑(formPerm (x :: y :: l)) x ≠ x ∧ ∀ ⦃y_1 : α⦄, ↑(formPerm (x :: y :: l)) y_1 …
    constructor
    -- ⊢ ↑(formPerm (x :: y :: l)) x ≠ x
    · rwa [formPerm_apply_mem_ne_self_iff _ hl _ (mem_cons_self _ _)]
      -- 🎉 no goals
    · intro w hw
      -- ⊢ SameCycle (formPerm (x :: y :: l)) x w
      have : w ∈ x::y::l := mem_of_formPerm_ne_self _ _ hw
      -- ⊢ SameCycle (formPerm (x :: y :: l)) x w
      obtain ⟨k, hk, rfl⟩ := nthLe_of_mem this
      -- ⊢ SameCycle (formPerm (x :: y :: l)) x (nthLe (x :: y :: l) k hk)
      use k
      -- ⊢ ↑(formPerm (x :: y :: l) ^ ↑k) x = nthLe (x :: y :: l) k hk
      simp only [zpow_ofNat, formPerm_pow_apply_head _ _ hl k, Nat.mod_eq_of_lt hk]
      -- 🎉 no goals
#align list.is_cycle_form_perm List.isCycle_formPerm

theorem pairwise_sameCycle_formPerm (hl : Nodup l) (hn : 2 ≤ l.length) :
    Pairwise l.formPerm.SameCycle l :=
  Pairwise.imp_mem.mpr
    (pairwise_of_forall fun _ _ hx hy =>
      (isCycle_formPerm hl hn).sameCycle ((formPerm_apply_mem_ne_self_iff _ hl _ hx).mpr hn)
        ((formPerm_apply_mem_ne_self_iff _ hl _ hy).mpr hn))
#align list.pairwise_same_cycle_form_perm List.pairwise_sameCycle_formPerm

theorem cycleOf_formPerm (hl : Nodup l) (hn : 2 ≤ l.length) (x) :
    cycleOf l.attach.formPerm x = l.attach.formPerm :=
  have hn : 2 ≤ l.attach.length := by rwa [← length_attach] at hn
                                      -- 🎉 no goals
  have hl : l.attach.Nodup := by rwa [← nodup_attach] at hl
                                 -- 🎉 no goals
  (isCycle_formPerm hl hn).cycleOf_eq
    ((formPerm_apply_mem_ne_self_iff _ hl _ (mem_attach _ _)).mpr hn)
#align list.cycle_of_form_perm List.cycleOf_formPerm

theorem cycleType_formPerm (hl : Nodup l) (hn : 2 ≤ l.length) :
    cycleType l.attach.formPerm = {l.length} := by
  rw [← length_attach] at hn
  -- ⊢ cycleType (formPerm (attach l)) = {length l}
  rw [← nodup_attach] at hl
  -- ⊢ cycleType (formPerm (attach l)) = {length l}
  rw [cycleType_eq [l.attach.formPerm]]
  · simp only [map, Function.comp_apply]
    -- ⊢ ↑[Finset.card (support (formPerm (attach l)))] = {length l}
    rw [support_formPerm_of_nodup _ hl, card_toFinset, dedup_eq_self.mpr hl]
    -- ⊢ ↑[length (attach l)] = {length l}
    · simp
      -- 🎉 no goals
    · intro x h
      -- ⊢ False
      simp [h, Nat.succ_le_succ_iff] at hn
      -- 🎉 no goals
  · simp
    -- 🎉 no goals
  · simpa using isCycle_formPerm hl hn
    -- 🎉 no goals
  · simp
    -- 🎉 no goals
#align list.cycle_type_form_perm List.cycleType_formPerm

set_option linter.deprecated false in
theorem formPerm_apply_mem_eq_next (hl : Nodup l) (x : α) (hx : x ∈ l) :
    formPerm l x = next l x hx := by
  obtain ⟨k, hk, rfl⟩ := nthLe_of_mem hx
  -- ⊢ ↑(formPerm l) (nthLe l k hk) = next l (nthLe l k hk) hx
  rw [next_nthLe _ hl, formPerm_apply_nthLe _ hl]
  -- 🎉 no goals
#align list.form_perm_apply_mem_eq_next List.formPerm_apply_mem_eq_next

end List

namespace Cycle

variable [DecidableEq α] (s s' : Cycle α)

/-- A cycle `s : Cycle α`, given `Nodup s` can be interpreted as an `Equiv.Perm α`
where each element in the list is permuted to the next one, defined as `formPerm`.
-/
def formPerm : ∀ (s : Cycle α) (_ : Nodup s), Equiv.Perm α :=
  fun s => Quotient.hrecOn s (fun l _ => List.formPerm l) fun l₁ l₂ (h : l₁ ~r l₂) => by
    apply Function.hfunext
    -- ⊢ Nodup (Quotient.mk (IsRotated.setoid α) l₁) = Nodup (Quotient.mk (IsRotated. …
    ext
    -- ⊢ Nodup (Quotient.mk (IsRotated.setoid α) l₁) ↔ Nodup (Quotient.mk (IsRotated. …
    · exact h.nodup_iff
      -- 🎉 no goals
    · intro h₁ h₂ _
      -- ⊢ HEq (List.formPerm l₁) (List.formPerm l₂)
      exact heq_of_eq (formPerm_eq_of_isRotated h₁ h)
      -- 🎉 no goals
#align cycle.form_perm Cycle.formPerm

@[simp]
theorem formPerm_coe (l : List α) (hl : l.Nodup) : formPerm (l : Cycle α) hl = l.formPerm :=
  rfl
#align cycle.form_perm_coe Cycle.formPerm_coe

theorem formPerm_subsingleton (s : Cycle α) (h : Subsingleton s) : formPerm s h.nodup = 1 := by
  induction' s using Quot.inductionOn with s
  -- ⊢ formPerm (Quot.mk Setoid.r s) (_ : Nodup (Quot.mk Setoid.r s)) = 1
  simp only [formPerm_coe, mk_eq_coe]
  -- ⊢ List.formPerm s = 1
  simp only [length_subsingleton_iff, length_coe, mk_eq_coe] at h
  -- ⊢ List.formPerm s = 1
  cases' s with hd tl
  -- ⊢ List.formPerm [] = 1
  · simp
    -- 🎉 no goals
  · simp only [length_eq_zero, add_le_iff_nonpos_left, List.length, nonpos_iff_eq_zero] at h
    -- ⊢ List.formPerm (hd :: tl) = 1
    simp [h]
    -- 🎉 no goals
#align cycle.form_perm_subsingleton Cycle.formPerm_subsingleton

theorem isCycle_formPerm (s : Cycle α) (h : Nodup s) (hn : Nontrivial s) :
    IsCycle (formPerm s h) := by
  induction s using Quot.inductionOn
  -- ⊢ IsCycle (formPerm (Quot.mk Setoid.r a✝) h)
  exact List.isCycle_formPerm h (length_nontrivial hn)
  -- 🎉 no goals
#align cycle.is_cycle_form_perm Cycle.isCycle_formPerm

theorem support_formPerm [Fintype α] (s : Cycle α) (h : Nodup s) (hn : Nontrivial s) :
    support (formPerm s h) = s.toFinset := by
  induction' s using Quot.inductionOn with s
  -- ⊢ support (formPerm (Quot.mk Setoid.r s) h) = toFinset (Quot.mk Setoid.r s)
  refine' support_formPerm_of_nodup s h _
  -- ⊢ ∀ (x : α), s ≠ [x]
  rintro _ rfl
  -- ⊢ False
  simpa [Nat.succ_le_succ_iff] using length_nontrivial hn
  -- 🎉 no goals
#align cycle.support_form_perm Cycle.support_formPerm

theorem formPerm_eq_self_of_not_mem (s : Cycle α) (h : Nodup s) (x : α) (hx : x ∉ s) :
    formPerm s h x = x := by
  induction s using Quot.inductionOn
  -- ⊢ ↑(formPerm (Quot.mk Setoid.r a✝) h) x = x
  simpa using List.formPerm_eq_self_of_not_mem _ _ hx
  -- 🎉 no goals
#align cycle.form_perm_eq_self_of_not_mem Cycle.formPerm_eq_self_of_not_mem

theorem formPerm_apply_mem_eq_next (s : Cycle α) (h : Nodup s) (x : α) (hx : x ∈ s) :
    formPerm s h x = next s h x hx := by
  induction s using Quot.inductionOn
  -- ⊢ ↑(formPerm (Quot.mk Setoid.r a✝) h) x = next (Quot.mk Setoid.r a✝) h x hx
  simpa using List.formPerm_apply_mem_eq_next h _ (by simp_all)
  -- 🎉 no goals
#align cycle.form_perm_apply_mem_eq_next Cycle.formPerm_apply_mem_eq_next

nonrec theorem formPerm_reverse (s : Cycle α) (h : Nodup s) :
    formPerm s.reverse (nodup_reverse_iff.mpr h) = (formPerm s h)⁻¹ := by
  induction s using Quot.inductionOn
  -- ⊢ formPerm (reverse (Quot.mk Setoid.r a✝)) (_ : Nodup (reverse (Quot.mk Setoid …
  simpa using formPerm_reverse _ h
  -- 🎉 no goals
#align cycle.form_perm_reverse Cycle.formPerm_reverse

nonrec theorem formPerm_eq_formPerm_iff {α : Type*} [DecidableEq α] {s s' : Cycle α} {hs : s.Nodup}
    {hs' : s'.Nodup} :
    s.formPerm hs = s'.formPerm hs' ↔ s = s' ∨ s.Subsingleton ∧ s'.Subsingleton := by
  rw [Cycle.length_subsingleton_iff, Cycle.length_subsingleton_iff]
  -- ⊢ formPerm s hs = formPerm s' hs' ↔ s = s' ∨ length s ≤ 1 ∧ length s' ≤ 1
  revert s s'
  -- ⊢ ∀ {s s' : Cycle α} {hs : Nodup s} {hs' : Nodup s'}, formPerm s hs = formPerm …
  intro s s'
  -- ⊢ ∀ {hs : Nodup s} {hs' : Nodup s'}, formPerm s hs = formPerm s' hs' ↔ s = s'  …
  apply @Quotient.inductionOn₂' _ _ _ _ _ s s'
  -- ⊢ ∀ (a₁ a₂ : List α) {hs : Nodup (Quotient.mk'' a₁)} {hs' : Nodup (Quotient.mk …
  intro l l'
  -- ⊢ ∀ {hs : Nodup (Quotient.mk'' l)} {hs' : Nodup (Quotient.mk'' l')}, formPerm  …
  -- Porting note: was `simpa using formPerm_eq_formPerm_iff`
  simp_all
  -- ⊢ ∀ {hs : List.Nodup l} {hs' : List.Nodup l'}, List.formPerm l = List.formPerm …
  intro hs hs'
  -- ⊢ List.formPerm l = List.formPerm l' ↔ l ~r l' ∨ List.length l ≤ 1 ∧ List.leng …
  constructor <;> intro h <;> simp_all only [formPerm_eq_formPerm_iff]
  -- ⊢ List.formPerm l = List.formPerm l' → l ~r l' ∨ List.length l ≤ 1 ∧ List.leng …
                  -- ⊢ l ~r l' ∨ List.length l ≤ 1 ∧ List.length l' ≤ 1
                  -- ⊢ List.formPerm l = List.formPerm l'
                              -- 🎉 no goals
                              -- 🎉 no goals
#align cycle.form_perm_eq_form_perm_iff Cycle.formPerm_eq_formPerm_iff

end Cycle

namespace Equiv.Perm

section Fintype

variable [Fintype α] [DecidableEq α] (p : Equiv.Perm α) (x : α)

/-- `Equiv.Perm.toList (f : Perm α) (x : α)` generates the list `[x, f x, f (f x), ...]`
until looping. That means when `f x = x`, `toList f x = []`.
-/
def toList : List α :=
  (List.range (cycleOf p x).support.card).map fun k => (p ^ k) x
#align equiv.perm.to_list Equiv.Perm.toList

@[simp]
theorem toList_one : toList (1 : Perm α) x = [] := by simp [toList, cycleOf_one]
                                                      -- 🎉 no goals
#align equiv.perm.to_list_one Equiv.Perm.toList_one

@[simp]
theorem toList_eq_nil_iff {p : Perm α} {x} : toList p x = [] ↔ x ∉ p.support := by simp [toList]
                                                                                   -- 🎉 no goals
#align equiv.perm.to_list_eq_nil_iff Equiv.Perm.toList_eq_nil_iff

@[simp]
theorem length_toList : length (toList p x) = (cycleOf p x).support.card := by simp [toList]
                                                                               -- 🎉 no goals
#align equiv.perm.length_to_list Equiv.Perm.length_toList

theorem toList_ne_singleton (y : α) : toList p x ≠ [y] := by
  intro H
  -- ⊢ False
  simpa [card_support_ne_one] using congr_arg length H
  -- 🎉 no goals
#align equiv.perm.to_list_ne_singleton Equiv.Perm.toList_ne_singleton

theorem two_le_length_toList_iff_mem_support {p : Perm α} {x : α} :
    2 ≤ length (toList p x) ↔ x ∈ p.support := by simp
                                                  -- 🎉 no goals
#align equiv.perm.two_le_length_to_list_iff_mem_support Equiv.Perm.two_le_length_toList_iff_mem_support

theorem length_toList_pos_of_mem_support (h : x ∈ p.support) : 0 < length (toList p x) :=
  zero_lt_two.trans_le (two_le_length_toList_iff_mem_support.mpr h)
#align equiv.perm.length_to_list_pos_of_mem_support Equiv.Perm.length_toList_pos_of_mem_support

theorem nthLe_toList (n : ℕ) (hn : n < length (toList p x)) : (toList p x).nthLe n hn = (p ^ n) x :=
  by simp [toList]
     -- 🎉 no goals
#align equiv.perm.nth_le_to_list Equiv.Perm.nthLe_toList

theorem toList_nthLe_zero (h : x ∈ p.support) :
    (toList p x).nthLe 0 (length_toList_pos_of_mem_support _ _ h) = x := by simp [toList]
                                                                            -- 🎉 no goals
#align equiv.perm.to_list_nth_le_zero Equiv.Perm.toList_nthLe_zero

variable {p} {x}

theorem mem_toList_iff {y : α} : y ∈ toList p x ↔ SameCycle p x y ∧ x ∈ p.support := by
  simp only [toList, mem_range, mem_map]
  -- ⊢ (∃ a, a < Finset.card (support (cycleOf p x)) ∧ ↑(p ^ a) x = y) ↔ SameCycle  …
  constructor
  -- ⊢ (∃ a, a < Finset.card (support (cycleOf p x)) ∧ ↑(p ^ a) x = y) → SameCycle  …
  · rintro ⟨n, hx, rfl⟩
    -- ⊢ SameCycle p x (↑(p ^ n) x) ∧ x ∈ support p
    refine' ⟨⟨n, rfl⟩, _⟩
    -- ⊢ x ∈ support p
    contrapose! hx
    -- ⊢ Finset.card (support (cycleOf p x)) ≤ n
    rw [← support_cycleOf_eq_nil_iff] at hx
    -- ⊢ Finset.card (support (cycleOf p x)) ≤ n
    simp [hx]
    -- 🎉 no goals
  · rintro ⟨h, hx⟩
    -- ⊢ ∃ a, a < Finset.card (support (cycleOf p x)) ∧ ↑(p ^ a) x = y
    simpa using h.exists_pow_eq_of_mem_support hx
    -- 🎉 no goals
#align equiv.perm.mem_to_list_iff Equiv.Perm.mem_toList_iff

set_option linter.deprecated false in
theorem nodup_toList (p : Perm α) (x : α) : Nodup (toList p x) := by
  by_cases hx : p x = x
  -- ⊢ Nodup (toList p x)
  · rw [← not_mem_support, ← toList_eq_nil_iff] at hx
    -- ⊢ Nodup (toList p x)
    simp [hx]
    -- 🎉 no goals
  have hc : IsCycle (cycleOf p x) := isCycle_cycleOf p hx
  -- ⊢ Nodup (toList p x)
  rw [nodup_iff_nthLe_inj]
  -- ⊢ ∀ (i j : ℕ) (h₁ : i < length (toList p x)) (h₂ : j < length (toList p x)), n …
  rintro n m hn hm
  -- ⊢ nthLe (toList p x) n hn = nthLe (toList p x) m hm → n = m
  rw [length_toList, ← hc.orderOf] at hm hn
  -- ⊢ nthLe (toList p x) n hn✝ = nthLe (toList p x) m hm✝ → n = m
  rw [← cycleOf_apply_self, ← Ne.def, ← mem_support] at hx
  -- ⊢ nthLe (toList p x) n hn✝ = nthLe (toList p x) m hm✝ → n = m
  rw [nthLe_toList, nthLe_toList, ← cycleOf_pow_apply_self p x n, ←
    cycleOf_pow_apply_self p x m]
  cases' n with n <;> cases' m with m
  -- ⊢ ↑(cycleOf p x ^ Nat.zero) x = ↑(cycleOf p x ^ m) x → Nat.zero = m
                      -- ⊢ ↑(cycleOf p x ^ Nat.zero) x = ↑(cycleOf p x ^ Nat.zero) x → Nat.zero = Nat.z …
                      -- ⊢ ↑(cycleOf p x ^ Nat.succ n) x = ↑(cycleOf p x ^ Nat.zero) x → Nat.succ n = N …
  · simp
    -- 🎉 no goals
  · rw [← hc.support_pow_of_pos_of_lt_orderOf m.zero_lt_succ hm, mem_support,
      cycleOf_pow_apply_self] at hx
    simp [hx.symm]
    -- 🎉 no goals
  · rw [← hc.support_pow_of_pos_of_lt_orderOf n.zero_lt_succ hn, mem_support,
      cycleOf_pow_apply_self] at hx
    simp [hx]
    -- 🎉 no goals
  intro h
  -- ⊢ Nat.succ n = Nat.succ m
  have hn' : ¬orderOf (p.cycleOf x) ∣ n.succ := Nat.not_dvd_of_pos_of_lt n.zero_lt_succ hn
  -- ⊢ Nat.succ n = Nat.succ m
  have hm' : ¬orderOf (p.cycleOf x) ∣ m.succ := Nat.not_dvd_of_pos_of_lt m.zero_lt_succ hm
  -- ⊢ Nat.succ n = Nat.succ m
  rw [← hc.support_pow_eq_iff] at hn' hm'
  -- ⊢ Nat.succ n = Nat.succ m
  rw [← Nat.mod_eq_of_lt hn, ← Nat.mod_eq_of_lt hm, ← pow_inj_mod]
  -- ⊢ cycleOf p x ^ Nat.succ n = cycleOf p x ^ Nat.succ m
  refine' support_congr _ _
  -- ⊢ support (cycleOf p x ^ Nat.succ n) ⊆ support (cycleOf p x ^ Nat.succ m)
  · rw [hm', hn']
    -- 🎉 no goals
  · rw [hm']
    -- ⊢ ∀ (x_1 : α), x_1 ∈ support (cycleOf p x) → ↑(cycleOf p x ^ Nat.succ n) x_1 = …
    intro y hy
    -- ⊢ ↑(cycleOf p x ^ Nat.succ n) y = ↑(cycleOf p x ^ Nat.succ m) y
    obtain ⟨k, rfl⟩ := hc.exists_pow_eq (mem_support.mp hx) (mem_support.mp hy)
    -- ⊢ ↑(cycleOf p x ^ Nat.succ n) (↑(cycleOf p x ^ k) x) = ↑(cycleOf p x ^ Nat.suc …
    rw [← mul_apply, (Commute.pow_pow_self _ _ _).eq, mul_apply, h, ← mul_apply, ← mul_apply,
      (Commute.pow_pow_self _ _ _).eq]
#align equiv.perm.nodup_to_list Equiv.Perm.nodup_toList

set_option linter.deprecated false in
theorem next_toList_eq_apply (p : Perm α) (x y : α) (hy : y ∈ toList p x) :
    next (toList p x) y hy = p y := by
  rw [mem_toList_iff] at hy
  -- ⊢ next (toList p x) y hy✝ = ↑p y
  obtain ⟨k, hk, hk'⟩ := hy.left.exists_pow_eq_of_mem_support hy.right
  -- ⊢ next (toList p x) y hy✝ = ↑p y
  rw [← nthLe_toList p x k (by simpa using hk)] at hk'
  -- ⊢ next (toList p x) y hy✝ = ↑p y
  simp_rw [← hk']
  -- ⊢ next (toList p x) (nthLe (toList p x) k (_ : k < length (toList p x))) (_ :  …
  rw [next_nthLe _ (nodup_toList _ _), nthLe_toList, nthLe_toList, ← mul_apply, ← pow_succ,
    length_toList, pow_apply_eq_pow_mod_orderOf_cycleOf_apply p (k + 1), IsCycle.orderOf]
  exact isCycle_cycleOf _ (mem_support.mp hy.right)
  -- 🎉 no goals
#align equiv.perm.next_to_list_eq_apply Equiv.Perm.next_toList_eq_apply

set_option linter.deprecated false in
theorem toList_pow_apply_eq_rotate (p : Perm α) (x : α) (k : ℕ) :
    p.toList ((p ^ k) x) = (p.toList x).rotate k := by
  apply ext_nthLe
  -- ⊢ length (toList p (↑(p ^ k) x)) = length (rotate (toList p x) k)
  · simp only [length_toList, cycleOf_self_apply_pow, length_rotate]
    -- 🎉 no goals
  · intro n hn hn'
    -- ⊢ nthLe (toList p (↑(p ^ k) x)) n hn = nthLe (rotate (toList p x) k) n hn'
    rw [nthLe_toList, nthLe_rotate, nthLe_toList, length_toList,
      pow_mod_card_support_cycleOf_self_apply, pow_add, mul_apply]
#align equiv.perm.to_list_pow_apply_eq_rotate Equiv.Perm.toList_pow_apply_eq_rotate

theorem SameCycle.toList_isRotated {f : Perm α} {x y : α} (h : SameCycle f x y) :
    toList f x ~r toList f y := by
  by_cases hx : x ∈ f.support
  -- ⊢ toList f x ~r toList f y
  · obtain ⟨_ | k, _, hy⟩ := h.exists_pow_eq_of_mem_support hx
    -- ⊢ toList f x ~r toList f y
    · simp only [coe_one, id.def, pow_zero, Nat.zero_eq] at hy
      -- ⊢ toList f x ~r toList f y
      -- Porting note: added `IsRotated.refl`
      simp [hy, IsRotated.refl]
      -- 🎉 no goals
    use k.succ
    -- ⊢ rotate (toList f x) (Nat.succ k) = toList f y
    rw [← toList_pow_apply_eq_rotate, hy]
    -- 🎉 no goals
  · rw [toList_eq_nil_iff.mpr hx, isRotated_nil_iff', eq_comm, toList_eq_nil_iff]
    -- ⊢ ¬y ∈ support f
    rwa [← h.mem_support_iff]
    -- 🎉 no goals
#align equiv.perm.same_cycle.to_list_is_rotated Equiv.Perm.SameCycle.toList_isRotated

theorem pow_apply_mem_toList_iff_mem_support {n : ℕ} : (p ^ n) x ∈ p.toList x ↔ x ∈ p.support := by
  rw [mem_toList_iff, and_iff_right_iff_imp]
  -- ⊢ x ∈ support p → SameCycle p x (↑(p ^ n) x)
  refine' fun _ => SameCycle.symm _
  -- ⊢ SameCycle p (↑(p ^ n) x) x
  rw [sameCycle_pow_left]
  -- 🎉 no goals
#align equiv.perm.pow_apply_mem_to_list_iff_mem_support Equiv.Perm.pow_apply_mem_toList_iff_mem_support

theorem toList_formPerm_nil (x : α) : toList (formPerm ([] : List α)) x = [] := by simp
                                                                                   -- 🎉 no goals
#align equiv.perm.to_list_form_perm_nil Equiv.Perm.toList_formPerm_nil

theorem toList_formPerm_singleton (x y : α) : toList (formPerm [x]) y = [] := by simp
                                                                                 -- 🎉 no goals
#align equiv.perm.to_list_form_perm_singleton Equiv.Perm.toList_formPerm_singleton

set_option linter.deprecated false in
theorem toList_formPerm_nontrivial (l : List α) (hl : 2 ≤ l.length) (hn : Nodup l) :
    toList (formPerm l) (l.nthLe 0 (zero_lt_two.trans_le hl)) = l := by
  have hc : l.formPerm.IsCycle := List.isCycle_formPerm hn hl
  -- ⊢ toList (formPerm l) (nthLe l 0 (_ : 0 < length l)) = l
  have hs : l.formPerm.support = l.toFinset := by
    refine' support_formPerm_of_nodup _ hn _
    rintro _ rfl
    simp [Nat.succ_le_succ_iff] at hl
  rw [toList, hc.cycleOf_eq (mem_support.mp _), hs, card_toFinset, dedup_eq_self.mpr hn]
  -- ⊢ map (fun k => ↑(formPerm l ^ k) (nthLe l 0 (_ : 0 < length l))) (range (leng …
  · refine' ext_get (by simp) fun k hk hk' => _
    -- ⊢ List.get (map (fun k => ↑(formPerm l ^ k) (nthLe l 0 (_ : 0 < length l))) (r …
    simp [formPerm_pow_apply_nthLe _ hn, Nat.mod_eq_of_lt hk']
    -- ⊢ nthLe l k (_ : k < length l) = List.get l { val := k, isLt := hk' }
    rw [nthLe_eq]
    -- 🎉 no goals
  · simpa [hs] using get_mem _ _ _
    -- 🎉 no goals
#align equiv.perm.to_list_form_perm_nontrivial Equiv.Perm.toList_formPerm_nontrivial

theorem toList_formPerm_isRotated_self (l : List α) (hl : 2 ≤ l.length) (hn : Nodup l) (x : α)
    (hx : x ∈ l) : toList (formPerm l) x ~r l := by
  obtain ⟨k, hk, rfl⟩ := get_of_mem hx
  -- ⊢ toList (formPerm l) (List.get l k) ~r l
  have hr : l ~r l.rotate k := ⟨k, rfl⟩
  -- ⊢ toList (formPerm l) (List.get l k) ~r l
  rw [formPerm_eq_of_isRotated hn hr]
  -- ⊢ toList (formPerm (rotate l ↑k)) (List.get l k) ~r l
  rw [get_eq_get_rotate l k k]
  -- ⊢ toList (formPerm (rotate l ↑k)) (List.get (rotate l ↑k) { val := (length l - …
  simp only [Nat.mod_eq_of_lt k.2, tsub_add_cancel_of_le (le_of_lt k.2), Nat.mod_self]
  -- ⊢ toList (formPerm (rotate l ↑k)) (List.get (rotate l ↑k) { val := 0, isLt :=  …
  erw [toList_formPerm_nontrivial]
  · simp
    -- 🎉 no goals
  · simpa using hl
    -- 🎉 no goals
  · simpa using hn
    -- 🎉 no goals
#align equiv.perm.to_list_form_perm_is_rotated_self Equiv.Perm.toList_formPerm_isRotated_self

theorem formPerm_toList (f : Perm α) (x : α) : formPerm (toList f x) = f.cycleOf x := by
  by_cases hx : f x = x
  -- ⊢ formPerm (toList f x) = cycleOf f x
  · rw [(cycleOf_eq_one_iff f).mpr hx, toList_eq_nil_iff.mpr (not_mem_support.mpr hx),
      formPerm_nil]
  ext y
  -- ⊢ ↑(formPerm (toList f x)) y = ↑(cycleOf f x) y
  by_cases hy : SameCycle f x y
  -- ⊢ ↑(formPerm (toList f x)) y = ↑(cycleOf f x) y
  · obtain ⟨k, _, rfl⟩ := hy.exists_pow_eq_of_mem_support (mem_support.mpr hx)
    -- ⊢ ↑(formPerm (toList f x)) (↑(f ^ k) x) = ↑(cycleOf f x) (↑(f ^ k) x)
    rw [cycleOf_apply_apply_pow_self, List.formPerm_apply_mem_eq_next (nodup_toList f x),
      next_toList_eq_apply, pow_succ, mul_apply]
    rw [mem_toList_iff]
    -- ⊢ SameCycle f x (↑(f ^ k) x) ∧ x ∈ support f
    exact ⟨⟨k, rfl⟩, mem_support.mpr hx⟩
    -- 🎉 no goals
  · rw [cycleOf_apply_of_not_sameCycle hy, formPerm_apply_of_not_mem]
    -- ⊢ ¬y ∈ toList f x
    simp [mem_toList_iff, hy]
    -- 🎉 no goals
#align equiv.perm.form_perm_to_list Equiv.Perm.formPerm_toList

/-- Given a cyclic `f : Perm α`, generate the `Cycle α` in the order
of application of `f`. Implemented by finding an element `x : α`
in the support of `f` in `Finset.univ`, and iterating on using
`Equiv.Perm.toList f x`.
-/
def toCycle (f : Perm α) (hf : IsCycle f) : Cycle α :=
  Multiset.recOn (Finset.univ : Finset α).val (Quot.mk _ [])
    (fun x _ l => if f x = x then l else toList f x)
    (by
      intro x y _ s
      -- ⊢ HEq (if ↑f x = x then if ↑f y = y then s else ↑(toList f y) else ↑(toList f  …
      refine' heq_of_eq _
      -- ⊢ (if ↑f x = x then if ↑f y = y then s else ↑(toList f y) else ↑(toList f x))  …
      split_ifs with hx hy hy <;> try rfl
                                  -- 🎉 no goals
                                  -- 🎉 no goals
                                  -- 🎉 no goals
                                  -- ⊢ ↑(toList f x) = ↑(toList f y)
      · have hc : SameCycle f x y := IsCycle.sameCycle hf hx hy
        -- ⊢ ↑(toList f x) = ↑(toList f y)
        exact Quotient.sound' hc.toList_isRotated)
        -- 🎉 no goals
#align equiv.perm.to_cycle Equiv.Perm.toCycle

theorem toCycle_eq_toList (f : Perm α) (hf : IsCycle f) (x : α) (hx : f x ≠ x) :
    toCycle f hf = toList f x := by
  have key : (Finset.univ : Finset α).val = x ::ₘ Finset.univ.val.erase x := by simp
  -- ⊢ toCycle f hf = ↑(toList f x)
  rw [toCycle, key]
  -- ⊢ Multiset.recOn (x ::ₘ Multiset.erase Finset.univ.val x) (Quot.mk Setoid.r [] …
  simp [hx]
  -- 🎉 no goals
#align equiv.perm.to_cycle_eq_to_list Equiv.Perm.toCycle_eq_toList

theorem nodup_toCycle (f : Perm α) (hf : IsCycle f) : (toCycle f hf).Nodup := by
  obtain ⟨x, hx, -⟩ := id hf
  -- ⊢ Cycle.Nodup (toCycle f hf)
  simpa [toCycle_eq_toList f hf x hx] using nodup_toList _ _
  -- 🎉 no goals
#align equiv.perm.nodup_to_cycle Equiv.Perm.nodup_toCycle

theorem nontrivial_toCycle (f : Perm α) (hf : IsCycle f) : (toCycle f hf).Nontrivial := by
  obtain ⟨x, hx, -⟩ := id hf
  -- ⊢ Cycle.Nontrivial (toCycle f hf)
  simp [toCycle_eq_toList f hf x hx, hx, Cycle.nontrivial_coe_nodup_iff (nodup_toList _ _)]
  -- 🎉 no goals
#align equiv.perm.nontrivial_to_cycle Equiv.Perm.nontrivial_toCycle

/-- Any cyclic `f : Perm α` is isomorphic to the nontrivial `Cycle α`
that corresponds to repeated application of `f`.
The forward direction is implemented by `Equiv.Perm.toCycle`.
-/
def isoCycle : { f : Perm α // IsCycle f } ≃ { s : Cycle α // s.Nodup ∧ s.Nontrivial } where
  toFun f := ⟨toCycle (f : Perm α) f.prop, nodup_toCycle f f.prop, nontrivial_toCycle _ f.prop⟩
  invFun s := ⟨(s : Cycle α).formPerm s.prop.left, (s : Cycle α).isCycle_formPerm _ s.prop.right⟩
  left_inv f := by
    obtain ⟨x, hx, -⟩ := id f.prop
    -- ⊢ (fun s => { val := Cycle.formPerm ↑s (_ : Cycle.Nodup ↑s), property := (_ :  …
    simpa [toCycle_eq_toList (f : Perm α) f.prop x hx, formPerm_toList, Subtype.ext_iff] using
      f.prop.cycleOf_eq hx
  right_inv s := by
    rcases s with ⟨⟨s⟩, hn, ht⟩
    -- ⊢ (fun f => { val := toCycle ↑f (_ : IsCycle ↑f), property := (_ : Cycle.Nodup …
    obtain ⟨x, -, -, hx, -⟩ := id ht
    -- ⊢ (fun f => { val := toCycle ↑f (_ : IsCycle ↑f), property := (_ : Cycle.Nodup …
    have hl : 2 ≤ s.length := by simpa using Cycle.length_nontrivial ht
    -- ⊢ (fun f => { val := toCycle ↑f (_ : IsCycle ↑f), property := (_ : Cycle.Nodup …
    simp only [Cycle.mk_eq_coe, Cycle.nodup_coe_iff, Cycle.mem_coe_iff, Subtype.coe_mk,
      Cycle.formPerm_coe] at hn hx ⊢
    apply Subtype.ext
    -- ⊢ ↑{ val := toCycle (formPerm s) (_ : IsCycle (formPerm s)), property := (_ :  …
    dsimp
    -- ⊢ toCycle (formPerm s) (_ : IsCycle ↑{ val := formPerm s, property := (_ : IsC …
    rw [toCycle_eq_toList _ _ x]
    -- ⊢ ↑(toList (formPerm s) x) = ↑s
    · refine' Quotient.sound' _
      -- ⊢ Setoid.r (toList (formPerm s) x) s
      exact toList_formPerm_isRotated_self _ hl hn _ hx
      -- 🎉 no goals
    · rw [← mem_support, support_formPerm_of_nodup _ hn]
      -- ⊢ x ∈ toFinset s
      · simpa using hx
        -- 🎉 no goals
      · rintro _ rfl
        -- ⊢ False
        simp [Nat.succ_le_succ_iff] at hl
        -- 🎉 no goals
#align equiv.perm.iso_cycle Equiv.Perm.isoCycle

end Fintype

section Finite

variable [Finite α] [DecidableEq α]

theorem IsCycle.existsUnique_cycle {f : Perm α} (hf : IsCycle f) :
    ∃! s : Cycle α, ∃ h : s.Nodup, s.formPerm h = f := by
  cases nonempty_fintype α
  -- ⊢ ∃! s, ∃ h, Cycle.formPerm s h = f
  obtain ⟨x, hx, hy⟩ := id hf
  -- ⊢ ∃! s, ∃ h, Cycle.formPerm s h = f
  refine' ⟨f.toList x, ⟨nodup_toList f x, _⟩, _⟩
  -- ⊢ Cycle.formPerm ↑(toList f x) (_ : Nodup (toList f x)) = f
  · simp [formPerm_toList, hf.cycleOf_eq hx]
    -- 🎉 no goals
  · rintro ⟨l⟩ ⟨hn, rfl⟩
    -- ⊢ Quot.mk Setoid.r l = ↑(toList (Cycle.formPerm (Quot.mk Setoid.r l) hn) x)
    simp only [Cycle.mk_eq_coe, Cycle.coe_eq_coe, Subtype.coe_mk, Cycle.formPerm_coe]
    -- ⊢ l ~r toList (formPerm l) x
    refine' (toList_formPerm_isRotated_self _ _ hn _ _).symm
    -- ⊢ 2 ≤ length l
    · contrapose! hx
      -- ⊢ ↑(Cycle.formPerm (Quot.mk Setoid.r l) hn) x = x
      suffices formPerm l = 1 by simp [this]
      -- ⊢ formPerm l = 1
      rw [formPerm_eq_one_iff _ hn]
      -- ⊢ length l ≤ 1
      exact Nat.le_of_lt_succ hx
      -- 🎉 no goals
    · rw [← mem_toFinset]
      -- ⊢ x ∈ toFinset l
      refine' support_formPerm_le l _
      -- ⊢ x ∈ support (formPerm l)
      simpa using hx
      -- 🎉 no goals
#align equiv.perm.is_cycle.exists_unique_cycle Equiv.Perm.IsCycle.existsUnique_cycle

theorem IsCycle.existsUnique_cycle_subtype {f : Perm α} (hf : IsCycle f) :
    ∃! s : { s : Cycle α // s.Nodup }, (s : Cycle α).formPerm s.prop = f := by
  obtain ⟨s, ⟨hs, rfl⟩, hs'⟩ := hf.existsUnique_cycle
  -- ⊢ ∃! s_1, Cycle.formPerm ↑s_1 (_ : Cycle.Nodup ↑s_1) = Cycle.formPerm s hs
  refine' ⟨⟨s, hs⟩, rfl, _⟩
  -- ⊢ ∀ (y : { s // Cycle.Nodup s }), (fun s_1 => Cycle.formPerm ↑s_1 (_ : Cycle.N …
  rintro ⟨t, ht⟩ ht'
  -- ⊢ { val := t, property := ht } = { val := s, property := hs }
  simpa using hs' _ ⟨ht, ht'⟩
  -- 🎉 no goals
#align equiv.perm.is_cycle.exists_unique_cycle_subtype Equiv.Perm.IsCycle.existsUnique_cycle_subtype

theorem IsCycle.existsUnique_cycle_nontrivial_subtype {f : Perm α} (hf : IsCycle f) :
    ∃! s : { s : Cycle α // s.Nodup ∧ s.Nontrivial }, (s : Cycle α).formPerm s.prop.left = f := by
  obtain ⟨⟨s, hn⟩, hs, hs'⟩ := hf.existsUnique_cycle_subtype
  -- ⊢ ∃! s, Cycle.formPerm ↑s (_ : Cycle.Nodup ↑s) = f
  refine' ⟨⟨s, hn, _⟩, _, _⟩
  · rw [hn.nontrivial_iff]
    -- ⊢ ¬Cycle.Subsingleton s
    subst f
    -- ⊢ ¬Cycle.Subsingleton s
    intro H
    -- ⊢ False
    refine' hf.ne_one _
    -- ⊢ Cycle.formPerm ↑{ val := s, property := hn } (_ : Cycle.Nodup ↑{ val := s, p …
    simpa using Cycle.formPerm_subsingleton _ H
    -- 🎉 no goals
  · simpa using hs
    -- 🎉 no goals
  · rintro ⟨t, ht, ht'⟩ ht''
    -- ⊢ { val := t, property := (_ : Cycle.Nodup t ∧ Cycle.Nontrivial t) } = { val : …
    simpa using hs' ⟨t, ht⟩ ht''
    -- 🎉 no goals
#align equiv.perm.is_cycle.exists_unique_cycle_nontrivial_subtype Equiv.Perm.IsCycle.existsUnique_cycle_nontrivial_subtype

end Finite

variable [Fintype α] [DecidableEq α]

/-- Any cyclic `f : Perm α` is isomorphic to the nontrivial `Cycle α`
that corresponds to repeated application of `f`.
The forward direction is implemented by finding this `Cycle α` using `Fintype.choose`.
-/
def isoCycle' : { f : Perm α // IsCycle f } ≃ { s : Cycle α // s.Nodup ∧ s.Nontrivial } :=
  let f : { s : Cycle α // s.Nodup ∧ s.Nontrivial } → { f : Perm α // IsCycle f } :=
    fun s => ⟨(s : Cycle α).formPerm s.prop.left, (s : Cycle α).isCycle_formPerm _ s.prop.right⟩
  { toFun := Fintype.bijInv (show Function.Bijective f by
      rw [Function.bijective_iff_existsUnique]
      -- ⊢ ∀ (b : { f // IsCycle f }), ∃! a, f a = b
      rintro ⟨f, hf⟩
      -- ⊢ ∃! a, f✝ a = { val := f, property := hf }
      simp only [Subtype.ext_iff]
      -- ⊢ ∃! a, Cycle.formPerm ↑a (_ : Cycle.Nodup ↑a) = f
      exact hf.existsUnique_cycle_nontrivial_subtype)
      -- 🎉 no goals
    invFun := f
    left_inv := Fintype.rightInverse_bijInv _
    right_inv := Fintype.leftInverse_bijInv _ }
#align equiv.perm.iso_cycle' Equiv.Perm.isoCycle'

notation3 "c["(l", "* => foldr (h t => List.cons h t) List.nil)"]" =>
  Cycle.formPerm (Cycle.ofList l) (Iff.mpr Cycle.nodup_coe_iff _)

unsafe instance repr_perm [Repr α] : Repr (Perm α) :=
  ⟨fun f _ => repr (Multiset.pmap (fun (g : Perm α) (hg : g.IsCycle) => isoCycle ⟨g, hg⟩)
    (Perm.cycleFactorsFinset f).val -- toCycle is faster?
    fun _ hg => (mem_cycleFactorsFinset_iff.mp (Finset.mem_def.mpr hg)).left)⟩
#align equiv.perm.repr_perm Equiv.Perm.repr_perm

end Equiv.Perm
