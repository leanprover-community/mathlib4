/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky

! This file was ported from Lean 3 source module group_theory.perm.cycle.concrete
! leanprover-community/mathlib commit 00638177efd1b2534fc5269363ebf42a7871df9a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Cycle
import Mathbin.GroupTheory.Perm.Cycle.Type
import Mathbin.GroupTheory.Perm.List

/-!

# Properties of cyclic permutations constructed from lists/cycles

In the following, `{α : Type*} [fintype α] [decidable_eq α]`.

## Main definitions

* `cycle.form_perm`: the cyclic permutation created by looping over a `cycle α`
* `equiv.perm.to_list`: the list formed by iterating application of a permutation
* `equiv.perm.to_cycle`: the cycle formed by iterating application of a permutation
* `equiv.perm.iso_cycle`: the equivalence between cyclic permutations `f : perm α`
  and the terms of `cycle α` that correspond to them
* `equiv.perm.iso_cycle'`: the same equivalence as `equiv.perm.iso_cycle`
  but with evaluation via choosing over fintypes
* The notation `c[1, 2, 3]` to emulate notation of cyclic permutations `(1 2 3)`
* A `has_repr` instance for any `perm α`, by representing the `finset` of
  `cycle α` that correspond to the cycle factors.

## Main results

* `list.is_cycle_form_perm`: a nontrivial list without duplicates, when interpreted as
  a permutation, is cyclic
* `equiv.perm.is_cycle.exists_unique_cycle`: there is only one nontrivial `cycle α`
  corresponding to each cyclic `f : perm α`

## Implementation details

The forward direction of `equiv.perm.iso_cycle'` uses `fintype.choose` of the uniqueness
result, relying on the `fintype` instance of a `cycle.nodup` subtype.
It is unclear if this works faster than the `equiv.perm.to_cycle`, which relies
on recursion over `finset.univ`.
Running `#eval` on even a simple noncyclic permutation `c[(1 : fin 7), 2, 3] * c[0, 5]`
to show it takes a long time. TODO: is this because computing the cycle factors is slow?

-/


open Equiv Equiv.Perm List

variable {α : Type _}

namespace List

variable [DecidableEq α] {l l' : List α}

theorem formPerm_disjoint_iff (hl : Nodup l) (hl' : Nodup l') (hn : 2 ≤ l.length)
    (hn' : 2 ≤ l'.length) : Perm.Disjoint (formPerm l) (formPerm l') ↔ l.Disjoint l' :=
  by
  rw [disjoint_iff_eq_or_eq, List.Disjoint]
  constructor
  · rintro h x hx hx'
    specialize h x
    rw [form_perm_apply_mem_eq_self_iff _ hl _ hx, form_perm_apply_mem_eq_self_iff _ hl' _ hx'] at h
    rcases h with (hl | hl') <;> linarith
  · intro h x
    by_cases hx : x ∈ l
    by_cases hx' : x ∈ l'
    · exact (h hx hx').elim
    all_goals have := form_perm_eq_self_of_not_mem _ _ ‹_›; tauto
#align list.form_perm_disjoint_iff List.formPerm_disjoint_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem isCycle_formPerm (hl : Nodup l) (hn : 2 ≤ l.length) : IsCycle (formPerm l) :=
  by
  cases' l with x l
  · norm_num at hn
  induction' l with y l IH generalizing x
  · norm_num at hn
  · use x
    constructor
    · rwa [form_perm_apply_mem_ne_self_iff _ hl _ (mem_cons_self _ _)]
    · intro w hw
      have : w ∈ x::y::l := mem_of_form_perm_ne_self _ _ hw
      obtain ⟨k, hk, rfl⟩ := nth_le_of_mem this
      use k
      simp only [zpow_ofNat, form_perm_pow_apply_head _ _ hl k, Nat.mod_eq_of_lt hk]
#align list.is_cycle_form_perm List.isCycle_formPerm

theorem pairwise_sameCycle_formPerm (hl : Nodup l) (hn : 2 ≤ l.length) :
    Pairwise l.formPerm.SameCycle l :=
  Pairwise.imp_mem.mpr
    (pairwise_of_forall fun x y hx hy =>
      (isCycle_formPerm hl hn).SameCycle ((formPerm_apply_mem_ne_self_iff _ hl _ hx).mpr hn)
        ((formPerm_apply_mem_ne_self_iff _ hl _ hy).mpr hn))
#align list.pairwise_same_cycle_form_perm List.pairwise_sameCycle_formPerm

theorem cycleOf_formPerm (hl : Nodup l) (hn : 2 ≤ l.length) (x) :
    cycleOf l.attach.formPerm x = l.attach.formPerm :=
  have hn : 2 ≤ l.attach.length := by rwa [← length_attach] at hn
  have hl : l.attach.Nodup := by rwa [← nodup_attach] at hl
  (isCycle_formPerm hl hn).cycleOf_eq
    ((formPerm_apply_mem_ne_self_iff _ hl _ (mem_attach _ _)).mpr hn)
#align list.cycle_of_form_perm List.cycleOf_formPerm

theorem cycleType_formPerm (hl : Nodup l) (hn : 2 ≤ l.length) :
    cycleType l.attach.formPerm = {l.length} :=
  by
  rw [← length_attach] at hn
  rw [← nodup_attach] at hl
  rw [cycle_type_eq [l.attach.form_perm]]
  · simp only [map, Function.comp_apply]
    rw [support_form_perm_of_nodup _ hl, card_to_finset, dedup_eq_self.mpr hl]
    · simp
    · intro x h
      simpa [h, Nat.succ_le_succ_iff] using hn
  · simp
  · simpa using is_cycle_form_perm hl hn
  · simp
#align list.cycle_type_form_perm List.cycleType_formPerm

theorem formPerm_apply_mem_eq_next (hl : Nodup l) (x : α) (hx : x ∈ l) :
    formPerm l x = next l x hx :=
  by
  obtain ⟨k, hk, rfl⟩ := nth_le_of_mem hx
  rw [next_nth_le _ hl, form_perm_apply_nth_le _ hl]
#align list.form_perm_apply_mem_eq_next List.formPerm_apply_mem_eq_next

end List

namespace Cycle

variable [DecidableEq α] (s s' : Cycle α)

/-- A cycle `s : cycle α` , given `nodup s` can be interpreted as a `equiv.perm α`
where each element in the list is permuted to the next one, defined as `form_perm`.
-/
def formPerm : ∀ (s : Cycle α) (h : Nodup s), Equiv.Perm α := fun s =>
  Quot.hrecOn s (fun l h => formPerm l) fun l₁ l₂ (h : l₁ ~r l₂) =>
    by
    ext
    · exact h.nodup_iff
    · intro h₁ h₂ _
      exact hEq_of_eq (form_perm_eq_of_is_rotated h₁ h)
#align cycle.form_perm Cycle.formPerm

@[simp]
theorem formPerm_coe (l : List α) (hl : l.Nodup) : formPerm (l : Cycle α) hl = l.formPerm :=
  rfl
#align cycle.form_perm_coe Cycle.formPerm_coe

theorem formPerm_subsingleton (s : Cycle α) (h : Subsingleton s) : formPerm s h.Nodup = 1 :=
  by
  induction s using Quot.inductionOn
  simp only [form_perm_coe, mk_eq_coe]
  simp only [length_subsingleton_iff, length_coe, mk_eq_coe] at h
  cases' s with hd tl
  · simp
  · simp only [length_eq_zero, add_le_iff_nonpos_left, List.length, nonpos_iff_eq_zero] at h
    simp [h]
#align cycle.form_perm_subsingleton Cycle.formPerm_subsingleton

theorem isCycle_formPerm (s : Cycle α) (h : Nodup s) (hn : Nontrivial s) : IsCycle (formPerm s h) :=
  by
  induction s using Quot.inductionOn
  exact List.isCycle_formPerm h (length_nontrivial hn)
#align cycle.is_cycle_form_perm Cycle.isCycle_formPerm

theorem support_formPerm [Fintype α] (s : Cycle α) (h : Nodup s) (hn : Nontrivial s) :
    support (formPerm s h) = s.toFinset :=
  by
  induction s using Quot.inductionOn
  refine' support_form_perm_of_nodup s h _
  rintro _ rfl
  simpa [Nat.succ_le_succ_iff] using length_nontrivial hn
#align cycle.support_form_perm Cycle.support_formPerm

theorem formPerm_eq_self_of_not_mem (s : Cycle α) (h : Nodup s) (x : α) (hx : x ∉ s) :
    formPerm s h x = x := by
  induction s using Quot.inductionOn
  simpa using List.formPerm_eq_self_of_not_mem _ _ hx
#align cycle.form_perm_eq_self_of_not_mem Cycle.formPerm_eq_self_of_not_mem

theorem formPerm_apply_mem_eq_next (s : Cycle α) (h : Nodup s) (x : α) (hx : x ∈ s) :
    formPerm s h x = next s h x hx :=
  by
  induction s using Quot.inductionOn
  simpa using List.formPerm_apply_mem_eq_next h _ _
#align cycle.form_perm_apply_mem_eq_next Cycle.formPerm_apply_mem_eq_next

theorem formPerm_reverse (s : Cycle α) (h : Nodup s) :
    formPerm s.reverse (nodup_reverse_iff.mpr h) = (formPerm s h)⁻¹ :=
  by
  induction s using Quot.inductionOn
  simpa using form_perm_reverse _ h
#align cycle.form_perm_reverse Cycle.formPerm_reverse

theorem formPerm_eq_formPerm_iff {α : Type _} [DecidableEq α] {s s' : Cycle α} {hs : s.Nodup}
    {hs' : s'.Nodup} :
    s.formPerm hs = s'.formPerm hs' ↔ s = s' ∨ s.Subsingleton ∧ s'.Subsingleton :=
  by
  rw [Cycle.length_subsingleton_iff, Cycle.length_subsingleton_iff]
  revert s s'
  intro s s'
  apply Quotient.inductionOn₂' s s'
  intro l l'
  simpa using form_perm_eq_form_perm_iff
#align cycle.form_perm_eq_form_perm_iff Cycle.formPerm_eq_formPerm_iff

end Cycle

namespace Equiv.Perm

section Fintype

variable [Fintype α] [DecidableEq α] (p : Equiv.Perm α) (x : α)

/-- `equiv.perm.to_list (f : perm α) (x : α)` generates the list `[x, f x, f (f x), ...]`
until looping. That means when `f x = x`, `to_list f x = []`.
-/
def toList : List α :=
  (List.range (cycleOf p x).support.card).map fun k => (p ^ k) x
#align equiv.perm.to_list Equiv.Perm.toList

@[simp]
theorem toList_one : toList (1 : Perm α) x = [] := by simp [to_list, cycle_of_one]
#align equiv.perm.to_list_one Equiv.Perm.toList_one

@[simp]
theorem toList_eq_nil_iff {p : Perm α} {x} : toList p x = [] ↔ x ∉ p.support := by simp [to_list]
#align equiv.perm.to_list_eq_nil_iff Equiv.Perm.toList_eq_nil_iff

@[simp]
theorem length_toList : length (toList p x) = (cycleOf p x).support.card := by simp [to_list]
#align equiv.perm.length_to_list Equiv.Perm.length_toList

theorem toList_ne_singleton (y : α) : toList p x ≠ [y] :=
  by
  intro H
  simpa [card_support_ne_one] using congr_arg length H
#align equiv.perm.to_list_ne_singleton Equiv.Perm.toList_ne_singleton

theorem two_le_length_toList_iff_mem_support {p : Perm α} {x : α} :
    2 ≤ length (toList p x) ↔ x ∈ p.support := by simp
#align equiv.perm.two_le_length_to_list_iff_mem_support Equiv.Perm.two_le_length_toList_iff_mem_support

theorem length_toList_pos_of_mem_support (h : x ∈ p.support) : 0 < length (toList p x) :=
  zero_lt_two.trans_le (two_le_length_toList_iff_mem_support.mpr h)
#align equiv.perm.length_to_list_pos_of_mem_support Equiv.Perm.length_toList_pos_of_mem_support

theorem nthLe_toList (n : ℕ) (hn : n < length (toList p x)) : nthLe (toList p x) n hn = (p ^ n) x :=
  by simp [to_list]
#align equiv.perm.nth_le_to_list Equiv.Perm.nthLe_toList

theorem toList_nthLe_zero (h : x ∈ p.support) :
    (toList p x).nthLe 0 (length_toList_pos_of_mem_support _ _ h) = x := by simp [to_list]
#align equiv.perm.to_list_nth_le_zero Equiv.Perm.toList_nthLe_zero

variable {p} {x}

theorem mem_toList_iff {y : α} : y ∈ toList p x ↔ SameCycle p x y ∧ x ∈ p.support :=
  by
  simp only [to_list, mem_range, mem_map]
  constructor
  · rintro ⟨n, hx, rfl⟩
    refine' ⟨⟨n, rfl⟩, _⟩
    contrapose! hx
    rw [← support_cycle_of_eq_nil_iff] at hx
    simp [hx]
  · rintro ⟨h, hx⟩
    simpa using h.exists_pow_eq_of_mem_support hx
#align equiv.perm.mem_to_list_iff Equiv.Perm.mem_toList_iff

theorem nodup_toList (p : Perm α) (x : α) : Nodup (toList p x) :=
  by
  by_cases hx : p x = x
  · rw [← not_mem_support, ← to_list_eq_nil_iff] at hx
    simp [hx]
  have hc : is_cycle (cycle_of p x) := is_cycle_cycle_of p hx
  rw [nodup_iff_nth_le_inj]
  rintro n m hn hm
  rw [length_to_list, ← hc.order_of] at hm hn
  rw [← cycle_of_apply_self, ← Ne.def, ← mem_support] at hx
  rw [nth_le_to_list, nth_le_to_list, ← cycle_of_pow_apply_self p x n, ←
    cycle_of_pow_apply_self p x m]
  cases n <;> cases m
  · simp
  · rw [← hc.support_pow_of_pos_of_lt_order_of m.zero_lt_succ hm, mem_support,
      cycle_of_pow_apply_self] at hx
    simp [hx.symm]
  · rw [← hc.support_pow_of_pos_of_lt_order_of n.zero_lt_succ hn, mem_support,
      cycle_of_pow_apply_self] at hx
    simp [hx]
  intro h
  have hn' : ¬orderOf (p.cycle_of x) ∣ n.succ := Nat.not_dvd_of_pos_of_lt n.zero_lt_succ hn
  have hm' : ¬orderOf (p.cycle_of x) ∣ m.succ := Nat.not_dvd_of_pos_of_lt m.zero_lt_succ hm
  rw [← hc.support_pow_eq_iff] at hn' hm'
  rw [← Nat.mod_eq_of_lt hn, ← Nat.mod_eq_of_lt hm, ← pow_inj_mod]
  refine' support_congr _ _
  · rw [hm', hn']
    exact Finset.Subset.refl _
  · rw [hm']
    intro y hy
    obtain ⟨k, rfl⟩ := hc.exists_pow_eq (mem_support.mp hx) (mem_support.mp hy)
    rw [← mul_apply, (Commute.pow_pow_self _ _ _).Eq, mul_apply, h, ← mul_apply, ← mul_apply,
      (Commute.pow_pow_self _ _ _).Eq]
#align equiv.perm.nodup_to_list Equiv.Perm.nodup_toList

theorem next_toList_eq_apply (p : Perm α) (x y : α) (hy : y ∈ toList p x) :
    next (toList p x) y hy = p y := by
  rw [mem_to_list_iff] at hy
  obtain ⟨k, hk, hk'⟩ := hy.left.exists_pow_eq_of_mem_support hy.right
  rw [← nth_le_to_list p x k (by simpa using hk)] at hk'
  simp_rw [← hk']
  rw [next_nth_le _ (nodup_to_list _ _), nth_le_to_list, nth_le_to_list, ← mul_apply, ← pow_succ,
    length_to_list, pow_apply_eq_pow_mod_order_of_cycle_of_apply p (k + 1), is_cycle.order_of]
  exact is_cycle_cycle_of _ (mem_support.mp hy.right)
#align equiv.perm.next_to_list_eq_apply Equiv.Perm.next_toList_eq_apply

theorem toList_pow_apply_eq_rotate (p : Perm α) (x : α) (k : ℕ) :
    p.toList ((p ^ k) x) = (p.toList x).rotate k :=
  by
  apply ext_le
  · simp only [length_to_list, cycle_of_self_apply_pow, length_rotate]
  · intro n hn hn'
    rw [nth_le_to_list, nth_le_rotate, nth_le_to_list, length_to_list,
      pow_mod_card_support_cycle_of_self_apply, pow_add, mul_apply]
#align equiv.perm.to_list_pow_apply_eq_rotate Equiv.Perm.toList_pow_apply_eq_rotate

theorem SameCycle.toList_isRotated {f : Perm α} {x y : α} (h : SameCycle f x y) :
    toList f x ~r toList f y := by
  by_cases hx : x ∈ f.support
  · obtain ⟨_ | k, hk, hy⟩ := h.exists_pow_eq_of_mem_support hx
    · simp only [coe_one, id.def, pow_zero] at hy
      simp [hy]
    use k.succ
    rw [← to_list_pow_apply_eq_rotate, hy]
  · rw [to_list_eq_nil_iff.mpr hx, is_rotated_nil_iff', eq_comm, to_list_eq_nil_iff]
    rwa [← h.mem_support_iff]
#align equiv.perm.same_cycle.to_list_is_rotated Equiv.Perm.SameCycle.toList_isRotated

theorem pow_apply_mem_toList_iff_mem_support {n : ℕ} : (p ^ n) x ∈ p.toList x ↔ x ∈ p.support :=
  by
  rw [mem_to_list_iff, and_iff_right_iff_imp]
  refine' fun _ => same_cycle.symm _
  rw [same_cycle_pow_left]
#align equiv.perm.pow_apply_mem_to_list_iff_mem_support Equiv.Perm.pow_apply_mem_toList_iff_mem_support

theorem toList_formPerm_nil (x : α) : toList (formPerm ([] : List α)) x = [] := by simp
#align equiv.perm.to_list_form_perm_nil Equiv.Perm.toList_formPerm_nil

theorem toList_formPerm_singleton (x y : α) : toList (formPerm [x]) y = [] := by simp
#align equiv.perm.to_list_form_perm_singleton Equiv.Perm.toList_formPerm_singleton

theorem toList_formPerm_nontrivial (l : List α) (hl : 2 ≤ l.length) (hn : Nodup l) :
    toList (formPerm l) (l.nthLe 0 (zero_lt_two.trans_le hl)) = l :=
  by
  have hc : l.form_perm.is_cycle := List.isCycle_formPerm hn hl
  have hs : l.form_perm.support = l.to_finset :=
    by
    refine' support_form_perm_of_nodup _ hn _
    rintro _ rfl
    simpa [Nat.succ_le_succ_iff] using hl
  rw [to_list, hc.cycle_of_eq (mem_support.mp _), hs, card_to_finset, dedup_eq_self.mpr hn]
  · refine' List.ext_nthLe (by simp) fun k hk hk' => _
    simp [form_perm_pow_apply_nth_le _ hn, Nat.mod_eq_of_lt hk']
  · simpa [hs] using nth_le_mem _ _ _
#align equiv.perm.to_list_form_perm_nontrivial Equiv.Perm.toList_formPerm_nontrivial

theorem toList_formPerm_isRotated_self (l : List α) (hl : 2 ≤ l.length) (hn : Nodup l) (x : α)
    (hx : x ∈ l) : toList (formPerm l) x ~r l :=
  by
  obtain ⟨k, hk, rfl⟩ := nth_le_of_mem hx
  have hr : l ~r l.rotate k := ⟨k, rfl⟩
  rw [form_perm_eq_of_is_rotated hn hr]
  rw [← nth_le_rotate' l k k]
  simp only [Nat.mod_eq_of_lt hk, tsub_add_cancel_of_le hk.le, Nat.mod_self]
  rw [to_list_form_perm_nontrivial]
  · simp
  · simpa using hl
  · simpa using hn
#align equiv.perm.to_list_form_perm_is_rotated_self Equiv.Perm.toList_formPerm_isRotated_self

theorem formPerm_toList (f : Perm α) (x : α) : formPerm (toList f x) = f.cycleOf x :=
  by
  by_cases hx : f x = x
  ·
    rw [(cycle_of_eq_one_iff f).mpr hx, to_list_eq_nil_iff.mpr (not_mem_support.mpr hx),
      form_perm_nil]
  ext y
  by_cases hy : same_cycle f x y
  · obtain ⟨k, hk, rfl⟩ := hy.exists_pow_eq_of_mem_support (mem_support.mpr hx)
    rw [cycle_of_apply_apply_pow_self, List.formPerm_apply_mem_eq_next (nodup_to_list f x),
      next_to_list_eq_apply, pow_succ, mul_apply]
    rw [mem_to_list_iff]
    exact ⟨⟨k, rfl⟩, mem_support.mpr hx⟩
  · rw [cycle_of_apply_of_not_same_cycle hy, form_perm_apply_of_not_mem]
    simp [mem_to_list_iff, hy]
#align equiv.perm.form_perm_to_list Equiv.Perm.formPerm_toList

/-- Given a cyclic `f : perm α`, generate the `cycle α` in the order
of application of `f`. Implemented by finding an element `x : α`
in the support of `f` in `finset.univ`, and iterating on using
`equiv.perm.to_list f x`.
-/
def toCycle (f : Perm α) (hf : IsCycle f) : Cycle α :=
  Multiset.recOn (Finset.univ : Finset α).val (Quot.mk _ [])
    (fun x s l => if f x = x then l else toList f x)
    (by
      intro x y m s
      refine' hEq_of_eq _
      split_ifs with hx hy hy <;> try rfl
      · have hc : same_cycle f x y := is_cycle.same_cycle hf hx hy
        exact Quotient.sound' hc.to_list_is_rotated)
#align equiv.perm.to_cycle Equiv.Perm.toCycle

theorem toCycle_eq_toList (f : Perm α) (hf : IsCycle f) (x : α) (hx : f x ≠ x) :
    toCycle f hf = toList f x :=
  by
  have key : (Finset.univ : Finset α).val = x ::ₘ finset.univ.val.erase x := by simp
  rw [to_cycle, key]
  simp [hx]
#align equiv.perm.to_cycle_eq_to_list Equiv.Perm.toCycle_eq_toList

theorem nodup_toCycle (f : Perm α) (hf : IsCycle f) : (toCycle f hf).Nodup :=
  by
  obtain ⟨x, hx, -⟩ := id hf
  simpa [to_cycle_eq_to_list f hf x hx] using nodup_to_list _ _
#align equiv.perm.nodup_to_cycle Equiv.Perm.nodup_toCycle

theorem nontrivial_toCycle (f : Perm α) (hf : IsCycle f) : (toCycle f hf).Nontrivial :=
  by
  obtain ⟨x, hx, -⟩ := id hf
  simp [to_cycle_eq_to_list f hf x hx, hx, Cycle.nontrivial_coe_nodup_iff (nodup_to_list _ _)]
#align equiv.perm.nontrivial_to_cycle Equiv.Perm.nontrivial_toCycle

/-- Any cyclic `f : perm α` is isomorphic to the nontrivial `cycle α`
that corresponds to repeated application of `f`.
The forward direction is implemented by `equiv.perm.to_cycle`.
-/
def isoCycle : { f : Perm α // IsCycle f } ≃ { s : Cycle α // s.Nodup ∧ s.Nontrivial }
    where
  toFun f := ⟨toCycle (f : Perm α) f.Prop, nodup_toCycle f f.Prop, nontrivial_toCycle _ f.Prop⟩
  invFun s := ⟨(s : Cycle α).formPerm s.Prop.left, (s : Cycle α).isCycle_formPerm _ s.Prop.right⟩
  left_inv f := by
    obtain ⟨x, hx, -⟩ := id f.prop
    simpa [to_cycle_eq_to_list (f : perm α) f.prop x hx, form_perm_to_list, Subtype.ext_iff] using
      f.prop.cycle_of_eq hx
  right_inv s := by
    rcases s with ⟨⟨s⟩, hn, ht⟩
    obtain ⟨x, -, -, hx, -⟩ := id ht
    have hl : 2 ≤ s.length := by simpa using Cycle.length_nontrivial ht
    simp only [Cycle.mk_eq_coe, Cycle.nodup_coe_iff, Cycle.mem_coe_iff, Subtype.coe_mk,
      Cycle.formPerm_coe] at hn hx⊢
    rw [to_cycle_eq_to_list _ _ x]
    · refine' Quotient.sound' _
      exact to_list_form_perm_is_rotated_self _ hl hn _ hx
    · rw [← mem_support, support_form_perm_of_nodup _ hn]
      · simpa using hx
      · rintro _ rfl
        simpa [Nat.succ_le_succ_iff] using hl
#align equiv.perm.iso_cycle Equiv.Perm.isoCycle

end Fintype

section Finite

variable [Finite α] [DecidableEq α]

theorem IsCycle.existsUnique_cycle {f : Perm α} (hf : IsCycle f) :
    ∃! s : Cycle α, ∃ h : s.Nodup, s.formPerm h = f :=
  by
  cases nonempty_fintype α
  obtain ⟨x, hx, hy⟩ := id hf
  refine' ⟨f.to_list x, ⟨nodup_to_list f x, _⟩, _⟩
  · simp [form_perm_to_list, hf.cycle_of_eq hx]
  · rintro ⟨l⟩ ⟨hn, rfl⟩
    simp only [Cycle.mk_eq_coe, Cycle.coe_eq_coe, Subtype.coe_mk, Cycle.formPerm_coe]
    refine' (to_list_form_perm_is_rotated_self _ _ hn _ _).symm
    · contrapose! hx
      suffices form_perm l = 1 by simp [this]
      rw [form_perm_eq_one_iff _ hn]
      exact Nat.le_of_lt_succ hx
    · rw [← mem_to_finset]
      refine' support_form_perm_le l _
      simpa using hx
#align equiv.perm.is_cycle.exists_unique_cycle Equiv.Perm.IsCycle.existsUnique_cycle

theorem IsCycle.existsUnique_cycle_subtype {f : Perm α} (hf : IsCycle f) :
    ∃! s : { s : Cycle α // s.Nodup }, (s : Cycle α).formPerm s.Prop = f :=
  by
  obtain ⟨s, ⟨hs, rfl⟩, hs'⟩ := hf.exists_unique_cycle
  refine' ⟨⟨s, hs⟩, rfl, _⟩
  rintro ⟨t, ht⟩ ht'
  simpa using hs' _ ⟨ht, ht'⟩
#align equiv.perm.is_cycle.exists_unique_cycle_subtype Equiv.Perm.IsCycle.existsUnique_cycle_subtype

theorem IsCycle.existsUnique_cycle_nontrivial_subtype {f : Perm α} (hf : IsCycle f) :
    ∃! s : { s : Cycle α // s.Nodup ∧ s.Nontrivial }, (s : Cycle α).formPerm s.Prop.left = f :=
  by
  obtain ⟨⟨s, hn⟩, hs, hs'⟩ := hf.exists_unique_cycle_subtype
  refine' ⟨⟨s, hn, _⟩, _, _⟩
  · rw [hn.nontrivial_iff]
    subst f
    intro H
    refine' hf.ne_one _
    simpa using Cycle.formPerm_subsingleton _ H
  · simpa using hs
  · rintro ⟨t, ht, ht'⟩ ht''
    simpa using hs' ⟨t, ht⟩ ht''
#align equiv.perm.is_cycle.exists_unique_cycle_nontrivial_subtype Equiv.Perm.IsCycle.existsUnique_cycle_nontrivial_subtype

end Finite

variable [Fintype α] [DecidableEq α]

/-- Any cyclic `f : perm α` is isomorphic to the nontrivial `cycle α`
that corresponds to repeated application of `f`.
The forward direction is implemented by finding this `cycle α` using `fintype.choose`.
-/
def isoCycle' : { f : Perm α // IsCycle f } ≃ { s : Cycle α // s.Nodup ∧ s.Nontrivial }
    where
  toFun f := Fintype.choose _ f.Prop.existsUnique_cycle_nontrivial_subtype
  invFun s := ⟨(s : Cycle α).formPerm s.Prop.left, (s : Cycle α).isCycle_formPerm _ s.Prop.right⟩
  left_inv f := by
    simpa [Subtype.ext_iff] using
      Fintype.choose_spec _ f.prop.exists_unique_cycle_nontrivial_subtype
  right_inv := fun ⟨s, hs, ht⟩ => by
    simp [Subtype.coe_mk]
    convert Fintype.choose_subtype_eq (fun s' : Cycle α => s'.Nodup ∧ s'.Nontrivial) _
    ext ⟨s', hs', ht'⟩
    simp [Cycle.formPerm_eq_formPerm_iff, iff_not_comm.mp hs.nontrivial_iff,
      iff_not_comm.mp hs'.nontrivial_iff, ht]
#align equiv.perm.iso_cycle' Equiv.Perm.isoCycle'

-- mathport name: «exprc[ ,]»
notation3"c["(l", "* => foldr (h t => List.cons h t) List.nil)"]" =>
  Cycle.formPerm (↑l) (Cycle.nodup_coe_iff.mpr (by decide))

unsafe instance repr_perm [Repr α] : Repr (Perm α) :=
  ⟨fun f =>
    repr
      (Multiset.pmap (fun (g : Perm α) (hg : g.IsCycle) => isoCycle ⟨g, hg⟩)
        (-- to_cycle is faster?
            Perm.cycleFactorsFinset
            f).val
        fun g hg => (mem_cycleFactorsFinset_iff.mp (Finset.mem_def.mpr hg)).left)⟩
#align equiv.perm.repr_perm equiv.perm.repr_perm

end Equiv.Perm

