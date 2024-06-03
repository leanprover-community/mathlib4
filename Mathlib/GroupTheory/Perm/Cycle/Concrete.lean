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
  constructor
  · rintro h x hx hx'
    specialize h x
    rw [formPerm_apply_mem_eq_self_iff _ hl _ hx, formPerm_apply_mem_eq_self_iff _ hl' _ hx'] at h
    omega
  · intro h x
    by_cases hx : x ∈ l
    on_goal 1 => by_cases hx' : x ∈ l'
    · exact (h hx hx').elim
    all_goals have := formPerm_eq_self_of_not_mem _ _ ‹_›; tauto
#align list.form_perm_disjoint_iff List.formPerm_disjoint_iff

theorem isCycle_formPerm (hl : Nodup l) (hn : 2 ≤ l.length) : IsCycle (formPerm l) := by
  cases' l with x l
  · set_option tactic.skipAssignedInstances false in norm_num at hn
  induction' l with y l generalizing x
  · set_option tactic.skipAssignedInstances false in norm_num at hn
  · use x
    constructor
    · rwa [formPerm_apply_mem_ne_self_iff _ hl _ (mem_cons_self _ _)]
    · intro w hw
      have : w ∈ x::y::l := mem_of_formPerm_ne_self _ _ hw
      obtain ⟨k, hk⟩ := get_of_mem this
      use k
      rw [← hk]
      simp only [zpow_natCast, formPerm_pow_apply_head _ _ hl k, Nat.mod_eq_of_lt k.isLt]
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
  have hl : l.attach.Nodup := by rwa [← nodup_attach] at hl
  (isCycle_formPerm hl hn).cycleOf_eq
    ((formPerm_apply_mem_ne_self_iff _ hl _ (mem_attach _ _)).mpr hn)
#align list.cycle_of_form_perm List.cycleOf_formPerm

theorem cycleType_formPerm (hl : Nodup l) (hn : 2 ≤ l.length) :
    cycleType l.attach.formPerm = {l.length} := by
  rw [← length_attach] at hn
  rw [← nodup_attach] at hl
  rw [cycleType_eq [l.attach.formPerm]]
  · simp only [map, Function.comp_apply]
    rw [support_formPerm_of_nodup _ hl, card_toFinset, dedup_eq_self.mpr hl]
    · simp
    · intro x h
      simp [h, Nat.succ_le_succ_iff] at hn
  · simp
  · simpa using isCycle_formPerm hl hn
  · simp
#align list.cycle_type_form_perm List.cycleType_formPerm

theorem formPerm_apply_mem_eq_next (hl : Nodup l) (x : α) (hx : x ∈ l) :
    formPerm l x = next l x hx := by
  obtain ⟨k, rfl⟩ := get_of_mem hx
  rw [next_get _ hl, formPerm_apply_get _ hl]
#align list.form_perm_apply_mem_eq_next List.formPerm_apply_mem_eq_next

end List

namespace Cycle

variable [DecidableEq α] (s s' : Cycle α)

/-- A cycle `s : Cycle α`, given `Nodup s` can be interpreted as an `Equiv.Perm α`
where each element in the list is permuted to the next one, defined as `formPerm`.
-/
def formPerm : ∀ s : Cycle α, Nodup s → Equiv.Perm α :=
  fun s => Quotient.hrecOn s (fun l _ => List.formPerm l) fun l₁ l₂ (h : l₁ ~r l₂) => by
    apply Function.hfunext
    · ext
      exact h.nodup_iff
    · intro h₁ h₂ _
      exact heq_of_eq (formPerm_eq_of_isRotated h₁ h)
#align cycle.form_perm Cycle.formPerm

@[simp]
theorem formPerm_coe (l : List α) (hl : l.Nodup) : formPerm (l : Cycle α) hl = l.formPerm :=
  rfl
#align cycle.form_perm_coe Cycle.formPerm_coe

theorem formPerm_subsingleton (s : Cycle α) (h : Subsingleton s) : formPerm s h.nodup = 1 := by
  induction' s using Quot.inductionOn with s
  simp only [formPerm_coe, mk_eq_coe]
  simp only [length_subsingleton_iff, length_coe, mk_eq_coe] at h
  cases' s with hd tl
  · simp
  · simp only [length_eq_zero, add_le_iff_nonpos_left, List.length, nonpos_iff_eq_zero] at h
    simp [h]
#align cycle.form_perm_subsingleton Cycle.formPerm_subsingleton

theorem isCycle_formPerm (s : Cycle α) (h : Nodup s) (hn : Nontrivial s) :
    IsCycle (formPerm s h) := by
  induction s using Quot.inductionOn
  exact List.isCycle_formPerm h (length_nontrivial hn)
#align cycle.is_cycle_form_perm Cycle.isCycle_formPerm

theorem support_formPerm [Fintype α] (s : Cycle α) (h : Nodup s) (hn : Nontrivial s) :
    support (formPerm s h) = s.toFinset := by
  induction' s using Quot.inductionOn with s
  refine support_formPerm_of_nodup s h ?_
  rintro _ rfl
  simpa [Nat.succ_le_succ_iff] using length_nontrivial hn
#align cycle.support_form_perm Cycle.support_formPerm

theorem formPerm_eq_self_of_not_mem (s : Cycle α) (h : Nodup s) (x : α) (hx : x ∉ s) :
    formPerm s h x = x := by
  induction s using Quot.inductionOn
  simpa using List.formPerm_eq_self_of_not_mem _ _ hx
#align cycle.form_perm_eq_self_of_not_mem Cycle.formPerm_eq_self_of_not_mem

theorem formPerm_apply_mem_eq_next (s : Cycle α) (h : Nodup s) (x : α) (hx : x ∈ s) :
    formPerm s h x = next s h x hx := by
  induction s using Quot.inductionOn
  simpa using List.formPerm_apply_mem_eq_next h _ (by simp_all)
#align cycle.form_perm_apply_mem_eq_next Cycle.formPerm_apply_mem_eq_next

nonrec theorem formPerm_reverse (s : Cycle α) (h : Nodup s) :
    formPerm s.reverse (nodup_reverse_iff.mpr h) = (formPerm s h)⁻¹ := by
  induction s using Quot.inductionOn
  simpa using formPerm_reverse _
#align cycle.form_perm_reverse Cycle.formPerm_reverse

nonrec theorem formPerm_eq_formPerm_iff {α : Type*} [DecidableEq α] {s s' : Cycle α} {hs : s.Nodup}
    {hs' : s'.Nodup} :
    s.formPerm hs = s'.formPerm hs' ↔ s = s' ∨ s.Subsingleton ∧ s'.Subsingleton := by
  rw [Cycle.length_subsingleton_iff, Cycle.length_subsingleton_iff]
  revert s s'
  intro s s'
  apply @Quotient.inductionOn₂' _ _ _ _ _ s s'
  intro l l'
  -- Porting note: was `simpa using formPerm_eq_formPerm_iff`
  simp_all
  intro hs hs'
  constructor <;> intro h <;> simp_all only [formPerm_eq_formPerm_iff]
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
#align equiv.perm.to_list_one Equiv.Perm.toList_one

@[simp]
theorem toList_eq_nil_iff {p : Perm α} {x} : toList p x = [] ↔ x ∉ p.support := by simp [toList]
#align equiv.perm.to_list_eq_nil_iff Equiv.Perm.toList_eq_nil_iff

@[simp]
theorem length_toList : length (toList p x) = (cycleOf p x).support.card := by simp [toList]
#align equiv.perm.length_to_list Equiv.Perm.length_toList

theorem toList_ne_singleton (y : α) : toList p x ≠ [y] := by
  intro H
  simpa [card_support_ne_one] using congr_arg length H
#align equiv.perm.to_list_ne_singleton Equiv.Perm.toList_ne_singleton

theorem two_le_length_toList_iff_mem_support {p : Perm α} {x : α} :
    2 ≤ length (toList p x) ↔ x ∈ p.support := by simp
#align equiv.perm.two_le_length_to_list_iff_mem_support Equiv.Perm.two_le_length_toList_iff_mem_support

theorem length_toList_pos_of_mem_support (h : x ∈ p.support) : 0 < length (toList p x) :=
  zero_lt_two.trans_le (two_le_length_toList_iff_mem_support.mpr h)
#align equiv.perm.length_to_list_pos_of_mem_support Equiv.Perm.length_toList_pos_of_mem_support

theorem get_toList (n : ℕ) (hn : n < length (toList p x)) :
    (toList p x).get ⟨n, hn⟩ = (p ^ n) x := by simp [toList]

theorem toList_get_zero (h : x ∈ p.support) :
    (toList p x).get ⟨0, (length_toList_pos_of_mem_support _ _ h)⟩ = x := by simp [toList]

set_option linter.deprecated false in
@[deprecated get_toList (since := "2024-05-08")]
theorem nthLe_toList (n : ℕ) (hn : n < length (toList p x)) :
    (toList p x).nthLe n hn = (p ^ n) x := by simp [toList]
#align equiv.perm.nth_le_to_list Equiv.Perm.nthLe_toList

set_option linter.deprecated false in
@[deprecated toList_get_zero (since := "2024-05-08")]
theorem toList_nthLe_zero (h : x ∈ p.support) :
    (toList p x).nthLe 0 (length_toList_pos_of_mem_support _ _ h) = x := by simp [toList]
#align equiv.perm.to_list_nth_le_zero Equiv.Perm.toList_nthLe_zero

variable {p} {x}

theorem mem_toList_iff {y : α} : y ∈ toList p x ↔ SameCycle p x y ∧ x ∈ p.support := by
  simp only [toList, mem_range, mem_map]
  constructor
  · rintro ⟨n, hx, rfl⟩
    refine ⟨⟨n, rfl⟩, ?_⟩
    contrapose! hx
    rw [← support_cycleOf_eq_nil_iff] at hx
    simp [hx]
  · rintro ⟨h, hx⟩
    simpa using h.exists_pow_eq_of_mem_support hx
#align equiv.perm.mem_to_list_iff Equiv.Perm.mem_toList_iff

set_option linter.deprecated false in
theorem nodup_toList (p : Perm α) (x : α) : Nodup (toList p x) := by
  by_cases hx : p x = x
  · rw [← not_mem_support, ← toList_eq_nil_iff] at hx
    simp [hx]
  have hc : IsCycle (cycleOf p x) := isCycle_cycleOf p hx
  rw [nodup_iff_nthLe_inj]
  rintro n m hn hm
  rw [length_toList, ← hc.orderOf] at hm hn
  rw [← cycleOf_apply_self, ← Ne, ← mem_support] at hx
  rw [nthLe_toList, nthLe_toList, ← cycleOf_pow_apply_self p x n, ←
    cycleOf_pow_apply_self p x m]
  cases' n with n <;> cases' m with m
  · simp
  · rw [← hc.support_pow_of_pos_of_lt_orderOf m.zero_lt_succ hm, mem_support,
      cycleOf_pow_apply_self] at hx
    simp [hx.symm]
  · rw [← hc.support_pow_of_pos_of_lt_orderOf n.zero_lt_succ hn, mem_support,
      cycleOf_pow_apply_self] at hx
    simp [hx]
  intro h
  have hn' : ¬orderOf (p.cycleOf x) ∣ n.succ := Nat.not_dvd_of_pos_of_lt n.zero_lt_succ hn
  have hm' : ¬orderOf (p.cycleOf x) ∣ m.succ := Nat.not_dvd_of_pos_of_lt m.zero_lt_succ hm
  rw [← hc.support_pow_eq_iff] at hn' hm'
  rw [← Nat.mod_eq_of_lt hn, ← Nat.mod_eq_of_lt hm, ← pow_inj_mod]
  refine support_congr ?_ ?_
  · rw [hm', hn']
  · rw [hm']
    intro y hy
    obtain ⟨k, rfl⟩ := hc.exists_pow_eq (mem_support.mp hx) (mem_support.mp hy)
    rw [← mul_apply, (Commute.pow_pow_self _ _ _).eq, mul_apply, h, ← mul_apply, ← mul_apply,
      (Commute.pow_pow_self _ _ _).eq]
#align equiv.perm.nodup_to_list Equiv.Perm.nodup_toList

set_option linter.deprecated false in
theorem next_toList_eq_apply (p : Perm α) (x y : α) (hy : y ∈ toList p x) :
    next (toList p x) y hy = p y := by
  rw [mem_toList_iff] at hy
  obtain ⟨k, hk, hk'⟩ := hy.left.exists_pow_eq_of_mem_support hy.right
  rw [← nthLe_toList p x k (by simpa using hk)] at hk'
  simp_rw [← hk']
  rw [next_nthLe _ (nodup_toList _ _), nthLe_toList, nthLe_toList, ← mul_apply, ← pow_succ',
    length_toList, ← pow_mod_orderOf_cycleOf_apply p (k + 1), IsCycle.orderOf]
  exact isCycle_cycleOf _ (mem_support.mp hy.right)
#align equiv.perm.next_to_list_eq_apply Equiv.Perm.next_toList_eq_apply

set_option linter.deprecated false in
theorem toList_pow_apply_eq_rotate (p : Perm α) (x : α) (k : ℕ) :
    p.toList ((p ^ k) x) = (p.toList x).rotate k := by
  apply ext_nthLe
  · simp only [length_toList, cycleOf_self_apply_pow, length_rotate]
  · intro n hn hn'
    rw [nthLe_toList, nthLe_rotate, nthLe_toList, length_toList,
      pow_mod_card_support_cycleOf_self_apply, pow_add, mul_apply]
#align equiv.perm.to_list_pow_apply_eq_rotate Equiv.Perm.toList_pow_apply_eq_rotate

theorem SameCycle.toList_isRotated {f : Perm α} {x y : α} (h : SameCycle f x y) :
    toList f x ~r toList f y := by
  by_cases hx : x ∈ f.support
  · obtain ⟨_ | k, _, hy⟩ := h.exists_pow_eq_of_mem_support hx
    · simp only [coe_one, id, pow_zero, Nat.zero_eq] at hy
      -- Porting note: added `IsRotated.refl`
      simp [hy, IsRotated.refl]
    use k.succ
    rw [← toList_pow_apply_eq_rotate, hy]
  · rw [toList_eq_nil_iff.mpr hx, isRotated_nil_iff', eq_comm, toList_eq_nil_iff]
    rwa [← h.mem_support_iff]
#align equiv.perm.same_cycle.to_list_is_rotated Equiv.Perm.SameCycle.toList_isRotated

theorem pow_apply_mem_toList_iff_mem_support {n : ℕ} : (p ^ n) x ∈ p.toList x ↔ x ∈ p.support := by
  rw [mem_toList_iff, and_iff_right_iff_imp]
  refine fun _ => SameCycle.symm ?_
  rw [sameCycle_pow_left]
#align equiv.perm.pow_apply_mem_to_list_iff_mem_support Equiv.Perm.pow_apply_mem_toList_iff_mem_support

theorem toList_formPerm_nil (x : α) : toList (formPerm ([] : List α)) x = [] := by simp
#align equiv.perm.to_list_form_perm_nil Equiv.Perm.toList_formPerm_nil

theorem toList_formPerm_singleton (x y : α) : toList (formPerm [x]) y = [] := by simp
#align equiv.perm.to_list_form_perm_singleton Equiv.Perm.toList_formPerm_singleton

theorem toList_formPerm_nontrivial (l : List α) (hl : 2 ≤ l.length) (hn : Nodup l) :
    toList (formPerm l) (l.get ⟨0, (zero_lt_two.trans_le hl)⟩) = l := by
  have hc : l.formPerm.IsCycle := List.isCycle_formPerm hn hl
  have hs : l.formPerm.support = l.toFinset := by
    refine support_formPerm_of_nodup _ hn ?_
    rintro _ rfl
    simp [Nat.succ_le_succ_iff] at hl
  rw [toList, hc.cycleOf_eq (mem_support.mp _), hs, card_toFinset, dedup_eq_self.mpr hn]
  · refine ext_get (by simp) fun k hk hk' => ?_
    simp only [Nat.zero_eq, get_map, get_range, formPerm_pow_apply_get _ hn, zero_add,
      Nat.mod_eq_of_lt hk']
  · simpa [hs] using get_mem _ _ _
#align equiv.perm.to_list_form_perm_nontrivial Equiv.Perm.toList_formPerm_nontrivial

theorem toList_formPerm_isRotated_self (l : List α) (hl : 2 ≤ l.length) (hn : Nodup l) (x : α)
    (hx : x ∈ l) : toList (formPerm l) x ~r l := by
  obtain ⟨k, hk, rfl⟩ := get_of_mem hx
  have hr : l ~r l.rotate k := ⟨k, rfl⟩
  rw [formPerm_eq_of_isRotated hn hr]
  rw [get_eq_get_rotate l k k]
  simp only [Nat.mod_eq_of_lt k.2, tsub_add_cancel_of_le (le_of_lt k.2), Nat.mod_self]
  erw [toList_formPerm_nontrivial]
  · simp
  · simpa using hl
  · simpa using hn
#align equiv.perm.to_list_form_perm_is_rotated_self Equiv.Perm.toList_formPerm_isRotated_self

theorem formPerm_toList (f : Perm α) (x : α) : formPerm (toList f x) = f.cycleOf x := by
  by_cases hx : f x = x
  · rw [(cycleOf_eq_one_iff f).mpr hx, toList_eq_nil_iff.mpr (not_mem_support.mpr hx),
      formPerm_nil]
  ext y
  by_cases hy : SameCycle f x y
  · obtain ⟨k, _, rfl⟩ := hy.exists_pow_eq_of_mem_support (mem_support.mpr hx)
    rw [cycleOf_apply_apply_pow_self, List.formPerm_apply_mem_eq_next (nodup_toList f x),
      next_toList_eq_apply, pow_succ', mul_apply]
    rw [mem_toList_iff]
    exact ⟨⟨k, rfl⟩, mem_support.mpr hx⟩
  · rw [cycleOf_apply_of_not_sameCycle hy, formPerm_apply_of_not_mem]
    simp [mem_toList_iff, hy]
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
      refine heq_of_eq ?_
      split_ifs with hx hy hy <;> try rfl
      have hc : SameCycle f x y := IsCycle.sameCycle hf hx hy
      exact Quotient.sound' hc.toList_isRotated)
#align equiv.perm.to_cycle Equiv.Perm.toCycle

theorem toCycle_eq_toList (f : Perm α) (hf : IsCycle f) (x : α) (hx : f x ≠ x) :
    toCycle f hf = toList f x := by
  have key : (Finset.univ : Finset α).val = x ::ₘ Finset.univ.val.erase x := by simp
  rw [toCycle, key]
  simp [hx]
#align equiv.perm.to_cycle_eq_to_list Equiv.Perm.toCycle_eq_toList

theorem nodup_toCycle (f : Perm α) (hf : IsCycle f) : (toCycle f hf).Nodup := by
  obtain ⟨x, hx, -⟩ := id hf
  simpa [toCycle_eq_toList f hf x hx] using nodup_toList _ _
#align equiv.perm.nodup_to_cycle Equiv.Perm.nodup_toCycle

theorem nontrivial_toCycle (f : Perm α) (hf : IsCycle f) : (toCycle f hf).Nontrivial := by
  obtain ⟨x, hx, -⟩ := id hf
  simp [toCycle_eq_toList f hf x hx, hx, Cycle.nontrivial_coe_nodup_iff (nodup_toList _ _)]
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
    simpa [toCycle_eq_toList (f : Perm α) f.prop x hx, formPerm_toList, Subtype.ext_iff] using
      f.prop.cycleOf_eq hx
  right_inv s := by
    rcases s with ⟨⟨s⟩, hn, ht⟩
    obtain ⟨x, -, -, hx, -⟩ := id ht
    have hl : 2 ≤ s.length := by simpa using Cycle.length_nontrivial ht
    simp only [Cycle.mk_eq_coe, Cycle.nodup_coe_iff, Cycle.mem_coe_iff, Subtype.coe_mk,
      Cycle.formPerm_coe] at hn hx ⊢
    apply Subtype.ext
    dsimp
    rw [toCycle_eq_toList _ _ x]
    · refine Quotient.sound' ?_
      exact toList_formPerm_isRotated_self _ hl hn _ hx
    · rw [← mem_support, support_formPerm_of_nodup _ hn]
      · simpa using hx
      · rintro _ rfl
        simp [Nat.succ_le_succ_iff] at hl
#align equiv.perm.iso_cycle Equiv.Perm.isoCycle

end Fintype

section Finite

variable [Finite α] [DecidableEq α]

theorem IsCycle.existsUnique_cycle {f : Perm α} (hf : IsCycle f) :
    ∃! s : Cycle α, ∃ h : s.Nodup, s.formPerm h = f := by
  cases nonempty_fintype α
  obtain ⟨x, hx, hy⟩ := id hf
  refine ⟨f.toList x, ⟨nodup_toList f x, ?_⟩, ?_⟩
  · simp [formPerm_toList, hf.cycleOf_eq hx]
  · rintro ⟨l⟩ ⟨hn, rfl⟩
    simp only [Cycle.mk_eq_coe, Cycle.coe_eq_coe, Subtype.coe_mk, Cycle.formPerm_coe]
    refine (toList_formPerm_isRotated_self _ ?_ hn _ ?_).symm
    · contrapose! hx
      suffices formPerm l = 1 by simp [this]
      rw [formPerm_eq_one_iff _ hn]
      exact Nat.le_of_lt_succ hx
    · rw [← mem_toFinset]
      refine support_formPerm_le l ?_
      simpa using hx
#align equiv.perm.is_cycle.exists_unique_cycle Equiv.Perm.IsCycle.existsUnique_cycle

theorem IsCycle.existsUnique_cycle_subtype {f : Perm α} (hf : IsCycle f) :
    ∃! s : { s : Cycle α // s.Nodup }, (s : Cycle α).formPerm s.prop = f := by
  obtain ⟨s, ⟨hs, rfl⟩, hs'⟩ := hf.existsUnique_cycle
  refine ⟨⟨s, hs⟩, rfl, ?_⟩
  rintro ⟨t, ht⟩ ht'
  simpa using hs' _ ⟨ht, ht'⟩
#align equiv.perm.is_cycle.exists_unique_cycle_subtype Equiv.Perm.IsCycle.existsUnique_cycle_subtype

theorem IsCycle.existsUnique_cycle_nontrivial_subtype {f : Perm α} (hf : IsCycle f) :
    ∃! s : { s : Cycle α // s.Nodup ∧ s.Nontrivial }, (s : Cycle α).formPerm s.prop.left = f := by
  obtain ⟨⟨s, hn⟩, hs, hs'⟩ := hf.existsUnique_cycle_subtype
  refine ⟨⟨s, hn, ?_⟩, ?_, ?_⟩
  · rw [hn.nontrivial_iff]
    subst f
    intro H
    refine hf.ne_one ?_
    simpa using Cycle.formPerm_subsingleton _ H
  · simpa using hs
  · rintro ⟨t, ht, ht'⟩ ht''
    simpa using hs' ⟨t, ht⟩ ht''
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
      rintro ⟨f, hf⟩
      simp only [Subtype.ext_iff]
      exact hf.existsUnique_cycle_nontrivial_subtype)
    invFun := f
    left_inv := Fintype.rightInverse_bijInv _
    right_inv := Fintype.leftInverse_bijInv _ }
#align equiv.perm.iso_cycle' Equiv.Perm.isoCycle'

notation3 (prettyPrint := false) "c["(l", "* => foldr (h t => List.cons h t) List.nil)"]" =>
  Cycle.formPerm (Cycle.ofList l) (Iff.mpr Cycle.nodup_coe_iff (by decide))

unsafe instance repr_perm [Repr α] : Repr (Perm α) :=
  ⟨fun f _ => repr (Multiset.pmap (fun (g : Perm α) (hg : g.IsCycle) => isoCycle ⟨g, hg⟩)
    (Perm.cycleFactorsFinset f).val -- toCycle is faster?
    fun _ hg => (mem_cycleFactorsFinset_iff.mp (Finset.mem_def.mpr hg)).left)⟩
#align equiv.perm.repr_perm Equiv.Perm.repr_perm

end Equiv.Perm
