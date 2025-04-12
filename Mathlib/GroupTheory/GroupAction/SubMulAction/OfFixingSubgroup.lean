/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer


/-!
# Sub_mul_actions on complements of invariant subsets

- We define sub_mul_action of an invariant subset in various contexts,
especially stabilizers and fixing subgroups : `sub_mul_action_of_compl`,
`sub_mul_action_of_stabilizer`, `sub_mul_action_of_fixing_subgroup`.

- We define equivariant maps that relate various of these sub_mul_actions
and permit to manipulate them in a relatively smooth way.
-/

open scoped Pointwise

open MulAction

namespace SubMulAction

variable (M : Type*) [Group M] {α : Type*} [MulAction M α]

/-- The SubMulAction of `fixingSubgroup M s` on the complement of `s` -/
def ofFixingSubgroup (s : Set α) : SubMulAction (fixingSubgroup M s) α where
  carrier := sᶜ
  smul_mem' := fun ⟨c, hc⟩ x ↦ by
    rw [← Subgroup.inv_mem_iff] at hc
    simp only [Set.mem_compl_iff, not_imp_not]
    intro hcx
    rwa [← one_smul M x, ← inv_mul_cancel c, mul_smul, (mem_fixingSubgroup_iff M).mp hc (c • x) hcx]

example (s : Set α) :
    SMul (fixingSubgroup M s) (ofFixingSubgroup M s) :=
  inferInstance

example (s : Set α) : MulAction (fixingSubgroup M s) (ofFixingSubgroup M s) :=
  inferInstance

theorem ofFixingSubgroup_carrier {s : Set α} :
    (ofFixingSubgroup M s).carrier = sᶜ := rfl

theorem mem_ofFixingSubgroup_iff {s : Set α} {x : α} :
    x ∈ ofFixingSubgroup M s ↔ x ∉ s :=
  Iff.rfl

theorem not_mem_of_mem_ofFixingSubgroup {s : Set α}
  (x : ofFixingSubgroup M s) : ↑x ∉ s := x.prop

example (s : Set α) : SMul { x // x ∈ fixingSubgroup M s }
    { x // x ∈ ofFixingSubgroup M s } :=
  SetLike.smul (ofFixingSubgroup M s)

example (s : Set α) :
    MulAction (fixingSubgroup M s) (ofFixingSubgroup M s) :=
  mulAction (ofFixingSubgroup M s)

theorem mem_fixingSubgroup_insert_iff {a : α} {s : Set α} {m : M} :
    m ∈ fixingSubgroup M (insert a s) ↔ m • a = a ∧ m ∈ fixingSubgroup M s := by
  simp [mem_fixingSubgroup_iff]

theorem fixingSubgroup_of_insert (a : α) (s : Set (ofStabilizer M a)) :
    fixingSubgroup M (insert a ((fun x ↦ x.val) '' s)) =
      (fixingSubgroup (↥(stabilizer M a)) s).map (stabilizer M a).subtype := by
  ext m
  simp only [Subgroup.mem_map, mem_fixingSubgroup_iff]
  constructor
  · intro hm
    use ⟨m, mem_stabilizer_iff.mpr (hm _ (Set.mem_insert a _))⟩
    simp only [Subgroup.coe_subtype, and_true, mem_fixingSubgroup_iff]
    rintro ⟨y, hy⟩ hy'
    simp only [SetLike.mk_smul_mk, Subtype.mk.injEq]
    exact hm y (Set.mem_insert_of_mem a ⟨⟨y, hy⟩, ⟨hy', rfl⟩⟩)
  · rintro ⟨⟨n, hn'⟩, hn, rfl⟩
    simp only [Subgroup.coe_subtype, SetLike.mem_coe, mem_fixingSubgroup_iff] at hn ⊢
    intro x hx
    rw [Set.mem_insert_iff] at hx
    rcases hx with hx | hx
    · simpa [hx] using hn'
    · simp only [Set.mem_image] at hx
      rcases hx with ⟨y, hy, rfl⟩
      conv_rhs => rw [← hn y hy, SubMulAction.val_smul, subgroup_smul_def]



end SubMulAction


