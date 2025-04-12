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

theorem ofFixingSubgroup_carrier {s : Set α} :
    (ofFixingSubgroup M s).carrier = sᶜ := rfl

theorem mem_ofFixingSubgroup_iff {s : Set α} {x : α} :
    x ∈ ofFixingSubgroup M s ↔ x ∉ s :=
  Iff.rfl

variable {M}

theorem not_mem_of_mem_ofFixingSubgroup {s : Set α}
  (x : ofFixingSubgroup M s) : ↑x ∉ s := x.prop

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

variable (M α) in
/-- The identity map of the sub_mul_action of the fixing_subgroup
of the empty set into the ambient set, as an equivariant map -/
def ofFixingSubgroupEmpty_equivariantMap :
    ofFixingSubgroup M (∅ : Set α) →ₑ[(fixingSubgroup M (∅ : Set α)).subtype] α where
  toFun x := x
  map_smul' _ _ := rfl

variable (α) in
theorem ofFixingSubgroupEmpty_equivariantMap_bijective :
    Function.Bijective (ofFixingSubgroupEmpty_equivariantMap M α) := by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp [Subtype.mk_eq_mk]; exact hxy
  · exact fun x ↦ ⟨⟨x, (mem_ofFixingSubgroup_iff M).mp (Set.not_mem_empty x)⟩, rfl⟩

theorem of_fixingSubgroupEmpty_mapScalars_surjective :
    Function.Surjective (fixingSubgroup M (∅ : Set α)).subtype := fun g ↦ by
  suffices g ∈ fixingSubgroup M (∅ : Set α) by
    exact ⟨⟨g, this⟩, rfl⟩
  simp [mem_fixingSubgroup_iff]

/-- The natural group morphism between fixing subgroups -/
def fixingSubgroupMap_insert (a : α) (s : Set (ofStabilizer M a)) :
    fixingSubgroup M (insert a (Subtype.val '' s)) →* fixingSubgroup (stabilizer M a) s where
  toFun m := ⟨⟨(m : M), (mem_fixingSubgroup_iff M).mp m.prop a (Set.mem_insert _ _)⟩,
      fun ⟨x, hx⟩ => by
        simp only [← SetLike.coe_eq_coe]
        refine (mem_fixingSubgroup_iff M).mp m.prop _ (Set.mem_insert_of_mem a ?_)
        exact ⟨⟨x, (SubMulAction.mem_ofStabilizer_iff  M a).mp x.prop⟩, hx, rfl⟩⟩
  map_one' := by simp
  map_mul' _ _ := by simp [← Subtype.coe_inj]

theorem fixingSubgroupMap_insert_bijective (a : α) (s : Set (ofStabilizer M a)) :
    Function.Bijective (fixingSubgroupMap_insert a s) := by
  constructor
  · rintro _ _ hmn
    simpa [← SetLike.coe_eq_coe] using hmn
  · rintro ⟨⟨m, hm⟩, hm'⟩
    refine ⟨⟨m, ?_⟩, rfl⟩
    rw [mem_fixingSubgroup_iff]
    intro x hx
    rcases Set.mem_insert_iff.mp hx with ⟨rfl⟩ | ⟨y, hy, rfl⟩
    · exact mem_stabilizer_iff.mp hm
    · rw [mem_fixingSubgroup_iff] at hm'
      simpa [← SetLike.coe_eq_coe] using hm' y hy

/-- The identity map of fixing subgroup of stabilizer
into the fixing subgroup of the extended set, as an equivariant map -/
def equivariantMap_ofFixingSubgroup_to_ofStabilizer (a : α) (s : Set (ofStabilizer M a)) :
    ofFixingSubgroup M (insert a (Subtype.val '' s))
      →ₑ[fixingSubgroupMap_insert a s] (ofFixingSubgroup (stabilizer M a) s) where
  toFun x := ⟨⟨x, fun h ↦ (mem_ofFixingSubgroup_iff M).mp x.prop (by
      rw [h]
      apply Set.mem_insert)⟩,
    fun h ↦ (mem_ofFixingSubgroup_iff M).mp x.prop <|
      Set.mem_insert_of_mem _ ⟨⟨(x : α), _⟩, ⟨h, rfl⟩⟩⟩
  map_smul' _ _ := rfl }

@[simp]
theorem equivariantMap_ofFixingSubgroup_to_ofStabilizer_coe {a : α} {s : Set (ofStabilizer M a)}
    {x : α} (hx : x ∈ ofFixingSubgroup M (insert a (Subtype.val '' s))) :
    ↑((equivariantMap_ofFixingSubgroup_to_ofStabilizer a s) ⟨x, hx⟩) = x :=
  rfl

theorem equivariantMap_ofFixingSubgroup_to_ofStabilizer_bijective
    (a : α) (s : Set (ofStabilizer M a)) :
    Function.Bijective (equivariantMap_ofFixingSubgroup_to_ofStabilizer a s) := by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    simp only [Subtype.mk_eq_mk]
    rw [← equivariantMap_ofFixingSubgroup_to_ofStabilizer_coe hx,
      ← equivariantMap_ofFixingSubgroup_to_ofStabilizer_coe hy, h]
  · rintro ⟨⟨x, hx1⟩, hx2⟩
    refine ⟨⟨x, ?_⟩, rfl⟩
    rw [mem_ofFixingSubgroup_iff]
    intro h
    rcases Set.mem_insert_iff.mp h with  h' | h'
    · exact (mem_ofStabilizer_iff _ _).mp hx1 h'
    · obtain ⟨x1, hx1', rfl⟩ := h'
      exact (mem_ofFixingSubgroup_iff _).mp hx2 hx1'

end SubMulAction


