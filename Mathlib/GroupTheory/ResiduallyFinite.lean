/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.GroupTheory.FiniteIndexNormalSubgroup

/-!
# Residually Finite Groups

In this file we define residually finite groups and prove some basic properties.

## Main definitions

- `Group.ResiduallyFinite G`: A group `G` is residually finite if the intersection of all
  finite index normal subgroups is trivial.

-/

@[expose] public section

class AddGroup.ResiduallyFinite (G : Type*) [AddGroup G] : Prop where
  inf_eq_bot : ⨅ H : FiniteIndexNormalAddSubgroup G, H.toAddSubgroup = ⊥

namespace Group

class ResiduallyFinite (G : Type*) [Group G] : Prop where
  inf_eq_bot : ⨅ H : FiniteIndexNormalSubgroup G, H.toSubgroup = ⊥

attribute [to_additive existing] ResiduallyFinite

variable {G : Type*} [Group G]

@[to_additive]
theorem residuallyFinite_def :
    ResiduallyFinite G ↔ ⨅ H : FiniteIndexNormalSubgroup G, H.toSubgroup = ⊥ :=
  ⟨fun h ↦ h.inf_eq_bot, fun h ↦ ⟨h⟩⟩

@[to_additive]
theorem residuallyFinite_iff_forall_finiteIndexNormalSubgroup :
    ResiduallyFinite G ↔ ∀ g : G, (∀ H : FiniteIndexNormalSubgroup G, g ∈ H) → g = 1 := by
  simp_rw [residuallyFinite_def, Subgroup.eq_bot_iff_forall, Subgroup.mem_iInf,
    FiniteIndexNormalSubgroup.mem_toSubgroup_iff]

@[to_additive]
theorem residuallyFinite_iff_exists_finiteIndexNormalSubgroup :
    ResiduallyFinite G ↔ ∀ g : G, g ≠ 1 → ∃ H : FiniteIndexNormalSubgroup G, g ∉ H := by
  simp_rw [residuallyFinite_iff_forall_finiteIndexNormalSubgroup, ← not_forall, not_imp_not]

-- todo: @[to_additive] once #34784 is merged
theorem residuallyFinite_iff_forall_finiteIndex :
    ResiduallyFinite G ↔ ∀ g : G, (∀ (H : Subgroup G) [H.FiniteIndex], g ∈ H) → g = 1 := by
  rw [residuallyFinite_iff_forall_finiteIndexNormalSubgroup]
  exact forall_congr' fun g ↦ ⟨fun h hg ↦ h fun H ↦ hg H,
    fun h hg ↦ h fun H hH ↦ H.normalCore_le (hg (.ofSubgroup H.normalCore))⟩

-- todo: @[to_additive] once #34784 is merged
theorem residuallyFinite_iff_exists_finiteIndex :
    ResiduallyFinite G ↔ ∀ g : G, g ≠ 1 → ∃ (H : Subgroup G), H.FiniteIndex ∧ g ∉ H := by
  simp_rw [residuallyFinite_iff_forall_finiteIndex, ← Classical.not_imp, ← not_forall,
    not_imp_not]

-- todo: @[to_additive] once #34784 is merged
instance [Finite G] : ResiduallyFinite G :=
  residuallyFinite_iff_forall_finiteIndex.mpr fun _ hg ↦ hg ⊥

end Group
