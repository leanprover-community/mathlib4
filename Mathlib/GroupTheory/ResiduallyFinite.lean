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

/-- An additive group `G` is residually finite if the intersection of all finite index normal
additive subgroups is trivial. -/
class AddGroup.ResiduallyFinite (G : Type*) [AddGroup G] : Prop where
  iInf_eq_bot : ⨅ H : FiniteIndexNormalAddSubgroup G, H.toAddSubgroup = ⊥

namespace Group

/-- A group `G` is residually finite if the intersection of all finite index normal subgroups is
trivial. -/
class ResiduallyFinite (G : Type*) [Group G] : Prop where
  iInf_eq_bot : ⨅ H : FiniteIndexNormalSubgroup G, H.toSubgroup = ⊥

attribute [to_additive existing] ResiduallyFinite

variable {G : Type*} [Group G]

@[to_additive]
theorem residuallyFinite_def :
    ResiduallyFinite G ↔ ⨅ H : FiniteIndexNormalSubgroup G, H.toSubgroup = ⊥ :=
  ⟨fun h ↦ h.iInf_eq_bot, fun h ↦ ⟨h⟩⟩

@[to_additive]
theorem residuallyFinite_iff_forall_finiteIndexNormalSubgroup :
    ResiduallyFinite G ↔ ∀ g : G, (∀ H : FiniteIndexNormalSubgroup G, g ∈ H) → g = 1 := by
  simp_rw [residuallyFinite_def, Subgroup.eq_bot_iff_forall, Subgroup.mem_iInf,
    FiniteIndexNormalSubgroup.mem_toSubgroup_iff]

@[to_additive]
theorem eq_one_iff_forall_finiteIndexNormalSubroup [ResiduallyFinite G]
    (g : G) (hg : ∀ H : FiniteIndexNormalSubgroup G, g ∈ H) : g = 1 :=
  residuallyFinite_iff_forall_finiteIndexNormalSubgroup.mp ‹_› g hg

@[to_additive]
theorem residuallyFinite_iff_exists_finiteIndexNormalSubgroup :
    ResiduallyFinite G ↔ ∀ g : G, g ≠ 1 → ∃ H : FiniteIndexNormalSubgroup G, g ∉ H := by
  simp_rw [residuallyFinite_iff_forall_finiteIndexNormalSubgroup, ← not_forall, not_imp_not]

@[to_additive]
theorem exists_finiteIndexNormalSubgroup_notMem [ResiduallyFinite G] (g : G) (hg : g ≠ 1):
    ∃ H : FiniteIndexNormalSubgroup G, g ∉ H :=
  residuallyFinite_iff_exists_finiteIndexNormalSubgroup.mp ‹_› g hg

@[to_additive]
theorem residuallyFinite_iff_forall_finiteIndex :
    ResiduallyFinite G ↔ ∀ g : G, (∀ (H : Subgroup G) [H.FiniteIndex], g ∈ H) → g = 1 := by
  rw [residuallyFinite_iff_forall_finiteIndexNormalSubgroup]
  exact forall_congr' fun g ↦ ⟨fun h hg ↦ h fun H ↦ hg H,
    fun h hg ↦ h fun H hH ↦ H.normalCore_le (hg (.ofSubgroup H.normalCore))⟩

@[to_additive]
theorem residuallyFinite_iff_exists_finiteIndex :
    ResiduallyFinite G ↔ ∀ g : G, g ≠ 1 → ∃ (H : Subgroup G), H.FiniteIndex ∧ g ∉ H := by
  simp_rw [residuallyFinite_iff_forall_finiteIndex, ← Classical.not_imp, ← not_forall,
    not_imp_not]

/-- If `G` is residually finite, for every pair of distinct elements `g`, `h` there exists a finite
index normal subgroup `H` such that `g` and `h` differ in the quotient `G ⧸ H`. -/
@[to_additive]
theorem exists_finiteIndexNormalSubgroup_of_residuallyFinite [ResiduallyFinite G] (g h : G)
    (hgh : g ≠ h) : ∃ H : FiniteIndexNormalSubgroup G, (g : G ⧸ H.toSubgroup) ≠ ↑h := by
  obtain ⟨H, hH⟩ := exists_finiteIndexNormalSubgroup_notMem (g⁻¹ * h)
    (fun h ↦ hgh <| eq_of_inv_mul_eq_one h)
  exact ⟨H, by simpa [QuotientGroup.eq]⟩

/-- `G` is residually finite if for every element `g` not equal to `1` there exists a group
homomorphism `f` to a finite group `H` such that `f g ≠ 1`. -/
@[to_additive]
theorem residuallyFinite_of_forall_exists_finite_monoidHom.{u}
    (h : ∀ g : G, g ≠ 1 → ∃ (H : Type u) (_ : Group H) (_ : Finite H) (f : G →* H), f g ≠ 1) :
    ResiduallyFinite G := by
  rw [residuallyFinite_iff_exists_finiteIndex]
  intro g hg
  obtain ⟨_, _, _, f, hf⟩ := h g hg
  exact ⟨f.ker, Subgroup.finiteIndex_ker f, by simpa using hf⟩

@[to_additive]
instance [Finite G] : ResiduallyFinite G :=
  residuallyFinite_iff_forall_finiteIndex.mpr fun _ hg ↦ hg ⊥

end Group
