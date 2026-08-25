/-
Copyright (c) 2026 Edison Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Edison Xie
-/
module

public import Mathlib.Algebra.GroupWithZero.Subgroup.ZPowers
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Cyclic groups with zero

A group with zero is cyclic when its group of units is.

## Main definitions

* `IsCyclicWithZero G₀`: all nonzero elements of `G₀` are integer powers of a single element.

## Implementation notes

**`IsCyclicWithZero` is not `IsCyclic`.** `IsCyclic` is declared over `[Pow G ℤ]`
(`Mathlib/Algebra/Group/DivInvMonoid.lean`), so `IsCyclic G₀` typechecks for a group with zero —
but it asks for `n ↦ g ^ n` to be surjective onto *all* of `G₀`, including `0`, which forces
`g = 0` and hence `G₀ = {0, 1}`. See `isCyclic_iff_subsingleton_units`. A stray `[IsCyclic Γ]`
binder on a group with zero therefore elaborates silently and is almost never satisfiable.

`IsCyclicWithZero` is a `class abbrev`, so instance search passes between it and
`IsCyclic G₀ˣ` in both directions and the existing `IsCyclic` ecosystem applies with no glue.

## Tags
group with zero, cyclic
-/

@[expose] public section

variable {G₀ : Type*} [GroupWithZero G₀]

/-- A group with zero is cyclic with zero when all of its nonzero elements are integer powers
of a single element, i.e. when its group of units is cyclic.

Warning: this is not `IsCyclic G₀`. Never write `[IsCyclic G₀]` for a group with zero. -/
class abbrev IsCyclicWithZero (G₀ : Type*) [GroupWithZero G₀] : Prop := IsCyclic G₀ˣ

theorem isCyclicWithZero_iff_isCyclic_units {G₀ : Type*} [GroupWithZero G₀] :
    IsCyclicWithZero G₀ ↔ IsCyclic G₀ˣ :=
  ⟨fun h ↦ h.toIsCyclic, fun h ↦ @IsCyclicWithZero.mk _ _ h⟩

/-- A subgroup with zero of a cyclic group with zero is cyclic with zero. -/
instance SubgroupWithZero.isCyclicWithZero (s : SubgroupWithZero G₀) [IsCyclicWithZero G₀] :
    IsCyclicWithZero s :=
  @IsCyclicWithZero.mk _ _ ((SubgroupWithZero.unitsMulEquiv s).isCyclic.mpr inferInstance)

/-- The units of a cyclic subgroup with zero form a cyclic subgroup of `G₀ˣ`. -/
instance SubgroupWithZero.isCyclic_units (s : SubgroupWithZero G₀) [IsCyclicWithZero s] :
    IsCyclic s.units := (SubgroupWithZero.unitsMulEquiv s).isCyclic.mp inferInstance

/-- For a group with zero, `IsCyclic G₀` holds exactly when its group of units is trivial. -/
theorem isCyclic_iff_subsingleton_units : IsCyclic G₀ ↔ Subsingleton G₀ˣ := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := IsCyclic.exists_zpow_surjective (G := G₀)
    obtain ⟨n, hn⟩ := hg 0
    have hg0 : g = 0 := by
      by_contra hg0
      exact absurd hn (zpow_ne_zero _ hg0)
    refine ⟨fun u w ↦ Units.ext ?_⟩
    have huw : ∀ y : G₀, y ≠ 0 → y = 1 := by
      intro y hy
      obtain ⟨m, hm⟩ := hg y
      rw [hg0] at hm
      simp only [] at hm
      rw [zero_zpow_eq] at hm
      split_ifs at hm with h
      · exact hm.symm ▸ rfl
      · exact absurd hm.symm hy
    rw [huw _ u.ne_zero, huw _ w.ne_zero]
  · intro h
    refine ⟨0, fun y ↦ ?_⟩
    rcases eq_or_ne y 0 with rfl | hy
    · exact ⟨1, by simp⟩
    · refine ⟨0, ?_⟩
      have : IsUnit y := isUnit_iff_ne_zero.2 hy
      obtain ⟨u, rfl⟩ := this
      rw [Subsingleton.elim u 1]
      simp

theorem isCyclicWithZero_iff_exists_zpowers₀_eq_top :
    IsCyclicWithZero G₀ ↔ ∃ g : G₀, SubgroupWithZero.zpowers₀ g = ⊤ := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := G₀ˣ)).1 h.toIsCyclic
    refine ⟨(u : G₀), ?_⟩
    rw [← SubgroupWithZero.withZero_units (SubgroupWithZero.zpowers₀ (u : G₀)),
      SubgroupWithZero.units_zpowers₀, hu]
    exact SubgroupWithZero.withZero_units ⊤
  · rintro ⟨g, hg⟩
    rcases eq_or_ne g 0 with rfl | hg0
    · rw [SubgroupWithZero.zpowers₀_zero] at hg
      have hsub : Subsingleton G₀ˣ := by
        refine ⟨fun u w ↦ Units.ext ?_⟩
        have h1 : ∀ y : G₀, y ≠ 0 → y = 1 := fun y hy ↦
          ((SubgroupWithZero.mem_bot).1 (hg ▸ SubgroupWithZero.mem_top y)).resolve_left hy
        rw [h1 _ u.ne_zero, h1 _ w.ne_zero]
      exact @IsCyclicWithZero.mk _ _ isCyclic_of_subsingleton
    · refine @IsCyclicWithZero.mk _ _
        ((isCyclic_iff_exists_zpowers_eq_top (α := G₀ˣ)).2 ⟨Units.mk0 g hg0, ?_⟩)
      rw [← SubgroupWithZero.units_zpowers₀, Units.val_mk0, hg, SubgroupWithZero.units_top]
