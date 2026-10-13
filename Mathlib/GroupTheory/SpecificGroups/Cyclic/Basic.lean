/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.IsCommutative
public import Mathlib.Algebra.Group.TypeTags.Basic

import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Contrapose

/-!
# Cyclic groups

This file develops basic properties of cyclic groups that only require minimal imports.

Note that `IsCyclic` is a predicate on a group stating that the group is cyclic. For the concrete
cyclic group of order `n`, see `Data.ZMod.Basic`.
-/

@[expose] public section

assert_not_exists Subgroup Ideal TwoSidedIdeal Field

variable {α G G' : Type*} {a : α}

section Cyclic

instance : IsAddCyclic ℤ := ⟨1, fun n ↦ ⟨n, by simp⟩⟩

@[to_additive]
instance (priority := 100) isCyclic_of_subsingleton [Group α] [Subsingleton α] : IsCyclic α :=
  ⟨⟨1, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩⟩

@[simp]
theorem isCyclic_multiplicative_iff [SubNegMonoid α] :
    IsCyclic (Multiplicative α) ↔ IsAddCyclic α :=
  ⟨fun H ↦ ⟨H.1⟩, fun H ↦ ⟨H.1⟩⟩

instance isCyclic_multiplicative [AddGroup α] [IsAddCyclic α] : IsCyclic (Multiplicative α) :=
  isCyclic_multiplicative_iff.mpr inferInstance

@[simp]
theorem isAddCyclic_additive_iff [DivInvMonoid α] : IsAddCyclic (Additive α) ↔ IsCyclic α :=
  ⟨fun H ↦ ⟨H.1⟩, fun H ↦ ⟨H.1⟩⟩

instance isAddCyclic_additive [Group α] [IsCyclic α] : IsAddCyclic (Additive α) :=
  isAddCyclic_additive_iff.mpr inferInstance

@[to_additive]
instance IsCyclic.isMulCommutative [Group α] [IsCyclic α] : IsMulCommutative α where
  is_comm.comm x y :=
    let ⟨_, hg⟩ := exists_zpow_surjective α
    let ⟨_, hx⟩ := hg x
    let ⟨_, hy⟩ := hg y
    hy ▸ hx ▸ zpow_mul_comm ..

@[deprecated (since := "2026-04-09")]
alias IsAddCyclic.commutative := IsAddCyclic.isAddCommutative
@[to_additive existing, deprecated (since := "2026-04-09")]
alias IsCyclic.commutative := IsCyclic.isMulCommutative

open scoped IsMulCommutative in
/-- A cyclic group is always commutative. This is not an `instance` because often we have a better
proof of `CommGroup`. -/
@[to_additive (attr := instance_reducible)
      /-- A cyclic group is always commutative. This is not an `instance` because often we have
      a better proof of `AddCommGroup`. -/]
def IsCyclic.commGroup [Group α] [IsCyclic α] : CommGroup α :=
  inferInstance

variable [Group α] [Group G] [Group G']

/-- A non-cyclic multiplicative group is non-trivial. -/
@[to_additive /-- A non-cyclic additive group is non-trivial. -/]
theorem Nontrivial.of_not_isCyclic (nc : ¬IsCyclic α) : Nontrivial α := by
  contrapose! nc
  exact isCyclic_of_subsingleton

@[to_additive]
theorem MonoidHom.map_cyclic [h : IsCyclic G] (σ : G →* G) :
    ∃ m : ℤ, ∀ g : G, σ g = g ^ m := by
  let ⟨h, hG⟩ := exists_zpow_surjective G
  obtain ⟨m, hm⟩ := hG (σ h)
  refine ⟨m, fun g => ?_⟩
  obtain ⟨n, rfl⟩ := hG g
  rw [map_zpow, ← hm, ← zpow_mul, ← zpow_mul']

@[to_additive]
theorem isCyclic_of_surjective {F : Type*} [hH : IsCyclic G']
    [FunLike F G' G] [MonoidHomClass F G' G] (f : F) (hf : Function.Surjective f) :
    IsCyclic G := by
  obtain ⟨x, hx⟩ := hH
  refine ⟨f x, fun a ↦ ?_⟩
  obtain ⟨a, rfl⟩ := hf a
  obtain ⟨n, rfl⟩ := hx a
  exact ⟨n, (map_zpow _ _ _).symm⟩

@[to_additive]
theorem MulEquiv.isCyclic (e : G ≃* G') :
    IsCyclic G ↔ IsCyclic G' :=
  ⟨fun _ ↦ isCyclic_of_surjective e e.surjective,
    fun _ ↦ isCyclic_of_surjective e.symm e.symm.surjective⟩

end Cyclic

end
