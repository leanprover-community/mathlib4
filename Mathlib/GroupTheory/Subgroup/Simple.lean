/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Order.Atoms
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Equiv.TransferInstance

/-!
# Simple groups

This file defines `IsSimpleGroup G`, a class indicating that a group has exactly two normal
subgroups.

## Main definitions

- `IsSimpleGroup G`, a class indicating that a group has exactly two normal subgroups.

## Tags
subgroup, subgroups

-/


variable {G : Type*} [Group G]
variable {A : Type*} [AddGroup A]

section

variable (G) (A)

/-- A `Group` is simple when it has exactly two normal `Subgroup`s. -/
@[mk_iff]
class IsSimpleGroup : Prop extends Nontrivial G where
  /-- Any normal subgroup is either `⊥` or `⊤` -/
  eq_bot_or_eq_top_of_normal : ∀ H : Subgroup G, H.Normal → H = ⊥ ∨ H = ⊤

/-- An `AddGroup` is simple when it has exactly two normal `AddSubgroup`s. -/
@[mk_iff]
class IsSimpleAddGroup : Prop extends Nontrivial A where
  /-- Any normal additive subgroup is either `⊥` or `⊤` -/
  eq_bot_or_eq_top_of_normal : ∀ H : AddSubgroup A, H.Normal → H = ⊥ ∨ H = ⊤

attribute [to_additive existing] IsSimpleGroup isSimpleGroup_iff

variable {G} {A}

@[to_additive]
theorem Subgroup.Normal.eq_bot_or_eq_top [IsSimpleGroup G] {H : Subgroup G} (Hn : H.Normal) :
    H = ⊥ ∨ H = ⊤ :=
  IsSimpleGroup.eq_bot_or_eq_top_of_normal H Hn

@[to_additive]
protected lemma Subgroup.isSimpleGroup_iff {H : Subgroup G} :
    IsSimpleGroup ↥H ↔ H ≠ ⊥ ∧
      ∀ (H' : Subgroup G) (_ : H' ≤ H) [(H'.subgroupOf H).Normal], H' = ⊥ ∨ H' = H := by
  rw [_root_.isSimpleGroup_iff]; congr! 1
  · rw [H.nontrivial_iff_ne_bot]
  · let e : Subgroup ↥H ≃ { H' : Subgroup G // H' ≤ H } :=
      { toFun H' := ⟨H'.map H.subtype, map_subtype_le H'⟩
        invFun sH' := sH'.1.subgroupOf H
        left_inv H' := comap_map_eq_self_of_injective H.subtype_injective H'
        right_inv sH' := Subtype.ext (map_subgroupOf_eq_of_le sH'.2) }
    simp +contextual [e.forall_congr_left, disjoint_of_le_iff_left_eq_bot, LE.le.ge_iff_eq, e]

namespace IsSimpleGroup

@[to_additive]
instance {C : Type*} [CommGroup C] [IsSimpleGroup C] : IsSimpleOrder (Subgroup C) :=
  ⟨fun H => H.normal_of_comm.eq_bot_or_eq_top⟩

open Subgroup

@[to_additive]
theorem isSimpleGroup_of_surjective {H : Type*} [Group H] [IsSimpleGroup G] [Nontrivial H]
    (f : G →* H) (hf : Function.Surjective f) : IsSimpleGroup H :=
  ⟨fun H iH => by
    refine (iH.comap f).eq_bot_or_eq_top.imp (fun h => ?_) fun h => ?_
    · rw [← map_bot f, ← h, map_comap_eq_self_of_surjective hf]
    · rw [← comap_top f] at h
      exact comap_injective hf h⟩

@[to_additive]
lemma _root_.MulEquiv.isSimpleGroup {H : Type*} [Group H] [IsSimpleGroup H] (e : G ≃* H) :
    IsSimpleGroup G :=
  haveI : Nontrivial G := e.toEquiv.nontrivial
  isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective

end IsSimpleGroup

end
