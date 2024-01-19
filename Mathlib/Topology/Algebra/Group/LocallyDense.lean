/-
Copyright (c) 2024 Emilie Burgun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Burgun
-/

import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Locally dense and locally moving group actions

The action of a group `G` on a topological space `α` is said to be **locally dense** if for all open
set `s` and for all points `p ∈ s`, `closure (MulAction.orbit (fixingSubgroup G sᶜ) p) ∈ 𝓝 p`.

The action of `G` on `α` is said to be **locally moving**, if for all open and nonempty set
`s : Set α`, `fixingSubgroup G sᶜ ≠ ⊥`. This a weaker statement than local denseness,
and automatic conversion can be done if the space is T1 and has no isolated points.

These structures impose some restrictions on the behavior that `G` may have.
Notably, `G` cannot be abelian if its action on a Hausdorff space `α` with no isolated points
needs to be locally dense and faithful (primarily given by `LocallyDenseSMul.center_eq_bot`).

`G` also cannot be trivial if the acted-on space is nonempty
(`LocallyMovingSMul.nontrivial_of_nonempty`).
-/

-- open Pointwise
open MulAction
open Topology

/--
The action of `G` on `α` is locally dense if for all open sets `s` and forall `p ∈ s`,
`closure (AddAction.orbit (fixingAddSubgroup G sᶜ) p) ∈ 𝓝 p`.
-/
class LocallyDenseVAdd (G α : Type*) [AddGroup G] [TopologicalSpace α] [AddAction G α] :=
  locally_dense_vadd : ∀ ⦃s : Set α⦄, IsOpen s → ∀ ⦃p : α⦄, p ∈ s →
    closure (AddAction.orbit (fixingAddSubgroup G sᶜ) p) ∈ 𝓝 p

/--
The action of `G` on `α` is locally dense if for all open sets `s` and forall `p ∈ s`,
`closure (MulAction.orbit (fixingSubgroup G sᶜ) p) ∈ 𝓝 p`.
-/
@[to_additive existing]
class LocallyDenseSMul (G α : Type*) [Group G] [TopologicalSpace α] [MulAction G α] :=
  locally_dense_smul : ∀ ⦃s : Set α⦄, IsOpen s → ∀ ⦃p : α⦄, p ∈ s →
    closure (MulAction.orbit (G•[sᶜ]) p) ∈ 𝓝 p

variable {G α : Type*} [Group G] [TopologicalSpace α] [MulAction G α]

namespace LocallyDenseSMul

variable [LocallyDenseSMul G α]

variable (G) in
@[to_additive]
theorem mem_interior_closure_orbit {s : Set α} (s_open : IsOpen s) {p : α}
    (p_in_s : p ∈ s) : p ∈ interior (closure (MulAction.orbit (G•[sᶜ]) p)) := by
  rw [mem_interior_iff_mem_nhds]
  apply locally_dense_smul <;> assumption

variable (G) in
@[to_additive]
theorem moving_elem_in_fixingSubgroup_compl [T1Space α] {s : Set α} {p : α}
    [ne_bot : Filter.NeBot (𝓝[≠] p)] (s_open : IsOpen s) (p_in_s : p ∈ s) :
    ∃ g ∈ G•[sᶜ], g • p ≠ p := by
  by_contra g_fixes
  simp only [ne_eq, not_exists, not_and, not_not] at g_fixes

  have orbit_eq_singleton : MulAction.orbit G•[sᶜ] p = {p} := by
    ext q
    rw [Set.mem_singleton_iff]
    constructor
    · rw [MulAction.mem_orbit_iff]
      intro ⟨⟨h, h_in_fixing⟩, hp_eq_q⟩
      symm
      rwa [Submonoid.mk_smul, g_fixes h h_in_fixing] at hp_eq_q
    · intro q_eq_p
      rw [q_eq_p]
      exact mem_orbit_self _

  rw [← Set.mem_empty_iff_false p]
  convert mem_interior_closure_orbit G s_open p_in_s using 1
  rw [orbit_eq_singleton, closure_singleton, interior_singleton]

open Pointwise in
variable (G α) in
/--
If a group action is locally moving and faithful and the topology is Hausdorff,
then only `1` commutes with every other member of `G`.
-/
@[to_additive]
theorem center_eq_bot [T2Space α] [FaithfulSMul G α] [NoIsolatedPoints α] :
    Subgroup.center G = ⊥ := by
  simp only [Subgroup.eq_bot_iff_forall, Subgroup.mem_center_iff]
  intro g g_in_center
  apply FaithfulSMul.eq_of_smul_eq_smul (α := α)
  intro x
  rw [one_smul]
  by_contra gx_ne_x

  let ⟨s, t, s_open, _, gx_in_s, x_in_t, st_disj⟩ := t2_separation gx_ne_x
  let ⟨h, h_in_movingSubgroup, hgx_ne_gx⟩ := moving_elem_in_fixingSubgroup_compl G s_open gx_in_s
  rw [mem_fixingSubgroup_compl_iff_movedBy_subset, Set.compl_subset_comm] at h_in_movingSubgroup

  rw [← mul_smul, g_in_center, mul_smul, ne_eq, smul_left_cancel_iff, ← mem_fixedBy] at hgx_ne_gx
  apply hgx_ne_gx

  apply h_in_movingSubgroup (st_disj.subset_compl_left x_in_t)

end LocallyDenseSMul

/--
An additive group action `G` on a topological space `α` is said to be locally moving if
the `fixingAddSubgroup` of `sᶜ` contains a nontrivial element if `s` is open and nonempty.
-/
class LocallyMovingVAdd (G α : Type*) [AddGroup G] [TopologicalSpace α] [AddAction G α] :=
  locally_moving : ∀ ⦃s : Set α⦄, IsOpen s → s.Nonempty → fixingAddSubgroup G sᶜ ≠ ⊥

/--
A multiplicative group action `G` on a topological space `α` is said to be locally moving if
the `fixingSubgroup` of `sᶜ` contains a nontrivial element if `s` is open and nonempty.
-/
@[to_additive existing]
class LocallyMovingSMul (G α : Type*) [Group G] [TopologicalSpace α] [MulAction G α] :=
  locally_moving : ∀ ⦃s : Set α⦄, IsOpen s → s.Nonempty → G•[sᶜ] ≠ ⊥

@[to_additive]
instance LocallyMovingSMul.of_locallyDense [LocallyDenseSMul G α] [T1Space α] [NoIsolatedPoints α] :
    LocallyMovingSMul G α := by
  constructor
  intro s s_open ⟨p, p_in_s⟩ fixingSubgroup_eq_bot
  rw [Subgroup.eq_bot_iff_forall] at fixingSubgroup_eq_bot
  let ⟨h, h_in_rist, h_ne_one⟩ := LocallyDenseSMul.moving_elem_in_fixingSubgroup_compl
    G s_open p_in_s
  rw [fixingSubgroup_eq_bot h h_in_rist, one_smul] at h_ne_one
  exact h_ne_one rfl

-- NOTE: if one can show that TopologicalSpace.RegularOpens is infinite if the space is Hausdorff
-- and has no isolated points, then we can show that G must be infinite too

variable (G α) in
/--
A locally moving group action cannot be trivial if the acted-on space is nonempty.
-/
@[to_additive]
theorem LocallyMovingSMul.nontrivial_of_nonempty [LocallyMovingSMul G α] [Nonempty α]:
    Nontrivial G := by
  by_contra trivial
  rw [not_nontrivial_iff_subsingleton, ← Subgroup.subsingleton_iff] at trivial
  apply LocallyMovingSMul.locally_moving (G := G) (α := α) isOpen_univ _ (trivial.elim _ _)
  exact Set.univ_nonempty

variable (G : Type*) [CommGroup G] [T2Space α] [Nonempty α] [MulAction G α] [FaithfulSMul G α]
  [NoIsolatedPoints α] in
/--
A faithful, locally moving group on a Hausdorff space with no isolated points cannot be abelian.
-/
theorem LocallyDenseSMul.nonabelian_of_t2space_nonempty [LocallyDenseSMul G α] : False := by
  have ⟨g, h, g_ne_h⟩ := LocallyMovingSMul.nontrivial_of_nonempty G α
  have center_bot := center_eq_bot G α
  rw [CommGroup.center_eq_top, Subgroup.eq_bot_iff_forall] at center_bot
  simp only [Subgroup.mem_top, forall_true_left] at center_bot
  rw [center_bot g, center_bot h] at g_ne_h
  exact g_ne_h rfl
