/-
Copyright (c) 2024 Emilie Burgun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Burgun
-/

import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.Topology.Basic
import Mathlib.Topology.Sets.RegularOpens
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Group.InjectiveAction

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

open Pointwise
open MulAction
open Topology

/--
The action of `G` on `α` is locally dense if for all open sets `s` and forall `p ∈ s`,
`closure (AddAction.orbit (fixingAddSubgroup G sᶜ) p) ∈ 𝓝 p`.
-/
class LocallyDenseVAdd (G α : Type*) [AddGroup G] [TopologicalSpace α] [AddAction G α]: Prop :=
  /-- The closure of the orbit of the moving subgroup of an open set must be part of the
  neighborhood filter. -/
  locally_dense_vadd : ∀ ⦃s : Set α⦄, IsOpen s → ∀ ⦃p : α⦄, p ∈ s →
    closure (AddAction.orbit (fixingAddSubgroup G sᶜ) p) ∈ 𝓝 p

/--
The action of `G` on `α` is locally dense if for all open sets `s` and forall `p ∈ s`,
`closure (MulAction.orbit (fixingSubgroup G sᶜ) p) ∈ 𝓝 p`.
-/
@[to_additive existing]
class LocallyDenseSMul (G α : Type*) [Group G] [TopologicalSpace α] [MulAction G α]: Prop :=
  /-- The closure of the orbit of the moving subgroup of an open set must be part of the
  neighborhood filter. -/
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
class LocallyMovingVAdd (G α : Type*) [AddGroup G] [TopologicalSpace α] [AddAction G α]: Prop :=
  locally_moving' : ∀ ⦃s : Set α⦄, IsOpen s → s.Nonempty → fixingAddSubgroup G sᶜ ≠ ⊥

/--
A multiplicative group action `G` on a topological space `α` is said to be locally moving if
the `fixingSubgroup` of `sᶜ` contains a nontrivial element if `s` is open and nonempty.
-/
@[to_additive existing]
class LocallyMovingSMul (G α : Type*) [Group G] [TopologicalSpace α] [MulAction G α]: Prop :=
  locally_moving' : ∀ ⦃s : Set α⦄, IsOpen s → s.Nonempty → G•[sᶜ] ≠ ⊥

variable (G) in
variable [LocallyMovingSMul G α] in
@[to_additive]
theorem LocallyMovingSMul.locally_moving {s : Set α} (s_open : IsOpen s) (s_nonempty : s.Nonempty) :
    G•[sᶜ] ≠ ⊥ := LocallyMovingSMul.locally_moving' (G := G) s_open s_nonempty

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

variable (G) in
@[to_additive]
theorem LocallyMovingSMul.nontrivial_elem_of_nonempty [LocallyMovingSMul G α] {s : Set α}
    (s_open : IsOpen s) (s_nonempty : s.Nonempty) : ∃ g ∈ G•[sᶜ], g ≠ 1 := by
  have fixing_ne_bot := LocallyMovingSMul.locally_moving (G := G) s_open s_nonempty
  let ⟨⟨g, g_in_fixing⟩, g_ne_one⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp fixing_ne_bot
  rw [ne_eq, Subgroup.mk_eq_one_iff] at g_ne_one
  exact ⟨g, g_in_fixing, g_ne_one⟩

variable (G : Type*) [CommGroup G] [T2Space α] [Nonempty α] [MulAction G α] [FaithfulSMul G α]
  [NoIsolatedPoints α] in
/--
A faithful, abelian group action on a Hausdorff space with no isolated points
cannot be locally moving.
-/
theorem not_locallyDenseSmul_of_comm_of_t2space : ¬LocallyDenseSMul G α := by
  intro locally_dense
  have ⟨g, h, g_ne_h⟩ := LocallyMovingSMul.nontrivial_of_nonempty G α
  have center_bot := LocallyDenseSMul.center_eq_bot G α
  rw [CommGroup.center_eq_top, Subgroup.eq_bot_iff_forall] at center_bot
  simp only [Subgroup.mem_top, forall_true_left] at center_bot
  rw [center_bot g, center_bot h] at g_ne_h
  exact g_ne_h rfl

variable (G) in
/--
If the action of `G` on `α` is locally moving, continuous and faithful, then the moving subgroup
of an open set does not have an exponent.

This corresponds to lemma 2.2 of [A Short Proof of Rubin's theorem].
-/
theorem LocallyMovingSMul.exponent_fixingSubgroup_eq_zero [LocallyMovingSMul G α]
    [ContinuousConstSMul G α] [FaithfulSMul G α] [T2Space α] {s : Set α} (s_open : IsOpen s)
    (s_nonempty : s.Nonempty) : Monoid.exponent G•[sᶜ] = 0 := by
  by_contra exp_ne_zero
  let ⟨⟨g, g_in_fixing⟩, x, x_in_s, period_pos, period_maximal⟩ :=
    exists_maximal_period_of_exponent_pos exp_ne_zero s_nonempty
  simp only [Subtype.forall, period_subgroup_mk] at period_pos period_maximal

  let ⟨t, t_open, x_in_t, pw_disj⟩ := t2_separation_of_smul_injOn
    (MulAction.smul_injOn_pow_lt_period g x)
    (Set.toFinite ((fun i => g ^ i) '' Set.Iio (period g x)))

  replace pw_disj : { g ^ i | i < period g x }.PairwiseDisjoint (· • (s ∩ t)) :=
    Set.PairwiseDisjoint.mono_on pw_disj fun h _ =>
      Set.smul_set_mono (Set.inter_subset_right _ _)

  let ⟨h, h_in_fixing, h_ne_one⟩ := nontrivial_elem_of_nonempty G (s_open.inter t_open)
    ⟨x, ⟨x_in_s, x_in_t⟩⟩
  have hg_in_fixing : h * g ∈ G•[sᶜ] := by
    rw [mem_fixingSubgroup_iff_subset_fixedBy] at *
    apply subset_trans _ (MulAction.fixedBy_mul α h g)
    apply Set.subset_inter _ g_in_fixing
    apply subset_trans _ h_in_fixing
    simp only [Set.compl_subset_compl, Set.inter_subset_left]

  let ⟨y, y_in_moved⟩ := fixedBy_compl_nonempty_of_ne_one α h_ne_one
  have y_in_st : y ∈ s ∩ t := by
    rw [mem_fixingSubgroup_compl_iff_movedBy_subset] at h_in_fixing
    exact h_in_fixing y_in_moved

  have hg_pow_eq : ∀ i < period g x, (h * g) ^ i • y = g ^ i • y := by
    intro i i_lt_period
    induction i with
    | zero => simp only [Nat.zero_eq, pow_zero, one_smul]
    | succ i h₁ =>
      specialize h₁ (Nat.lt_of_succ_lt i_lt_period)
      rw [mem_fixingSubgroup_compl_iff_movedBy_subset] at h_in_fixing
      rw [pow_succ, mul_smul, h₁, ← mul_smul, mul_assoc, ← pow_succ, mul_smul, Nat.succ_eq_add_one,
        ← mem_fixedBy, ← Set.not_mem_compl_iff]
      refine mt (fun mem => h_in_fixing mem) fun mem_st => ?ff
      specialize pw_disj ⟨0, period_pos, rfl⟩ ⟨i + 1, i_lt_period, rfl⟩ (by
        apply mt (smul_pow_inj_of_lt_period period_pos i_lt_period)
        tauto
      )
      rw [pow_zero, Function.onFun, Set.smul_set_disjoint_inv_of_comm (Commute.one_left _), inv_one,
        one_smul, Set.disjoint_iff] at pw_disj
      rw [← Set.mem_inv_smul_set_iff] at mem_st
      exact pw_disj ⟨y_in_st, mem_st⟩

  -- We now need to show that `(h * g) ^ i • y ≠ y` for `i < period g x` (which is quite easy),
  -- and for `i = period g x` (which reduces to `h * g ^ i • y = h • y ≠ y`).
  -- From this, we derive a contradiction with `period g x < period (h * g) y ≤ Monoid.exponent _`

  have periods_pos : ∀ i ∈ G•[sᶜ], 0 < period i y := by
    intro i i_in_fixing
    show 0 < period ({ val := i, property := i_in_fixing } : G•[sᶜ]).val y
    rw [← period_subgroup_mk (H := G•[sᶜ]) i_in_fixing]
    apply period_pos_of_exponent_pos exp_ne_zero

  have period_y_eq_x : period g x = period g y := by
    apply le_antisymm _ (period_maximal _ g_in_fixing _ y_in_st.left)
    apply le_period_of_moved (periods_pos g g_in_fixing)
    intro i pos lt_period
    nth_rw 2 [← one_smul G y]
    rw [← pow_zero g]
    apply Set.disjoint_iff_forall_ne.mp (pw_disj ⟨i, lt_period, rfl⟩ ⟨0, period_pos, rfl⟩ ?inj)
    · exact Set.smul_mem_smul_set_iff.mpr y_in_st
    · exact Set.smul_mem_smul_set_iff.mpr y_in_st
    · exact mt (smul_pow_inj_of_lt_period lt_period period_pos) pos.ne'

  apply Nat.not_lt.mpr (period_maximal _ hg_in_fixing y y_in_st.left)
  rw [Nat.lt_iff_add_one_le]
  apply le_period_of_moved (periods_pos _ hg_in_fixing)
  intro k pos lt
  by_cases k = period g x
  case pos eq =>
    rw [← Nat.succ_pred pos.ne', pow_succ, mul_smul, hg_pow_eq _ ?pred_lt, ← mul_smul, mul_assoc,
      ← pow_succ, ← Nat.succ_eq_add_one, Nat.succ_pred pos.ne', mul_smul, eq, period_y_eq_x,
      smul_pow_period_fixed]
    exact y_in_moved

    case pred_lt =>
      rw [Nat.lt_iff_add_one_le, ← Nat.succ_eq_add_one, Nat.succ_pred pos.ne']
      rwa [Nat.lt_iff_add_one_le, add_le_add_iff_right] at lt

  case neg ne =>
    replace lt: k < period g x := by
      rw [Nat.lt_iff_add_one_le, add_le_add_iff_right] at lt
      rw [Nat.lt_iff_le_and_ne]
      exact ⟨lt, ne⟩

    rw [hg_pow_eq k lt]
    exact moved_of_lt_period pos (period_y_eq_x ▸ lt)

variable (G α) in
/--
A corollary of `LocallyMovingSMul.exponent_fixingSubgroup_eq_zero` is that the group `G`
does not have an exponent.
-/
theorem LocallyMovingSMul.exponent_eq_zero [LocallyMovingSMul G α] [ContinuousConstSMul G α]
    [FaithfulSMul G α] [T2Space α] [Nonempty α]: Monoid.exponent G = 0 := by
  have exp_top_eq_zero := exponent_fixingSubgroup_eq_zero G (isOpen_univ (α := α)) Set.univ_nonempty
  rwa [Set.compl_univ, fixingSubgroup_empty, Subgroup.exponent_top] at exp_top_eq_zero

section FixingSubgroup


section FixingSubgroup

open TopologicalSpace (RegularOpens)

variable [LocallyMovingSMul G α] [T2Space α]

/-
theorem fixingSubgroup_compl_le_iff_le_of_regularOpen (s t : RegularOpens α) :
    G•[(↑s : Set α)ᶜ] ≤ G•[(↑t : Set α)ᶜ] ↔ s ≤ t := by
  refine ⟨fun fixing_le => ?le, fun le => (fixingSubgroup_antitone G α).comp
    (compl_antitone (Set α)) le⟩

  sorry
-/

end FixingSubgroup

end FixingSubgroup
