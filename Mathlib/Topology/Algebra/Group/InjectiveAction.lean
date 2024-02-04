/-
Copyright (c) 2024 Emilie Burgun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Burgun
-/

import Mathlib.Topology.Separation
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.GroupTheory.GroupAction.FixedPoints

/-!
# Injective group actions on a topological space

This module describes a few useful properties of injective group actions on elements of
topological spaces.

-/

variable {G α : Type*} [Group G] [MulAction G α]

variable [TopologicalSpace α] [T2Space α] [ContinuousConstSMul G α]
variable {s : Set G} {x : α}

open Pointwise
open MulAction

variable (α) in
@[to_additive]
theorem MulAction.isClosed_fixedBy (g : G) : IsClosed (fixedBy α g) := by
  rw [← isOpen_compl_iff]
  refine isOpen_iff_forall_mem_open.mpr (fun x x_moved => ?ex_subset)
  let ⟨s, t, s_open, t_open, gx_in_s, x_in_t, disj_st⟩ := t2_separation x_moved

  exact ⟨
    (g⁻¹ • s) ∩ t,
    fun y ⟨gy_in_s, y_in_t⟩ =>
      Disjoint.ne_of_mem disj_st (Set.mem_inv_smul_set_iff.mp gy_in_s) y_in_t,
    (s_open.smul g⁻¹).inter t_open,
    ⟨Set.mem_inv_smul_set_iff.mpr gx_in_s, x_in_t⟩
  ⟩

section Separation

/--
If the action of `G` on `α` is continuous in `α`, then for all points not fixed by `g : G`,
there exists an open set `s` such that `x ∈ s` and `g • s` is disjoint from `s`.
-/
theorem t2_separation_smul {x : α} {g : G}
    (x_moved : x ∉ fixedBy α g) :
    ∃ s : Set α, IsOpen s ∧ x ∈ s ∧ Disjoint s (g • s) := by
  let ⟨s, t, s_open, t_open, gx_in_s, x_in_t, disj_st⟩ := t2_separation x_moved
  let u := (g⁻¹ • s) ∩ t
  have u_open : IsOpen u := (s_open.smul g⁻¹).inter t_open

  refine ⟨u, u_open, ⟨?gx_in_gs, x_in_t⟩, ?disj⟩
  · rwa [Set.mem_inv_smul_set_iff]
  · simp only [Set.smul_set_inter, smul_inv_smul]
    exact Set.disjoint_of_subset
      (Set.inter_subset_right _ _)
      (Set.inter_subset_left _ _)
      disj_st.symm

theorem t2_separation_smul_subset {x : α} {g : G} {s : Set α} (s_open : IsOpen s) (x_in_s : x ∈ s)
    (x_moved : x ∉ fixedBy α g) :
    ∃ t : Set α, IsOpen t ∧ x ∈ t ∧ t ⊆ s ∧ Disjoint t (g • t) := by
  let ⟨t, t_open, x_in_t, disj_t_gt⟩ := t2_separation_smul x_moved
  refine ⟨s ∩ t, s_open.inter t_open, ⟨x_in_s, x_in_t⟩, Set.inter_subset_left _ _, ?disj⟩
  rw [Set.smul_set_inter]
  exact Set.disjoint_of_subset (Set.inter_subset_right _ _) (Set.inter_subset_right _ _) disj_t_gt

-- Unfortunately, there does not seem to be an easy way to construct the set for
-- `t2_separation_of_smul_injOn` without a few helper lemmas. These are marked as private so as to
-- not pollute the rest of the module's exports.

-- TODO: investigate whether Set.Finite.t2_separation or the `choose` tactic can help remove this

private def t2_of_smul_injOn_pair (inj_on : s.InjOn (· • x)) (g h : s) (g_ne_h : g.val ≠ h.val) :
    Set α :=
  t2_separation_smul (mem_fixedBy_compl_mul_of_smul_injOn inj_on g.prop h.prop g_ne_h)
    |>.choose

private theorem t2_of_smul_injOn_pair.isOpen (inj_on : s.InjOn (· • x)) (g h : s)
    (g_ne_h : g.val ≠ h.val) : IsOpen (t2_of_smul_injOn_pair inj_on g h g_ne_h) :=
  t2_separation_smul (mem_fixedBy_compl_mul_of_smul_injOn inj_on g.prop h.prop g_ne_h)
    |>.choose_spec.1

private theorem t2_of_smul_injOn_pair.mem (inj_on : s.InjOn (· • x)) (g h : s)
    (g_ne_h : g.val ≠ h.val) : x ∈ (t2_of_smul_injOn_pair inj_on g h g_ne_h) :=
  t2_separation_smul (mem_fixedBy_compl_mul_of_smul_injOn inj_on g.prop h.prop g_ne_h)
    |>.choose_spec.2.1

private theorem t2_of_smul_injOn_pair.disjoint (inj_on : s.InjOn (· • x)) (g h : s)
    (g_ne_h : g.val ≠ h.val) :
    Disjoint (t2_of_smul_injOn_pair inj_on g h g_ne_h)
      ((h.val⁻¹ * g.val) • t2_of_smul_injOn_pair inj_on g h g_ne_h) :=
  t2_separation_smul (mem_fixedBy_compl_mul_of_smul_injOn inj_on g.prop h.prop g_ne_h)
    |>.choose_spec.2.2

/--
One can construct an open set `t` such that for every pair `g ≠ h` of `s`,
`g • t` is disjoint from `h • t`.
-/
theorem t2_separation_of_smul_injOn {s : Set G} {x : α} (inj_on : s.InjOn (· • x))
    (s_finite : s.Finite) : ∃ t : Set α, IsOpen t ∧ x ∈ t ∧
      s.Pairwise (fun g h => Disjoint (g • t) (h • t)) := by
  let pairs := { pair : G × G | pair.1 ∈ s ∧ pair.2 ∈ s ∧ pair.1 ≠ pair.2 }
  have pairs_finite : Set.Finite pairs := by
    apply Set.Finite.subset (s_finite.prod s_finite)
    intro ⟨g, h⟩ ⟨g_in_s, h_in_s, _⟩
    exact ⟨g_in_s, h_in_s⟩

  let sets : pairs → Set α := fun ⟨pair, ⟨g_in_s, h_in_s, g_ne_h⟩⟩ =>
    t2_of_smul_injOn_pair inj_on ⟨pair.1, g_in_s⟩ ⟨pair.2, h_in_s⟩ g_ne_h

  refine ⟨⋂ pair, sets pair, ?isOpen, ?x_in_sets, ?pairwise_disjoint⟩
  case isOpen =>
    have := pairs_finite.fintype
    apply isOpen_iInter_of_finite
    intro ⟨⟨g, h⟩, ⟨g_in_s, h_in_s, g_ne_h⟩⟩
    apply t2_of_smul_injOn_pair.isOpen
  case x_in_sets =>
    apply Set.mem_iInter_of_mem
    intro ⟨⟨g, h⟩, ⟨g_in_s, h_in_s, g_ne_h⟩⟩
    apply t2_of_smul_injOn_pair.mem
  case pairwise_disjoint =>
    intro g g_in_s h h_in_s g_ne_h
    let pair : pairs := ⟨⟨g, h⟩, ⟨g_in_s, h_in_s, g_ne_h⟩⟩
    apply Set.disjoint_of_subset
    · show g • ⋂ pair, sets pair ⊆ g • sets pair
      apply Set.smul_set_mono
      apply Set.iInter_subset _ pair
    · show h • ⋂ pair, sets pair ⊆ h • sets pair
      apply Set.smul_set_mono
      apply Set.iInter_subset _ pair
    · rw [Set.smul_set_disjoint h⁻¹, inv_smul_smul]
      apply Disjoint.symm
      rw [← mul_smul]
      apply t2_of_smul_injOn_pair.disjoint

end Separation
