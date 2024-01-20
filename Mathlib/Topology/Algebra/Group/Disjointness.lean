/-
Copyright (c) 2024 Emilie Burgun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Burgun
-/

import Mathlib.Topology.Separation
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Group.LocallyDense
import Mathlib.GroupTheory.Commutator
import Mathlib.GroupTheory.GroupAction.FixedPoints

/-!
# Group-theoretical condition for the disjointness of `(fixedBy α g)ᶜ` sets

This module describes a somewhat mysterious condition for two group elements to have disjoint
`(fixedBy α g)ᶜ` sets, assuming the group action is locally dense.

TODO: link to locally dense

This is a key construction in the proof of Rubin's theorem, as the `(fixedBy α g)ᶜ` sets can be used
to describe a topological basis of the acted-upon topological space.
-/

namespace Rubin

open Pointwise
open MulAction

variable {G : Type*} [Group G] {g h : G}
variable {α : Type*} [TopologicalSpace α] [MulAction G α]

/--
A bundled pair `(fst, snd)` such that `fst`, `snd` and `⁅fst, ⁅snd, h⁆⁆` are elements
of the centralizer of `g` and `⁅fst, ⁅snd, h⁆⁆` is nontrivial.
-/
structure AlgDisjointElem (g h : G) :=
  /-- The first element of the pair -/
  fst : G
  /-- The second element of the pair -/
  snd : G
  /-- `fst` must be an element of the centralizer of `g` -/
  fst_comm : Commute fst g
  /-- `snd` must be an element of the centralizer of `g` -/
  snd_comm : Commute snd g
  /-- `comm_elem` must be an element of the centralizer of `g` -/
  comm_elem_commute' : Commute ⁅fst, ⁅snd, h⁆⁆ g
  /-- `comm_elem` must not be trivial -/
  comm_elem_nontrivial' : ⁅fst, ⁅snd, h⁆⁆ ≠ 1

def AlgDisjointElem.comm_elem (elem : AlgDisjointElem g h) : G :=
  ⁅elem.fst, ⁅elem.snd, h⁆⁆

theorem AlgDisjointElem.comm_elem_commute (elem : AlgDisjointElem g h) :
    Commute elem.comm_elem g := elem.comm_elem_commute'

theorem AlgDisjointElem.comm_elem_nontrivial (elem : AlgDisjointElem g h) :
    elem.comm_elem ≠ 1 := elem.comm_elem_nontrivial'

def AlgDisjointElem.conj (elem : AlgDisjointElem g h) (i : G) :
    AlgDisjointElem (i * g * i⁻¹) (i * h * i⁻¹) where
  fst := i * elem.fst * i⁻¹
  snd := i * elem.snd * i⁻¹
  fst_comm := by
    rw [Commute.conj_iff]
    exact elem.fst_comm
  snd_comm := by
    rw [Commute.conj_iff]
    exact elem.snd_comm
  comm_elem_commute' := by
    rw [← conjugate_commutatorElement, ← conjugate_commutatorElement, Commute.conj_iff]
    exact elem.comm_elem_commute'
  comm_elem_nontrivial' := by
    rw [← conjugate_commutatorElement, ← conjugate_commutatorElement, ne_eq, conj_eq_one_iff]
    exact elem.comm_elem_nontrivial'

/--
`f` is said to be algebraically disjoint with `g` if for all element `h` that doesn't commute with
`f`, one can construct `AlgDisjointElem g h`.
-/
def IsAlgDisjoint (f g : G) : Prop := ∀ h : G, ¬Commute f h → Nonempty (AlgDisjointElem g h)

theorem IsAlgDisjoint.conj {f g : G} (disj : IsAlgDisjoint f g) (h : G) :
    IsAlgDisjoint (h * f * h⁻¹) (h * g * h⁻¹) := by
  intro i nc
  rw [← Commute.conj_iff h⁻¹] at nc
  group at nc
  refine (disj _ nc).elim (fun elem => ⟨?elem⟩)
  have res := elem.conj h
  group at res
  rwa [zpow_neg_one] at res



/--
The algebraic centralizer of `g` contains all the elements `h` that commute with `f^12`,
such that `f` is some group element that is algebraically disjoint with `g`.

If the group action is locally moving and faithful on a topological space,
then `algCentralizer g = fixingSubgroup (interior (closure (fixedBy α g)))`.
-/
def algCentralizer (g : G) : Subgroup G :=
  Subgroup.centralizer { f^12 | (f : G) (_: IsAlgDisjoint f g) }

variable [T2Space α] [ContinuousConstSMul G α]

/--
If the action of `G` on `α` is continuous in `α`, then for all points not fixed by `g : G`,
there exists an open set `s` such that `x ∈ s` and `g • s` is disjoint from `s`.
-/
theorem t2_separation_smul {x : α} {g : G}
    (x_moved : x ∉ fixedBy α g) :
    ∃ s : Set α, x ∈ s ∧ IsOpen s ∧ Disjoint s (g • s) := by
  let ⟨s, t, s_open, t_open, gx_in_s, x_in_t, disj_st⟩ := t2_separation x_moved
  let u := (g⁻¹ • s) ∩ t
  have u_open : IsOpen u := (s_open.smul g⁻¹).inter t_open

  refine ⟨u, ⟨?gx_in_gs, x_in_t⟩, u_open, ?disj⟩
  · rwa [Set.mem_inv_smul_set_iff]
  · simp only [Set.smul_set_inter, smul_inv_smul]
    exact Set.disjoint_of_subset
      (Set.inter_subset_right _ _)
      (Set.inter_subset_left _ _)
      disj_st.symm

theorem t2_separation_smul_subset {x : α} {g : G} {s : Set α} (s_open : IsOpen s) (x_in_s : x ∈ s)
    (x_moved : x ∉ fixedBy α g) :
    ∃ t : Set α, x ∈ t ∧ t ⊆ s ∧ IsOpen t ∧ Disjoint t (g • t) := by
  let ⟨t, x_in_t, t_open, disj_t_gt⟩ := t2_separation_smul x_moved
  refine ⟨s ∩ t, ⟨x_in_s, x_in_t⟩, Set.inter_subset_left _ _, s_open.inter t_open, ?disj⟩
  rw [Set.smul_set_inter]
  exact Set.disjoint_of_subset (Set.inter_subset_right _ _) (Set.inter_subset_right _ _) disj_t_gt

variable (α) in
theorem isOpen_movedBy (g : G) : IsOpen (fixedBy α g)ᶜ := by
  refine isOpen_iff_forall_mem_open.mpr (fun x x_moved => ?ex_subset)
  let ⟨s, t, s_open, t_open, gx_in_s, x_in_t, disj_st⟩ := t2_separation x_moved

  exact ⟨
    (g⁻¹ • s) ∩ t,
    fun y ⟨gy_in_s, y_in_t⟩ =>
      Disjoint.ne_of_mem disj_st (Set.mem_inv_smul_set_iff.mp gy_in_s) y_in_t,
    (s_open.smul g⁻¹).inter t_open,
    ⟨Set.mem_inv_smul_set_iff.mpr gx_in_s, x_in_t⟩
  ⟩

/--
If two points have disjoint `(fixedBy α g)ᶜ` sets, then they are algebraically disjoint.
-/
theorem IsAlgDisjoint.of_disjoint_movedBy [LocallyDenseSMul G α] [FaithfulSMul G α]
    [NoIsolatedPoints α] {f g : G} (disj_fg : Disjoint (fixedBy α f)ᶜ (fixedBy α g)ᶜ) :
    IsAlgDisjoint f g := by
  intro i nc

  -- Since f and i do not commute, there must exist a point `x ∈ (fixedBy α f)ᶜ ∩ (fixedBy α i)ᶜ`
  have fi_not_disj := mt (commute_of_disjoint_movedBy (α := α)) nc
  have ⟨x, ⟨x_in_movedBy_f, x_in_movedBy_i⟩⟩ := Set.not_disjoint_iff.mp fi_not_disj

  -- We get from the Hausdorff property that `∃ s ∋ x, s ∩ i • s = ∅`
  have ⟨s, x_in_s, s_ss_movedBy, s_open, disj_s_is⟩ := t2_separation_smul_subset
    (isOpen_movedBy α f) x_in_movedBy_f x_in_movedBy_i
  clear x_in_movedBy_i fi_not_disj

  -- Since the action is locally dense, we can extract `f₂` such that `f₂` only moves within `s`
  -- and `f₂ • x ≠ x`
  have ⟨f₂, f₂_in_fixing, f₂_moving⟩ := LocallyDenseSMul.moving_elem_in_fixingSubgroup_compl
    G s_open x_in_s
  rw [mem_fixingSubgroup_compl_iff_movedBy_subset] at f₂_in_fixing

  -- Use the Hausdorff property again to get `∃ t ∋ x, t ∩ f₂ • t = ∅`
  have ⟨t, x_in_t, t_ss_s, t_open, disj_t_f₂t⟩ := t2_separation_smul_subset
    s_open x_in_s f₂_moving

  -- Use the local denseness again, to extract `f₁` such that `f₁` only moves within `t` and
  -- `f₁ • x ≠ x`
  have ⟨f₁, f₁_in_fixing, f₁_moving⟩ := LocallyDenseSMul.moving_elem_in_fixingSubgroup_compl
    G t_open x_in_t
  rw [mem_fixingSubgroup_compl_iff_movedBy_subset] at f₁_in_fixing

  -- Since `Disjoint s (i • s)` and `t ⊆ s`, while a point `x` is multiplied by `i`, the action of
  -- `f₂` does not affect it, so `(i * f₂ * i⁻¹) • t = t`
  have f₂i_smul_t_eq : ⁅f₂, i⁆ • t = f₂ • t := by
    apply commutatorElement_smul_eq_of_subset_fixedBy_conj
    apply subset_trans t_ss_s
    exact subset_fixedBy_conj_of_movedBy_subset_of_disj f₂_in_fixing disj_s_is

  refine ⟨⟨f₁, f₂, ?nc_f₁, ?nc_f₂, ?nc_comm_elem, ?comm_elem_ne_one⟩⟩
  case nc_f₁ =>
    apply commute_of_disjoint_movedBy (α := α)
    apply Set.disjoint_of_subset_left _ disj_fg
    exact subset_trans f₁_in_fixing (subset_trans t_ss_s s_ss_movedBy)
  case nc_f₂ =>
    apply commute_of_disjoint_movedBy (α := α)
    apply Set.disjoint_of_subset_left _ disj_fg
    exact subset_trans f₂_in_fixing s_ss_movedBy
  case nc_comm_elem =>
    apply commute_of_disjoint_movedBy (α := α)
    apply Set.disjoint_of_subset_left _ disj_fg
    -- `⁅f₁, ⁅f₂, i⁆⁆` does not move any point outside of `s`, although showing this is the case
    -- requires a few intermediate steps:
    calc
      (fixedBy α ⁅f₁, ⁅f₂, i⁆⁆)ᶜ = (fixedBy α ⁅⁅f₂, i⁆, f₁⁆)ᶜ := by
        rw [← fixedBy_inv_eq_fixedBy, commutatorElement_inv]
      _ ⊆ (fixedBy α f₁)ᶜ ∪ ⁅f₂, i⁆ • (fixedBy α f₁)ᶜ := by
        rw [Set.smul_set_compl, ← Set.compl_inter, Set.compl_subset_compl,
          commutatorElement_def _ f₁]
        apply subset_trans _ (fixedBy_commutatorElement α _ _)
        exact subset_of_eq rfl
      _ ⊆ t ∪ ⁅f₂, i⁆ • t := by
        apply Set.union_subset_union
        · assumption
        · apply Set.smul_set_mono
          assumption
      _ = t ∪ f₂ • t := by rw [f₂i_smul_t_eq]
      _ ⊆ s ∪ f₂ • t := Set.union_subset_union_left _ t_ss_s
      _ ⊆ s ∪ s := by
        apply Set.union_subset_union_right
        apply smul_subset_of_set_mem_fixedBy t_ss_s
        exact set_mem_fixedBy_of_movedBy_subset f₂_in_fixing
      _ = s := Set.union_self s
      _ ⊆ (fixedBy α f)ᶜ := s_ss_movedBy
  case comm_elem_ne_one =>
    intro eq_one
    apply f₁_moving
    -- Show that `⁅f₁, ⁅f₂, i⁆⁆ • x = f₁ • x`
    nth_rw 2 [← one_smul (M := G) x]
    rw [← eq_one, ← Set.singleton_eq_singleton_iff, ← Set.smul_set_singleton,
      ← Set.smul_set_singleton, eq_comm]
    apply commutatorElement_smul_eq_of_subset_fixedBy_conj
    apply subset_trans (Set.singleton_subset_iff.mpr x_in_t)
    apply subset_fixedBy_conj_of_movedBy_subset_of_disj f₁_in_fixing
    rw [f₂i_smul_t_eq]
    exact disj_t_f₂t

end Rubin
