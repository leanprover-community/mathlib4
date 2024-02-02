/-
Copyright (c) 2024 Emilie Burgun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Burgun
-/

import Mathlib.Topology.Separation
import Mathlib.Topology.Algebra.Group.LocallyDense
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.Topology.Sets.RegularOpens

/-!
# Regular supports in Rubin's theorem

This module defines the notion of a regular support in the proof of Rubin's theorem.
The regular support of a group element `g` is the `interior` of the `closure` of the set
`(fixedBy α g)ᶜ`.

## References

* [J. Belk, L. Elliott, F. Matucci, *A short proof of Rubin's theorem*][belk2023short]
-/

namespace Rubin

open Topology
open TopologicalSpace (RegularOpens)
open MulAction
open Pointwise

variable {G α : Type*} [Group G] [MulAction G α] [TopologicalSpace α]

variable (α) in
/--
The regular support of a group element `g` on the topology `α` that the group is acting on is
the interior of the closure of the set of points moved by `g`.
-/
def RegularSupport (g : G) : RegularOpens α := RegularOpens.fromSet (fixedBy α g)ᶜ

variable (α) in
lemma regularSupport_def (g : G) : RegularSupport α g = RegularOpens.fromSet (fixedBy α g)ᶜ := rfl

namespace RegularSupport

variable (α) in
theorem subset_closure_fixedBy_compl (g : G) :
    (RegularSupport α g : Set α) ⊆ closure (fixedBy α g)ᶜ := interior_subset

variable [T2Space α] [ContinuousConstSMul G α]

variable (α) in
theorem fixedBy_compl_subset (g : G) : (fixedBy α g)ᶜ ⊆ RegularSupport α g :=
  RegularOpens.subset_fromSet_of_isOpen (isClosed_fixedBy α g).isOpen_compl

theorem le_iff_fixedBy_compl_subset (g : G) (s : RegularOpens α) :
    (fixedBy α g)ᶜ ⊆ s ↔ RegularSupport α g ≤ s := by
  nth_rw 2 [← RegularOpens.fromSet_coe s]
  constructor
  · intro subset
    exact RegularOpens.fromSet_mono subset
  · intro le
    apply subset_trans (fixedBy_compl_subset α g)
    rw [← s.regularOpen]
    exact le

theorem le_iff_mem_fixingSubgroup_compl (g : G) (s : RegularOpens α) :
    g ∈ G•[(↑s : Set α)ᶜ] ↔ RegularSupport α g ≤ s := by
  rw [mem_fixingSubgroup_compl_iff_movedBy_subset]
  exact le_iff_fixedBy_compl_subset g s

variable (α) in
theorem smul (g h : G) : h • RegularSupport α g = RegularSupport α (h * g * h⁻¹) := by
  unfold RegularSupport
  rw [RegularOpens.smul_fromSet, Set.smul_set_compl, smul_fixedBy]

end RegularSupport

variable (G α) in
def RegularSupportBasis :=
  { s : Set α | ∃ t : Set G, t.Finite ∧ (s : Set α) = ⋂ g ∈ t, RegularSupport α g }

-- instance RegularSupportBasis.setLike : SetLike (RegularSupportBasis G α) α where
--   coe := fun b => b.val
--   coe_injective' := Subtype.val_injective

-- theorem RegularSupportBasis.exists_finite_generator (b : RegularSupportBasis G α) :
--     ∃ t : Set G, t.Finite ∧ (b : Set α) = ⋂ g ∈ t, RegularSupport α g := b.prop

instance RegularSupportBasis.semiLatticeInf : SemilatticeInf (RegularSupportBasis G α) where
  inf := fun b₁ b₂ => ⟨
    b₁.val ∩ b₂.val,
    by
      let ⟨s₁, s₁_finite, b₁_eq⟩ := b₁.prop
      let ⟨s₂, s₂_finite, b₂_eq⟩ := b₂.prop
      refine ⟨s₁ ∪ s₂, s₁_finite.union s₂_finite, ?iInf_eq⟩
      rw [b₁_eq, b₂_eq, Set.biInter_union]
  ⟩
  inf_le_left := fun b₁ b₂ => (inf_le_left : b₁.val ⊓ b₂.val ≤ b₁.val)
  inf_le_right := fun b₁ b₂ => (inf_le_right : b₁.val ⊓ b₂.val ≤ b₂.val)
  le_inf := fun b₁ b₂ b₃ h₁₂ h₁₃ => (le_inf h₁₂ h₁₃ : b₁.val ≤ b₂.val ⊓ b₃.val)

instance RegularSupportBasis.orderTop : OrderTop (RegularSupportBasis G α) where
  top := ⟨
    ⊤,
    by
      use ∅
      simp
  ⟩
  le_top := fun b => (le_top : b.val ≤ ⊤)

instance RegularSupportBasis.orderBot : OrderBot (RegularSupportBasis G α) where
  bot := ⟨
    ⊥,
    by
      use {1}
      simp [RegularSupport]
  ⟩
  bot_le := fun b => (bot_le : ⊥ ≤ b.val)

theorem RegularSupportBasis.regularOpen (b : RegularSupportBasis G α) :
    IsRegularOpen (b : Set α) := by
  let ⟨s, s_finite, b_eq⟩ := b.prop
  rw [b_eq]
  exact IsRegularOpen.biInter_of_finite s_finite fun g _ => RegularOpens.regularOpen _

variable (α) in
/--
The element of the regular support basis constructed from the finite set `s`.
-/
def RegularSupportBasis.ofFinite (s : Set G) (s_finite : s.Finite) : RegularSupportBasis G α :=
  ⟨⋂ g ∈ s, RegularSupport α g, s, s_finite, rfl⟩

@[simp]
theorem RegularSupportBasis.coe_ofFinite {s : Set G} (s_finite : s.Finite) :
    (↑(RegularSupportBasis.ofFinite α s s_finite) : Set α) = ⋂ g ∈ s, RegularSupport α g := rfl

variable [LocallyCompactSpace α] [T2Space α] [NoIsolatedPoints α]
variable [ContinuousConstSMul G α] [LocallyDenseSMul G α]

variable (G) in
/--
This corresponds to proposition 3.2 of [*A short proof of Rubin's theorem*][belk2023short].
-/
theorem exists_regularSupport_subset {s : Set α} (s_open : IsOpen s) {p : α} (p_in_s : p ∈ s) :
    ∃ g : G, p ∈ RegularSupport α g ∧ ↑(RegularSupport α g) ⊆ s := by
  have s_in_nhds : s ∈ 𝓝 p := IsOpen.mem_nhds s_open p_in_s
  let ⟨t', t'_in_nhds, t'_ss_s, t'_compact⟩ := local_compact_nhds s_in_nhds

  let ⟨t, _, t_closed, t'_ss_int_t, t_ss_s⟩ := exists_compact_closed_between t'_compact s_open
    t'_ss_s

  have p_in_int : p ∈ interior t := t'_ss_int_t (mem_of_mem_nhds t'_in_nhds)
  let ⟨g, g_in_fixing, g_moves⟩ := LocallyDenseSMul.moving_elem_in_fixingSubgroup_compl G
    isOpen_interior p_in_int

  refine ⟨g, RegularSupport.fixedBy_compl_subset _ _ g_moves, ?rsupp_subset⟩
  rw [mem_fixingSubgroup_compl_iff_movedBy_subset] at g_in_fixing
  rw [RegularSupport, RegularOpens.coe_fromSet, ← s_open.interior_eq]
  apply interior_mono
  apply subset_trans _ t_ss_s
  rw [← t_closed.closure_eq]
  exact closure_mono (subset_trans g_in_fixing interior_subset)

/--
In a locally compact, Hausdorff space `α` with no isolated points, and a locally dense,
continuous group action, the sets of `RegularSupportBasis G α` form a topological basis for `α`.
-/
theorem RegularSupportBasis.isBasis :
    TopologicalSpace.IsTopologicalBasis (RegularSupportBasis G α) := by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · exact fun _ mem => (RegularSupportBasis.regularOpen ⟨_, mem⟩).isOpen
  · intro a s a_in_s s_open
    let ⟨g, a_in_supp, supp_ss⟩ := exists_regularSupport_subset G s_open a_in_s
    refine ⟨_, ⟨{g}, Set.finite_singleton g, rfl⟩, ?rest⟩
    simp only [Set.mem_singleton_iff, Set.iInter_iInter_eq_left, SetLike.mem_coe]
    exact ⟨a_in_supp, supp_ss⟩

end Rubin
