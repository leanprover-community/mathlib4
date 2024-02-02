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

variable {G : Type*} (α : Type*) [Group G] [MulAction G α] [TopologicalSpace α]

/--
The regular support of a group element `g` on the topology `α` that the group is acting on is
the interior of the closure of the set of points moved by `g`.
-/
def RegularSupport (g : G) : RegularOpens α := RegularOpens.fromSet (fixedBy α g)ᶜ

lemma regularSupport_def (g : G) : RegularSupport α g = RegularOpens.fromSet (fixedBy α g)ᶜ := rfl

namespace RegularSupport

theorem subset_closure_fixedBy_compl (g : G) :
    (RegularSupport α g : Set α) ⊆ closure (fixedBy α g)ᶜ := interior_subset

variable [T2Space α] [ContinuousConstSMul G α]

theorem fixedBy_compl_subset (g : G) : (fixedBy α g)ᶜ ⊆ RegularSupport α g :=
  RegularOpens.subset_fromSet_of_isOpen (isClosed_fixedBy α g).isOpen_compl

variable {α} in
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

variable {α} in
theorem le_iff_mem_fixingSubgroup_compl (g : G) (s : RegularOpens α) :
    g ∈ G•[(↑s : Set α)ᶜ] ↔ RegularSupport α g ≤ s := by
  rw [mem_fixingSubgroup_compl_iff_movedBy_subset]
  exact le_iff_fixedBy_compl_subset g s

theorem smul (g h : G) : h • RegularSupport α g = RegularSupport α (h * g * h⁻¹) := by
  unfold RegularSupport
  rw [RegularOpens.smul_fromSet, Set.smul_set_compl, smul_fixedBy]

end RegularSupport

-- Note: there does not seem to be any benefit in requiring `t` to be finite
variable (G) in
def RegularSupportBasis :=
  { s : RegularOpens α // ∃ t : Set G, t.Finite ∧ (s : Set α) = ⋂ g ∈ t, RegularSupport α g }

-- Note: this seems to cause issues
instance RegularSupportBasis.setLike : SetLike (RegularSupportBasis G α) α where
  coe := fun b => ↑b.val
  coe_injective' := SetLike.coe_injective.comp Subtype.val_injective

instance RegularSupportBasis.semiLatticeInf : SemilatticeInf (RegularSupportBasis G α) where
  inf := fun b₁ b₂ => ⟨
    b₁.val ⊓ b₂.val,
    by
      let ⟨s₁, s₁_finite, b₁_eq⟩ := b₁.prop
      let ⟨s₂, s₂_finite, b₂_eq⟩ := b₂.prop
      refine ⟨s₁ ∪ s₂, s₁_finite.union s₂_finite, ?iInf_eq⟩
      rw [RegularOpens.coe_inf, b₁_eq, b₂_eq, Set.biInter_union]
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

/--
The element of the regular support basis constructed from the finite set `s`.
-/
def RegularSupportBasis.ofFinite (s : Set G) (s_finite : s.Finite) : RegularSupportBasis G α :=
  ⟨⟨
    ⋂ g ∈ s, RegularSupport α g,
    IsRegularOpen.biInter_of_finite s_finite fun _ _ => RegularOpens.regularOpen _
  ⟩, ⟨s, ⟨s_finite, rfl⟩⟩⟩

@[simp]
theorem RegularSupportBasis.coe_ofFinite {s : Set G} (s_finite : s.Finite) :
    (↑(RegularSupportBasis.ofFinite α s s_finite) : Set α) = ⋂ g ∈ s, RegularSupport α g := rfl

end Rubin
