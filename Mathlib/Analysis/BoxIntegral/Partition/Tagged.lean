/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module analysis.box_integral.partition.tagged
! leanprover-community/mathlib commit 6ca1a09bc9aa75824bf97388c9e3b441fc4ccf3f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.BoxIntegral.Partition.Basic

/-!
# Tagged partitions

A tagged (pre)partition is a (pre)partition `π` enriched with a tagged point for each box of
‵π`. For simplicity we require that the function `box_integral.tagged_prepartition.tag` is defined
on all boxes `J : box ι` but use its values only on boxes of the partition. Given `π :
box_integral.tagged_partition I`, we require that each `box_integral.tagged_partition π J` belongs
to `box_integral.box.Icc I`. If for every `J ∈ π`, `π.tag J` belongs to `J.Icc`, then `π` is called
a *Henstock* partition. We do not include this assumption into the definition of a tagged
(pre)partition because McShane integral is defined as a limit along tagged partitions without this
requirement.

### Tags

rectangular box, box partition
-/


noncomputable section

open Classical ENNReal NNReal

open Set Function

namespace BoxIntegral

variable {ι : Type _}

/-- A tagged prepartition is a prepartition enriched with a tagged point for each box of the
prepartition. For simiplicity we require that `tag` is defined for all boxes in `ι → ℝ` but
we will use onle the values of `tag` on the boxes of the partition. -/
structure TaggedPrepartition (I : Box ι) extends Prepartition I where
  Tag : Box ι → ι → ℝ
  tag_mem_Icc : ∀ J, tag J ∈ I.Icc
#align box_integral.tagged_prepartition BoxIntegral.TaggedPrepartition

namespace TaggedPrepartition

variable {I J J₁ J₂ : Box ι} (π : TaggedPrepartition I) {x : ι → ℝ}

instance : Membership (Box ι) (TaggedPrepartition I) :=
  ⟨fun J π => J ∈ π.boxes⟩

@[simp]
theorem mem_toPrepartition {π : TaggedPrepartition I} : J ∈ π.toPrepartition ↔ J ∈ π :=
  Iff.rfl
#align box_integral.tagged_prepartition.mem_to_prepartition BoxIntegral.TaggedPrepartition.mem_toPrepartition

@[simp]
theorem mem_mk (π : Prepartition I) (f h) : J ∈ mk π f h ↔ J ∈ π :=
  Iff.rfl
#align box_integral.tagged_prepartition.mem_mk BoxIntegral.TaggedPrepartition.mem_mk

/-- Union of all boxes of a tagged prepartition. -/
def union : Set (ι → ℝ) :=
  π.toPrepartition.unionᵢ
#align box_integral.tagged_prepartition.Union BoxIntegral.TaggedPrepartition.union

theorem union_def : π.unionᵢ = ⋃ J ∈ π, ↑J :=
  rfl
#align box_integral.tagged_prepartition.Union_def BoxIntegral.TaggedPrepartition.union_def

@[simp]
theorem union_mk (π : Prepartition I) (f h) : (mk π f h).unionᵢ = π.unionᵢ :=
  rfl
#align box_integral.tagged_prepartition.Union_mk BoxIntegral.TaggedPrepartition.union_mk

@[simp]
theorem unionᵢ_toPrepartition : π.toPrepartition.unionᵢ = π.unionᵢ :=
  rfl
#align box_integral.tagged_prepartition.Union_to_prepartition BoxIntegral.TaggedPrepartition.unionᵢ_toPrepartition

@[simp]
theorem mem_union : x ∈ π.unionᵢ ↔ ∃ J ∈ π, x ∈ J :=
  Set.mem_unionᵢ₂
#align box_integral.tagged_prepartition.mem_Union BoxIntegral.TaggedPrepartition.mem_union

theorem subset_union (h : J ∈ π) : ↑J ⊆ π.unionᵢ :=
  subset_bunionᵢ_of_mem h
#align box_integral.tagged_prepartition.subset_Union BoxIntegral.TaggedPrepartition.subset_union

theorem union_subset : π.unionᵢ ⊆ I :=
  unionᵢ₂_subset π.le_of_mem'
#align box_integral.tagged_prepartition.Union_subset BoxIntegral.TaggedPrepartition.union_subset

/-- A tagged prepartition is a partition if it covers the whole box. -/
def IsPartition :=
  π.toPrepartition.IsPartition
#align box_integral.tagged_prepartition.is_partition BoxIntegral.TaggedPrepartition.IsPartition

theorem isPartition_iff_union_eq : IsPartition π ↔ π.unionᵢ = I :=
  Prepartition.isPartition_iff_unionᵢ_eq
#align box_integral.tagged_prepartition.is_partition_iff_Union_eq BoxIntegral.TaggedPrepartition.isPartition_iff_union_eq

/-- The tagged partition made of boxes of `π` that satisfy predicate `p`. -/
@[simps (config := { fullyApplied := false })]
def filter (p : Box ι → Prop) : TaggedPrepartition I :=
  ⟨π.1.filterₓ p, π.2, π.3⟩
#align box_integral.tagged_prepartition.filter BoxIntegral.TaggedPrepartition.filter

@[simp]
theorem mem_filter {p : Box ι → Prop} : J ∈ π.filterₓ p ↔ J ∈ π ∧ p J :=
  Finset.mem_filter
#align box_integral.tagged_prepartition.mem_filter BoxIntegral.TaggedPrepartition.mem_filter

@[simp]
theorem union_filter_not (π : TaggedPrepartition I) (p : Box ι → Prop) :
    (π.filterₓ fun J => ¬p J).unionᵢ = π.unionᵢ \ (π.filterₓ p).unionᵢ :=
  π.toPrepartition.unionᵢ_filter_not p
#align box_integral.tagged_prepartition.Union_filter_not BoxIntegral.TaggedPrepartition.union_filter_not

end TaggedPrepartition

namespace Prepartition

variable {I J : Box ι}

/-- Given a partition `π` of `I : box_integral.box ι` and a collection of tagged partitions
`πi J` of all boxes `J ∈ π`, returns the tagged partition of `I` into all the boxes of `πi J`
with tags coming from `(πi J).tag`. -/
def bUnionTagged (π : Prepartition I) (πi : ∀ J, TaggedPrepartition J) : TaggedPrepartition I
    where
  toPrepartition := π.bunionᵢ fun J => (πi J).toPrepartition
  Tag J := (πi (π.bunionᵢIndex (fun J => (πi J).toPrepartition) J)).Tag J
  tag_mem_Icc J := Box.le_iff_Icc.1 (π.bunionᵢIndex_le _ _) ((πi _).tag_mem_Icc _)
#align box_integral.prepartition.bUnion_tagged BoxIntegral.Prepartition.bUnionTagged

@[simp]
theorem mem_bUnionTagged (π : Prepartition I) {πi : ∀ J, TaggedPrepartition J} :
    J ∈ π.bUnionTagged πi ↔ ∃ J' ∈ π, J ∈ πi J' :=
  π.mem_bunionᵢ
#align box_integral.prepartition.mem_bUnion_tagged BoxIntegral.Prepartition.mem_bUnionTagged

theorem tag_bUnionTagged (π : Prepartition I) {πi : ∀ J, TaggedPrepartition J} (hJ : J ∈ π) {J'}
    (hJ' : J' ∈ πi J) : (π.bUnionTagged πi).Tag J' = (πi J).Tag J' :=
  by
  have : J' ∈ π.bUnion_tagged πi := π.mem_bUnion.2 ⟨J, hJ, hJ'⟩
  obtain rfl := π.bUnion_index_of_mem hJ hJ'
  rfl
#align box_integral.prepartition.tag_bUnion_tagged BoxIntegral.Prepartition.tag_bUnionTagged

@[simp]
theorem union_bUnionTagged (π : Prepartition I) (πi : ∀ J, TaggedPrepartition J) :
    (π.bUnionTagged πi).unionᵢ = ⋃ J ∈ π, (πi J).unionᵢ :=
  unionᵢ_bunionᵢ _ _
#align box_integral.prepartition.Union_bUnion_tagged BoxIntegral.Prepartition.union_bUnionTagged

theorem forall_bUnionTagged (p : (ι → ℝ) → Box ι → Prop) (π : Prepartition I)
    (πi : ∀ J, TaggedPrepartition J) :
    (∀ J ∈ π.bUnionTagged πi, p ((π.bUnionTagged πi).Tag J) J) ↔
      ∀ J ∈ π, ∀ J' ∈ πi J, p ((πi J).Tag J') J' :=
  by
  simp only [bex_imp, mem_bUnion_tagged]
  refine' ⟨fun H J hJ J' hJ' => _, fun H J' J hJ hJ' => _⟩
  · rw [← π.tag_bUnion_tagged hJ hJ']
    exact H J' J hJ hJ'
  · rw [π.tag_bUnion_tagged hJ hJ']
    exact H J hJ J' hJ'
#align box_integral.prepartition.forall_bUnion_tagged BoxIntegral.Prepartition.forall_bUnionTagged

theorem IsPartition.bUnionTagged {π : Prepartition I} (h : IsPartition π)
    {πi : ∀ J, TaggedPrepartition J} (hi : ∀ J ∈ π, (πi J).IsPartition) :
    (π.bUnionTagged πi).IsPartition :=
  h.bunionᵢ hi
#align box_integral.prepartition.is_partition.bUnion_tagged BoxIntegral.Prepartition.IsPartition.bUnionTagged

end Prepartition

namespace TaggedPrepartition

variable {I J : Box ι} {π π₁ π₂ : TaggedPrepartition I} {x : ι → ℝ}

/-- Given a tagged partition `π` of `I` and a (not tagged) partition `πi J hJ` of each `J ∈ π`,
returns the tagged partition of `I` into all the boxes of all `πi J hJ`. The tag of a box `J`
is defined to be the `π.tag` of the box of the partition `π` that includes `J`.

Note that usually the result is not a Henstock partition. -/
@[simps (config := { fullyApplied := false }) Tag]
def bUnionPrepartition (π : TaggedPrepartition I) (πi : ∀ J, Prepartition J) : TaggedPrepartition I
    where
  toPrepartition := π.toPrepartition.bunionᵢ πi
  Tag J := π.Tag (π.toPrepartition.bunionᵢIndex πi J)
  tag_mem_Icc J := π.tag_mem_Icc _
#align box_integral.tagged_prepartition.bUnion_prepartition BoxIntegral.TaggedPrepartition.bUnionPrepartition

theorem IsPartition.bUnionPrepartition {π : TaggedPrepartition I} (h : IsPartition π)
    {πi : ∀ J, Prepartition J} (hi : ∀ J ∈ π, (πi J).IsPartition) :
    (π.bUnionPrepartition πi).IsPartition :=
  h.bunionᵢ hi
#align box_integral.tagged_prepartition.is_partition.bUnion_prepartition BoxIntegral.TaggedPrepartition.IsPartition.bUnionPrepartition

/-- Given two partitions `π₁` and `π₁`, one of them tagged and the other is not, returns the tagged
partition with `to_partition = π₁.to_partition ⊓ π₂` and tags coming from `π₁`.

Note that usually the result is not a Henstock partition. -/
def infPrepartition (π : TaggedPrepartition I) (π' : Prepartition I) : TaggedPrepartition I :=
  π.bUnionPrepartition fun J => π'.restrict J
#align box_integral.tagged_prepartition.inf_prepartition BoxIntegral.TaggedPrepartition.infPrepartition

@[simp]
theorem infPrepartition_toPrepartition (π : TaggedPrepartition I) (π' : Prepartition I) :
    (π.infPrepartition π').toPrepartition = π.toPrepartition ⊓ π' :=
  rfl
#align box_integral.tagged_prepartition.inf_prepartition_to_prepartition BoxIntegral.TaggedPrepartition.infPrepartition_toPrepartition

theorem mem_infPrepartition_comm :
    J ∈ π₁.infPrepartition π₂.toPrepartition ↔ J ∈ π₂.infPrepartition π₁.toPrepartition := by
  simp only [← mem_to_prepartition, inf_prepartition_to_prepartition, inf_comm]
#align box_integral.tagged_prepartition.mem_inf_prepartition_comm BoxIntegral.TaggedPrepartition.mem_infPrepartition_comm

theorem IsPartition.infPrepartition (h₁ : π₁.IsPartition) {π₂ : Prepartition I}
    (h₂ : π₂.IsPartition) : (π₁.infPrepartition π₂).IsPartition :=
  h₁.inf h₂
#align box_integral.tagged_prepartition.is_partition.inf_prepartition BoxIntegral.TaggedPrepartition.IsPartition.infPrepartition

open Metric

/-- A tagged partition is said to be a Henstock partition if for each `J ∈ π`, the tag of `J`
belongs to `J.Icc`. -/
def IsHenstock (π : TaggedPrepartition I) : Prop :=
  ∀ J ∈ π, π.Tag J ∈ J.Icc
#align box_integral.tagged_prepartition.is_Henstock BoxIntegral.TaggedPrepartition.IsHenstock

@[simp]
theorem isHenstock_bUnionTagged {π : Prepartition I} {πi : ∀ J, TaggedPrepartition J} :
    IsHenstock (π.bUnionTagged πi) ↔ ∀ J ∈ π, (πi J).IsHenstock :=
  π.forall_bUnionTagged (fun x J => x ∈ J.Icc) πi
#align box_integral.tagged_prepartition.is_Henstock_bUnion_tagged BoxIntegral.TaggedPrepartition.isHenstock_bUnionTagged

/-- In a Henstock prepartition, there are at most `2 ^ fintype.card ι` boxes with a given tag. -/
theorem IsHenstock.card_filter_tag_eq_le [Fintype ι] (h : π.IsHenstock) (x : ι → ℝ) :
    (π.boxes.filterₓ fun J => π.Tag J = x).card ≤ 2 ^ Fintype.card ι :=
  calc
    (π.boxes.filterₓ fun J => π.Tag J = x).card ≤
        (π.boxes.filterₓ fun J : Box ι => x ∈ J.Icc).card :=
      by
      refine' Finset.card_le_of_subset fun J hJ => _
      rw [Finset.mem_filter] at hJ⊢; rcases hJ with ⟨hJ, rfl⟩
      exact ⟨hJ, h J hJ⟩
    _ ≤ 2 ^ Fintype.card ι := π.toPrepartition.card_filter_mem_Icc_le x
    
#align box_integral.tagged_prepartition.is_Henstock.card_filter_tag_eq_le BoxIntegral.TaggedPrepartition.IsHenstock.card_filter_tag_eq_le

/-- A tagged partition `π` is subordinate to `r : (ι → ℝ) → ℝ` if each box `J ∈ π` is included in
the closed ball with center `π.tag J` and radius `r (π.tag J)`. -/
def IsSubordinate [Fintype ι] (π : TaggedPrepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) : Prop :=
  ∀ J ∈ π, (J : _).Icc ⊆ closedBall (π.Tag J) (r <| π.Tag J)
#align box_integral.tagged_prepartition.is_subordinate BoxIntegral.TaggedPrepartition.IsSubordinate

variable {r r₁ r₂ : (ι → ℝ) → Ioi (0 : ℝ)}

@[simp]
theorem isSubordinate_bUnionTagged [Fintype ι] {π : Prepartition I}
    {πi : ∀ J, TaggedPrepartition J} :
    IsSubordinate (π.bUnionTagged πi) r ↔ ∀ J ∈ π, (πi J).IsSubordinate r :=
  π.forall_bUnionTagged (fun x J => J.Icc ⊆ closedBall x (r x)) πi
#align box_integral.tagged_prepartition.is_subordinate_bUnion_tagged BoxIntegral.TaggedPrepartition.isSubordinate_bUnionTagged

theorem IsSubordinate.bUnionPrepartition [Fintype ι] (h : IsSubordinate π r)
    (πi : ∀ J, Prepartition J) : IsSubordinate (π.bUnionPrepartition πi) r := fun J hJ =>
  Subset.trans (Box.le_iff_Icc.1 <| π.toPrepartition.le_bunionᵢIndex hJ) <|
    h _ <| π.toPrepartition.bunionᵢIndex_mem hJ
#align box_integral.tagged_prepartition.is_subordinate.bUnion_prepartition BoxIntegral.TaggedPrepartition.IsSubordinate.bUnionPrepartition

theorem IsSubordinate.infPrepartition [Fintype ι] (h : IsSubordinate π r) (π' : Prepartition I) :
    IsSubordinate (π.infPrepartition π') r :=
  h.bUnionPrepartition _
#align box_integral.tagged_prepartition.is_subordinate.inf_prepartition BoxIntegral.TaggedPrepartition.IsSubordinate.infPrepartition

theorem IsSubordinate.mono' [Fintype ι] {π : TaggedPrepartition I} (hr₁ : π.IsSubordinate r₁)
    (h : ∀ J ∈ π, r₁ (π.Tag J) ≤ r₂ (π.Tag J)) : π.IsSubordinate r₂ := fun J hJ x hx =>
  closedBall_subset_closedBall (h _ hJ) (hr₁ _ hJ hx)
#align box_integral.tagged_prepartition.is_subordinate.mono' BoxIntegral.TaggedPrepartition.IsSubordinate.mono'

theorem IsSubordinate.mono [Fintype ι] {π : TaggedPrepartition I} (hr₁ : π.IsSubordinate r₁)
    (h : ∀ x ∈ I.Icc, r₁ x ≤ r₂ x) : π.IsSubordinate r₂ :=
  hr₁.mono' fun J _ => h _ <| π.tag_mem_Icc J
#align box_integral.tagged_prepartition.is_subordinate.mono BoxIntegral.TaggedPrepartition.IsSubordinate.mono

theorem IsSubordinate.diam_le [Fintype ι] {π : TaggedPrepartition I} (h : π.IsSubordinate r)
    (hJ : J ∈ π.boxes) : diam J.Icc ≤ 2 * r (π.Tag J) :=
  calc
    diam J.Icc ≤ diam (closedBall (π.Tag J) (r <| π.Tag J)) := diam_mono (h J hJ) bounded_closedBall
    _ ≤ 2 * r (π.Tag J) := diam_closedBall (le_of_lt (r _).2)
    
#align box_integral.tagged_prepartition.is_subordinate.diam_le BoxIntegral.TaggedPrepartition.IsSubordinate.diam_le

/-- Tagged prepartition with single box and prescribed tag. -/
@[simps (config := { fullyApplied := false })]
def single (I J : Box ι) (hJ : J ≤ I) (x : ι → ℝ) (h : x ∈ I.Icc) : TaggedPrepartition I :=
  ⟨Prepartition.single I J hJ, fun J => x, fun J => h⟩
#align box_integral.tagged_prepartition.single BoxIntegral.TaggedPrepartition.single

@[simp]
theorem mem_single {J'} (hJ : J ≤ I) (h : x ∈ I.Icc) : J' ∈ single I J hJ x h ↔ J' = J :=
  Finset.mem_singleton
#align box_integral.tagged_prepartition.mem_single BoxIntegral.TaggedPrepartition.mem_single

instance (I : Box ι) : Inhabited (TaggedPrepartition I) :=
  ⟨single I I le_rfl I.upper I.upper_mem_Icc⟩

theorem isPartition_single_iff (hJ : J ≤ I) (h : x ∈ I.Icc) :
    (single I J hJ x h).IsPartition ↔ J = I :=
  Prepartition.isPartition_single_iff hJ
#align box_integral.tagged_prepartition.is_partition_single_iff BoxIntegral.TaggedPrepartition.isPartition_single_iff

theorem isPartition_single (h : x ∈ I.Icc) : (single I I le_rfl x h).IsPartition :=
  Prepartition.isPartitionTop I
#align box_integral.tagged_prepartition.is_partition_single BoxIntegral.TaggedPrepartition.isPartition_single

theorem forall_mem_single (p : (ι → ℝ) → Box ι → Prop) (hJ : J ≤ I) (h : x ∈ I.Icc) :
    (∀ J' ∈ single I J hJ x h, p ((single I J hJ x h).Tag J') J') ↔ p x J := by simp
#align box_integral.tagged_prepartition.forall_mem_single BoxIntegral.TaggedPrepartition.forall_mem_single

@[simp]
theorem isHenstock_single_iff (hJ : J ≤ I) (h : x ∈ I.Icc) :
    IsHenstock (single I J hJ x h) ↔ x ∈ J.Icc :=
  forall_mem_single (fun x J => x ∈ J.Icc) hJ h
#align box_integral.tagged_prepartition.is_Henstock_single_iff BoxIntegral.TaggedPrepartition.isHenstock_single_iff

@[simp]
theorem isHenstock_single (h : x ∈ I.Icc) : IsHenstock (single I I le_rfl x h) :=
  (isHenstock_single_iff (le_refl I) h).2 h
#align box_integral.tagged_prepartition.is_Henstock_single BoxIntegral.TaggedPrepartition.isHenstock_single

@[simp]
theorem isSubordinate_single [Fintype ι] (hJ : J ≤ I) (h : x ∈ I.Icc) :
    IsSubordinate (single I J hJ x h) r ↔ J.Icc ⊆ closedBall x (r x) :=
  forall_mem_single (fun x J => J.Icc ⊆ closedBall x (r x)) hJ h
#align box_integral.tagged_prepartition.is_subordinate_single BoxIntegral.TaggedPrepartition.isSubordinate_single

@[simp]
theorem union_single (hJ : J ≤ I) (h : x ∈ I.Icc) : (single I J hJ x h).unionᵢ = J :=
  Prepartition.unionᵢ_single hJ
#align box_integral.tagged_prepartition.Union_single BoxIntegral.TaggedPrepartition.union_single

/-- Union of two tagged prepartitions with disjoint unions of boxes. -/
def disjUnion (π₁ π₂ : TaggedPrepartition I) (h : Disjoint π₁.unionᵢ π₂.unionᵢ) :
    TaggedPrepartition I
    where
  toPrepartition := π₁.toPrepartition.disjUnion π₂.toPrepartition h
  Tag := π₁.boxes.piecewise π₁.Tag π₂.Tag
  tag_mem_Icc J := by
    dsimp only [Finset.piecewise]
    split_ifs
    exacts[π₁.tag_mem_Icc J, π₂.tag_mem_Icc J]
#align box_integral.tagged_prepartition.disj_union BoxIntegral.TaggedPrepartition.disjUnion

@[simp]
theorem disjUnion_boxes (h : Disjoint π₁.unionᵢ π₂.unionᵢ) :
    (π₁.disjUnion π₂ h).boxes = π₁.boxes ∪ π₂.boxes :=
  rfl
#align box_integral.tagged_prepartition.disj_union_boxes BoxIntegral.TaggedPrepartition.disjUnion_boxes

@[simp]
theorem mem_disjUnion (h : Disjoint π₁.unionᵢ π₂.unionᵢ) :
    J ∈ π₁.disjUnion π₂ h ↔ J ∈ π₁ ∨ J ∈ π₂ :=
  Finset.mem_union
#align box_integral.tagged_prepartition.mem_disj_union BoxIntegral.TaggedPrepartition.mem_disjUnion

@[simp]
theorem union_disjUnion (h : Disjoint π₁.unionᵢ π₂.unionᵢ) :
    (π₁.disjUnion π₂ h).unionᵢ = π₁.unionᵢ ∪ π₂.unionᵢ :=
  Prepartition.unionᵢ_disjUnion _
#align box_integral.tagged_prepartition.Union_disj_union BoxIntegral.TaggedPrepartition.union_disjUnion

theorem disjUnion_tag_of_mem_left (h : Disjoint π₁.unionᵢ π₂.unionᵢ) (hJ : J ∈ π₁) :
    (π₁.disjUnion π₂ h).Tag J = π₁.Tag J :=
  dif_pos hJ
#align box_integral.tagged_prepartition.disj_union_tag_of_mem_left BoxIntegral.TaggedPrepartition.disjUnion_tag_of_mem_left

theorem disjUnion_tag_of_mem_right (h : Disjoint π₁.unionᵢ π₂.unionᵢ) (hJ : J ∈ π₂) :
    (π₁.disjUnion π₂ h).Tag J = π₂.Tag J :=
  dif_neg fun h₁ => h.le_bot ⟨π₁.subset_unionᵢ h₁ J.upper_mem, π₂.subset_unionᵢ hJ J.upper_mem⟩
#align box_integral.tagged_prepartition.disj_union_tag_of_mem_right BoxIntegral.TaggedPrepartition.disjUnion_tag_of_mem_right

theorem IsSubordinate.disjUnion [Fintype ι] (h₁ : IsSubordinate π₁ r) (h₂ : IsSubordinate π₂ r)
    (h : Disjoint π₁.unionᵢ π₂.unionᵢ) : IsSubordinate (π₁.disjUnion π₂ h) r :=
  by
  refine' fun J hJ => (Finset.mem_union.1 hJ).elim (fun hJ => _) fun hJ => _
  · rw [disj_union_tag_of_mem_left _ hJ]
    exact h₁ _ hJ
  · rw [disj_union_tag_of_mem_right _ hJ]
    exact h₂ _ hJ
#align box_integral.tagged_prepartition.is_subordinate.disj_union BoxIntegral.TaggedPrepartition.IsSubordinate.disjUnion

theorem IsHenstock.disjUnion (h₁ : IsHenstock π₁) (h₂ : IsHenstock π₂)
    (h : Disjoint π₁.unionᵢ π₂.unionᵢ) : IsHenstock (π₁.disjUnion π₂ h) :=
  by
  refine' fun J hJ => (Finset.mem_union.1 hJ).elim (fun hJ => _) fun hJ => _
  · rw [disj_union_tag_of_mem_left _ hJ]
    exact h₁ _ hJ
  · rw [disj_union_tag_of_mem_right _ hJ]
    exact h₂ _ hJ
#align box_integral.tagged_prepartition.is_Henstock.disj_union BoxIntegral.TaggedPrepartition.IsHenstock.disjUnion

/-- If `I ≤ J`, then every tagged prepartition of `I` is a tagged prepartition of `J`. -/
def embedBox (I J : Box ι) (h : I ≤ J) : TaggedPrepartition I ↪ TaggedPrepartition J
    where
  toFun π :=
    { π with
      le_of_mem' := fun J' hJ' => (π.le_of_mem' J' hJ').trans h
      tag_mem_Icc := fun J => Box.le_iff_Icc.1 h (π.tag_mem_Icc J) }
  inj' := by
    rintro ⟨⟨b₁, h₁le, h₁d⟩, t₁, ht₁⟩ ⟨⟨b₂, h₂le, h₂d⟩, t₂, ht₂⟩ H
    simpa using H
#align box_integral.tagged_prepartition.embed_box BoxIntegral.TaggedPrepartition.embedBox

section Distortion

variable [Fintype ι] (π)

open Finset

/-- The distortion of a tagged prepartition is the maximum of distortions of its boxes. -/
def distortion : ℝ≥0 :=
  π.toPrepartition.distortion
#align box_integral.tagged_prepartition.distortion BoxIntegral.TaggedPrepartition.distortion

theorem distortion_le_of_mem (h : J ∈ π) : J.distortion ≤ π.distortion :=
  le_sup h
#align box_integral.tagged_prepartition.distortion_le_of_mem BoxIntegral.TaggedPrepartition.distortion_le_of_mem

theorem distortion_le_iff {c : ℝ≥0} : π.distortion ≤ c ↔ ∀ J ∈ π, Box.distortion J ≤ c :=
  Finset.sup_le_iff
#align box_integral.tagged_prepartition.distortion_le_iff BoxIntegral.TaggedPrepartition.distortion_le_iff

@[simp]
theorem BoxIntegral.Prepartition.distortion_bUnionTagged (π : Prepartition I)
    (πi : ∀ J, TaggedPrepartition J) :
    (π.bUnionTagged πi).distortion = π.boxes.sup fun J => (πi J).distortion :=
  sup_bunionᵢ _ _
#align box_integral.prepartition.distortion_bUnion_tagged BoxIntegral.Prepartition.distortion_bUnionTagged

@[simp]
theorem distortion_bUnionPrepartition (π : TaggedPrepartition I) (πi : ∀ J, Prepartition J) :
    (π.bUnionPrepartition πi).distortion = π.boxes.sup fun J => (πi J).distortion :=
  sup_bunionᵢ _ _
#align box_integral.tagged_prepartition.distortion_bUnion_prepartition BoxIntegral.TaggedPrepartition.distortion_bUnionPrepartition

@[simp]
theorem distortion_disjUnion (h : Disjoint π₁.unionᵢ π₂.unionᵢ) :
    (π₁.disjUnion π₂ h).distortion = max π₁.distortion π₂.distortion :=
  sup_union
#align box_integral.tagged_prepartition.distortion_disj_union BoxIntegral.TaggedPrepartition.distortion_disjUnion

theorem distortion_of_const {c} (h₁ : π.boxes.Nonempty) (h₂ : ∀ J ∈ π, Box.distortion J = c) :
    π.distortion = c :=
  (sup_congr rfl h₂).trans (sup_const h₁ _)
#align box_integral.tagged_prepartition.distortion_of_const BoxIntegral.TaggedPrepartition.distortion_of_const

@[simp]
theorem distortion_single (hJ : J ≤ I) (h : x ∈ I.Icc) :
    distortion (single I J hJ x h) = J.distortion :=
  sup_singleton
#align box_integral.tagged_prepartition.distortion_single BoxIntegral.TaggedPrepartition.distortion_single

theorem distortion_filter_le (p : Box ι → Prop) : (π.filterₓ p).distortion ≤ π.distortion :=
  sup_mono (filter_subset _ _)
#align box_integral.tagged_prepartition.distortion_filter_le BoxIntegral.TaggedPrepartition.distortion_filter_le

end Distortion

end TaggedPrepartition

end BoxIntegral

