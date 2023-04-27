/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module analysis.box_integral.partition.tagged
! leanprover-community/mathlib commit 6ca1a09bc9aa75824bf97388c9e3b441fc4ccf3f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Analysis.BoxIntegral.Partition.Basic

/-!
# Tagged partitions

A tagged (pre)partition is a (pre)partition `π` enriched with a tagged point for each box of
`π`. For simplicity we require that the function `BoxIntegral.TaggedPrepartition.tag` is defined
on all boxes `J : Box ι` but use its values only on boxes of the partition. Given
`π : BoxIntegral.TaggedPrepartition I`, we require that each `BoxIntegral.TaggedPrepartition π J`
belongs to `BoxIntegral.Box.Icc I`. If for every `J ∈ π`, `π.tag J` belongs to `J.Icc`, then `π` is
called a *Henstock* partition. We do not include this assumption into the definition of a tagged
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
  tag : Box ι → ι → ℝ
  tag_mem_Icc : ∀ J, tag J ∈ Box.Icc I
#align box_integral.tagged_prepartition BoxIntegral.TaggedPrepartition

namespace TaggedPrepartition

variable {I J J₁ J₂ : Box ι} (π : TaggedPrepartition I) {x : ι → ℝ}

instance : Membership (Box ι) (TaggedPrepartition I) :=
  ⟨fun J π => J ∈ π.boxes⟩

@[simp]
theorem mem_toPrepartition {π : TaggedPrepartition I} : J ∈ π.toPrepartition ↔ J ∈ π := Iff.rfl
#align box_integral.tagged_prepartition.mem_to_prepartition BoxIntegral.TaggedPrepartition.mem_toPrepartition

@[simp]
theorem mem_mk (π : Prepartition I) (f h) : J ∈ mk π f h ↔ J ∈ π := Iff.rfl
#align box_integral.tagged_prepartition.mem_mk BoxIntegral.TaggedPrepartition.mem_mk

/-- Union of all boxes of a tagged prepartition. -/
def unionᵢ : Set (ι → ℝ) :=
  π.toPrepartition.unionᵢ
#align box_integral.tagged_prepartition.Union BoxIntegral.TaggedPrepartition.unionᵢ

theorem unionᵢ_def : π.unionᵢ = ⋃ J ∈ π, ↑J := rfl
#align box_integral.tagged_prepartition.Union_def BoxIntegral.TaggedPrepartition.unionᵢ_def

@[simp]
theorem unionᵢ_mk (π : Prepartition I) (f h) : (mk π f h).unionᵢ = π.unionᵢ := rfl
#align box_integral.tagged_prepartition.Union_mk BoxIntegral.TaggedPrepartition.unionᵢ_mk

@[simp]
theorem unionᵢ_toPrepartition : π.toPrepartition.unionᵢ = π.unionᵢ := rfl
#align box_integral.tagged_prepartition.Union_to_prepartition BoxIntegral.TaggedPrepartition.unionᵢ_toPrepartition

-- Porting note: Previous proof was `:= Set.mem_unionᵢ₂`
@[simp]
theorem mem_unionᵢ : x ∈ π.unionᵢ ↔ ∃ J ∈ π, x ∈ J := by
  convert Set.mem_unionᵢ₂
  rw [Box.mem_coe, mem_toPrepartition, exists_prop]
#align box_integral.tagged_prepartition.mem_Union BoxIntegral.TaggedPrepartition.mem_unionᵢ

theorem subset_unionᵢ (h : J ∈ π) : ↑J ⊆ π.unionᵢ :=
  subset_bunionᵢ_of_mem h
#align box_integral.tagged_prepartition.subset_Union BoxIntegral.TaggedPrepartition.subset_unionᵢ

theorem unionᵢ_subset : π.unionᵢ ⊆ I :=
  unionᵢ₂_subset π.le_of_mem'
#align box_integral.tagged_prepartition.Union_subset BoxIntegral.TaggedPrepartition.unionᵢ_subset

/-- A tagged prepartition is a partition if it covers the whole box. -/
def IsPartition :=
  π.toPrepartition.IsPartition
#align box_integral.tagged_prepartition.is_partition BoxIntegral.TaggedPrepartition.IsPartition

theorem isPartition_iff_unionᵢ_eq : IsPartition π ↔ π.unionᵢ = I :=
  Prepartition.isPartition_iff_unionᵢ_eq
#align box_integral.tagged_prepartition.is_partition_iff_Union_eq BoxIntegral.TaggedPrepartition.isPartition_iff_unionᵢ_eq

/-- The tagged partition made of boxes of `π` that satisfy predicate `p`. -/
@[simps (config := { fullyApplied := false })]
def filter (p : Box ι → Prop) : TaggedPrepartition I :=
  ⟨π.1.filter p, π.2, π.3⟩
#align box_integral.tagged_prepartition.filter BoxIntegral.TaggedPrepartition.filter

@[simp]
theorem mem_filter {p : Box ι → Prop} : J ∈ π.filter p ↔ J ∈ π ∧ p J :=
  Finset.mem_filter
#align box_integral.tagged_prepartition.mem_filter BoxIntegral.TaggedPrepartition.mem_filter

@[simp]
theorem unionᵢ_filter_not (π : TaggedPrepartition I) (p : Box ι → Prop) :
    (π.filter fun J => ¬p J).unionᵢ = π.unionᵢ \ (π.filter p).unionᵢ :=
  π.toPrepartition.unionᵢ_filter_not p
#align box_integral.tagged_prepartition.Union_filter_not BoxIntegral.TaggedPrepartition.unionᵢ_filter_not

end TaggedPrepartition

namespace Prepartition

variable {I J : Box ι}

/-- Given a partition `π` of `I : BoxIntegral.Box ι` and a collection of tagged partitions
`πi J` of all boxes `J ∈ π`, returns the tagged partition of `I` into all the boxes of `πi J`
with tags coming from `(πi J).tag`. -/
def bunionᵢTagged (π : Prepartition I) (πi : ∀ J : Box ι, TaggedPrepartition J) :
    TaggedPrepartition I where
  toPrepartition := π.bunionᵢ fun J => (πi J).toPrepartition
  tag J := (πi (π.bunionᵢIndex (fun J => (πi J).toPrepartition) J)).tag J
  tag_mem_Icc _ := Box.le_iff_Icc.1 (π.bunionᵢIndex_le _ _) ((πi _).tag_mem_Icc _)
#align box_integral.prepartition.bUnion_tagged BoxIntegral.Prepartition.bunionᵢTagged

@[simp]
theorem mem_bunionᵢTagged (π : Prepartition I) {πi : ∀ J, TaggedPrepartition J} :
    J ∈ π.bunionᵢTagged πi ↔ ∃ J' ∈ π, J ∈ πi J' :=
  π.mem_bunionᵢ
#align box_integral.prepartition.mem_bUnion_tagged BoxIntegral.Prepartition.mem_bunionᵢTagged

theorem tag_bunionᵢTagged (π : Prepartition I) {πi : ∀ J, TaggedPrepartition J} (hJ : J ∈ π) {J'}
    (hJ' : J' ∈ πi J) : (π.bunionᵢTagged πi).tag J' = (πi J).tag J' := by
  rw [← π.bunionᵢIndex_of_mem (πi := fun J => (πi J).toPrepartition) hJ hJ']
  rfl
#align box_integral.prepartition.tag_bUnion_tagged BoxIntegral.Prepartition.tag_bunionᵢTagged

@[simp]
theorem unionᵢ_bunionᵢTagged (π : Prepartition I) (πi : ∀ J, TaggedPrepartition J) :
    (π.bunionᵢTagged πi).unionᵢ = ⋃ J ∈ π, (πi J).unionᵢ :=
  unionᵢ_bunionᵢ _ _
#align box_integral.prepartition.Union_bUnion_tagged BoxIntegral.Prepartition.unionᵢ_bunionᵢTagged

theorem forall_bunionᵢTagged (p : (ι → ℝ) → Box ι → Prop) (π : Prepartition I)
    (πi : ∀ J, TaggedPrepartition J) :
    (∀ J ∈ π.bunionᵢTagged πi, p ((π.bunionᵢTagged πi).tag J) J) ↔
      ∀ J ∈ π, ∀ J' ∈ πi J, p ((πi J).tag J') J' := by
  simp only [mem_bunionᵢTagged]
  refine' ⟨fun H J hJ J' hJ' => _, fun H J' ⟨J, hJ, hJ'⟩ => _⟩
  · rw [← π.tag_bunionᵢTagged hJ hJ']
    exact H J' ⟨J, hJ, hJ'⟩
  · rw [π.tag_bunionᵢTagged hJ hJ']
    exact H J hJ J' hJ'
#align box_integral.prepartition.forall_bUnion_tagged BoxIntegral.Prepartition.forall_bunionᵢTagged

theorem IsPartition.bunionᵢTagged {π : Prepartition I} (h : IsPartition π)
    {πi : ∀ J, TaggedPrepartition J} (hi : ∀ J ∈ π, (πi J).IsPartition) :
    (π.bunionᵢTagged πi).IsPartition :=
  h.bunionᵢ hi
#align box_integral.prepartition.is_partition.bUnion_tagged BoxIntegral.Prepartition.IsPartition.bunionᵢTagged

end Prepartition

namespace TaggedPrepartition

variable {I J : Box ι} {π π₁ π₂ : TaggedPrepartition I} {x : ι → ℝ}

/-- Given a tagged partition `π` of `I` and a (not tagged) partition `πi J hJ` of each `J ∈ π`,
returns the tagged partition of `I` into all the boxes of all `πi J hJ`. The tag of a box `J`
is defined to be the `π.tag` of the box of the partition `π` that includes `J`.

Note that usually the result is not a Henstock partition. -/
@[simps (config := { fullyApplied := false }) tag]
def bunionᵢPrepartition (π : TaggedPrepartition I) (πi : ∀ J : Box ι, Prepartition J) :
    TaggedPrepartition I where
  toPrepartition := π.toPrepartition.bunionᵢ πi
  tag J := π.tag (π.toPrepartition.bunionᵢIndex πi J)
  tag_mem_Icc _ := π.tag_mem_Icc _
#align box_integral.tagged_prepartition.bUnion_prepartition BoxIntegral.TaggedPrepartition.bunionᵢPrepartition

theorem IsPartition.bunionᵢPrepartition {π : TaggedPrepartition I} (h : IsPartition π)
    {πi : ∀ J, Prepartition J} (hi : ∀ J ∈ π, (πi J).IsPartition) :
    (π.bunionᵢPrepartition πi).IsPartition :=
  h.bunionᵢ hi
#align box_integral.tagged_prepartition.is_partition.bUnion_prepartition BoxIntegral.TaggedPrepartition.IsPartition.bunionᵢPrepartition

/-- Given two partitions `π₁` and `π₁`, one of them tagged and the other is not, returns the tagged
partition with `toPrepartition = π₁.toPrepartition ⊓ π₂` and tags coming from `π₁`.

Note that usually the result is not a Henstock partition. -/
def infPrepartition (π : TaggedPrepartition I) (π' : Prepartition I) : TaggedPrepartition I :=
  π.bunionᵢPrepartition fun J => π'.restrict J
#align box_integral.tagged_prepartition.inf_prepartition BoxIntegral.TaggedPrepartition.infPrepartition

@[simp]
theorem infPrepartition_toPrepartition (π : TaggedPrepartition I) (π' : Prepartition I) :
    (π.infPrepartition π').toPrepartition = π.toPrepartition ⊓ π' := rfl
#align box_integral.tagged_prepartition.inf_prepartition_to_prepartition BoxIntegral.TaggedPrepartition.infPrepartition_toPrepartition

theorem mem_infPrepartition_comm :
    J ∈ π₁.infPrepartition π₂.toPrepartition ↔ J ∈ π₂.infPrepartition π₁.toPrepartition := by
  simp only [← mem_toPrepartition, infPrepartition_toPrepartition, inf_comm]
#align box_integral.tagged_prepartition.mem_inf_prepartition_comm BoxIntegral.TaggedPrepartition.mem_infPrepartition_comm

theorem IsPartition.infPrepartition (h₁ : π₁.IsPartition) {π₂ : Prepartition I}
    (h₂ : π₂.IsPartition) : (π₁.infPrepartition π₂).IsPartition :=
  h₁.inf h₂
#align box_integral.tagged_prepartition.is_partition.inf_prepartition BoxIntegral.TaggedPrepartition.IsPartition.infPrepartition

open Metric

/-- A tagged partition is said to be a Henstock partition if for each `J ∈ π`, the tag of `J`
belongs to `J.Icc`. -/
def IsHenstock (π : TaggedPrepartition I) : Prop :=
  ∀ J ∈ π, π.tag J ∈ Box.Icc J
set_option linter.uppercaseLean3 false in
#align box_integral.tagged_prepartition.is_Henstock BoxIntegral.TaggedPrepartition.IsHenstock

@[simp]
theorem isHenstock_bunionᵢTagged {π : Prepartition I} {πi : ∀ J, TaggedPrepartition J} :
    IsHenstock (π.bunionᵢTagged πi) ↔ ∀ J ∈ π, (πi J).IsHenstock :=
  π.forall_bunionᵢTagged (fun x J => x ∈ Box.Icc J) πi
set_option linter.uppercaseLean3 false in
#align box_integral.tagged_prepartition.is_Henstock_bUnion_tagged BoxIntegral.TaggedPrepartition.isHenstock_bunionᵢTagged

/-- In a Henstock prepartition, there are at most `2 ^ Fintype.card ι` boxes with a given tag. -/
theorem IsHenstock.card_filter_tag_eq_le [Fintype ι] (h : π.IsHenstock) (x : ι → ℝ) :
    (π.boxes.filter fun J => π.tag J = x).card ≤ 2 ^ Fintype.card ι :=
  calc
    (π.boxes.filter fun J => π.tag J = x).card ≤
        (π.boxes.filter fun J : Box ι => x ∈ Box.Icc J).card := by
      refine' Finset.card_le_of_subset fun J hJ => _
      rw [Finset.mem_filter] at hJ⊢; rcases hJ with ⟨hJ, rfl⟩
      exact ⟨hJ, h J hJ⟩
    _ ≤ 2 ^ Fintype.card ι := π.toPrepartition.card_filter_mem_Icc_le x
set_option linter.uppercaseLean3 false in
#align box_integral.tagged_prepartition.is_Henstock.card_filter_tag_eq_le BoxIntegral.TaggedPrepartition.IsHenstock.card_filter_tag_eq_le

/-- A tagged partition `π` is subordinate to `r : (ι → ℝ) → ℝ` if each box `J ∈ π` is included in
the closed ball with center `π.tag J` and radius `r (π.tag J)`. -/
def IsSubordinate [Fintype ι] (π : TaggedPrepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) : Prop :=
  ∀ J ∈ π, Box.Icc J ⊆ closedBall (π.tag J) (r <| π.tag J)
#align box_integral.tagged_prepartition.is_subordinate BoxIntegral.TaggedPrepartition.IsSubordinate

variable {r r₁ r₂ : (ι → ℝ) → Ioi (0 : ℝ)}

@[simp]
theorem isSubordinate_bunionᵢTagged [Fintype ι] {π : Prepartition I}
    {πi : ∀ J, TaggedPrepartition J} :
    IsSubordinate (π.bunionᵢTagged πi) r ↔ ∀ J ∈ π, (πi J).IsSubordinate r :=
  π.forall_bunionᵢTagged (fun x J => Box.Icc J ⊆ closedBall x (r x)) πi
#align box_integral.tagged_prepartition.is_subordinate_bUnion_tagged BoxIntegral.TaggedPrepartition.isSubordinate_bunionᵢTagged

theorem IsSubordinate.bunionᵢPrepartition [Fintype ι] (h : IsSubordinate π r)
    (πi : ∀ J, Prepartition J) : IsSubordinate (π.bunionᵢPrepartition πi) r :=
  fun _ hJ => Subset.trans (Box.le_iff_Icc.1 <| π.toPrepartition.le_bunionᵢIndex hJ) <|
    h _ <| π.toPrepartition.bunionᵢIndex_mem hJ
#align box_integral.tagged_prepartition.is_subordinate.bUnion_prepartition BoxIntegral.TaggedPrepartition.IsSubordinate.bunionᵢPrepartition

theorem IsSubordinate.infPrepartition [Fintype ι] (h : IsSubordinate π r) (π' : Prepartition I) :
    IsSubordinate (π.infPrepartition π') r :=
  h.bunionᵢPrepartition _
#align box_integral.tagged_prepartition.is_subordinate.inf_prepartition BoxIntegral.TaggedPrepartition.IsSubordinate.infPrepartition

theorem IsSubordinate.mono' [Fintype ι] {π : TaggedPrepartition I} (hr₁ : π.IsSubordinate r₁)
    (h : ∀ J ∈ π, r₁ (π.tag J) ≤ r₂ (π.tag J)) : π.IsSubordinate r₂ :=
  fun _ hJ _ hx => closedBall_subset_closedBall (h _ hJ) (hr₁ _ hJ hx)
#align box_integral.tagged_prepartition.is_subordinate.mono' BoxIntegral.TaggedPrepartition.IsSubordinate.mono'

theorem IsSubordinate.mono [Fintype ι] {π : TaggedPrepartition I} (hr₁ : π.IsSubordinate r₁)
    (h : ∀ x ∈ Box.Icc I, r₁ x ≤ r₂ x) : π.IsSubordinate r₂ :=
  hr₁.mono' fun J _ => h _ <| π.tag_mem_Icc J
#align box_integral.tagged_prepartition.is_subordinate.mono BoxIntegral.TaggedPrepartition.IsSubordinate.mono

theorem IsSubordinate.diam_le [Fintype ι] {π : TaggedPrepartition I} (h : π.IsSubordinate r)
    (hJ : J ∈ π.boxes) : diam (Box.Icc J) ≤ 2 * r (π.tag J) :=
  calc
    diam (Box.Icc J) ≤ diam (closedBall (π.tag J) (r <| π.tag J)) :=
      diam_mono (h J hJ) bounded_closedBall
    _ ≤ 2 * r (π.tag J) := diam_closedBall (le_of_lt (r _).2)
#align box_integral.tagged_prepartition.is_subordinate.diam_le BoxIntegral.TaggedPrepartition.IsSubordinate.diam_le

/-- Tagged prepartition with single box and prescribed tag. -/
@[simps (config := { fullyApplied := false })]
def single (I J : Box ι) (hJ : J ≤ I) (x : ι → ℝ) (h : x ∈ Box.Icc I) : TaggedPrepartition I :=
  ⟨Prepartition.single I J hJ, fun J => x, fun J => h⟩
#align box_integral.tagged_prepartition.single BoxIntegral.TaggedPrepartition.single

@[simp]
theorem mem_single {J'} (hJ : J ≤ I) (h : x ∈ Box.Icc I) : J' ∈ single I J hJ x h ↔ J' = J :=
  Finset.mem_singleton
#align box_integral.tagged_prepartition.mem_single BoxIntegral.TaggedPrepartition.mem_single

instance (I : Box ι) : Inhabited (TaggedPrepartition I) :=
  ⟨single I I le_rfl I.upper I.upper_mem_Icc⟩

theorem isPartition_single_iff (hJ : J ≤ I) (h : x ∈ Box.Icc I) :
    (single I J hJ x h).IsPartition ↔ J = I :=
  Prepartition.isPartition_single_iff hJ
#align box_integral.tagged_prepartition.is_partition_single_iff BoxIntegral.TaggedPrepartition.isPartition_single_iff

theorem isPartition_single (h : x ∈ Box.Icc I) : (single I I le_rfl x h).IsPartition :=
  Prepartition.isPartitionTop I
#align box_integral.tagged_prepartition.is_partition_single BoxIntegral.TaggedPrepartition.isPartition_single

theorem forall_mem_single (p : (ι → ℝ) → Box ι → Prop) (hJ : J ≤ I) (h : x ∈ Box.Icc I) :
    (∀ J' ∈ single I J hJ x h, p ((single I J hJ x h).tag J') J') ↔ p x J := by simp
#align box_integral.tagged_prepartition.forall_mem_single BoxIntegral.TaggedPrepartition.forall_mem_single

@[simp]
theorem isHenstock_single_iff (hJ : J ≤ I) (h : x ∈ Box.Icc I) :
    IsHenstock (single I J hJ x h) ↔ x ∈ Box.Icc J :=
  forall_mem_single (fun x J => x ∈ Box.Icc J) hJ h
set_option linter.uppercaseLean3 false in
#align box_integral.tagged_prepartition.is_Henstock_single_iff BoxIntegral.TaggedPrepartition.isHenstock_single_iff

@[simp]
theorem isHenstock_single (h : x ∈ Box.Icc I) : IsHenstock (single I I le_rfl x h) :=
  (isHenstock_single_iff (le_refl I) h).2 h
set_option linter.uppercaseLean3 false in
#align box_integral.tagged_prepartition.is_Henstock_single BoxIntegral.TaggedPrepartition.isHenstock_single

@[simp]
theorem isSubordinate_single [Fintype ι] (hJ : J ≤ I) (h : x ∈ Box.Icc I) :
    IsSubordinate (single I J hJ x h) r ↔ Box.Icc J ⊆ closedBall x (r x) :=
  forall_mem_single (fun x J => Box.Icc J ⊆ closedBall x (r x)) hJ h
#align box_integral.tagged_prepartition.is_subordinate_single BoxIntegral.TaggedPrepartition.isSubordinate_single

@[simp]
theorem unionᵢ_single (hJ : J ≤ I) (h : x ∈ Box.Icc I) : (single I J hJ x h).unionᵢ = J :=
  Prepartition.unionᵢ_single hJ
#align box_integral.tagged_prepartition.Union_single BoxIntegral.TaggedPrepartition.unionᵢ_single

/-- Union of two tagged prepartitions with disjoint unions of boxes. -/
def disjUnion (π₁ π₂ : TaggedPrepartition I) (h : Disjoint π₁.unionᵢ π₂.unionᵢ) :
    TaggedPrepartition I where
  toPrepartition := π₁.toPrepartition.disjUnion π₂.toPrepartition h
  tag := π₁.boxes.piecewise π₁.tag π₂.tag
  tag_mem_Icc J := by
    dsimp only [Finset.piecewise]
    split_ifs
    exacts[π₁.tag_mem_Icc J, π₂.tag_mem_Icc J]
#align box_integral.tagged_prepartition.disj_union BoxIntegral.TaggedPrepartition.disjUnion

@[simp]
theorem disjUnion_boxes (h : Disjoint π₁.unionᵢ π₂.unionᵢ) :
    (π₁.disjUnion π₂ h).boxes = π₁.boxes ∪ π₂.boxes := rfl
#align box_integral.tagged_prepartition.disj_union_boxes BoxIntegral.TaggedPrepartition.disjUnion_boxes

@[simp]
theorem mem_disjUnion (h : Disjoint π₁.unionᵢ π₂.unionᵢ) :
    J ∈ π₁.disjUnion π₂ h ↔ J ∈ π₁ ∨ J ∈ π₂ :=
  Finset.mem_union
#align box_integral.tagged_prepartition.mem_disj_union BoxIntegral.TaggedPrepartition.mem_disjUnion

@[simp]
theorem unionᵢ_disjUnion (h : Disjoint π₁.unionᵢ π₂.unionᵢ) :
    (π₁.disjUnion π₂ h).unionᵢ = π₁.unionᵢ ∪ π₂.unionᵢ :=
  Prepartition.unionᵢ_disjUnion h
#align box_integral.tagged_prepartition.Union_disj_union BoxIntegral.TaggedPrepartition.unionᵢ_disjUnion

theorem disjUnion_tag_of_mem_left (h : Disjoint π₁.unionᵢ π₂.unionᵢ) (hJ : J ∈ π₁) :
    (π₁.disjUnion π₂ h).tag J = π₁.tag J :=
  dif_pos hJ
#align box_integral.tagged_prepartition.disj_union_tag_of_mem_left BoxIntegral.TaggedPrepartition.disjUnion_tag_of_mem_left

theorem disjUnion_tag_of_mem_right (h : Disjoint π₁.unionᵢ π₂.unionᵢ) (hJ : J ∈ π₂) :
    (π₁.disjUnion π₂ h).tag J = π₂.tag J :=
  dif_neg fun h₁ => h.le_bot ⟨π₁.subset_unionᵢ h₁ J.upper_mem, π₂.subset_unionᵢ hJ J.upper_mem⟩
#align box_integral.tagged_prepartition.disj_union_tag_of_mem_right BoxIntegral.TaggedPrepartition.disjUnion_tag_of_mem_right

theorem IsSubordinate.disjUnion [Fintype ι] (h₁ : IsSubordinate π₁ r) (h₂ : IsSubordinate π₂ r)
    (h : Disjoint π₁.unionᵢ π₂.unionᵢ) : IsSubordinate (π₁.disjUnion π₂ h) r := by
  refine' fun J hJ => (Finset.mem_union.1 hJ).elim (fun hJ => _) fun hJ => _
  · rw [disjUnion_tag_of_mem_left _ hJ]
    exact h₁ _ hJ
  · rw [disjUnion_tag_of_mem_right _ hJ]
    exact h₂ _ hJ
#align box_integral.tagged_prepartition.is_subordinate.disj_union BoxIntegral.TaggedPrepartition.IsSubordinate.disjUnion

theorem IsHenstock.disjUnion (h₁ : IsHenstock π₁) (h₂ : IsHenstock π₂)
    (h : Disjoint π₁.unionᵢ π₂.unionᵢ) : IsHenstock (π₁.disjUnion π₂ h) := by
  refine' fun J hJ => (Finset.mem_union.1 hJ).elim (fun hJ => _) fun hJ => _
  · rw [disjUnion_tag_of_mem_left _ hJ]
    exact h₁ _ hJ
  · rw [disjUnion_tag_of_mem_right _ hJ]
    exact h₂ _ hJ
set_option linter.uppercaseLean3 false in
#align box_integral.tagged_prepartition.is_Henstock.disj_union BoxIntegral.TaggedPrepartition.IsHenstock.disjUnion

/-- If `I ≤ J`, then every tagged prepartition of `I` is a tagged prepartition of `J`. -/
def embedBox (I J : Box ι) (h : I ≤ J) : TaggedPrepartition I ↪ TaggedPrepartition J where
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
theorem _root_.BoxIntegral.Prepartition.distortion_bunionᵢTagged (π : Prepartition I)
    (πi : ∀ J, TaggedPrepartition J) :
    (π.bunionᵢTagged πi).distortion = π.boxes.sup fun J => (πi J).distortion :=
  sup_bunionᵢ _ _
#align box_integral.prepartition.distortion_bUnion_tagged BoxIntegral.Prepartition.distortion_bunionᵢTagged

@[simp]
theorem distortion_bunionᵢPrepartition (π : TaggedPrepartition I) (πi : ∀ J, Prepartition J) :
    (π.bunionᵢPrepartition πi).distortion = π.boxes.sup fun J => (πi J).distortion :=
  sup_bunionᵢ _ _
#align box_integral.tagged_prepartition.distortion_bUnion_prepartition BoxIntegral.TaggedPrepartition.distortion_bunionᵢPrepartition

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
theorem distortion_single (hJ : J ≤ I) (h : x ∈ Box.Icc I) :
    distortion (single I J hJ x h) = J.distortion :=
  sup_singleton
#align box_integral.tagged_prepartition.distortion_single BoxIntegral.TaggedPrepartition.distortion_single

theorem distortion_filter_le (p : Box ι → Prop) : (π.filter p).distortion ≤ π.distortion :=
  sup_mono (filter_subset _ _)
#align box_integral.tagged_prepartition.distortion_filter_le BoxIntegral.TaggedPrepartition.distortion_filter_le

end Distortion

end TaggedPrepartition

end BoxIntegral
