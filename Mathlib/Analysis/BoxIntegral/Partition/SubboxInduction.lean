/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module analysis.box_integral.partition.subbox_induction
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.BoxIntegral.Box.SubboxInduction
import Mathbin.Analysis.BoxIntegral.Partition.Tagged

/-!
# Induction on subboxes

In this file we prove (see
`box_integral.tagged_partition.exists_is_Henstock_is_subordinate_homothetic`) that for every box `I`
in `ℝⁿ` and a function `r : ℝⁿ → ℝ` positive on `I` there exists a tagged partition `π` of `I` such
that

* `π` is a Henstock partition;
* `π` is subordinate to `r`;
* each box in `π` is homothetic to `I` with coefficient of the form `1 / 2 ^ n`.

Later we will use this lemma to prove that the Henstock filter is nontrivial, hence the Henstock
integral is well-defined.

## Tags

partition, tagged partition, Henstock integral
-/


namespace BoxIntegral

open Set Metric

open Classical Topology

noncomputable section

variable {ι : Type _} [Fintype ι] {I J : Box ι}

namespace Prepartition

/-- Split a box in `ℝⁿ` into `2 ^ n` boxes by hyperplanes passing through its center. -/
def splitCenter (I : Box ι) : Prepartition I
    where
  boxes := Finset.univ.map (Box.splitCenterBoxEmb I)
  le_of_mem' := by simp [I.split_center_box_le]
  PairwiseDisjoint := by
    rw [Finset.coe_map, Finset.coe_univ, image_univ]
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ Hne
    exact I.disjoint_split_center_box (mt (congr_arg _) Hne)
#align box_integral.prepartition.split_center BoxIntegral.Prepartition.splitCenter

@[simp]
theorem mem_splitCenter : J ∈ splitCenter I ↔ ∃ s, I.splitCenterBox s = J := by simp [split_center]
#align box_integral.prepartition.mem_split_center BoxIntegral.Prepartition.mem_splitCenter

theorem isPartition_splitCenter (I : Box ι) : IsPartition (splitCenter I) := fun x hx => by
  simp [hx]
#align box_integral.prepartition.is_partition_split_center BoxIntegral.Prepartition.isPartition_splitCenter

theorem upper_sub_lower_of_mem_splitCenter (h : J ∈ splitCenter I) (i : ι) :
    J.upper i - J.lower i = (I.upper i - I.lower i) / 2 :=
  let ⟨s, hs⟩ := mem_splitCenter.1 h
  hs ▸ I.upper_sub_lower_splitCenterBox s i
#align box_integral.prepartition.upper_sub_lower_of_mem_split_center BoxIntegral.Prepartition.upper_sub_lower_of_mem_splitCenter

end Prepartition

namespace Box

open Prepartition TaggedPrepartition

/-- Let `p` be a predicate on `box ι`, let `I` be a box. Suppose that the following two properties
hold true.

* Consider a smaller box `J ≤ I`. The hyperplanes passing through the center of `J` split it into
  `2 ^ n` boxes. If `p` holds true on each of these boxes, then it true on `J`.
* For each `z` in the closed box `I.Icc` there exists a neighborhood `U` of `z` within `I.Icc` such
  that for every box `J ≤ I` such that `z ∈ J.Icc ⊆ U`, if `J` is homothetic to `I` with a
  coefficient of the form `1 / 2 ^ m`, then `p` is true on `J`.

Then `p I` is true. See also `box_integral.box.subbox_induction_on'` for a version using
`box_integral.box.split_center_box` instead of `box_integral.prepartition.split_center`. -/
@[elab_as_elim]
theorem subbox_induction_on {p : Box ι → Prop} (I : Box ι)
    (H_ind : ∀ J ≤ I, (∀ J' ∈ splitCenter J, p J') → p J)
    (H_nhds :
      ∀ z ∈ I.Icc,
        ∃ U ∈ 𝓝[I.Icc] z,
          ∀ J ≤ I,
            ∀ (m : ℕ),
              z ∈ J.Icc →
                J.Icc ⊆ U → (∀ i, J.upper i - J.lower i = (I.upper i - I.lower i) / 2 ^ m) → p J) :
    p I :=
  by
  refine' subbox_induction_on' I (fun J hle hs => H_ind J hle fun J' h' => _) H_nhds
  rcases mem_split_center.1 h' with ⟨s, rfl⟩
  exact hs s
#align box_integral.box.subbox_induction_on BoxIntegral.Box.subbox_induction_on

/-- Given a box `I` in `ℝⁿ` and a function `r : ℝⁿ → (0, ∞)`, there exists a tagged partition `π` of
`I` such that

* `π` is a Henstock partition;
* `π` is subordinate to `r`;
* each box in `π` is homothetic to `I` with coefficient of the form `1 / 2 ^ m`.

This lemma implies that the Henstock filter is nontrivial, hence the Henstock integral is
well-defined. -/
theorem exists_tagged_partition_isHenstock_isSubordinate_homothetic (I : Box ι)
    (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    ∃ π : TaggedPrepartition I,
      π.IsPartition ∧
        π.IsHenstock ∧
          π.IsSubordinate r ∧
            (∀ J ∈ π, ∃ m : ℕ, ∀ i, (J : _).upper i - J.lower i = (I.upper i - I.lower i) / 2 ^ m) ∧
              π.distortion = I.distortion :=
  by
  refine' subbox_induction_on I (fun J hle hJ => _) fun z hz => _
  · choose! πi hP hHen hr Hn Hd using hJ
    choose! n hn using Hn
    have hP : ((split_center J).biUnionTagged πi).IsPartition :=
      (is_partition_split_center _).biUnionTagged hP
    have hsub :
      ∀ J' ∈ (split_center J).biUnionTagged πi,
        ∃ n : ℕ, ∀ i, (J' : _).upper i - J'.lower i = (J.upper i - J.lower i) / 2 ^ n :=
      by
      intro J' hJ'
      rcases(split_center J).mem_biUnionTagged.1 hJ' with ⟨J₁, h₁, h₂⟩
      refine' ⟨n J₁ J' + 1, fun i => _⟩
      simp only [hn J₁ h₁ J' h₂, upper_sub_lower_of_mem_split_center h₁, pow_succ, div_div]
    refine' ⟨_, hP, is_Henstock_bUnion_tagged.2 hHen, is_subordinate_bUnion_tagged.2 hr, hsub, _⟩
    refine' tagged_prepartition.distortion_of_const _ hP.nonempty_boxes fun J' h' => _
    rcases hsub J' h' with ⟨n, hn⟩
    exact box.distortion_eq_of_sub_eq_div hn
  · refine'
      ⟨I.Icc ∩ closed_ball z (r z), inter_mem_nhdsWithin _ (closed_ball_mem_nhds _ (r z).coe_prop),
        _⟩
    intro J Hle n Hmem HIcc Hsub
    rw [Set.subset_inter_iff] at HIcc
    refine'
      ⟨single _ _ le_rfl _ Hmem, is_partition_single _, is_Henstock_single _,
        (is_subordinate_single _ _).2 HIcc.2, _, distortion_single _ _⟩
    simp only [tagged_prepartition.mem_single, forall_eq]
    refine' ⟨0, fun i => _⟩
    simp
#align box_integral.box.exists_tagged_partition_is_Henstock_is_subordinate_homothetic BoxIntegral.Box.exists_tagged_partition_isHenstock_isSubordinate_homothetic

end Box

namespace Prepartition

open TaggedPrepartition Finset Function

/-- Given a box `I` in `ℝⁿ`, a function `r : ℝⁿ → (0, ∞)`, and a prepartition `π` of `I`, there
exists a tagged prepartition `π'` of `I` such that

* each box of `π'` is included in some box of `π`;
* `π'` is a Henstock partition;
* `π'` is subordinate to `r`;
* `π'` covers exactly the same part of `I` as `π`;
* the distortion of `π'` is equal to the distortion of `π`.
-/
theorem exists_tagged_le_isHenstock_isSubordinate_iUnion_eq {I : Box ι} (r : (ι → ℝ) → Ioi (0 : ℝ))
    (π : Prepartition I) :
    ∃ π' : TaggedPrepartition I,
      π'.toPrepartition ≤ π ∧
        π'.IsHenstock ∧ π'.IsSubordinate r ∧ π'.distortion = π.distortion ∧ π'.iUnion = π.iUnion :=
  by
  have := fun J => box.exists_tagged_partition_is_Henstock_is_subordinate_homothetic J r
  choose! πi πip πiH πir hsub πid; clear hsub
  refine'
    ⟨π.bUnion_tagged πi, bUnion_le _ _, is_Henstock_bUnion_tagged.2 fun J _ => πiH J,
      is_subordinate_bUnion_tagged.2 fun J _ => πir J, _, π.Union_bUnion_partition fun J _ => πip J⟩
  rw [distortion_bUnion_tagged]
  exact sup_congr rfl fun J _ => πid J
#align box_integral.prepartition.exists_tagged_le_is_Henstock_is_subordinate_Union_eq BoxIntegral.Prepartition.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq

/-- Given a prepartition `π` of a box `I` and a function `r : ℝⁿ → (0, ∞)`, `π.to_subordinate r`
is a tagged partition `π'` such that

* each box of `π'` is included in some box of `π`;
* `π'` is a Henstock partition;
* `π'` is subordinate to `r`;
* `π'` covers exactly the same part of `I` as `π`;
* the distortion of `π'` is equal to the distortion of `π`.
-/
def toSubordinate (π : Prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) : TaggedPrepartition I :=
  (π.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r).some
#align box_integral.prepartition.to_subordinate BoxIntegral.Prepartition.toSubordinate

theorem toSubordinate_toPrepartition_le (π : Prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π.toSubordinate r).toPrepartition ≤ π :=
  (π.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r).choose_spec.1
#align box_integral.prepartition.to_subordinate_to_prepartition_le BoxIntegral.Prepartition.toSubordinate_toPrepartition_le

theorem isHenstock_toSubordinate (π : Prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π.toSubordinate r).IsHenstock :=
  (π.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r).choose_spec.2.1
#align box_integral.prepartition.is_Henstock_to_subordinate BoxIntegral.Prepartition.isHenstock_toSubordinate

theorem isSubordinate_toSubordinate (π : Prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π.toSubordinate r).IsSubordinate r :=
  (π.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r).choose_spec.2.2.1
#align box_integral.prepartition.is_subordinate_to_subordinate BoxIntegral.Prepartition.isSubordinate_toSubordinate

@[simp]
theorem distortion_toSubordinate (π : Prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π.toSubordinate r).distortion = π.distortion :=
  (π.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r).choose_spec.2.2.2.1
#align box_integral.prepartition.distortion_to_subordinate BoxIntegral.Prepartition.distortion_toSubordinate

@[simp]
theorem iUnion_toSubordinate (π : Prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π.toSubordinate r).iUnion = π.iUnion :=
  (π.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r).choose_spec.2.2.2.2
#align box_integral.prepartition.Union_to_subordinate BoxIntegral.Prepartition.iUnion_toSubordinate

end Prepartition

namespace TaggedPrepartition

/-- Given a tagged prepartition `π₁`, a prepartition `π₂` that covers exactly `I \ π₁.Union`, and
a function `r : ℝⁿ → (0, ∞)`, returns the union of `π₁` and `π₂.to_subordinate r`. This partition
`π` has the following properties:

* `π` is a partition, i.e. it covers the whole `I`;
* `π₁.boxes ⊆ π.boxes`;
* `π.tag J = π₁.tag J` whenever `J ∈ π₁`;
* `π` is Henstock outside of `π₁`: `π.tag J ∈ J.Icc` whenever `J ∈ π`, `J ∉ π₁`;
* `π` is subordinate to `r` outside of `π₁`;
* the distortion of `π` is equal to the maximum of the distortions of `π₁` and `π₂`.
-/
def unionComplToSubordinate (π₁ : TaggedPrepartition I) (π₂ : Prepartition I)
    (hU : π₂.iUnion = I \ π₁.iUnion) (r : (ι → ℝ) → Ioi (0 : ℝ)) : TaggedPrepartition I :=
  π₁.disjUnion (π₂.toSubordinate r)
    (((π₂.iUnion_toSubordinate r).trans hU).symm ▸ disjoint_sdiff_self_right)
#align box_integral.tagged_prepartition.union_compl_to_subordinate BoxIntegral.TaggedPrepartition.unionComplToSubordinate

theorem isPartition_unionComplToSubordinate (π₁ : TaggedPrepartition I) (π₂ : Prepartition I)
    (hU : π₂.iUnion = I \ π₁.iUnion) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    IsPartition (π₁.unionComplToSubordinate π₂ hU r) :=
  Prepartition.isPartitionDisjUnionOfEqDiff ((π₂.iUnion_toSubordinate r).trans hU)
#align box_integral.tagged_prepartition.is_partition_union_compl_to_subordinate BoxIntegral.TaggedPrepartition.isPartition_unionComplToSubordinate

@[simp]
theorem unionComplToSubordinate_boxes (π₁ : TaggedPrepartition I) (π₂ : Prepartition I)
    (hU : π₂.iUnion = I \ π₁.iUnion) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π₁.unionComplToSubordinate π₂ hU r).boxes = π₁.boxes ∪ (π₂.toSubordinate r).boxes :=
  rfl
#align box_integral.tagged_prepartition.union_compl_to_subordinate_boxes BoxIntegral.TaggedPrepartition.unionComplToSubordinate_boxes

@[simp]
theorem iUnion_unionComplToSubordinate_boxes (π₁ : TaggedPrepartition I) (π₂ : Prepartition I)
    (hU : π₂.iUnion = I \ π₁.iUnion) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π₁.unionComplToSubordinate π₂ hU r).iUnion = I :=
  (isPartition_unionComplToSubordinate _ _ _ _).iUnion_eq
#align box_integral.tagged_prepartition.Union_union_compl_to_subordinate_boxes BoxIntegral.TaggedPrepartition.iUnion_unionComplToSubordinate_boxes

@[simp]
theorem distortion_unionComplToSubordinate (π₁ : TaggedPrepartition I) (π₂ : Prepartition I)
    (hU : π₂.iUnion = I \ π₁.iUnion) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π₁.unionComplToSubordinate π₂ hU r).distortion = max π₁.distortion π₂.distortion := by
  simp [union_compl_to_subordinate]
#align box_integral.tagged_prepartition.distortion_union_compl_to_subordinate BoxIntegral.TaggedPrepartition.distortion_unionComplToSubordinate

end TaggedPrepartition

end BoxIntegral

