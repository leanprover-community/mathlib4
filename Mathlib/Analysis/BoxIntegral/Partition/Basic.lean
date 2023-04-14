/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module analysis.box_integral.partition.basic
! leanprover-community/mathlib commit 84dc0bd6619acaea625086d6f53cb35cdd554219
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Option
import Mathbin.Analysis.BoxIntegral.Box.Basic

/-!
# Partitions of rectangular boxes in `ℝⁿ`

In this file we define (pre)partitions of rectangular boxes in `ℝⁿ`.  A partition of a box `I` in
`ℝⁿ` (see `box_integral.prepartition` and `box_integral.prepartition.is_partition`) is a finite set
of pairwise disjoint boxes such that their union is exactly `I`. We use `boxes : finset (box ι)` to
store the set of boxes.

Many lemmas about box integrals deal with pairwise disjoint collections of subboxes, so we define a
structure `box_integral.prepartition (I : box_integral.box ι)` that stores a collection of boxes
such that

* each box `J ∈ boxes` is a subbox of `I`;
* the boxes are pairwise disjoint as sets in `ℝⁿ`.

Then we define a predicate `box_integral.prepartition.is_partition`; `π.is_partition` means that the
boxes of `π` actually cover the whole `I`. We also define some operations on prepartitions:

* `box_integral.partition.bUnion`: split each box of a partition into smaller boxes;
* `box_integral.partition.restrict`: restrict a partition to a smaller box.

We also define a `semilattice_inf` structure on `box_integral.partition I` for all
`I : box_integral.box ι`.

## Tags

rectangular box, partition
-/


open Set Finset Function

open Classical NNReal BigOperators

noncomputable section

namespace BoxIntegral

variable {ι : Type _}

/-- A prepartition of `I : box_integral.box ι` is a finite set of pairwise disjoint subboxes of
`I`. -/
structure Prepartition (I : Box ι) where
  boxes : Finset (Box ι)
  le_of_mem' : ∀ J ∈ boxes, J ≤ I
  PairwiseDisjoint : Set.Pairwise (↑boxes) (Disjoint on (coe : Box ι → Set (ι → ℝ)))
#align box_integral.prepartition BoxIntegral.Prepartition

namespace Prepartition

variable {I J J₁ J₂ : Box ι} (π : Prepartition I) {π₁ π₂ : Prepartition I} {x : ι → ℝ}

instance : Membership (Box ι) (Prepartition I) :=
  ⟨fun J π => J ∈ π.boxes⟩

@[simp]
theorem mem_boxes : J ∈ π.boxes ↔ J ∈ π :=
  Iff.rfl
#align box_integral.prepartition.mem_boxes BoxIntegral.Prepartition.mem_boxes

@[simp]
theorem mem_mk {s h₁ h₂} : J ∈ (mk s h₁ h₂ : Prepartition I) ↔ J ∈ s :=
  Iff.rfl
#align box_integral.prepartition.mem_mk BoxIntegral.Prepartition.mem_mk

theorem disjoint_coe_of_mem (h₁ : J₁ ∈ π) (h₂ : J₂ ∈ π) (h : J₁ ≠ J₂) :
    Disjoint (J₁ : Set (ι → ℝ)) J₂ :=
  π.PairwiseDisjoint h₁ h₂ h
#align box_integral.prepartition.disjoint_coe_of_mem BoxIntegral.Prepartition.disjoint_coe_of_mem

theorem eq_of_mem_of_mem (h₁ : J₁ ∈ π) (h₂ : J₂ ∈ π) (hx₁ : x ∈ J₁) (hx₂ : x ∈ J₂) : J₁ = J₂ :=
  by_contra fun H => (π.disjoint_coe_of_mem h₁ h₂ H).le_bot ⟨hx₁, hx₂⟩
#align box_integral.prepartition.eq_of_mem_of_mem BoxIntegral.Prepartition.eq_of_mem_of_mem

theorem eq_of_le_of_le (h₁ : J₁ ∈ π) (h₂ : J₂ ∈ π) (hle₁ : J ≤ J₁) (hle₂ : J ≤ J₂) : J₁ = J₂ :=
  π.eq_of_mem_of_mem h₁ h₂ (hle₁ J.upper_mem) (hle₂ J.upper_mem)
#align box_integral.prepartition.eq_of_le_of_le BoxIntegral.Prepartition.eq_of_le_of_le

theorem eq_of_le (h₁ : J₁ ∈ π) (h₂ : J₂ ∈ π) (hle : J₁ ≤ J₂) : J₁ = J₂ :=
  π.eq_of_le_of_le h₁ h₂ le_rfl hle
#align box_integral.prepartition.eq_of_le BoxIntegral.Prepartition.eq_of_le

theorem le_of_mem (hJ : J ∈ π) : J ≤ I :=
  π.le_of_mem' J hJ
#align box_integral.prepartition.le_of_mem BoxIntegral.Prepartition.le_of_mem

theorem lower_le_lower (hJ : J ∈ π) : I.lower ≤ J.lower :=
  Box.antitone_lower (π.le_of_mem hJ)
#align box_integral.prepartition.lower_le_lower BoxIntegral.Prepartition.lower_le_lower

theorem upper_le_upper (hJ : J ∈ π) : J.upper ≤ I.upper :=
  Box.monotone_upper (π.le_of_mem hJ)
#align box_integral.prepartition.upper_le_upper BoxIntegral.Prepartition.upper_le_upper

theorem injective_boxes : Function.Injective (boxes : Prepartition I → Finset (Box ι)) :=
  by
  rintro ⟨s₁, h₁, h₁'⟩ ⟨s₂, h₂, h₂'⟩ (rfl : s₁ = s₂)
  rfl
#align box_integral.prepartition.injective_boxes BoxIntegral.Prepartition.injective_boxes

@[ext]
theorem ext (h : ∀ J, J ∈ π₁ ↔ J ∈ π₂) : π₁ = π₂ :=
  injective_boxes <| Finset.ext h
#align box_integral.prepartition.ext BoxIntegral.Prepartition.ext

/-- The singleton prepartition `{J}`, `J ≤ I`. -/
@[simps]
def single (I J : Box ι) (h : J ≤ I) : Prepartition I :=
  ⟨{J}, by simpa, by simp⟩
#align box_integral.prepartition.single BoxIntegral.Prepartition.single

@[simp]
theorem mem_single {J'} (h : J ≤ I) : J' ∈ single I J h ↔ J' = J :=
  mem_singleton
#align box_integral.prepartition.mem_single BoxIntegral.Prepartition.mem_single

/-- We say that `π ≤ π'` if each box of `π` is a subbox of some box of `π'`. -/
instance : LE (Prepartition I) :=
  ⟨fun π π' => ∀ ⦃I⦄, I ∈ π → ∃ I' ∈ π', I ≤ I'⟩

instance : PartialOrder (Prepartition I)
    where
  le := (· ≤ ·)
  le_refl π I hI := ⟨I, hI, le_rfl⟩
  le_trans π₁ π₂ π₃ h₁₂ h₂₃ I₁ hI₁ :=
    let ⟨I₂, hI₂, hI₁₂⟩ := h₁₂ hI₁
    let ⟨I₃, hI₃, hI₂₃⟩ := h₂₃ hI₂
    ⟨I₃, hI₃, hI₁₂.trans hI₂₃⟩
  le_antisymm :=
    by
    suffices : ∀ {π₁ π₂ : prepartition I}, π₁ ≤ π₂ → π₂ ≤ π₁ → π₁.boxes ⊆ π₂.boxes
    exact fun π₁ π₂ h₁ h₂ => injective_boxes (subset.antisymm (this h₁ h₂) (this h₂ h₁))
    intro π₁ π₂ h₁ h₂ J hJ
    rcases h₁ hJ with ⟨J', hJ', hle⟩; rcases h₂ hJ' with ⟨J'', hJ'', hle'⟩
    obtain rfl : J = J''; exact π₁.eq_of_le hJ hJ'' (hle.trans hle')
    obtain rfl : J' = J; exact le_antisymm ‹_› ‹_›
    assumption

instance : OrderTop (Prepartition I)
    where
  top := single I I le_rfl
  le_top π J hJ := ⟨I, by simp, π.le_of_mem hJ⟩

instance : OrderBot (Prepartition I)
    where
  bot := ⟨∅, fun J hJ => False.elim hJ, fun J hJ => False.elim hJ⟩
  bot_le π J hJ := False.elim hJ

instance : Inhabited (Prepartition I) :=
  ⟨⊤⟩

theorem le_def : π₁ ≤ π₂ ↔ ∀ J ∈ π₁, ∃ J' ∈ π₂, J ≤ J' :=
  Iff.rfl
#align box_integral.prepartition.le_def BoxIntegral.Prepartition.le_def

@[simp]
theorem mem_top : J ∈ (⊤ : Prepartition I) ↔ J = I :=
  mem_singleton
#align box_integral.prepartition.mem_top BoxIntegral.Prepartition.mem_top

@[simp]
theorem top_boxes : (⊤ : Prepartition I).boxes = {I} :=
  rfl
#align box_integral.prepartition.top_boxes BoxIntegral.Prepartition.top_boxes

@[simp]
theorem not_mem_bot : J ∉ (⊥ : Prepartition I) :=
  id
#align box_integral.prepartition.not_mem_bot BoxIntegral.Prepartition.not_mem_bot

@[simp]
theorem bot_boxes : (⊥ : Prepartition I).boxes = ∅ :=
  rfl
#align box_integral.prepartition.bot_boxes BoxIntegral.Prepartition.bot_boxes

/-- An auxiliary lemma used to prove that the same point can't belong to more than
`2 ^ fintype.card ι` closed boxes of a prepartition. -/
theorem injOn_setOf_mem_icc_setOf_lower_eq (x : ι → ℝ) :
    InjOn (fun J : Box ι => { i | J.lower i = x i }) { J | J ∈ π ∧ x ∈ J.Icc } :=
  by
  rintro J₁ ⟨h₁, hx₁⟩ J₂ ⟨h₂, hx₂⟩ (H : { i | J₁.lower i = x i } = { i | J₂.lower i = x i })
  suffices ∀ i, (Ioc (J₁.lower i) (J₁.upper i) ∩ Ioc (J₂.lower i) (J₂.upper i)).Nonempty
    by
    choose y hy₁ hy₂
    exact π.eq_of_mem_of_mem h₁ h₂ hy₁ hy₂
  intro i
  simp only [Set.ext_iff, mem_set_of_eq] at H
  cases' (hx₁.1 i).eq_or_lt with hi₁ hi₁
  · have hi₂ : J₂.lower i = x i := (H _).1 hi₁
    have H₁ : x i < J₁.upper i := by simpa only [hi₁] using J₁.lower_lt_upper i
    have H₂ : x i < J₂.upper i := by simpa only [hi₂] using J₂.lower_lt_upper i
    rw [Ioc_inter_Ioc, hi₁, hi₂, sup_idem, Set.nonempty_Ioc]
    exact lt_min H₁ H₂
  · have hi₂ : J₂.lower i < x i := (hx₂.1 i).lt_of_ne (mt (H _).2 hi₁.ne)
    exact ⟨x i, ⟨hi₁, hx₁.2 i⟩, ⟨hi₂, hx₂.2 i⟩⟩
#align box_integral.prepartition.inj_on_set_of_mem_Icc_set_of_lower_eq BoxIntegral.Prepartition.injOn_setOf_mem_icc_setOf_lower_eq

/-- The set of boxes of a prepartition that contain `x` in their closures has cardinality
at most `2 ^ fintype.card ι`. -/
theorem card_filter_mem_icc_le [Fintype ι] (x : ι → ℝ) :
    (π.boxes.filterₓ fun J : Box ι => x ∈ J.Icc).card ≤ 2 ^ Fintype.card ι :=
  by
  rw [← Fintype.card_set]
  refine'
    Finset.card_le_card_of_inj_on (fun J : box ι => { i | J.lower i = x i })
      (fun _ _ => Finset.mem_univ _) _
  simpa only [Finset.mem_filter] using π.inj_on_set_of_mem_Icc_set_of_lower_eq x
#align box_integral.prepartition.card_filter_mem_Icc_le BoxIntegral.Prepartition.card_filter_mem_icc_le

/-- Given a prepartition `π : box_integral.prepartition I`, `π.Union` is the part of `I` covered by
the boxes of `π`. -/
protected def union : Set (ι → ℝ) :=
  ⋃ J ∈ π, ↑J
#align box_integral.prepartition.Union BoxIntegral.Prepartition.union

theorem union_def : π.unionᵢ = ⋃ J ∈ π, ↑J :=
  rfl
#align box_integral.prepartition.Union_def BoxIntegral.Prepartition.union_def

theorem union_def' : π.unionᵢ = ⋃ J ∈ π.boxes, ↑J :=
  rfl
#align box_integral.prepartition.Union_def' BoxIntegral.Prepartition.union_def'

@[simp]
theorem mem_union : x ∈ π.unionᵢ ↔ ∃ J ∈ π, x ∈ J :=
  Set.mem_unionᵢ₂
#align box_integral.prepartition.mem_Union BoxIntegral.Prepartition.mem_union

@[simp]
theorem union_single (h : J ≤ I) : (single I J h).unionᵢ = J := by simp [Union_def]
#align box_integral.prepartition.Union_single BoxIntegral.Prepartition.union_single

@[simp]
theorem union_top : (⊤ : Prepartition I).unionᵢ = I := by simp [prepartition.Union]
#align box_integral.prepartition.Union_top BoxIntegral.Prepartition.union_top

@[simp]
theorem union_eq_empty : π₁.unionᵢ = ∅ ↔ π₁ = ⊥ := by
  simp [← injective_boxes.eq_iff, Finset.ext_iff, prepartition.Union, imp_false]
#align box_integral.prepartition.Union_eq_empty BoxIntegral.Prepartition.union_eq_empty

@[simp]
theorem union_bot : (⊥ : Prepartition I).unionᵢ = ∅ :=
  union_eq_empty.2 rfl
#align box_integral.prepartition.Union_bot BoxIntegral.Prepartition.union_bot

theorem subset_union (h : J ∈ π) : ↑J ⊆ π.unionᵢ :=
  subset_bunionᵢ_of_mem h
#align box_integral.prepartition.subset_Union BoxIntegral.Prepartition.subset_union

theorem union_subset : π.unionᵢ ⊆ I :=
  unionᵢ₂_subset π.le_of_mem'
#align box_integral.prepartition.Union_subset BoxIntegral.Prepartition.union_subset

@[mono]
theorem union_mono (h : π₁ ≤ π₂) : π₁.unionᵢ ⊆ π₂.unionᵢ := fun x hx =>
  let ⟨J₁, hJ₁, hx⟩ := π₁.mem_unionᵢ.1 hx
  let ⟨J₂, hJ₂, hle⟩ := h hJ₁
  π₂.mem_unionᵢ.2 ⟨J₂, hJ₂, hle hx⟩
#align box_integral.prepartition.Union_mono BoxIntegral.Prepartition.union_mono

theorem disjoint_boxes_of_disjoint_union (h : Disjoint π₁.unionᵢ π₂.unionᵢ) :
    Disjoint π₁.boxes π₂.boxes :=
  Finset.disjoint_left.2 fun J h₁ h₂ =>
    Disjoint.le_bot (h.mono (π₁.subset_unionᵢ h₁) (π₂.subset_unionᵢ h₂)) ⟨J.upper_mem, J.upper_mem⟩
#align box_integral.prepartition.disjoint_boxes_of_disjoint_Union BoxIntegral.Prepartition.disjoint_boxes_of_disjoint_union

theorem le_iff_nonempty_imp_le_and_union_subset :
    π₁ ≤ π₂ ↔
      (∀ J ∈ π₁, ∀ J' ∈ π₂, (J ∩ J' : Set (ι → ℝ)).Nonempty → J ≤ J') ∧ π₁.unionᵢ ⊆ π₂.unionᵢ :=
  by
  fconstructor
  · refine' fun H => ⟨fun J hJ J' hJ' Hne => _, Union_mono H⟩
    rcases H hJ with ⟨J'', hJ'', Hle⟩
    rcases Hne with ⟨x, hx, hx'⟩
    rwa [π₂.eq_of_mem_of_mem hJ' hJ'' hx' (Hle hx)]
  · rintro ⟨H, HU⟩ J hJ
    simp only [Set.subset_def, mem_Union] at HU
    rcases HU J.upper ⟨J, hJ, J.upper_mem⟩ with ⟨J₂, hJ₂, hx⟩
    exact ⟨J₂, hJ₂, H _ hJ _ hJ₂ ⟨_, J.upper_mem, hx⟩⟩
#align box_integral.prepartition.le_iff_nonempty_imp_le_and_Union_subset BoxIntegral.Prepartition.le_iff_nonempty_imp_le_and_union_subset

theorem eq_of_boxes_subset_union_superset (h₁ : π₁.boxes ⊆ π₂.boxes) (h₂ : π₂.unionᵢ ⊆ π₁.unionᵢ) :
    π₁ = π₂ :=
  (le_antisymm fun J hJ => ⟨J, h₁ hJ, le_rfl⟩) <|
    le_iff_nonempty_imp_le_and_union_subset.2
      ⟨fun J₁ hJ₁ J₂ hJ₂ Hne =>
        (π₂.eq_of_mem_of_mem hJ₁ (h₁ hJ₂) Hne.choose_spec.1 Hne.choose_spec.2).le, h₂⟩
#align box_integral.prepartition.eq_of_boxes_subset_Union_superset BoxIntegral.Prepartition.eq_of_boxes_subset_union_superset

/-- Given a prepartition `π` of a box `I` and a collection of prepartitions `πi J` of all boxes
`J ∈ π`, returns the prepartition of `I` into the union of the boxes of all `πi J`.

Though we only use the values of `πi` on the boxes of `π`, we require `πi` to be a globally defined
function. -/
@[simps]
def bUnion (πi : ∀ J : Box ι, Prepartition J) : Prepartition I
    where
  boxes := π.boxes.bunionᵢ fun J => (πi J).boxes
  le_of_mem' J hJ :=
    by
    simp only [Finset.mem_bunionᵢ, exists_prop, mem_boxes] at hJ
    rcases hJ with ⟨J', hJ', hJ⟩
    exact ((πi J').le_of_mem hJ).trans (π.le_of_mem hJ')
  PairwiseDisjoint :=
    by
    simp only [Set.Pairwise, Finset.mem_coe, Finset.mem_bunionᵢ]
    rintro J₁' ⟨J₁, hJ₁, hJ₁'⟩ J₂' ⟨J₂, hJ₂, hJ₂'⟩ Hne
    rw [Function.onFun, Set.disjoint_left]
    rintro x hx₁ hx₂; apply Hne
    obtain rfl : J₁ = J₂
    exact π.eq_of_mem_of_mem hJ₁ hJ₂ ((πi J₁).le_of_mem hJ₁' hx₁) ((πi J₂).le_of_mem hJ₂' hx₂)
    exact (πi J₁).eq_of_mem_of_mem hJ₁' hJ₂' hx₁ hx₂
#align box_integral.prepartition.bUnion BoxIntegral.Prepartition.bUnion

variable {πi πi₁ πi₂ : ∀ J : Box ι, Prepartition J}

@[simp]
theorem mem_bUnion : J ∈ π.bunionᵢ πi ↔ ∃ J' ∈ π, J ∈ πi J' := by simp [bUnion]
#align box_integral.prepartition.mem_bUnion BoxIntegral.Prepartition.mem_bUnion

theorem bUnion_le (πi : ∀ J, Prepartition J) : π.bunionᵢ πi ≤ π := fun J hJ =>
  let ⟨J', hJ', hJ⟩ := π.mem_bunionᵢ.1 hJ
  ⟨J', hJ', (πi J').le_of_mem hJ⟩
#align box_integral.prepartition.bUnion_le BoxIntegral.Prepartition.bUnion_le

@[simp]
theorem bUnion_top : (π.bunionᵢ fun _ => ⊤) = π :=
  by
  ext
  simp
#align box_integral.prepartition.bUnion_top BoxIntegral.Prepartition.bUnion_top

@[congr]
theorem bUnion_congr (h : π₁ = π₂) (hi : ∀ J ∈ π₁, πi₁ J = πi₂ J) :
    π₁.bunionᵢ πi₁ = π₂.bunionᵢ πi₂ := by
  subst π₂
  ext J
  simp (config := { contextual := true }) [hi]
#align box_integral.prepartition.bUnion_congr BoxIntegral.Prepartition.bUnion_congr

theorem bUnion_congr_of_le (h : π₁ = π₂) (hi : ∀ J ≤ I, πi₁ J = πi₂ J) :
    π₁.bunionᵢ πi₁ = π₂.bunionᵢ πi₂ :=
  bUnion_congr h fun J hJ => hi J (π₁.le_of_mem hJ)
#align box_integral.prepartition.bUnion_congr_of_le BoxIntegral.Prepartition.bUnion_congr_of_le

@[simp]
theorem union_bUnion (πi : ∀ J : Box ι, Prepartition J) :
    (π.bunionᵢ πi).unionᵢ = ⋃ J ∈ π, (πi J).unionᵢ := by simp [prepartition.Union]
#align box_integral.prepartition.Union_bUnion BoxIntegral.Prepartition.union_bUnion

@[simp]
theorem sum_bunionᵢ_boxes {M : Type _} [AddCommMonoid M] (π : Prepartition I)
    (πi : ∀ J, Prepartition J) (f : Box ι → M) :
    (∑ J in π.boxes.bunionᵢ fun J => (πi J).boxes, f J) =
      ∑ J in π.boxes, ∑ J' in (πi J).boxes, f J' :=
  by
  refine' Finset.sum_bunionᵢ fun J₁ h₁ J₂ h₂ hne => Finset.disjoint_left.2 fun J' h₁' h₂' => _
  exact hne (π.eq_of_le_of_le h₁ h₂ ((πi J₁).le_of_mem h₁') ((πi J₂).le_of_mem h₂'))
#align box_integral.prepartition.sum_bUnion_boxes BoxIntegral.Prepartition.sum_bunionᵢ_boxes

/-- Given a box `J ∈ π.bUnion πi`, returns the box `J' ∈ π` such that `J ∈ πi J'`.
For `J ∉ π.bUnion πi`, returns `I`. -/
def bUnionIndex (πi : ∀ J, Prepartition J) (J : Box ι) : Box ι :=
  if hJ : J ∈ π.bunionᵢ πi then (π.mem_bunionᵢ.1 hJ).some else I
#align box_integral.prepartition.bUnion_index BoxIntegral.Prepartition.bUnionIndex

theorem bUnionIndex_mem (hJ : J ∈ π.bunionᵢ πi) : π.bUnionIndex πi J ∈ π :=
  by
  rw [bUnion_index, dif_pos hJ]
  exact (π.mem_bUnion.1 hJ).choose_spec.fst
#align box_integral.prepartition.bUnion_index_mem BoxIntegral.Prepartition.bUnionIndex_mem

theorem bUnionIndex_le (πi : ∀ J, Prepartition J) (J : Box ι) : π.bUnionIndex πi J ≤ I :=
  by
  by_cases hJ : J ∈ π.bUnion πi
  · exact π.le_of_mem (π.bUnion_index_mem hJ)
  · rw [bUnion_index, dif_neg hJ]
    exact le_rfl
#align box_integral.prepartition.bUnion_index_le BoxIntegral.Prepartition.bUnionIndex_le

theorem mem_bUnionIndex (hJ : J ∈ π.bunionᵢ πi) : J ∈ πi (π.bUnionIndex πi J) := by
  convert(π.mem_bUnion.1 hJ).choose_spec.snd <;> exact dif_pos hJ
#align box_integral.prepartition.mem_bUnion_index BoxIntegral.Prepartition.mem_bUnionIndex

theorem le_bUnionIndex (hJ : J ∈ π.bunionᵢ πi) : J ≤ π.bUnionIndex πi J :=
  le_of_mem _ (π.mem_bUnionIndex hJ)
#align box_integral.prepartition.le_bUnion_index BoxIntegral.Prepartition.le_bUnionIndex

/-- Uniqueness property of `box_integral.partition.bUnion_index`. -/
theorem bUnionIndex_of_mem (hJ : J ∈ π) {J'} (hJ' : J' ∈ πi J) : π.bUnionIndex πi J' = J :=
  have : J' ∈ π.bunionᵢ πi := π.mem_bunionᵢ.2 ⟨J, hJ, hJ'⟩
  π.eq_of_le_of_le (π.bUnionIndex_mem this) hJ (π.le_bUnionIndex this) (le_of_mem _ hJ')
#align box_integral.prepartition.bUnion_index_of_mem BoxIntegral.Prepartition.bUnionIndex_of_mem

theorem bUnion_assoc (πi : ∀ J, Prepartition J) (πi' : Box ι → ∀ J : Box ι, Prepartition J) :
    (π.bunionᵢ fun J => (πi J).bunionᵢ (πi' J)) =
      (π.bunionᵢ πi).bunionᵢ fun J => πi' (π.bUnionIndex πi J) J :=
  by
  ext J
  simp only [mem_bUnion, exists_prop]
  fconstructor
  · rintro ⟨J₁, hJ₁, J₂, hJ₂, hJ⟩
    refine' ⟨J₂, ⟨J₁, hJ₁, hJ₂⟩, _⟩
    rwa [π.bUnion_index_of_mem hJ₁ hJ₂]
  · rintro ⟨J₁, ⟨J₂, hJ₂, hJ₁⟩, hJ⟩
    refine' ⟨J₂, hJ₂, J₁, hJ₁, _⟩
    rwa [π.bUnion_index_of_mem hJ₂ hJ₁] at hJ
#align box_integral.prepartition.bUnion_assoc BoxIntegral.Prepartition.bUnion_assoc

/-- Create a `box_integral.prepartition` from a collection of possibly empty boxes by filtering out
the empty one if it exists. -/
def ofWithBot (boxes : Finset (WithBot (Box ι)))
    (le_of_mem : ∀ J ∈ boxes, (J : WithBot (Box ι)) ≤ I)
    (pairwise_disjoint : Set.Pairwise (boxes : Set (WithBot (Box ι))) Disjoint) : Prepartition I
    where
  boxes := boxes.eraseNone
  le_of_mem' J hJ := by
    rw [mem_erase_none] at hJ
    simpa only [WithBot.some_eq_coe, WithBot.coe_le_coe] using le_of_mem _ hJ
  PairwiseDisjoint J₁ h₁ J₂ h₂ hne :=
    by
    simp only [mem_coe, mem_erase_none] at h₁ h₂
    exact box.disjoint_coe.1 (pairwise_disjoint h₁ h₂ (mt Option.some_inj.1 hne))
#align box_integral.prepartition.of_with_bot BoxIntegral.Prepartition.ofWithBot

@[simp]
theorem mem_ofWithBot {boxes : Finset (WithBot (Box ι))} {h₁ h₂} :
    J ∈ (ofWithBot boxes h₁ h₂ : Prepartition I) ↔ (J : WithBot (Box ι)) ∈ boxes :=
  mem_eraseNone
#align box_integral.prepartition.mem_of_with_bot BoxIntegral.Prepartition.mem_ofWithBot

@[simp]
theorem union_ofWithBot (boxes : Finset (WithBot (Box ι)))
    (le_of_mem : ∀ J ∈ boxes, (J : WithBot (Box ι)) ≤ I)
    (pairwise_disjoint : Set.Pairwise (boxes : Set (WithBot (Box ι))) Disjoint) :
    (ofWithBot boxes le_of_mem pairwise_disjoint).unionᵢ = ⋃ J ∈ boxes, ↑J :=
  by
  suffices (⋃ (J : box ι) (hJ : ↑J ∈ boxes), ↑J) = ⋃ J ∈ boxes, ↑J by
    simpa [of_with_bot, prepartition.Union]
  simp only [← box.bUnion_coe_eq_coe, @Union_comm _ _ (box ι), @Union_comm _ _ (@Eq _ _ _),
    Union_Union_eq_right]
#align box_integral.prepartition.Union_of_with_bot BoxIntegral.Prepartition.union_ofWithBot

theorem ofWithBot_le {boxes : Finset (WithBot (Box ι))}
    {le_of_mem : ∀ J ∈ boxes, (J : WithBot (Box ι)) ≤ I}
    {pairwise_disjoint : Set.Pairwise (boxes : Set (WithBot (Box ι))) Disjoint}
    (H : ∀ J ∈ boxes, J ≠ ⊥ → ∃ J' ∈ π, J ≤ ↑J') :
    ofWithBot boxes le_of_mem pairwise_disjoint ≤ π :=
  by
  have : ∀ J : Box ι, ↑J ∈ boxes → ∃ J' ∈ π, J ≤ J' := fun J hJ => by
    simpa only [WithBot.coe_le_coe] using H J hJ WithBot.coe_ne_bot
  simpa [of_with_bot, le_def]
#align box_integral.prepartition.of_with_bot_le BoxIntegral.Prepartition.ofWithBot_le

theorem le_ofWithBot {boxes : Finset (WithBot (Box ι))}
    {le_of_mem : ∀ J ∈ boxes, (J : WithBot (Box ι)) ≤ I}
    {pairwise_disjoint : Set.Pairwise (boxes : Set (WithBot (Box ι))) Disjoint}
    (H : ∀ J ∈ π, ∃ J' ∈ boxes, ↑J ≤ J') : π ≤ ofWithBot boxes le_of_mem pairwise_disjoint :=
  by
  intro J hJ
  rcases H J hJ with ⟨J', J'mem, hle⟩
  lift J' to box ι using ne_bot_of_le_ne_bot WithBot.coe_ne_bot hle
  exact ⟨J', mem_of_with_bot.2 J'mem, WithBot.coe_le_coe.1 hle⟩
#align box_integral.prepartition.le_of_with_bot BoxIntegral.Prepartition.le_ofWithBot

theorem ofWithBot_mono {boxes₁ : Finset (WithBot (Box ι))}
    {le_of_mem₁ : ∀ J ∈ boxes₁, (J : WithBot (Box ι)) ≤ I}
    {pairwise_disjoint₁ : Set.Pairwise (boxes₁ : Set (WithBot (Box ι))) Disjoint}
    {boxes₂ : Finset (WithBot (Box ι))} {le_of_mem₂ : ∀ J ∈ boxes₂, (J : WithBot (Box ι)) ≤ I}
    {pairwise_disjoint₂ : Set.Pairwise (boxes₂ : Set (WithBot (Box ι))) Disjoint}
    (H : ∀ J ∈ boxes₁, J ≠ ⊥ → ∃ J' ∈ boxes₂, J ≤ J') :
    ofWithBot boxes₁ le_of_mem₁ pairwise_disjoint₁ ≤
      ofWithBot boxes₂ le_of_mem₂ pairwise_disjoint₂ :=
  le_ofWithBot _ fun J hJ => H J (mem_ofWithBot.1 hJ) WithBot.coe_ne_bot
#align box_integral.prepartition.of_with_bot_mono BoxIntegral.Prepartition.ofWithBot_mono

theorem sum_ofWithBot {M : Type _} [AddCommMonoid M] (boxes : Finset (WithBot (Box ι)))
    (le_of_mem : ∀ J ∈ boxes, (J : WithBot (Box ι)) ≤ I)
    (pairwise_disjoint : Set.Pairwise (boxes : Set (WithBot (Box ι))) Disjoint) (f : Box ι → M) :
    (∑ J in (ofWithBot boxes le_of_mem pairwise_disjoint).boxes, f J) =
      ∑ J in boxes, Option.elim' 0 f J :=
  Finset.sum_eraseNone _ _
#align box_integral.prepartition.sum_of_with_bot BoxIntegral.Prepartition.sum_ofWithBot

/-- Restrict a prepartition to a box. -/
def restrict (π : Prepartition I) (J : Box ι) : Prepartition J :=
  ofWithBot (π.boxes.image fun J' => J ⊓ J')
    (fun J' hJ' => by
      rcases Finset.mem_image.1 hJ' with ⟨J', -, rfl⟩
      exact inf_le_left)
    (by
      simp only [Set.Pairwise, on_fun, Finset.mem_coe, Finset.mem_image]
      rintro _ ⟨J₁, h₁, rfl⟩ _ ⟨J₂, h₂, rfl⟩ Hne
      have : J₁ ≠ J₂ := by
        rintro rfl
        exact Hne rfl
      exact ((box.disjoint_coe.2 <| π.disjoint_coe_of_mem h₁ h₂ this).inf_left' _).inf_right' _)
#align box_integral.prepartition.restrict BoxIntegral.Prepartition.restrict

@[simp]
theorem mem_restrict : J₁ ∈ π.restrict J ↔ ∃ J' ∈ π, (J₁ : WithBot (Box ι)) = J ⊓ J' := by
  simp [restrict, eq_comm]
#align box_integral.prepartition.mem_restrict BoxIntegral.Prepartition.mem_restrict

theorem mem_restrict' : J₁ ∈ π.restrict J ↔ ∃ J' ∈ π, (J₁ : Set (ι → ℝ)) = J ∩ J' := by
  simp only [mem_restrict, ← box.with_bot_coe_inj, box.coe_inf, box.coe_coe]
#align box_integral.prepartition.mem_restrict' BoxIntegral.Prepartition.mem_restrict'

@[mono]
theorem restrict_mono {π₁ π₂ : Prepartition I} (Hle : π₁ ≤ π₂) : π₁.restrict J ≤ π₂.restrict J :=
  by
  refine' of_with_bot_mono fun J₁ hJ₁ hne => _
  rw [Finset.mem_image] at hJ₁; rcases hJ₁ with ⟨J₁, hJ₁, rfl⟩
  rcases Hle hJ₁ with ⟨J₂, hJ₂, hle⟩
  exact ⟨_, Finset.mem_image_of_mem _ hJ₂, inf_le_inf_left _ <| WithBot.coe_le_coe.2 hle⟩
#align box_integral.prepartition.restrict_mono BoxIntegral.Prepartition.restrict_mono

theorem monotone_restrict : Monotone fun π : Prepartition I => restrict π J := fun π₁ π₂ =>
  restrict_mono
#align box_integral.prepartition.monotone_restrict BoxIntegral.Prepartition.monotone_restrict

/-- Restricting to a larger box does not change the set of boxes. We cannot claim equality
of prepartitions because they have different types. -/
theorem restrict_boxes_of_le (π : Prepartition I) (h : I ≤ J) : (π.restrict J).boxes = π.boxes :=
  by
  simp only [restrict, of_with_bot, erase_none_eq_bUnion]
  refine' finset.image_bUnion.trans _
  refine' (Finset.bunionᵢ_congr rfl _).trans Finset.bunionᵢ_singleton_eq_self
  intro J' hJ'
  rw [inf_of_le_right, ← WithBot.some_eq_coe, Option.toFinset_some]
  exact WithBot.coe_le_coe.2 ((π.le_of_mem hJ').trans h)
#align box_integral.prepartition.restrict_boxes_of_le BoxIntegral.Prepartition.restrict_boxes_of_le

@[simp]
theorem restrict_self : π.restrict I = π :=
  injective_boxes <| restrict_boxes_of_le π le_rfl
#align box_integral.prepartition.restrict_self BoxIntegral.Prepartition.restrict_self

@[simp]
theorem union_restrict : (π.restrict J).unionᵢ = J ∩ π.unionᵢ := by
  simp [restrict, ← inter_Union, ← Union_def]
#align box_integral.prepartition.Union_restrict BoxIntegral.Prepartition.union_restrict

@[simp]
theorem restrict_bUnion (πi : ∀ J, Prepartition J) (hJ : J ∈ π) :
    (π.bunionᵢ πi).restrict J = πi J :=
  by
  refine' (eq_of_boxes_subset_Union_superset (fun J₁ h₁ => _) _).symm
  · refine' (mem_restrict _).2 ⟨J₁, π.mem_bUnion.2 ⟨J, hJ, h₁⟩, (inf_of_le_right _).symm⟩
    exact WithBot.coe_le_coe.2 (le_of_mem _ h₁)
  · simp only [Union_restrict, Union_bUnion, Set.subset_def, Set.mem_inter_iff, Set.mem_unionᵢ]
    rintro x ⟨hxJ, J₁, h₁, hx⟩
    obtain rfl : J = J₁
    exact π.eq_of_mem_of_mem hJ h₁ hxJ (Union_subset _ hx)
    exact hx
#align box_integral.prepartition.restrict_bUnion BoxIntegral.Prepartition.restrict_bUnion

theorem bUnion_le_iff {πi : ∀ J, Prepartition J} {π' : Prepartition I} :
    π.bunionᵢ πi ≤ π' ↔ ∀ J ∈ π, πi J ≤ π'.restrict J :=
  by
  fconstructor <;> intro H J hJ
  · rw [← π.restrict_bUnion πi hJ]
    exact restrict_mono H
  · rw [mem_bUnion] at hJ
    rcases hJ with ⟨J₁, h₁, hJ⟩
    rcases H J₁ h₁ hJ with ⟨J₂, h₂, Hle⟩
    rcases π'.mem_restrict.mp h₂ with ⟨J₃, h₃, H⟩
    exact ⟨J₃, h₃, Hle.trans <| WithBot.coe_le_coe.1 <| H.trans_le inf_le_right⟩
#align box_integral.prepartition.bUnion_le_iff BoxIntegral.Prepartition.bUnion_le_iff

theorem le_bUnion_iff {πi : ∀ J, Prepartition J} {π' : Prepartition I} :
    π' ≤ π.bunionᵢ πi ↔ π' ≤ π ∧ ∀ J ∈ π, π'.restrict J ≤ πi J :=
  by
  refine' ⟨fun H => ⟨H.trans (π.bUnion_le πi), fun J hJ => _⟩, _⟩
  · rw [← π.restrict_bUnion πi hJ]
    exact restrict_mono H
  · rintro ⟨H, Hi⟩ J' hJ'
    rcases H hJ' with ⟨J, hJ, hle⟩
    have : J' ∈ π'.restrict J :=
      π'.mem_restrict.2 ⟨J', hJ', (inf_of_le_right <| WithBot.coe_le_coe.2 hle).symm⟩
    rcases Hi J hJ this with ⟨Ji, hJi, hlei⟩
    exact ⟨Ji, π.mem_bUnion.2 ⟨J, hJ, hJi⟩, hlei⟩
#align box_integral.prepartition.le_bUnion_iff BoxIntegral.Prepartition.le_bUnion_iff

instance : Inf (Prepartition I) :=
  ⟨fun π₁ π₂ => π₁.bunionᵢ fun J => π₂.restrict J⟩

theorem inf_def (π₁ π₂ : Prepartition I) : π₁ ⊓ π₂ = π₁.bunionᵢ fun J => π₂.restrict J :=
  rfl
#align box_integral.prepartition.inf_def BoxIntegral.Prepartition.inf_def

@[simp]
theorem mem_inf {π₁ π₂ : Prepartition I} :
    J ∈ π₁ ⊓ π₂ ↔ ∃ J₁ ∈ π₁, ∃ J₂ ∈ π₂, (J : WithBot (Box ι)) = J₁ ⊓ J₂ := by
  simp only [inf_def, mem_bUnion, mem_restrict]
#align box_integral.prepartition.mem_inf BoxIntegral.Prepartition.mem_inf

@[simp]
theorem union_inf (π₁ π₂ : Prepartition I) : (π₁ ⊓ π₂).unionᵢ = π₁.unionᵢ ∩ π₂.unionᵢ := by
  simp only [inf_def, Union_bUnion, Union_restrict, ← Union_inter, ← Union_def]
#align box_integral.prepartition.Union_inf BoxIntegral.Prepartition.union_inf

instance : SemilatticeInf (Prepartition I) :=
  { Prepartition.hasInf,
    Prepartition.partialOrder with
    inf_le_left := fun π₁ π₂ => π₁.bUnion_le _
    inf_le_right := fun π₁ π₂ => (bUnion_le_iff _).2 fun J hJ => le_rfl
    le_inf := fun π π₁ π₂ h₁ h₂ => π₁.le_bUnion_iff.2 ⟨h₁, fun J hJ => restrict_mono h₂⟩ }

/-- The prepartition with boxes `{J ∈ π | p J}`. -/
@[simps]
def filter (π : Prepartition I) (p : Box ι → Prop) : Prepartition I
    where
  boxes := π.boxes.filterₓ p
  le_of_mem' J hJ := π.le_of_mem (mem_filter.1 hJ).1
  PairwiseDisjoint J₁ h₁ J₂ h₂ := π.disjoint_coe_of_mem (mem_filter.1 h₁).1 (mem_filter.1 h₂).1
#align box_integral.prepartition.filter BoxIntegral.Prepartition.filter

@[simp]
theorem mem_filter {p : Box ι → Prop} : J ∈ π.filterₓ p ↔ J ∈ π ∧ p J :=
  Finset.mem_filter
#align box_integral.prepartition.mem_filter BoxIntegral.Prepartition.mem_filter

theorem filter_le (π : Prepartition I) (p : Box ι → Prop) : π.filterₓ p ≤ π := fun J hJ =>
  let ⟨hπ, hp⟩ := π.mem_filter.1 hJ
  ⟨J, hπ, le_rfl⟩
#align box_integral.prepartition.filter_le BoxIntegral.Prepartition.filter_le

theorem filter_of_true {p : Box ι → Prop} (hp : ∀ J ∈ π, p J) : π.filterₓ p = π :=
  by
  ext J
  simpa using hp J
#align box_integral.prepartition.filter_of_true BoxIntegral.Prepartition.filter_of_true

@[simp]
theorem filter_true : (π.filterₓ fun _ => True) = π :=
  π.filter_of_true fun _ _ => trivial
#align box_integral.prepartition.filter_true BoxIntegral.Prepartition.filter_true

@[simp]
theorem union_filter_not (π : Prepartition I) (p : Box ι → Prop) :
    (π.filterₓ fun J => ¬p J).unionᵢ = π.unionᵢ \ (π.filterₓ p).unionᵢ :=
  by
  simp only [prepartition.Union]
  convert(@Set.bunionᵢ_diff_bunionᵢ_eq _ (box ι) π.boxes (π.filter p).boxes coe _).symm
  · ext (J x)
    simp (config := { contextual := true })
  · convert π.pairwise_disjoint
    simp
#align box_integral.prepartition.Union_filter_not BoxIntegral.Prepartition.union_filter_not

theorem sum_fiberwise {α M} [AddCommMonoid M] (π : Prepartition I) (f : Box ι → α) (g : Box ι → M) :
    (∑ y in π.boxes.image f, ∑ J in (π.filterₓ fun J => f J = y).boxes, g J) =
      ∑ J in π.boxes, g J :=
  by convert sum_fiberwise_of_maps_to (fun _ => Finset.mem_image_of_mem f) g
#align box_integral.prepartition.sum_fiberwise BoxIntegral.Prepartition.sum_fiberwise

/-- Union of two disjoint prepartitions. -/
@[simps]
def disjUnion (π₁ π₂ : Prepartition I) (h : Disjoint π₁.unionᵢ π₂.unionᵢ) : Prepartition I
    where
  boxes := π₁.boxes ∪ π₂.boxes
  le_of_mem' J hJ := (Finset.mem_union.1 hJ).elim π₁.le_of_mem π₂.le_of_mem
  PairwiseDisjoint :=
    suffices ∀ J₁ ∈ π₁, ∀ J₂ ∈ π₂, J₁ ≠ J₂ → Disjoint (J₁ : Set (ι → ℝ)) J₂ by
      simpa [pairwise_union_of_symmetric (symmetric_disjoint.comap _), pairwise_disjoint]
    fun J₁ h₁ J₂ h₂ _ => h.mono (π₁.subset_unionᵢ h₁) (π₂.subset_unionᵢ h₂)
#align box_integral.prepartition.disj_union BoxIntegral.Prepartition.disjUnion

@[simp]
theorem mem_disjUnion (H : Disjoint π₁.unionᵢ π₂.unionᵢ) :
    J ∈ π₁.disjUnion π₂ H ↔ J ∈ π₁ ∨ J ∈ π₂ :=
  Finset.mem_union
#align box_integral.prepartition.mem_disj_union BoxIntegral.Prepartition.mem_disjUnion

@[simp]
theorem union_disjUnion (h : Disjoint π₁.unionᵢ π₂.unionᵢ) :
    (π₁.disjUnion π₂ h).unionᵢ = π₁.unionᵢ ∪ π₂.unionᵢ := by
  simp [disj_union, prepartition.Union, Union_or, Union_union_distrib]
#align box_integral.prepartition.Union_disj_union BoxIntegral.Prepartition.union_disjUnion

@[simp]
theorem sum_disj_union_boxes {M : Type _} [AddCommMonoid M] (h : Disjoint π₁.unionᵢ π₂.unionᵢ)
    (f : Box ι → M) :
    (∑ J in π₁.boxes ∪ π₂.boxes, f J) = (∑ J in π₁.boxes, f J) + ∑ J in π₂.boxes, f J :=
  sum_union <| disjoint_boxes_of_disjoint_union h
#align box_integral.prepartition.sum_disj_union_boxes BoxIntegral.Prepartition.sum_disj_union_boxes

section Distortion

variable [Fintype ι]

/-- The distortion of a prepartition is the maximum of the distortions of the boxes of this
prepartition. -/
def distortion : ℝ≥0 :=
  π.boxes.sup Box.distortion
#align box_integral.prepartition.distortion BoxIntegral.Prepartition.distortion

theorem distortion_le_of_mem (h : J ∈ π) : J.distortion ≤ π.distortion :=
  le_sup h
#align box_integral.prepartition.distortion_le_of_mem BoxIntegral.Prepartition.distortion_le_of_mem

theorem distortion_le_iff {c : ℝ≥0} : π.distortion ≤ c ↔ ∀ J ∈ π, Box.distortion J ≤ c :=
  Finset.sup_le_iff
#align box_integral.prepartition.distortion_le_iff BoxIntegral.Prepartition.distortion_le_iff

theorem distortion_bUnion (π : Prepartition I) (πi : ∀ J, Prepartition J) :
    (π.bunionᵢ πi).distortion = π.boxes.sup fun J => (πi J).distortion :=
  sup_bunionᵢ _ _
#align box_integral.prepartition.distortion_bUnion BoxIntegral.Prepartition.distortion_bUnion

@[simp]
theorem distortion_disjUnion (h : Disjoint π₁.unionᵢ π₂.unionᵢ) :
    (π₁.disjUnion π₂ h).distortion = max π₁.distortion π₂.distortion :=
  sup_union
#align box_integral.prepartition.distortion_disj_union BoxIntegral.Prepartition.distortion_disjUnion

theorem distortion_of_const {c} (h₁ : π.boxes.Nonempty) (h₂ : ∀ J ∈ π, Box.distortion J = c) :
    π.distortion = c :=
  (sup_congr rfl h₂).trans (sup_const h₁ _)
#align box_integral.prepartition.distortion_of_const BoxIntegral.Prepartition.distortion_of_const

@[simp]
theorem distortion_top (I : Box ι) : distortion (⊤ : Prepartition I) = I.distortion :=
  sup_singleton
#align box_integral.prepartition.distortion_top BoxIntegral.Prepartition.distortion_top

@[simp]
theorem distortion_bot (I : Box ι) : distortion (⊥ : Prepartition I) = 0 :=
  sup_empty
#align box_integral.prepartition.distortion_bot BoxIntegral.Prepartition.distortion_bot

end Distortion

/-- A prepartition `π` of `I` is a partition if the boxes of `π` cover the whole `I`. -/
def IsPartition (π : Prepartition I) :=
  ∀ x ∈ I, ∃ J ∈ π, x ∈ J
#align box_integral.prepartition.is_partition BoxIntegral.Prepartition.IsPartition

theorem isPartition_iff_union_eq {π : Prepartition I} : π.IsPartition ↔ π.unionᵢ = I := by
  simp_rw [is_partition, Set.Subset.antisymm_iff, π.Union_subset, true_and_iff, Set.subset_def,
    mem_Union, box.mem_coe]
#align box_integral.prepartition.is_partition_iff_Union_eq BoxIntegral.Prepartition.isPartition_iff_union_eq

@[simp]
theorem isPartition_single_iff (h : J ≤ I) : IsPartition (single I J h) ↔ J = I := by
  simp [is_partition_iff_Union_eq]
#align box_integral.prepartition.is_partition_single_iff BoxIntegral.Prepartition.isPartition_single_iff

theorem isPartitionTop (I : Box ι) : IsPartition (⊤ : Prepartition I) := fun x hx =>
  ⟨I, mem_top.2 rfl, hx⟩
#align box_integral.prepartition.is_partition_top BoxIntegral.Prepartition.isPartitionTop

namespace IsPartition

variable {π}

theorem union_eq (h : π.IsPartition) : π.unionᵢ = I :=
  isPartition_iff_union_eq.1 h
#align box_integral.prepartition.is_partition.Union_eq BoxIntegral.Prepartition.IsPartition.union_eq

theorem union_subset (h : π.IsPartition) (π₁ : Prepartition I) : π₁.unionᵢ ⊆ π.unionᵢ :=
  h.unionᵢ_eq.symm ▸ π₁.unionᵢ_subset
#align box_integral.prepartition.is_partition.Union_subset BoxIntegral.Prepartition.IsPartition.union_subset

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (J «expr ∈ » π) -/
protected theorem existsUnique (h : π.IsPartition) (hx : x ∈ I) : ∃! (J : _)(_ : J ∈ π), x ∈ J :=
  by
  rcases h x hx with ⟨J, h, hx⟩
  exact ExistsUnique.intro₂ J h hx fun J' h' hx' => π.eq_of_mem_of_mem h' h hx' hx
#align box_integral.prepartition.is_partition.exists_unique BoxIntegral.Prepartition.IsPartition.existsUnique

theorem nonempty_boxes (h : π.IsPartition) : π.boxes.Nonempty :=
  let ⟨J, hJ, _⟩ := h _ I.upper_mem
  ⟨J, hJ⟩
#align box_integral.prepartition.is_partition.nonempty_boxes BoxIntegral.Prepartition.IsPartition.nonempty_boxes

theorem eq_of_boxes_subset (h₁ : π₁.IsPartition) (h₂ : π₁.boxes ⊆ π₂.boxes) : π₁ = π₂ :=
  eq_of_boxes_subset_union_superset h₂ <| h₁.unionᵢ_subset _
#align box_integral.prepartition.is_partition.eq_of_boxes_subset BoxIntegral.Prepartition.IsPartition.eq_of_boxes_subset

theorem le_iff (h : π₂.IsPartition) :
    π₁ ≤ π₂ ↔ ∀ J ∈ π₁, ∀ J' ∈ π₂, (J ∩ J' : Set (ι → ℝ)).Nonempty → J ≤ J' :=
  le_iff_nonempty_imp_le_and_union_subset.trans <| and_iff_left <| h.unionᵢ_subset _
#align box_integral.prepartition.is_partition.le_iff BoxIntegral.Prepartition.IsPartition.le_iff

protected theorem bUnion (h : IsPartition π) (hi : ∀ J ∈ π, IsPartition (πi J)) :
    IsPartition (π.bunionᵢ πi) := fun x hx =>
  let ⟨J, hJ, hxi⟩ := h x hx
  let ⟨Ji, hJi, hx⟩ := hi J hJ x hxi
  ⟨Ji, π.mem_bunionᵢ.2 ⟨J, hJ, hJi⟩, hx⟩
#align box_integral.prepartition.is_partition.bUnion BoxIntegral.Prepartition.IsPartition.bUnion

protected theorem restrict (h : IsPartition π) (hJ : J ≤ I) : IsPartition (π.restrict J) :=
  isPartition_iff_union_eq.2 <| by simp [h.Union_eq, hJ]
#align box_integral.prepartition.is_partition.restrict BoxIntegral.Prepartition.IsPartition.restrict

protected theorem inf (h₁ : IsPartition π₁) (h₂ : IsPartition π₂) : IsPartition (π₁ ⊓ π₂) :=
  isPartition_iff_union_eq.2 <| by simp [h₁.Union_eq, h₂.Union_eq]
#align box_integral.prepartition.is_partition.inf BoxIntegral.Prepartition.IsPartition.inf

end IsPartition

theorem union_bUnion_partition (h : ∀ J ∈ π, (πi J).IsPartition) :
    (π.bunionᵢ πi).unionᵢ = π.unionᵢ :=
  (union_bUnion _ _).trans <|
    unionᵢ_congr_of_surjective id surjective_id fun J =>
      unionᵢ_congr_of_surjective id surjective_id fun hJ => (h J hJ).unionᵢ_eq
#align box_integral.prepartition.Union_bUnion_partition BoxIntegral.Prepartition.union_bUnion_partition

theorem isPartitionDisjUnionOfEqDiff (h : π₂.unionᵢ = I \ π₁.unionᵢ) :
    IsPartition (π₁.disjUnion π₂ <| h.symm ▸ disjoint_sdiff_self_right) :=
  isPartition_iff_union_eq.2 <| (union_disjUnion _).trans <| by simp [h, π₁.Union_subset]
#align box_integral.prepartition.is_partition_disj_union_of_eq_diff BoxIntegral.Prepartition.isPartitionDisjUnionOfEqDiff

end Prepartition

end BoxIntegral

