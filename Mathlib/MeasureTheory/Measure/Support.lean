/-
Copyright (c) 2025 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/

import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Support of a Measure

This file develops the theory of the **support** of a measure `μ` on a
topological measurable space. The support is defined as the set of points whose every open
neighborhood has positive measure. We give equivalent characterizations, prove basic
measure-theoretic properties, and study interactions with sums, restrictions, and
absolute continuity. Under various Lindelöf conditions, the support is conull,
and various descriptions of the complement of the support are provided.

## Main definitions

* `Measure.support` : the support of a measure `μ`, defined as
  `{x | ∃ᶠ u in (𝓝 x).smallSets, 0 < μ u}` — equivalently, every neighborhood of `x`
  has positive `μ`-measure.

## Main results

* `compl_support_eq_sUnion` and `support_eq_sInter` : the complement of the support is the
  union of open measure-zero sets, and the support is the intersection of closed sets whose
  complements have measure zero.
* `isClosed_support` : the support is a closed set.
* `support_mem_ae_of_isLindelof` and `support_mem_ae` : under Lindelöf (or hereditarily
  Lindelöf) hypotheses, the support is conull.

## Tags

measure, support, Lindelöf
-/

section Support

namespace MeasureTheory

namespace Measure

open scoped Topology

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- A point `x` is in the support of `μ` if any open neighborhood of `x` has positive measure.
We provide the definition in terms of the filter-theoretic equivalent
`∃ᶠ u in (𝓝 x).smallSets, 0 < μ u`. -/
protected def support (μ : Measure X) : Set X := {x : X | ∃ᶠ u in (𝓝 x).smallSets, 0 < μ u}

variable {μ : Measure X}

theorem _root_.Filter.HasBasis.mem_measureSupport {ι : Sort*} {p : ι → Prop}
    {s : ι → Set X} {x : X} (hl : (𝓝 x).HasBasis p s) :
    x ∈ μ.support ↔ ∀ (i : ι), p i → 0 < μ (s i) :=
  hl.frequently_smallSets pos_mono

/-- A point `x` is in the support of measure `μ` iff any neighborhood of `x` contains a
subset with positive measure. -/
lemma mem_support_iff {x : X} : x ∈ μ.support ↔
    ∃ᶠ u in (𝓝 x).smallSets, 0 < μ u := Iff.rfl

/-- A point `x` is in the support of measure `μ` iff every neighborhood of `x` has positive
measure. -/
lemma mem_support_iff_forall (x : X) : x ∈ μ.support ↔ ∀ U ∈ 𝓝 x, 0 < μ U :=
  (𝓝 x).basis_sets.mem_measureSupport

lemma support_eq_univ [μ.IsOpenPosMeasure] : μ.support = Set.univ := by
  simpa [Set.eq_univ_iff_forall, mem_support_iff_forall] using fun _ _ ↦ μ.measure_pos_of_mem_nhds

lemma AbsolutelyContinuous.support_mono {μ ν : Measure X} (hμν : μ ≪ ν) :
    μ.support ⊆ ν.support :=
  fun _ hx ↦ hx.mp <| .of_forall hμν.pos_mono

lemma support_mono {ν : Measure X} (h : μ ≤ ν) : μ.support ⊆ ν.support :=
  h.absolutelyContinuous.support_mono

/-- A point `x` lies outside the support of `μ` iff all of the subsets of one of its neighborhoods
have measure zero. -/
lemma notMem_support_iff {x : X} : x ∉ μ.support ↔ ∀ᶠ u in (𝓝 x).smallSets, μ u = 0 := by
  simp [mem_support_iff]

theorem _root_.Filter.HasBasis.notMem_measureSupport {ι : Sort*} {p : ι → Prop}
    {s : ι → Set X} {x : X} (hl : (𝓝 x).HasBasis p s) :
    x ∉ μ.support ↔ ∃ i, p i ∧ μ (s i) = 0 := by
  simp [hl.mem_measureSupport]

@[simp]
lemma support_zero : (0 : Measure X).support = ∅ := by simp [Measure.support]

/-- The support of the sum of two measures is the union of the supports. -/
lemma support_add (μ ν : Measure X) : (μ + ν).support = μ.support ∪ ν.support := by
  ext; simp [mem_support_iff]

/-- A point `x` lies outside the support of `μ` iff some neighborhood of `x` has measure zero. -/
lemma notMem_support_iff_exists {x : X} : x ∉ μ.support ↔ ∃ U ∈ 𝓝 x, μ U = 0 := by
  simp [mem_support_iff_forall]

/-- The support of a measure equals the set of points whose open neighborhoods
all have positive measure. -/
lemma support_eq_forall_isOpen : μ.support =
    {x : X | ∀ u : Set X, x ∈ u → IsOpen u → 0 < μ u} := by
  simp [Set.ext_iff, nhds_basis_opens _ |>.mem_measureSupport]

lemma isClosed_support {μ : Measure X} : IsClosed μ.support := by
  simp_rw [isClosed_iff_frequently, nhds_basis_opens _ |>.mem_measureSupport,
    nhds_basis_opens _ |>.frequently_iff]
  grind

lemma isOpen_compl_support {μ : Measure X} : IsOpen μ.supportᶜ :=
  isOpen_compl_iff.mpr μ.isClosed_support

lemma subset_compl_support_of_isOpen {t : Set X} (ht : IsOpen t) (h : μ t = 0) :
    t ⊆ μ.supportᶜ :=
  fun _ hx ↦ notMem_support_iff_exists.mpr ⟨t, ht.mem_nhds hx, h⟩

lemma support_subset_of_isClosed {t : Set X} (ht : IsClosed t) (h : t ∈ ae μ) :
    μ.support ⊆ t :=
  Set.compl_subset_compl.mp <| subset_compl_support_of_isOpen ht.isOpen_compl h

lemma compl_support_eq_sUnion : μ.supportᶜ = ⋃₀ {t : Set X | IsOpen t ∧ μ t = 0} := by
  ext x; simp only [Set.mem_compl_iff, Set.mem_sUnion, Set.mem_setOf_eq, and_right_comm,
     nhds_basis_opens x |>.notMem_measureSupport, fun t ↦ and_comm (b := x ∈ t)]

lemma support_eq_sInter : μ.support = ⋂₀ {t : Set X | IsClosed t ∧ μ tᶜ = 0} := by
  convert congr($(compl_support_eq_sUnion (μ := μ))ᶜ)
  all_goals simp [Set.compl_sUnion, compl_involutive.image_eq_preimage]

section Lindelof

/-- If the complement of the support is Lindelöf, then the support of a measure is conull. -/
lemma support_mem_ae_of_isLindelof (h : IsLindelof μ.supportᶜ) : μ.support ∈ ae μ := by
  refine compl_compl μ.support ▸ h.compl_mem_sets_of_nhdsWithin fun s hs ↦ ?_
  simpa [compl_mem_ae_iff, isOpen_compl_support.nhdsWithin_eq hs]
    using notMem_support_iff_exists.mp hs

variable [HereditarilyLindelofSpace X]

/-- In a hereditarily Lindelöf space, the support of a measure is conull. -/
lemma support_mem_ae : μ.support ∈ ae μ :=
  support_mem_ae_of_isLindelof <| HereditarilyLindelof_LindelofSets μ.supportᶜ

@[simp]
lemma measure_compl_support : μ μ.supportᶜ = 0 := support_mem_ae

open Set

lemma nonempty_inter_support_of_pos {s : Set X} (hμ : 0 < μ s) :
    (s ∩ μ.support).Nonempty := by
  rw [← Set.not_disjoint_iff_nonempty_inter]
  contrapose! hμ
  exact μ.mono hμ.subset_compl_right |>.trans <| by simp

/-- Under the assumption `OpensMeasurableSpace`, this is redundant because
the complement of the support is open, and therefore measurable. -/
lemma nullMeasurableSet_compl_support : NullMeasurableSet (μ.supportᶜ) μ :=
  NullMeasurableSet.of_null measure_compl_support

/-- Under the assumption `OpensMeasurableSpace`, this is redundant because
the support is closed, and therefore measurable. -/
lemma nullMeasurableSet_support : NullMeasurableSet μ.support μ :=
  NullMeasurableSet.compl_iff.mp nullMeasurableSet_compl_support

lemma nonempty_support (hμ : μ ≠ 0) : μ.support.Nonempty :=
   Nonempty.right <| nonempty_inter_support_of_pos <| measure_univ_pos.mpr hμ

lemma nonempty_support_iff : μ.support.Nonempty ↔ μ ≠ 0 :=
  ⟨fun h e ↦ (not_nonempty_iff_eq_empty.mpr <| congrArg Measure.support e |>.trans
    <| support_zero) h, fun h ↦ nonempty_support h⟩

end Lindelof

section Restrict

variable [OpensMeasurableSpace X]

lemma mem_support_restrict {s : Set X} {x : X} :
    x ∈ (μ.restrict s).support ↔ ∃ᶠ u in (𝓝[s] x).smallSets, 0 < μ u := by
  rw [nhds_basis_opens x |>.mem_measureSupport,
    (nhdsWithin_basis_open x s).frequently_smallSets pos_mono]
  grind [IsOpen.measurableSet, restrict_apply]

lemma interior_inter_support {s : Set X} :
    interior s ∩ μ.support ⊆ (μ.restrict s).support := by
  rintro x ⟨hxs, hxμ⟩
  rw [mem_support_restrict, (nhdsWithin_basis_open x s).frequently_smallSets pos_mono]
  rw [(nhds_basis_opens x).mem_measureSupport] at hxμ
  rintro u ⟨hxu, hu⟩
  apply hxμ (u ∩ interior s) ⟨⟨hxu, hxs⟩, hu.inter isOpen_interior⟩ |>.trans_le
  gcongr
  exact interior_subset

lemma support_restrict_subset {s : Set X} :
    (μ.restrict s).support ⊆ closure s ∩ μ.support := by
  refine Set.subset_inter (support_subset_of_isClosed isClosed_closure ?_)
    (support_mono restrict_le_self)
  rw [mem_ae_iff, μ.restrict_apply isClosed_closure.isOpen_compl.measurableSet]
  convert μ.empty
  exact subset_closure.disjoint_compl_left.eq_bot

end Restrict

end Measure

end MeasureTheory

end Support
