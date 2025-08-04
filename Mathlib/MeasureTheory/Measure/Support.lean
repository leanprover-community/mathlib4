/-
Copyright (c) 2025 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Topology.Defs.Filter
import Mathlib.Order.Filter.SmallSets

/-!
# Support of a Measure

This file develops the theory of the **topological support** of a measure `μ` on a
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

* `mem_support_iff` and `mem_support_iff_forall` : filter-theoretic and
  neighborhood characterizations of membership in the support.
* `notMem_support_iff` and `notMem_support_iff_exists` : characterizations of lying
  outside the support.
* `support_eq_univ` : if `IsOpenPosMeasure μ`, then the support of `μ` is the whole space.
* `support_zero` : the support of the zero measure is empty.
* `support_mono` and `AbsolutelyContinuous.support_mono` : monotonicity of support under
  measure domination and absolute continuity.
* `support_add` : the support of the sum of two measures is the union of their supports.
* `support_eq_forall_isOpen` : description of the support via open sets.
* `compl_support_eq_sUnion` and `support_eq_sInter` : the complement of the support is the
  union of open measure-zero sets, and the support is the intersection of closed sets whose
  complements have measure zero.
* `isClosed_support` / `isOpen_compl_support` : topological closure properties of the support.
* `support_mem_ae_of_isLindelof` and `support_mem_ae` : under Lindelöf (or hereditarily
  Lindelöf) hypotheses, the support is conull.
* `measure_compl_support` and its corollaries (`nullMeasurableSet_support`, `measure_support`,
  `nonempty_support`, `nonempty_support_iff`) : measure-theoretic consequences, including that
  the complement has measure zero and nonemptiness criteria.
* `support_restrict_subset_closure`, `mem_support_restrict`, and
  `interior_inter_support` : interaction of support with restriction to a set and the
  relation between `interior s ∩ μ.support` and the support of `μ.restrict s`.

## Notation

* `μ.support` : the support of measure `μ`.
* `(𝓝 x).smallSets` : the frequently-small-sets filter used in the filter-theoretic definition.

## Implementation notes

Have to go through and resolve some of these, and remove the associated bullets!

* TO DO: Rename `MeasureTheory.measure_mono_null` as `MeasureTheory.Measure.mono_null`
  to enable dot notation. (In a separate PR?)
* The lemma `support_restrict_subset_closure_inter_support` is currently a placeholder and
  explicitly marked for replacement: it should be proved directly without relying on the
  existing commented strategy.
* The file mixes several related but conceptually separate themes (`Add`, `Restrict`,
  `AbsolutelyContinuous`); consider reorganizing so that core support theory is grouped, with
  extensions in well-delineated subsections or submodules.
* Some proofs contain “golf” comments or ad hoc constructions—adding focused docstrings and
  cleaning those proofs (and their invariants) will improve maintainability.

## Tags

measure theory, support, topological support, filter, Lindelöf, hereditarily Lindelöf,
absolute continuity, restriction, sum of measures, null measurable, conull
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

lemma pos_mono {α : Type*} [MeasurableSpace α]
    (μ : Measure α) ⦃s t : Set α⦄ (h : s ⊆ t) (hs : 0 < μ s) :
    0 < μ t :=
  hs.trans_le <| μ.mono h

theorem _root_.Filter.HasBasis.mem_measureSupport {ι : Sort*} {p : ι → Prop}
    {s : ι → Set X} {x : X} (hl : (𝓝 x).HasBasis p s) :
    x ∈ μ.support ↔ ∀ (i : ι), p i → 0 < μ (s i) :=
  Filter.HasBasis.frequently_smallSets (hl := hl) μ.pos_mono

/-- A point `x` is in the support of measure `μ` iff any neighborhood of `x` contains a
subset with positive measure. -/
lemma mem_support_iff {x : X} : x ∈ μ.support ↔
    ∃ᶠ u in (𝓝 x).smallSets, 0 < μ u := Iff.rfl

/-- A point `x` is in the support of measure `μ` iff every neighborhood of `x` has positive
measure. -/
lemma mem_support_iff_forall (x : X) : x ∈ μ.support ↔ ∀ U ∈ 𝓝 x, 0 < μ U :=
  Filter.HasBasis.mem_measureSupport <| (𝓝 x).basis_sets

lemma support_eq_univ [μ.IsOpenPosMeasure] : μ.support = Set.univ :=
  Set.ext fun x ↦ (mem_support_iff_forall x).trans (Iff.intro (fun _ ↦ trivial)
    (fun _ _ ↦ measure_pos_of_mem_nhds μ))

lemma support_mono {ν : Measure X} (h : μ ≤ ν) : μ.support ≤ ν.support :=
  fun _ hx ↦ mem_support_iff_forall _ |>.mpr fun _ hU ↦
    lt_of_lt_of_le (mem_support_iff_forall _ |>.mp hx _ hU) (h _)

lemma AbsolutelyContinuous.support_mono {μ ν : Measure X} (hμν : μ ≪ ν) :
     μ.support ≤ ν.support := by
  intro x
  contrapose
  simp only [mem_support_iff, Filter.not_frequently, not_lt, nonpos_iff_eq_zero] at *
  exact fun a ↦ Filter.Eventually.mono a hμν

/-- A point `x` lies outside the support of `μ` iff all of the subsets of one of its neighborhoods
have measure zero. -/
lemma notMem_support_iff {x : X} : x ∉ μ.support ↔ ∀ᶠ u in (𝓝 x).smallSets, μ u = 0 := by
  simp [mem_support_iff]

theorem _root_.Filter.HasBasis.notMem_measureSupport {ι : Sort*} {p : ι → Prop}
    {s : ι → Set X} {x : X} (hl : (𝓝 x).HasBasis p s) :
    x ∉ μ.support ↔ ∃ i, p i ∧ μ (s i) = 0 := by
  simp only [hl.mem_measureSupport, not_forall, not_lt, nonpos_iff_eq_zero, bex_def]

@[simp]
lemma support_zero : (0 : Measure X).support = ∅ := by
  ext; simp only [Set.mem_empty_iff_false, iff_false, notMem_support_iff]
  exact Filter.Eventually.of_forall (congrFun rfl)

/-- The support of the sum of two measures is the union of the supports. -/
lemma support_add (μ ν : Measure X) :
  (μ + ν).support = μ.support ∪ ν.support := by
  ext; simp [mem_support_iff]

/-- A point `x` lies outside the support of `μ` iff some neighborhood of `x` has measure zero. -/
lemma notMem_support_iff_exists {x : X} : x ∉ μ.support ↔ ∃ U ∈ 𝓝 x, μ U = 0 := by
  simp [mem_support_iff_forall]

/-- The support of a measure equals the set of points whose open neighborhoods
all have positive measure. -/
lemma support_eq_forall_isOpen : μ.support =
    {x : X | ∀ u : Set X, x ∈ u → IsOpen u → 0 < μ u} := by
  simp [Set.ext_iff, (nhds_basis_opens _).mem_measureSupport]

lemma isClosed_support {μ : Measure X} : IsClosed μ.support := by
  simp_rw [isClosed_iff_frequently, (nhds_basis_opens _).mem_measureSupport,
    (nhds_basis_opens _).frequently_iff]
  grind

lemma isOpen_compl_support {μ : Measure X} : IsOpen μ.supportᶜ :=
  isOpen_compl_iff.mpr μ.isClosed_support

lemma subset_compl_support_of_isOpen {t : Set X} (ht : IsOpen t) (h : μ t = 0) :
  t ⊆ μ.supportᶜ := fun _ hx ↦
  notMem_support_iff_exists.mpr ⟨t, ht.mem_nhds hx, h⟩

lemma compl_support_eq_sUnion : μ.supportᶜ = ⋃₀ {t : Set X | IsOpen t ∧ μ t = 0} := by
  ext x; simp only [Set.mem_compl_iff, Set.mem_sUnion, Set.mem_setOf_eq, and_right_comm,
     (nhds_basis_opens x).notMem_measureSupport, fun t ↦ and_comm (b := x ∈ t)]

lemma support_eq_sInter : μ.support = ⋂₀ {t : Set X | IsClosed t ∧ μ tᶜ = 0} := by
  ext x
  simp only [(nhds_basis_opens x).mem_measureSupport, and_imp, Set.mem_sInter, Set.mem_setOf_eq]
  rw [← not_iff_not]
  push_neg
  constructor
  · rintro ⟨t, ht, htc, htc1⟩; use tᶜ; rw [← compl_compl t] at htc1 ht
    exact ⟨htc.isClosed_compl, nonpos_iff_eq_zero.mp htc1, (Set.mem_compl_iff tᶜ x).mp ht⟩
  · rintro ⟨t, ht, htc, htc1⟩; use tᶜ
    exact ⟨Set.mem_compl htc1, ht.isOpen_compl, le_of_eq htc⟩

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
lemma measure_compl_support : μ (μ.support)ᶜ = 0 := support_mem_ae

open Set

lemma nonempty_inter_support_of_pos {s : Set X} (hμ : 0 < μ s) :
    (s ∩ μ.support).Nonempty := by
  by_contra H
  have :=  LE.le.not_gt <| (OuterMeasureClass.measure_mono μ <| Disjoint.subset_compl_right
    <| disjoint_iff_inter_eq_empty.mpr <| Set.not_nonempty_iff_eq_empty.mp H).trans
      <| le_of_eq (measure_compl_support)
  contradiction

lemma nullMeasurableSet_compl_support : NullMeasurableSet (μ.supportᶜ) μ :=
  NullMeasurableSet.of_null measure_compl_support

@[simp]
lemma nullMeasurableSet_support : NullMeasurableSet μ.support μ :=
  NullMeasurableSet.compl_iff.mp (nullMeasurableSet_compl_support)

@[simp]
lemma measure_support : μ μ.support = μ Set.univ :=
  measure_of_measure_compl_eq_zero measure_compl_support

lemma nonempty_support (hμ : μ ≠ 0) : μ.support.Nonempty :=
   Nonempty.right <| nonempty_inter_support_of_pos <| measure_univ_pos.mpr hμ

lemma nonempty_support_iff : μ.support.Nonempty ↔ μ ≠ 0 :=
  ⟨fun h e ↦ (not_nonempty_iff_eq_empty.mpr <| congrArg Measure.support e|>.trans
    <| support_zero) h, fun h ↦ nonempty_support h⟩

end Lindelof
section Restrict

lemma support_restrict_subset_closure [OpensMeasurableSpace X] {s : Set X} :
    (μ.restrict s).support ⊆ closure s := by
  intro x hx
  simp only [mem_closure_iff_nhds]
  rw [nhds_basis_opens x |>.forall_iff <| fun _ _ h ↦ Set.Nonempty.mono <| by gcongr]
  intro U ⟨hxU, hU⟩
  by_cases H : (s ∩ U).Nonempty
  · exact Set.inter_nonempty_iff_exists_right.mpr H
  · have h_restr : (μ.restrict s) U = μ (U ∩ s) := by
      simp [Measure.restrict_apply hU.measurableSet, Set.inter_comm]
    rw [nhds_basis_opens x |>.mem_measureSupport] at hx
    exact MeasureTheory.nonempty_of_measure_ne_zero
      (ne_of_gt (h_restr ▸ hx U ⟨hxU, hU⟩))

lemma mem_support_restrict [OpensMeasurableSpace X] {s : Set X} {x : X} :
    x ∈ (μ.restrict s).support ↔ ∃ᶠ u in (𝓝[s] x).smallSets, 0 < μ u := by
  rw [(nhds_basis_opens x).mem_measureSupport,
    Filter.HasBasis.frequently_smallSets (hl := nhdsWithin_basis_open x s) (hq := pos_mono μ)] at *
  constructor
  all_goals
  · intro h i hi
    have D := h i hi
    rw [restrict_apply] at *
    · exact D
    · exact IsOpen.measurableSet hi.2

lemma interior_inter_support [OpensMeasurableSpace X] {s : Set X} :
    interior s ∩ μ.support ⊆ (μ.restrict s).support := by
  intro x ⟨⟨y, hy1, hy2⟩, hxp⟩
  apply mem_support_restrict.mpr
  rw [Filter.HasBasis.frequently_smallSets (hl := nhdsWithin_basis_open x s) (hq := pos_mono μ)]
  intro V ⟨hs1, hs2⟩
  rw [(nhds_basis_opens x).mem_measureSupport] at hxp
  exact lt_of_lt_of_le (hxp (V ∩ y) ⟨Set.mem_inter hs1 hy2, IsOpen.inter hs2 hy1.1⟩)
    <| OuterMeasureClass.measure_mono μ <| Set.inter_subset_inter (fun ⦃a⦄ a ↦ a) hy1.2

-- Prove the following directly, without appeal to `support_restrict_subset_closure`

-- SO THE PROOF BELOW MUST BE REPLACED!

lemma support_restrict_subset_closure_inter_support [OpensMeasurableSpace X] {s : Set X} :
  (μ.restrict s).support ⊆ closure s ∩ μ.support :=
  Set.subset_inter (support_restrict_subset_closure) (support_mono restrict_le_self)

end Restrict

end Measure

end MeasureTheory

end Support
