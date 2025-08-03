/-
Copyright (c) 2025 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Topology.Defs.Filter

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

/- MeasureTheory.measure_mono_null should be renamed to allow for dot notation. -/

/- Move the next three Filter results near the definition of `smallSets` filter. -/

theorem Filter.frequently_smallSets' {α : Type*} {l : Filter α} {p : Set α → Prop}
    (hp : ∀ ⦃s t : Set α⦄, s ⊆ t → p s → p t) :
    (∃ᶠ s in l.smallSets, p s) ↔ ∀ t ∈ l, p t := by
  convert not_iff_not.mpr <| l.eventually_smallSets' (p := (¬ p ·)) (by tauto)
  simp

theorem Filter.HasBasis.frequently_smallSets {α : Type*} {ι : Sort*} {p : ι → Prop} {l : Filter α}
    {s : ι → Set α} {q : Set α → Prop} {hl : l.HasBasis p s}
    (hq : ∀ ⦃s t : Set α⦄, s ⊆ t → q s → q t) :
    (∃ᶠ s in l.smallSets, q s) ↔ ∀ i, p i → q (s i) := by
  rw [Filter.frequently_smallSets' hq, hl.forall_iff hq]

theorem eventually_smallSets {α : Type*} {ι : Sort*} {p : ι → Prop} {l : Filter α}
    {s : ι → Set α} {q : Set α → Prop} {hl : l.HasBasis p s}
    (hq : ∀ ⦃s t : Set α⦄, s ⊆ t → q t → q s) :
    (∀ᶠ s in l.smallSets, q s) ↔ ∃ i, p i ∧ q (s i) := by
  rw [l.eventually_smallSets' hq, hl.exists_iff hq]

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
  mem_support_iff.trans <| Filter.frequently_smallSets.trans
    ⟨fun h _ hU ↦ let ⟨_, ht, μt⟩ := h _ hU; μt.trans_le (measure_mono ht),
     fun h _ hU ↦ ⟨_, Set.Subset.rfl, h _ hU⟩⟩ --GOLF THIS WITH `Filter.basis_sets`

lemma support_eq_univ [μ.IsOpenPosMeasure] : μ.support = Set.univ := by
  ext
  simp only [Set.mem_univ, iff_true, mem_support_iff_forall]
  exact fun _ a ↦ measure_pos_of_mem_nhds μ a

lemma support_mono {ν : Measure X} (h : μ ≤ ν) : μ.support ≤ ν.support := by
  intro x hx
  simp only [mem_support_iff_forall] at *
  intro U hU
  exact lt_of_lt_of_le (hx U hU) (h U)

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
  ext
  simp only [Set.mem_empty_iff_false, iff_false, notMem_support_iff]
  exact Filter.Eventually.of_forall (congrFun rfl)

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
  t ⊆ μ.supportᶜ := fun _ hx =>
  notMem_support_iff_exists.mpr ⟨t, ht.mem_nhds hx, h⟩

lemma compl_support_eq_sUnion : μ.supportᶜ = ⋃₀ {t : Set X | IsOpen t ∧ μ t = 0} := by
  ext x
  have A (t : Set X) := and_comm (a := IsOpen t) (b := x ∈ t)
  simp only [Set.mem_compl_iff, Set.mem_sUnion, Set.mem_setOf_eq, and_right_comm,
     (nhds_basis_opens x).notMem_measureSupport, A]

lemma support_eq_sInter : μ.support = ⋂₀ {t : Set X | IsClosed t ∧ μ tᶜ = 0} := by
  ext x
  simp only [(nhds_basis_opens x).mem_measureSupport, and_imp, Set.mem_sInter, Set.mem_setOf_eq]
  rw [← not_iff_not]
  push_neg
  constructor
  · intro h
    obtain ⟨t, ht, htc, htc1⟩ := h
    use tᶜ
    have A := htc.isClosed_compl
    have B := nonpos_iff_eq_zero.mp htc1
    rw [← compl_compl t] at B ht
    have C := (Set.mem_compl_iff tᶜ x).mp ht
    exact ⟨htc.isClosed_compl, B, C⟩
  · intro h
    obtain ⟨t, ht, htc, htc1⟩ := h
    use tᶜ
    exact ⟨Set.mem_compl htc1, ht.isOpen_compl, le_of_eq htc⟩

open Set

/-- If the complement of the support is Lindelöf, then the support of a measure is conull. -/
lemma support_mem_ae_of_isLindelof (h : IsLindelof μ.supportᶜ) : μ.support ∈ ae μ := by
  refine compl_compl μ.support ▸ h.compl_mem_sets_of_nhdsWithin fun s hs ↦ ?_
  simpa [compl_mem_ae_iff, isOpen_compl_support.nhdsWithin_eq hs]
    using notMem_support_iff_exists.mp hs

/-- In a hereditarily Lindelöf space, the support of a measure is conull. -/
lemma support_mem_ae [HereditarilyLindelofSpace X] : μ.support ∈ ae μ :=
  support_mem_ae_of_isLindelof <| HereditarilyLindelof_LindelofSets μ.supportᶜ

variable [HereditarilyLindelofSpace X]

@[simp]
lemma measure_compl_support : μ (μ.support)ᶜ = 0 := support_mem_ae

lemma nonempty_inter_support_of_pos {s : Set X} (hμ : 0 < μ s) :
    (s ∩ μ.support).Nonempty := by
  by_contra H
  have :=  LE.le.not_gt <| (OuterMeasureClass.measure_mono μ <| Disjoint.subset_compl_right
    <| disjoint_iff_inter_eq_empty.mpr <| Set.not_nonempty_iff_eq_empty.mp H).trans
      <| le_of_eq (measure_compl_support)
  contradiction

@[simp]
lemma nullMeasurableSet_compl_support : NullMeasurableSet (μ.supportᶜ) μ :=
  NullMeasurableSet.of_null measure_compl_support

@[simp]
lemma nullMeasurableSet_support : NullMeasurableSet μ.support μ :=
  NullMeasurableSet.compl_iff.mp nullMeasurableSet_compl_support

@[simp]
lemma measure_support : μ μ.support = μ Set.univ :=
  measure_of_measure_compl_eq_zero measure_compl_support

lemma nonempty_support (hμ : μ ≠ 0) : μ.support.Nonempty :=
   Nonempty.right <| nonempty_inter_support_of_pos <| measure_univ_pos.mpr hμ

lemma nonempty_support_iff : μ.support.Nonempty ↔ μ ≠ 0 :=
  ⟨fun h e ↦ (not_nonempty_iff_eq_empty.mpr <| (congrArg Measure.support e).trans
    <| support_zero) h, fun h ↦ nonempty_support h⟩

end Measure

end MeasureTheory

end Support

section Add

/- This will need reincorporation into the above. -/

open MeasureTheory

open Measure

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- The support of the sum of two measures is the union of the supports. -/
lemma support_add (μ ν : Measure X) :
  (μ + ν).support = μ.support ∪ ν.support := by
  ext; simp [mem_support_iff]

end Add

section Restrict

open MeasureTheory Measure

open scoped Topology

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

variable {μ : Measure X}

lemma support_restrict_subset_closure [OpensMeasurableSpace X] {s : Set X} :
  (μ.restrict s).support ⊆ closure s := by
  intro x hx
  simp only [mem_closure_iff_nhds]
  rw [(nhds_basis_opens x).forall_iff (fun _ _ h ↦ Set.Nonempty.mono (by gcongr))]
  intro U ⟨hxU, hU⟩
  by_cases H : (s ∩ U).Nonempty
  · exact Set.inter_nonempty_iff_exists_right.mpr H
  · have h_restr : (μ.restrict s) U = μ (U ∩ s) := by
      simp [Measure.restrict_apply hU.measurableSet, Set.inter_comm]
    rw [(nhds_basis_opens x).mem_measureSupport] at hx
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
  intro x ⟨hxs, hxp⟩
  apply mem_support_restrict.mpr
  rw [Filter.HasBasis.frequently_smallSets (hl := nhdsWithin_basis_open x s) (hq := pos_mono μ)]
  intro V ⟨hs1, hs2⟩
  obtain ⟨y, hy1, hy2⟩ := hxs
  rw [(nhds_basis_opens x).mem_measureSupport] at hxp
  exact lt_of_lt_of_le (hxp (V ∩ y) ⟨Set.mem_inter hs1 hy2, IsOpen.inter hs2 hy1.1⟩)
    <| OuterMeasureClass.measure_mono μ <| Set.inter_subset_inter (fun ⦃a⦄ a ↦ a) hy1.2

-- Prove the following directly, without appeal to `support_restrict_subset_closure`

-- SO THE PROOF BELOW MUST BE REPLACED!

lemma support_restrict_subset_closure_inter_support [OpensMeasurableSpace X] {s : Set X} :
  (μ.restrict s).support ⊆ closure s ∩ μ.support :=
  Set.subset_inter (support_restrict_subset_closure) (support_mono restrict_le_self)

end Restrict

section AbsolutelyContinuous

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

open MeasureTheory

open Measure

lemma AbsolutelyContinuous.support_mono {μ ν : Measure X} (hμν : μ ≪ ν) :
     μ.support ≤ ν.support := by
  intro x
  contrapose
  simp only [mem_support_iff, Filter.not_frequently, not_lt, nonpos_iff_eq_zero] at *
  exact fun a ↦ Filter.Eventually.mono a hμν

end AbsolutelyContinuous
