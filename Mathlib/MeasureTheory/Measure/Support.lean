/-
Copyright (c) 2025 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
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

/-- A point `x` lies outside the support of `μ` iff all of the subsets of one of its neighborhoods
have measure zero. -/
lemma notMem_support_iff {x : X} : x ∉ μ.support ↔ ∀ᶠ u in (𝓝 x).smallSets, μ u = 0 := by
  simp [mem_support_iff]

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

lemma subset_compl_support_of_isOpen ⦃t : Set X⦄ (ht : IsOpen t) (h : μ t = 0) :
    t ⊆ μ.supportᶜ := by
  sorry

lemma compl_support_eq_sUnion : μ.supportᶜ = ⋃₀ {t : Set X | IsOpen t ∧ μ t = 0} := by
  sorry

lemma support_eq_sInter : μ.support = ⋂₀ {t : Set X | IsClosed t ∧ μ tᶜ = 0} := by
  sorry

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
lemma measure_compl_support : μ (μ.support)ᶜ = 0 := sorry

lemma nonempty_inter_support_of_pos {s : Set X} (hμ : 0 < μ s) :
    (s ∩ μ.support).Nonempty :=
  sorry

-- this is optional, as with the common assumption `OpensMeasurableSpace` the
-- set will simply be measurable because it is open
@[simp]
lemma nullMeasurableSet_compl_support : NullMeasurableSet (μ.supportᶜ) μ := sorry

-- likewise, optional
@[simp]
lemma nullMeasurableSet_support : NullMeasurableSet μ.support μ := sorry

@[simp]
lemma measure_support : μ μ.support = μ Set.univ := sorry

lemma nonempty_support (hμ : μ ≠ 0) : μ.support.Nonempty := sorry

lemma nonempty_support_iff : μ.support.Nonempty ↔ μ ≠ 0 := sorry

end Measure

end MeasureTheory

end Support

section SupportAdd

/- This will need reincorporation into the above. -/

open MeasureTheory

open Measure

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- The support of the sum of two measures is the union of the supports. -/
lemma support_add (μ ν : Measure X) :
  (μ + ν).support = μ.support ∪ ν.support := by
  ext; simp [mem_support_iff]

end SupportAdd
