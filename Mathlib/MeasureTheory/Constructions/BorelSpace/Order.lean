/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

#align_import measure_theory.constructions.borel_space.basic from "leanprover-community/mathlib"@"9f55d0d4363ae59948c33864cbc52e0b12e0e8ce"

/-!
# Borel sigma algebras on spaces with orders

## Main definitions

## Main statements

-/

open Set Filter MeasureTheory MeasurableSpace TopologicalSpace

open scoped Classical BigOperators Topology NNReal ENNReal MeasureTheory

universe u v w x y

variable {α β γ δ : Type*} {ι : Sort y} {s t u : Set α}

section Orders

variable [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
variable [MeasurableSpace δ]

section Preorder

variable [Preorder α] [OrderClosedTopology α] {a b x : α}

@[simp, measurability]
theorem measurableSet_Ici : MeasurableSet (Ici a) :=
  isClosed_Ici.measurableSet
#align measurable_set_Ici measurableSet_Ici

@[simp, measurability]
theorem measurableSet_Iic : MeasurableSet (Iic a) :=
  isClosed_Iic.measurableSet
#align measurable_set_Iic measurableSet_Iic

@[simp, measurability]
theorem measurableSet_Icc : MeasurableSet (Icc a b) :=
  isClosed_Icc.measurableSet
#align measurable_set_Icc measurableSet_Icc

instance nhdsWithin_Ici_isMeasurablyGenerated : (𝓝[Ici b] a).IsMeasurablyGenerated :=
  measurableSet_Ici.nhdsWithin_isMeasurablyGenerated _
#align nhds_within_Ici_is_measurably_generated nhdsWithin_Ici_isMeasurablyGenerated

instance nhdsWithin_Iic_isMeasurablyGenerated : (𝓝[Iic b] a).IsMeasurablyGenerated :=
  measurableSet_Iic.nhdsWithin_isMeasurablyGenerated _
#align nhds_within_Iic_is_measurably_generated nhdsWithin_Iic_isMeasurablyGenerated

instance nhdsWithin_Icc_isMeasurablyGenerated : IsMeasurablyGenerated (𝓝[Icc a b] x) := by
  rw [← Ici_inter_Iic, nhdsWithin_inter]
  infer_instance
#align nhds_within_Icc_is_measurably_generated nhdsWithin_Icc_isMeasurablyGenerated

instance atTop_isMeasurablyGenerated : (Filter.atTop : Filter α).IsMeasurablyGenerated :=
  @Filter.iInf_isMeasurablyGenerated _ _ _ _ fun a =>
    (measurableSet_Ici : MeasurableSet (Ici a)).principal_isMeasurablyGenerated
#align at_top_is_measurably_generated atTop_isMeasurablyGenerated

instance atBot_isMeasurablyGenerated : (Filter.atBot : Filter α).IsMeasurablyGenerated :=
  @Filter.iInf_isMeasurablyGenerated _ _ _ _ fun a =>
    (measurableSet_Iic : MeasurableSet (Iic a)).principal_isMeasurablyGenerated
#align at_bot_is_measurably_generated atBot_isMeasurablyGenerated

instance [R1Space α] : IsMeasurablyGenerated (cocompact α) where
  exists_measurable_subset := by
    intro _ hs
    obtain ⟨t, ht, hts⟩ := mem_cocompact.mp hs
    exact ⟨(closure t)ᶜ, ht.closure.compl_mem_cocompact, isClosed_closure.measurableSet.compl,
      (compl_subset_compl.2 subset_closure).trans hts⟩

end Preorder

section PartialOrder

variable [PartialOrder α] [OrderClosedTopology α] [SecondCountableTopology α] {a b : α}

@[measurability]
theorem measurableSet_le' : MeasurableSet { p : α × α | p.1 ≤ p.2 } :=
  OrderClosedTopology.isClosed_le'.measurableSet
#align measurable_set_le' measurableSet_le'

@[measurability]
theorem measurableSet_le {f g : δ → α} (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet { a | f a ≤ g a } :=
  hf.prod_mk hg measurableSet_le'
#align measurable_set_le measurableSet_le

end PartialOrder

section LinearOrder

variable [LinearOrder α] [OrderClosedTopology α] {a b x : α}

-- we open this locale only here to avoid issues with list being treated as intervals above
open Interval

@[simp, measurability]
theorem measurableSet_Iio : MeasurableSet (Iio a) :=
  isOpen_Iio.measurableSet
#align measurable_set_Iio measurableSet_Iio

@[simp, measurability]
theorem measurableSet_Ioi : MeasurableSet (Ioi a) :=
  isOpen_Ioi.measurableSet
#align measurable_set_Ioi measurableSet_Ioi

@[simp, measurability]
theorem measurableSet_Ioo : MeasurableSet (Ioo a b) :=
  isOpen_Ioo.measurableSet
#align measurable_set_Ioo measurableSet_Ioo

@[simp, measurability]
theorem measurableSet_Ioc : MeasurableSet (Ioc a b) :=
  measurableSet_Ioi.inter measurableSet_Iic
#align measurable_set_Ioc measurableSet_Ioc

@[simp, measurability]
theorem measurableSet_Ico : MeasurableSet (Ico a b) :=
  measurableSet_Ici.inter measurableSet_Iio
#align measurable_set_Ico measurableSet_Ico

instance nhdsWithin_Ioi_isMeasurablyGenerated : (𝓝[Ioi b] a).IsMeasurablyGenerated :=
  measurableSet_Ioi.nhdsWithin_isMeasurablyGenerated _
#align nhds_within_Ioi_is_measurably_generated nhdsWithin_Ioi_isMeasurablyGenerated

instance nhdsWithin_Iio_isMeasurablyGenerated : (𝓝[Iio b] a).IsMeasurablyGenerated :=
  measurableSet_Iio.nhdsWithin_isMeasurablyGenerated _
#align nhds_within_Iio_is_measurably_generated nhdsWithin_Iio_isMeasurablyGenerated

instance nhdsWithin_uIcc_isMeasurablyGenerated : IsMeasurablyGenerated (𝓝[[[a, b]]] x) :=
  nhdsWithin_Icc_isMeasurablyGenerated
#align nhds_within_uIcc_is_measurably_generated nhdsWithin_uIcc_isMeasurablyGenerated

@[measurability]
theorem measurableSet_lt' [SecondCountableTopology α] : MeasurableSet { p : α × α | p.1 < p.2 } :=
  (isOpen_lt continuous_fst continuous_snd).measurableSet
#align measurable_set_lt' measurableSet_lt'

@[measurability]
theorem measurableSet_lt [SecondCountableTopology α] {f g : δ → α} (hf : Measurable f)
    (hg : Measurable g) : MeasurableSet { a | f a < g a } :=
  hf.prod_mk hg measurableSet_lt'
#align measurable_set_lt measurableSet_lt

theorem nullMeasurableSet_lt [SecondCountableTopology α] {μ : Measure δ} {f g : δ → α}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) : NullMeasurableSet { a | f a < g a } μ :=
  (hf.prod_mk hg).nullMeasurable measurableSet_lt'
#align null_measurable_set_lt nullMeasurableSet_lt

theorem nullMeasurableSet_lt' [SecondCountableTopology α] {μ : Measure (α × α)} :
    NullMeasurableSet { p : α × α | p.1 < p.2 } μ :=
  measurableSet_lt'.nullMeasurableSet

theorem nullMeasurableSet_le [SecondCountableTopology α] {μ : Measure δ}
    {f g : δ → α} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    NullMeasurableSet { a | f a ≤ g a } μ :=
  (hf.prod_mk hg).nullMeasurable measurableSet_le'

theorem Set.OrdConnected.measurableSet (h : OrdConnected s) : MeasurableSet s := by
  let u := ⋃ (x ∈ s) (y ∈ s), Ioo x y
  have huopen : IsOpen u := isOpen_biUnion fun _ _ => isOpen_biUnion fun _ _ => isOpen_Ioo
  have humeas : MeasurableSet u := huopen.measurableSet
  have hfinite : (s \ u).Finite := s.finite_diff_iUnion_Ioo
  have : u ⊆ s := iUnion₂_subset fun x hx => iUnion₂_subset fun y hy =>
    Ioo_subset_Icc_self.trans (h.out hx hy)
  rw [← union_diff_cancel this]
  exact humeas.union hfinite.measurableSet
#align set.ord_connected.measurable_set Set.OrdConnected.measurableSet

theorem IsPreconnected.measurableSet (h : IsPreconnected s) : MeasurableSet s :=
  h.ordConnected.measurableSet
#align is_preconnected.measurable_set IsPreconnected.measurableSet

theorem generateFrom_Ico_mem_le_borel {α : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderClosedTopology α] (s t : Set α) :
    MeasurableSpace.generateFrom { S | ∃ l ∈ s, ∃ u ∈ t, l < u ∧ Ico l u = S }
      ≤ borel α := by
  apply generateFrom_le
  borelize α
  rintro _ ⟨a, -, b, -, -, rfl⟩
  exact measurableSet_Ico
#align generate_from_Ico_mem_le_borel generateFrom_Ico_mem_le_borel

theorem Dense.borel_eq_generateFrom_Ico_mem_aux {α : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] [SecondCountableTopology α] {s : Set α} (hd : Dense s)
    (hbot : ∀ x, IsBot x → x ∈ s) (hIoo : ∀ x y : α, x < y → Ioo x y = ∅ → y ∈ s) :
    borel α = .generateFrom { S : Set α | ∃ l ∈ s, ∃ u ∈ s, l < u ∧ Ico l u = S } := by
  set S : Set (Set α) := { S | ∃ l ∈ s, ∃ u ∈ s, l < u ∧ Ico l u = S }
  refine' le_antisymm _ (generateFrom_Ico_mem_le_borel _ _)
  letI : MeasurableSpace α := generateFrom S
  rw [borel_eq_generateFrom_Iio]
  refine' generateFrom_le (forall_mem_range.2 fun a => _)
  rcases hd.exists_countable_dense_subset_bot_top with ⟨t, hts, hc, htd, htb, -⟩
  by_cases ha : ∀ b < a, (Ioo b a).Nonempty
  · convert_to MeasurableSet (⋃ (l ∈ t) (u ∈ t) (_ : l < u) (_ : u ≤ a), Ico l u)
    · ext y
      simp only [mem_iUnion, mem_Iio, mem_Ico]
      constructor
      · intro hy
        rcases htd.exists_le' (fun b hb => htb _ hb (hbot b hb)) y with ⟨l, hlt, hly⟩
        rcases htd.exists_mem_open isOpen_Ioo (ha y hy) with ⟨u, hut, hyu, hua⟩
        exact ⟨l, hlt, u, hut, hly.trans_lt hyu, hua.le, hly, hyu⟩
      · rintro ⟨l, -, u, -, -, hua, -, hyu⟩
        exact hyu.trans_le hua
    · refine' MeasurableSet.biUnion hc fun a ha => MeasurableSet.biUnion hc fun b hb => _
      refine' MeasurableSet.iUnion fun hab => MeasurableSet.iUnion fun _ => _
      exact .basic _ ⟨a, hts ha, b, hts hb, hab, mem_singleton _⟩
  · simp only [not_forall, not_nonempty_iff_eq_empty] at ha
    replace ha : a ∈ s := hIoo ha.choose a ha.choose_spec.fst ha.choose_spec.snd
    convert_to MeasurableSet (⋃ (l ∈ t) (_ : l < a), Ico l a)
    · symm
      simp only [← Ici_inter_Iio, ← iUnion_inter, inter_eq_right, subset_def, mem_iUnion,
        mem_Ici, mem_Iio]
      intro x hx
      rcases htd.exists_le' (fun b hb => htb _ hb (hbot b hb)) x with ⟨z, hzt, hzx⟩
      exact ⟨z, hzt, hzx.trans_lt hx, hzx⟩
    · refine' .biUnion hc fun x hx => MeasurableSet.iUnion fun hlt => _
      exact .basic _ ⟨x, hts hx, a, ha, hlt, mem_singleton _⟩
#align dense.borel_eq_generate_from_Ico_mem_aux Dense.borel_eq_generateFrom_Ico_mem_aux

theorem Dense.borel_eq_generateFrom_Ico_mem {α : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] [SecondCountableTopology α] [DenselyOrdered α] [NoMinOrder α] {s : Set α}
    (hd : Dense s) :
    borel α = .generateFrom { S : Set α | ∃ l ∈ s, ∃ u ∈ s, l < u ∧ Ico l u = S } :=
  hd.borel_eq_generateFrom_Ico_mem_aux (by simp) fun x y hxy H =>
    ((nonempty_Ioo.2 hxy).ne_empty H).elim
#align dense.borel_eq_generate_from_Ico_mem Dense.borel_eq_generateFrom_Ico_mem

theorem borel_eq_generateFrom_Ico (α : Type*) [TopologicalSpace α] [SecondCountableTopology α]
    [LinearOrder α] [OrderTopology α] :
    borel α = .generateFrom { S : Set α | ∃ (l u : α), l < u ∧ Ico l u = S } := by
  simpa only [exists_prop, mem_univ, true_and_iff] using
    (@dense_univ α _).borel_eq_generateFrom_Ico_mem_aux (fun _ _ => mem_univ _) fun _ _ _ _ =>
      mem_univ _
#align borel_eq_generate_from_Ico borel_eq_generateFrom_Ico

theorem Dense.borel_eq_generateFrom_Ioc_mem_aux {α : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] [SecondCountableTopology α] {s : Set α} (hd : Dense s)
    (hbot : ∀ x, IsTop x → x ∈ s) (hIoo : ∀ x y : α, x < y → Ioo x y = ∅ → x ∈ s) :
    borel α = .generateFrom { S : Set α | ∃ l ∈ s, ∃ u ∈ s, l < u ∧ Ioc l u = S } := by
  convert hd.orderDual.borel_eq_generateFrom_Ico_mem_aux hbot fun x y hlt he => hIoo y x hlt _
    using 2
  · ext s
    constructor <;> rintro ⟨l, hl, u, hu, hlt, rfl⟩
    exacts [⟨u, hu, l, hl, hlt, dual_Ico⟩, ⟨u, hu, l, hl, hlt, dual_Ioc⟩]
  · erw [dual_Ioo]
    exact he
#align dense.borel_eq_generate_from_Ioc_mem_aux Dense.borel_eq_generateFrom_Ioc_mem_aux

theorem Dense.borel_eq_generateFrom_Ioc_mem {α : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] [SecondCountableTopology α] [DenselyOrdered α] [NoMaxOrder α] {s : Set α}
    (hd : Dense s) :
    borel α = .generateFrom { S : Set α | ∃ l ∈ s, ∃ u ∈ s, l < u ∧ Ioc l u = S } :=
  hd.borel_eq_generateFrom_Ioc_mem_aux (by simp) fun x y hxy H =>
    ((nonempty_Ioo.2 hxy).ne_empty H).elim
#align dense.borel_eq_generate_from_Ioc_mem Dense.borel_eq_generateFrom_Ioc_mem

theorem borel_eq_generateFrom_Ioc (α : Type*) [TopologicalSpace α] [SecondCountableTopology α]
    [LinearOrder α] [OrderTopology α] :
    borel α = .generateFrom { S : Set α | ∃ l u, l < u ∧ Ioc l u = S } := by
  simpa only [exists_prop, mem_univ, true_and_iff] using
    (@dense_univ α _).borel_eq_generateFrom_Ioc_mem_aux (fun _ _ => mem_univ _) fun _ _ _ _ =>
      mem_univ _
#align borel_eq_generate_from_Ioc borel_eq_generateFrom_Ioc

namespace MeasureTheory.Measure

/-- Two finite measures on a Borel space are equal if they agree on all closed-open intervals.  If
`α` is a conditionally complete linear order with no top element,
`MeasureTheory.Measure.ext_of_Ico` is an extensionality lemma with weaker assumptions on `μ` and
`ν`. -/
theorem ext_of_Ico_finite {α : Type*} [TopologicalSpace α] {m : MeasurableSpace α}
    [SecondCountableTopology α] [LinearOrder α] [OrderTopology α] [BorelSpace α] (μ ν : Measure α)
    [IsFiniteMeasure μ] (hμν : μ univ = ν univ) (h : ∀ ⦃a b⦄, a < b → μ (Ico a b) = ν (Ico a b)) :
    μ = ν := by
  refine'
    ext_of_generate_finite _ (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ico α))
      (isPiSystem_Ico (id : α → α) id) _ hμν
  · rintro - ⟨a, b, hlt, rfl⟩
    exact h hlt
#align measure_theory.measure.ext_of_Ico_finite MeasureTheory.Measure.ext_of_Ico_finite

/-- Two finite measures on a Borel space are equal if they agree on all open-closed intervals.  If
`α` is a conditionally complete linear order with no top element,
`MeasureTheory.Measure.ext_of_Ioc` is an extensionality lemma with weaker assumptions on `μ` and
`ν`. -/
theorem ext_of_Ioc_finite {α : Type*} [TopologicalSpace α] {m : MeasurableSpace α}
    [SecondCountableTopology α] [LinearOrder α] [OrderTopology α] [BorelSpace α] (μ ν : Measure α)
    [IsFiniteMeasure μ] (hμν : μ univ = ν univ) (h : ∀ ⦃a b⦄, a < b → μ (Ioc a b) = ν (Ioc a b)) :
    μ = ν := by
  refine' @ext_of_Ico_finite αᵒᵈ _ _ _ _ _ ‹_› μ ν _ hμν fun a b hab => _
  erw [dual_Ico (α := α)]
  exact h hab
#align measure_theory.measure.ext_of_Ioc_finite MeasureTheory.Measure.ext_of_Ioc_finite

/-- Two measures which are finite on closed-open intervals are equal if they agree on all
closed-open intervals. -/
theorem ext_of_Ico' {α : Type*} [TopologicalSpace α] {m : MeasurableSpace α}
    [SecondCountableTopology α] [LinearOrder α] [OrderTopology α] [BorelSpace α] [NoMaxOrder α]
    (μ ν : Measure α) (hμ : ∀ ⦃a b⦄, a < b → μ (Ico a b) ≠ ∞)
    (h : ∀ ⦃a b⦄, a < b → μ (Ico a b) = ν (Ico a b)) : μ = ν := by
  rcases exists_countable_dense_bot_top α with ⟨s, hsc, hsd, hsb, _⟩
  have : (⋃ (l ∈ s) (u ∈ s) (_ : l < u), {Ico l u} : Set (Set α)).Countable :=
    hsc.biUnion fun l _ => hsc.biUnion fun u _ => countable_iUnion fun _ => countable_singleton _
  simp only [← setOf_eq_eq_singleton, ← setOf_exists] at this
  refine'
    Measure.ext_of_generateFrom_of_cover_subset
      (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ico α)) (isPiSystem_Ico id id) _ this
      _ _ _
  · rintro _ ⟨l, -, u, -, h, rfl⟩
    exact ⟨l, u, h, rfl⟩
  · refine' sUnion_eq_univ_iff.2 fun x => _
    rcases hsd.exists_le' hsb x with ⟨l, hls, hlx⟩
    rcases hsd.exists_gt x with ⟨u, hus, hxu⟩
    exact ⟨_, ⟨l, hls, u, hus, hlx.trans_lt hxu, rfl⟩, hlx, hxu⟩
  · rintro _ ⟨l, -, u, -, hlt, rfl⟩
    exact hμ hlt
  · rintro _ ⟨l, u, hlt, rfl⟩
    exact h hlt
#align measure_theory.measure.ext_of_Ico' MeasureTheory.Measure.ext_of_Ico'

/-- Two measures which are finite on closed-open intervals are equal if they agree on all
open-closed intervals. -/
theorem ext_of_Ioc' {α : Type*} [TopologicalSpace α] {m : MeasurableSpace α}
    [SecondCountableTopology α] [LinearOrder α] [OrderTopology α] [BorelSpace α] [NoMinOrder α]
    (μ ν : Measure α) (hμ : ∀ ⦃a b⦄, a < b → μ (Ioc a b) ≠ ∞)
    (h : ∀ ⦃a b⦄, a < b → μ (Ioc a b) = ν (Ioc a b)) : μ = ν := by
  refine' @ext_of_Ico' αᵒᵈ _ _ _ _ _ ‹_› _ μ ν _ _ <;> intro a b hab <;> erw [dual_Ico (α := α)]
  exacts [hμ hab, h hab]
#align measure_theory.measure.ext_of_Ioc' MeasureTheory.Measure.ext_of_Ioc'

/-- Two measures which are finite on closed-open intervals are equal if they agree on all
closed-open intervals. -/
theorem ext_of_Ico {α : Type*} [TopologicalSpace α] {_m : MeasurableSpace α}
    [SecondCountableTopology α] [ConditionallyCompleteLinearOrder α] [OrderTopology α]
    [BorelSpace α] [NoMaxOrder α] (μ ν : Measure α) [IsLocallyFiniteMeasure μ]
    (h : ∀ ⦃a b⦄, a < b → μ (Ico a b) = ν (Ico a b)) : μ = ν :=
  μ.ext_of_Ico' ν (fun _ _ _ => measure_Ico_lt_top.ne) h
#align measure_theory.measure.ext_of_Ico MeasureTheory.Measure.ext_of_Ico

/-- Two measures which are finite on closed-open intervals are equal if they agree on all
open-closed intervals. -/
theorem ext_of_Ioc {α : Type*} [TopologicalSpace α] {_m : MeasurableSpace α}
    [SecondCountableTopology α] [ConditionallyCompleteLinearOrder α] [OrderTopology α]
    [BorelSpace α] [NoMinOrder α] (μ ν : Measure α) [IsLocallyFiniteMeasure μ]
    (h : ∀ ⦃a b⦄, a < b → μ (Ioc a b) = ν (Ioc a b)) : μ = ν :=
  μ.ext_of_Ioc' ν (fun _ _ _ => measure_Ioc_lt_top.ne) h
#align measure_theory.measure.ext_of_Ioc MeasureTheory.Measure.ext_of_Ioc

/-- Two finite measures on a Borel space are equal if they agree on all left-infinite right-closed
intervals. -/
theorem ext_of_Iic {α : Type*} [TopologicalSpace α] {m : MeasurableSpace α}
    [SecondCountableTopology α] [LinearOrder α] [OrderTopology α] [BorelSpace α] (μ ν : Measure α)
    [IsFiniteMeasure μ] (h : ∀ a, μ (Iic a) = ν (Iic a)) : μ = ν := by
  refine' ext_of_Ioc_finite μ ν _ fun a b hlt => _
  · rcases exists_countable_dense_bot_top α with ⟨s, hsc, hsd, -, hst⟩
    have : DirectedOn (· ≤ ·) s := directedOn_iff_directed.2 (Subtype.mono_coe _).directed_le
    simp only [← biSup_measure_Iic hsc (hsd.exists_ge' hst) this, h]
  rw [← Iic_diff_Iic, measure_diff (Iic_subset_Iic.2 hlt.le) measurableSet_Iic,
    measure_diff (Iic_subset_Iic.2 hlt.le) measurableSet_Iic, h a, h b]
  · rw [← h a]
    exact (measure_lt_top μ _).ne
  · exact (measure_lt_top μ _).ne
#align measure_theory.measure.ext_of_Iic MeasureTheory.Measure.ext_of_Iic

/-- Two finite measures on a Borel space are equal if they agree on all left-closed right-infinite
intervals. -/
theorem ext_of_Ici {α : Type*} [TopologicalSpace α] {m : MeasurableSpace α}
    [SecondCountableTopology α] [LinearOrder α] [OrderTopology α] [BorelSpace α] (μ ν : Measure α)
    [IsFiniteMeasure μ] (h : ∀ a, μ (Ici a) = ν (Ici a)) : μ = ν :=
  @ext_of_Iic αᵒᵈ _ _ _ _ _ ‹_› _ _ _ h
#align measure_theory.measure.ext_of_Ici MeasureTheory.Measure.ext_of_Ici

end MeasureTheory.Measure

@[measurability]
theorem measurableSet_uIcc : MeasurableSet (uIcc a b) :=
  measurableSet_Icc
#align measurable_set_uIcc measurableSet_uIcc

@[measurability]
theorem measurableSet_uIoc : MeasurableSet (uIoc a b) :=
  measurableSet_Ioc
#align measurable_set_uIoc measurableSet_uIoc

variable [SecondCountableTopology α]

@[measurability]
theorem Measurable.max {f g : δ → α} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => max (f a) (g a) := by
  simpa only [max_def'] using hf.piecewise (measurableSet_le hg hf) hg
#align measurable.max Measurable.max

@[measurability]
nonrec theorem AEMeasurable.max {f g : δ → α} {μ : Measure δ} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) : AEMeasurable (fun a => max (f a) (g a)) μ :=
  ⟨fun a => max (hf.mk f a) (hg.mk g a), hf.measurable_mk.max hg.measurable_mk,
    EventuallyEq.comp₂ hf.ae_eq_mk _ hg.ae_eq_mk⟩
#align ae_measurable.max AEMeasurable.max

@[measurability]
theorem Measurable.min {f g : δ → α} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => min (f a) (g a) := by
  simpa only [min_def] using hf.piecewise (measurableSet_le hf hg) hg
#align measurable.min Measurable.min

@[measurability]
nonrec theorem AEMeasurable.min {f g : δ → α} {μ : Measure δ} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) : AEMeasurable (fun a => min (f a) (g a)) μ :=
  ⟨fun a => min (hf.mk f a) (hg.mk g a), hf.measurable_mk.min hg.measurable_mk,
    EventuallyEq.comp₂ hf.ae_eq_mk _ hg.ae_eq_mk⟩
#align ae_measurable.min AEMeasurable.min

end LinearOrder


section Lattice

variable [TopologicalSpace γ] [MeasurableSpace γ] [BorelSpace γ]

instance (priority := 100) ContinuousSup.measurableSup [Sup γ] [ContinuousSup γ] :
    MeasurableSup γ where
  measurable_const_sup _ := (continuous_const.sup continuous_id).measurable
  measurable_sup_const _ := (continuous_id.sup continuous_const).measurable
#align has_continuous_sup.has_measurable_sup ContinuousSup.measurableSup

instance (priority := 100) ContinuousSup.measurableSup₂ [SecondCountableTopology γ] [Sup γ]
    [ContinuousSup γ] : MeasurableSup₂ γ :=
  ⟨continuous_sup.measurable⟩
#align has_continuous_sup.has_measurable_sup₂ ContinuousSup.measurableSup₂

instance (priority := 100) ContinuousInf.measurableInf [Inf γ] [ContinuousInf γ] :
    MeasurableInf γ where
  measurable_const_inf _ := (continuous_const.inf continuous_id).measurable
  measurable_inf_const _ := (continuous_id.inf continuous_const).measurable
#align has_continuous_inf.has_measurable_inf ContinuousInf.measurableInf

instance (priority := 100) ContinuousInf.measurableInf₂ [SecondCountableTopology γ] [Inf γ]
    [ContinuousInf γ] : MeasurableInf₂ γ :=
  ⟨continuous_inf.measurable⟩
#align has_continuous_inf.has_measurable_inf₂ ContinuousInf.measurableInf₂

end Lattice

end Orders

section BorelSpace

variable [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
variable [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
variable [MeasurableSpace δ]

section LinearOrder

variable [LinearOrder α] [OrderTopology α] [SecondCountableTopology α]

theorem measurable_of_Iio {f : δ → α} (hf : ∀ x, MeasurableSet (f ⁻¹' Iio x)) : Measurable f := by
  convert measurable_generateFrom (α := δ) _
  · exact BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iio _)
  · rintro _ ⟨x, rfl⟩; exact hf x
#align measurable_of_Iio measurable_of_Iio

theorem UpperSemicontinuous.measurable [TopologicalSpace δ] [OpensMeasurableSpace δ] {f : δ → α}
    (hf : UpperSemicontinuous f) : Measurable f :=
  measurable_of_Iio fun y => (hf.isOpen_preimage y).measurableSet
#align upper_semicontinuous.measurable UpperSemicontinuous.measurable

theorem measurable_of_Ioi {f : δ → α} (hf : ∀ x, MeasurableSet (f ⁻¹' Ioi x)) : Measurable f := by
  convert measurable_generateFrom (α := δ) _
  · exact BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioi _)
  · rintro _ ⟨x, rfl⟩; exact hf x
#align measurable_of_Ioi measurable_of_Ioi

theorem LowerSemicontinuous.measurable [TopologicalSpace δ] [OpensMeasurableSpace δ] {f : δ → α}
    (hf : LowerSemicontinuous f) : Measurable f :=
  measurable_of_Ioi fun y => (hf.isOpen_preimage y).measurableSet
#align lower_semicontinuous.measurable LowerSemicontinuous.measurable

theorem measurable_of_Iic {f : δ → α} (hf : ∀ x, MeasurableSet (f ⁻¹' Iic x)) : Measurable f := by
  apply measurable_of_Ioi
  simp_rw [← compl_Iic, preimage_compl, MeasurableSet.compl_iff]
  assumption
#align measurable_of_Iic measurable_of_Iic

theorem measurable_of_Ici {f : δ → α} (hf : ∀ x, MeasurableSet (f ⁻¹' Ici x)) : Measurable f := by
  apply measurable_of_Iio
  simp_rw [← compl_Ici, preimage_compl, MeasurableSet.compl_iff]
  assumption
#align measurable_of_Ici measurable_of_Ici

/-- If a function is the least upper bound of countably many measurable functions,
then it is measurable. -/
theorem Measurable.isLUB {ι} [Countable ι] {f : ι → δ → α} {g : δ → α} (hf : ∀ i, Measurable (f i))
    (hg : ∀ b, IsLUB { a | ∃ i, f i b = a } (g b)) : Measurable g := by
  change ∀ b, IsLUB (range fun i => f i b) (g b) at hg
  rw [‹BorelSpace α›.measurable_eq, borel_eq_generateFrom_Ioi α]
  apply measurable_generateFrom
  rintro _ ⟨a, rfl⟩
  simp_rw [Set.preimage, mem_Ioi, lt_isLUB_iff (hg _), exists_range_iff, setOf_exists]
  exact MeasurableSet.iUnion fun i => hf i (isOpen_lt' _).measurableSet
#align measurable.is_lub Measurable.isLUB

/-- If a function is the least upper bound of countably many measurable functions on a measurable
set `s`, and coincides with a measurable function outside of `s`, then it is measurable. -/
theorem Measurable.isLUB_of_mem {ι} [Countable ι] {f : ι → δ → α} {g g' : δ → α}
    (hf : ∀ i, Measurable (f i))
    {s : Set δ} (hs : MeasurableSet s) (hg : ∀ b ∈ s, IsLUB { a | ∃ i, f i b = a } (g b))
    (hg' : EqOn g g' sᶜ) (g'_meas : Measurable g') : Measurable g := by
  rcases isEmpty_or_nonempty ι with hι|⟨⟨i⟩⟩
  · rcases eq_empty_or_nonempty s with rfl|⟨x, hx⟩
    · convert g'_meas
      rwa [compl_empty, eqOn_univ] at hg'
    · have A : ∀ b ∈ s, IsBot (g b) := by simpa using hg
      have B : ∀ b ∈ s, g b = g x := by
        intro b hb
        apply le_antisymm (A b hb (g x)) (A x hx (g b))
      have : g = s.piecewise (fun _y ↦ g x) g' := by
        ext b
        by_cases hb : b ∈ s
        · simp [hb, B]
        · simp [hb, hg' hb]
      rw [this]
      exact Measurable.piecewise hs measurable_const g'_meas
  · let f' : ι → δ → α := fun i ↦ s.piecewise (f i) g'
    suffices ∀ b, IsLUB { a | ∃ i, f' i b = a } (g b) from
      Measurable.isLUB (fun i ↦ Measurable.piecewise hs (hf i) g'_meas) this
    intro b
    by_cases hb : b ∈ s
    · have A : ∀ i, f' i b = f i b := fun i ↦ by simp [f', hb]
      simpa [A] using hg b hb
    · have A : ∀ i, f' i b = g' b := fun i ↦ by simp [f', hb]
      have : {a | ∃ (_i : ι), g' b = a} = {g' b} := by
        apply Subset.antisymm
        · rintro - ⟨_j, rfl⟩
          simp only [mem_singleton_iff]
        · rintro - rfl
          exact ⟨i, rfl⟩
      simp [A, this, hg' hb, isLUB_singleton]

theorem AEMeasurable.isLUB {ι} {μ : Measure δ} [Countable ι] {f : ι → δ → α} {g : δ → α}
    (hf : ∀ i, AEMeasurable (f i) μ) (hg : ∀ᵐ b ∂μ, IsLUB { a | ∃ i, f i b = a } (g b)) :
    AEMeasurable g μ := by
  nontriviality α
  haveI hα : Nonempty α := inferInstance
  cases' isEmpty_or_nonempty ι with hι hι
  · simp only [IsEmpty.exists_iff, setOf_false, isLUB_empty_iff] at hg
    exact aemeasurable_const' (hg.mono fun a ha => hg.mono fun b hb => (ha _).antisymm (hb _))
  let p : δ → (ι → α) → Prop := fun x f' => IsLUB { a | ∃ i, f' i = a } (g x)
  let g_seq := (aeSeqSet hf p).piecewise g fun _ => hα.some
  have hg_seq : ∀ b, IsLUB { a | ∃ i, aeSeq hf p i b = a } (g_seq b) := by
    intro b
    simp only [g_seq, aeSeq, Set.piecewise]
    split_ifs with h
    · have h_set_eq : { a : α | ∃ i : ι, (hf i).mk (f i) b = a } =
        { a : α | ∃ i : ι, f i b = a } := by
        ext x
        simp_rw [Set.mem_setOf_eq, aeSeq.mk_eq_fun_of_mem_aeSeqSet hf h]
      rw [h_set_eq]
      exact aeSeq.fun_prop_of_mem_aeSeqSet hf h
    · exact IsGreatest.isLUB ⟨(@exists_const (hα.some = hα.some) ι _).2 rfl, fun x ⟨i, hi⟩ => hi.ge⟩
  refine' ⟨g_seq, Measurable.isLUB (aeSeq.measurable hf p) hg_seq, _⟩
  exact
    (ite_ae_eq_of_measure_compl_zero g (fun _ => hα.some) (aeSeqSet hf p)
        (aeSeq.measure_compl_aeSeqSet_eq_zero hf hg)).symm
#align ae_measurable.is_lub AEMeasurable.isLUB

/-- If a function is the greatest lower bound of countably many measurable functions,
then it is measurable. -/
theorem Measurable.isGLB {ι} [Countable ι] {f : ι → δ → α} {g : δ → α} (hf : ∀ i, Measurable (f i))
    (hg : ∀ b, IsGLB { a | ∃ i, f i b = a } (g b)) : Measurable g :=
  Measurable.isLUB (α := αᵒᵈ) hf hg
#align measurable.is_glb Measurable.isGLB

/-- If a function is the greatest lower bound of countably many measurable functions on a measurable
set `s`, and coincides with a measurable function outside of `s`, then it is measurable. -/
theorem Measurable.isGLB_of_mem {ι} [Countable ι] {f : ι → δ → α} {g g' : δ → α}
    (hf : ∀ i, Measurable (f i))
    {s : Set δ} (hs : MeasurableSet s) (hg : ∀ b ∈ s, IsGLB { a | ∃ i, f i b = a } (g b))
    (hg' : EqOn g g' sᶜ) (g'_meas : Measurable g') : Measurable g :=
  Measurable.isLUB_of_mem (α := αᵒᵈ) hf hs hg hg'  g'_meas

theorem AEMeasurable.isGLB {ι} {μ : Measure δ} [Countable ι] {f : ι → δ → α} {g : δ → α}
    (hf : ∀ i, AEMeasurable (f i) μ) (hg : ∀ᵐ b ∂μ, IsGLB { a | ∃ i, f i b = a } (g b)) :
    AEMeasurable g μ :=
  AEMeasurable.isLUB (α := αᵒᵈ) hf hg
#align ae_measurable.is_glb AEMeasurable.isGLB

protected theorem Monotone.measurable [LinearOrder β] [OrderClosedTopology β] {f : β → α}
    (hf : Monotone f) : Measurable f :=
  suffices h : ∀ x, OrdConnected (f ⁻¹' Ioi x) from measurable_of_Ioi fun x => (h x).measurableSet
  fun _ => ordConnected_def.mpr fun _a ha _ _ _c hc => lt_of_lt_of_le ha (hf hc.1)
#align monotone.measurable Monotone.measurable

theorem aemeasurable_restrict_of_monotoneOn [LinearOrder β] [OrderClosedTopology β] {μ : Measure β}
    {s : Set β} (hs : MeasurableSet s) {f : β → α} (hf : MonotoneOn f s) :
    AEMeasurable f (μ.restrict s) :=
  have : Monotone (f ∘ (↑) : s → α) := fun ⟨x, hx⟩ ⟨y, hy⟩ => fun (hxy : x ≤ y) => hf hx hy hxy
  aemeasurable_restrict_of_measurable_subtype hs this.measurable
#align ae_measurable_restrict_of_monotone_on aemeasurable_restrict_of_monotoneOn

protected theorem Antitone.measurable [LinearOrder β] [OrderClosedTopology β] {f : β → α}
    (hf : Antitone f) : Measurable f :=
  @Monotone.measurable αᵒᵈ β _ _ ‹_› _ _ _ _ _ ‹_› _ _ _ hf
#align antitone.measurable Antitone.measurable

theorem aemeasurable_restrict_of_antitoneOn [LinearOrder β] [OrderClosedTopology β] {μ : Measure β}
    {s : Set β} (hs : MeasurableSet s) {f : β → α} (hf : AntitoneOn f s) :
    AEMeasurable f (μ.restrict s) :=
  @aemeasurable_restrict_of_monotoneOn αᵒᵈ β _ _ ‹_› _ _ _ _ _ ‹_› _ _ _ _ hs _ hf
#align ae_measurable_restrict_of_antitone_on aemeasurable_restrict_of_antitoneOn

theorem measurableSet_of_mem_nhdsWithin_Ioi_aux {s : Set α} (h : ∀ x ∈ s, s ∈ 𝓝[>] x)
    (h' : ∀ x ∈ s, ∃ y, x < y) : MeasurableSet s := by
  choose! M hM using h'
  suffices H : (s \ interior s).Countable by
    have : s = interior s ∪ s \ interior s := by rw [union_diff_cancel interior_subset]
    rw [this]
    exact isOpen_interior.measurableSet.union H.measurableSet
  have A : ∀ x ∈ s, ∃ y ∈ Ioi x, Ioo x y ⊆ s := fun x hx =>
    (mem_nhdsWithin_Ioi_iff_exists_Ioo_subset' (hM x hx)).1 (h x hx)
  choose! y hy h'y using A
  have B : Set.PairwiseDisjoint (s \ interior s) fun x => Ioo x (y x) := by
    intro x hx x' hx' hxx'
    rcases lt_or_gt_of_ne hxx' with (h' | h')
    · refine disjoint_left.2 fun z hz h'z => ?_
      have : x' ∈ interior s :=
        mem_interior.2 ⟨Ioo x (y x), h'y _ hx.1, isOpen_Ioo, ⟨h', h'z.1.trans hz.2⟩⟩
      exact False.elim (hx'.2 this)
    · refine disjoint_left.2 fun z hz h'z => ?_
      have : x ∈ interior s :=
        mem_interior.2 ⟨Ioo x' (y x'), h'y _ hx'.1, isOpen_Ioo, ⟨h', hz.1.trans h'z.2⟩⟩
      exact False.elim (hx.2 this)
  exact B.countable_of_Ioo fun x hx => hy x hx.1
#align measurable_set_of_mem_nhds_within_Ioi_aux measurableSet_of_mem_nhdsWithin_Ioi_aux

/-- If a set is a right-neighborhood of all of its points, then it is measurable. -/
theorem measurableSet_of_mem_nhdsWithin_Ioi {s : Set α} (h : ∀ x ∈ s, s ∈ 𝓝[>] x) :
    MeasurableSet s := by
  by_cases H : ∃ x ∈ s, IsTop x
  · rcases H with ⟨x₀, x₀s, h₀⟩
    have : s = {x₀} ∪ s \ {x₀} := by rw [union_diff_cancel (singleton_subset_iff.2 x₀s)]
    rw [this]
    refine' (measurableSet_singleton _).union _
    have A : ∀ x ∈ s \ {x₀}, x < x₀ := fun x hx => lt_of_le_of_ne (h₀ _) (by simpa using hx.2)
    refine' measurableSet_of_mem_nhdsWithin_Ioi_aux (fun x hx => _) fun x hx => ⟨x₀, A x hx⟩
    obtain ⟨u, hu, us⟩ : ∃ (u : α), u ∈ Ioi x ∧ Ioo x u ⊆ s :=
      (mem_nhdsWithin_Ioi_iff_exists_Ioo_subset' (A x hx)).1 (h x hx.1)
    refine' (mem_nhdsWithin_Ioi_iff_exists_Ioo_subset' (A x hx)).2 ⟨u, hu, fun y hy => ⟨us hy, _⟩⟩
    exact ne_of_lt (hy.2.trans_le (h₀ _))
  · apply measurableSet_of_mem_nhdsWithin_Ioi_aux h
    simp only [IsTop] at H
    push_neg at H
    exact H
#align measurable_set_of_mem_nhds_within_Ioi measurableSet_of_mem_nhdsWithin_Ioi

lemma measurableSet_bddAbove_range {ι} [Countable ι] {f : ι → δ → α} (hf : ∀ i, Measurable (f i)) :
    MeasurableSet {b | BddAbove (range (fun i ↦ f i b))} := by
  rcases isEmpty_or_nonempty α with hα|hα
  · have : ∀ b, range (fun i ↦ f i b) = ∅ := fun b ↦ eq_empty_of_isEmpty _
    simp [this]
  have A : ∀ (i : ι) (c : α), MeasurableSet {x | f i x ≤ c} := by
    intro i c
    exact measurableSet_le (hf i) measurable_const
  have B : ∀ (c : α), MeasurableSet {x | ∀ i, f i x ≤ c} := by
    intro c
    rw [setOf_forall]
    exact MeasurableSet.iInter (fun i ↦ A i c)
  obtain ⟨u, hu⟩ : ∃ (u : ℕ → α), Tendsto u atTop atTop := exists_seq_tendsto (atTop : Filter α)
  have : {b | BddAbove (range (fun i ↦ f i b))} = {x | ∃ n, ∀ i, f i x ≤ u n} := by
    apply Subset.antisymm
    · rintro x ⟨c, hc⟩
      obtain ⟨n, hn⟩ : ∃ n, c ≤ u n := (tendsto_atTop.1 hu c).exists
      exact ⟨n, fun i ↦ (hc ((mem_range_self i))).trans hn⟩
    · rintro x ⟨n, hn⟩
      refine ⟨u n, ?_⟩
      rintro - ⟨i, rfl⟩
      exact hn i
  rw [this, setOf_exists]
  exact MeasurableSet.iUnion (fun n ↦ B (u n))

lemma measurableSet_bddBelow_range {ι} [Countable ι] {f : ι → δ → α} (hf : ∀ i, Measurable (f i)) :
    MeasurableSet {b | BddBelow (range (fun i ↦ f i b))} :=
  measurableSet_bddAbove_range (α := αᵒᵈ) hf

end LinearOrder

@[measurability]
theorem Measurable.iSup_Prop {α} [MeasurableSpace α] [ConditionallyCompleteLattice α]
    (p : Prop) {f : δ → α} (hf : Measurable f) : Measurable fun b => ⨆ _ : p, f b := by
  simp_rw [ciSup_eq_ite]
  split_ifs with h
  · exact hf
  · exact measurable_const
#align measurable.supr_Prop Measurable.iSup_Prop

@[measurability]
theorem Measurable.iInf_Prop {α} [MeasurableSpace α] [ConditionallyCompleteLattice α]
    (p : Prop) {f : δ → α} (hf : Measurable f) : Measurable fun b => ⨅ _ : p, f b := by
  simp_rw [ciInf_eq_ite]
  split_ifs with h
  · exact hf
  · exact measurable_const
#align measurable.infi_Prop Measurable.iInf_Prop

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] [OrderTopology α] [SecondCountableTopology α]

@[measurability]
theorem measurable_iSup {ι} [Countable ι] {f : ι → δ → α} (hf : ∀ i, Measurable (f i)) :
    Measurable (fun b ↦ ⨆ i, f i b) := by
  rcases isEmpty_or_nonempty ι with hι|hι
  · simp [iSup_of_empty']
  have A : MeasurableSet {b | BddAbove (range (fun i ↦ f i b))} :=
    measurableSet_bddAbove_range hf
  have : Measurable (fun (_b : δ) ↦ sSup (∅ : Set α)) := measurable_const
  apply Measurable.isLUB_of_mem hf A _ _ this
  · rintro b ⟨c, hc⟩
    apply isLUB_ciSup
    refine ⟨c, ?_⟩
    rintro d ⟨i, rfl⟩
    exact hc (mem_range_self i)
  · intro b hb
    apply csSup_of_not_bddAbove
    exact hb

@[measurability]
theorem aemeasurable_iSup {ι} {μ : Measure δ} [Countable ι] {f : ι → δ → α}
    (hf : ∀ i, AEMeasurable (f i) μ) : AEMeasurable (fun b => ⨆ i, f i b) μ := by
  refine ⟨fun b ↦ ⨆ i, (hf i).mk (f i) b, measurable_iSup (fun i ↦ (hf i).measurable_mk), ?_⟩
  filter_upwards [ae_all_iff.2 (fun i ↦ (hf i).ae_eq_mk)] with b hb using by simp [hb]
#align ae_measurable_supr aemeasurable_iSup

@[measurability]
theorem measurable_iInf {ι} [Countable ι] {f : ι → δ → α} (hf : ∀ i, Measurable (f i)) :
    Measurable fun b => ⨅ i, f i b :=
  measurable_iSup (α := αᵒᵈ) hf
#align measurable_infi measurable_iInf

@[measurability]
theorem aemeasurable_iInf {ι} {μ : Measure δ} [Countable ι] {f : ι → δ → α}
    (hf : ∀ i, AEMeasurable (f i) μ) : AEMeasurable (fun b => ⨅ i, f i b) μ :=
  aemeasurable_iSup (α := αᵒᵈ) hf
#align ae_measurable_infi aemeasurable_iInf

theorem measurable_sSup {ι} {f : ι → δ → α} {s : Set ι} (hs : s.Countable)
    (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable fun x => sSup ((fun i => f i x) '' s) := by
  have : Countable ↑s := countable_coe_iff.2 hs
  convert measurable_iSup (f := (fun (i : s) ↦ f i)) (fun i ↦ hf i i.2) using 1
  ext b
  congr
  exact image_eq_range (fun i ↦ f i b) s
#align measurable_cSup measurable_sSup

theorem measurable_sInf {ι} {f : ι → δ → α} {s : Set ι} (hs : s.Countable)
    (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable fun x => sInf ((fun i => f i x) '' s) :=
  measurable_sSup (α := αᵒᵈ) hs hf
#align measurable_cInf measurable_sInf

theorem measurable_biSup {ι} (s : Set ι) {f : ι → δ → α} (hs : s.Countable)
    (hf : ∀ i ∈ s, Measurable (f i)) : Measurable fun b => ⨆ i ∈ s, f i b := by
  haveI : Encodable s := hs.toEncodable
  by_cases H : ∀ i, i ∈ s
  · have : ∀ b, ⨆ i ∈ s, f i b = ⨆ (i : s), f i b :=
      fun b ↦ cbiSup_eq_of_forall (f := fun i ↦ f i b) H
    simp only [this]
    exact measurable_iSup (fun (i : s) ↦ hf i i.2)
  · have : ∀ b, ⨆ i ∈ s, f i b = (⨆ (i : s), f i b) ⊔ sSup ∅ :=
      fun b ↦ cbiSup_eq_of_not_forall (f := fun i ↦ f i b) H
    simp only [this]
    apply Measurable.sup _ measurable_const
    exact measurable_iSup (fun (i : s) ↦ hf i i.2)
#align measurable_bsupr measurable_biSup

theorem aemeasurable_biSup {ι} {μ : Measure δ} (s : Set ι) {f : ι → δ → α} (hs : s.Countable)
    (hf : ∀ i ∈ s, AEMeasurable (f i) μ) : AEMeasurable (fun b => ⨆ i ∈ s, f i b) μ := by
  let g : ι → δ → α := fun i ↦ if hi : i ∈ s then (hf i hi).mk (f i) else fun _b ↦ sSup ∅
  have : ∀ i ∈ s, Measurable (g i) := by
    intro i hi
    simpa [g, hi] using (hf i hi).measurable_mk
  refine ⟨fun b ↦ ⨆ (i) (_ : i ∈ s), g i b, measurable_biSup s hs this, ?_⟩
  have : ∀ i ∈ s, ∀ᵐ b ∂μ, f i b = g i b :=
    fun i hi ↦ by simpa [g, hi] using (hf i hi).ae_eq_mk
  filter_upwards [(ae_ball_iff hs).2 this] with b hb
  exact iSup_congr fun i => iSup_congr (hb i)
#align ae_measurable_bsupr aemeasurable_biSup

theorem measurable_biInf {ι} (s : Set ι) {f : ι → δ → α} (hs : s.Countable)
    (hf : ∀ i ∈ s, Measurable (f i)) : Measurable fun b => ⨅ i ∈ s, f i b :=
  measurable_biSup (α := αᵒᵈ) s hs hf
#align measurable_binfi measurable_biInf

theorem aemeasurable_biInf {ι} {μ : Measure δ} (s : Set ι) {f : ι → δ → α} (hs : s.Countable)
    (hf : ∀ i ∈ s, AEMeasurable (f i) μ) : AEMeasurable (fun b => ⨅ i ∈ s, f i b) μ :=
  aemeasurable_biSup (α := αᵒᵈ) s hs hf
#align ae_measurable_binfi aemeasurable_biInf

/-- `liminf` over a general filter is measurable. See `measurable_liminf` for the version over `ℕ`.
-/
theorem measurable_liminf' {ι ι'} {f : ι → δ → α} {v : Filter ι} (hf : ∀ i, Measurable (f i))
    {p : ι' → Prop} {s : ι' → Set ι} (hv : v.HasCountableBasis p s) (hs : ∀ j, (s j).Countable) :
    Measurable fun x => liminf (f · x) v := by
  /- We would like to write the liminf as `⨆ (j : Subtype p), ⨅ (i : s j), f i x`, as the
  measurability would follow from the measurability of infs and sups. Unfortunately, this is not
  true in general conditionally complete linear orders because of issues with empty sets or sets
  which are not bounded above or below. A slightly more complicated expression for the liminf,
  valid in general, is given in `Filter.HasBasis.liminf_eq_ite`. This expression, built from
  `if ... then ... else` and infs and sups, can be readily checked to be measurable. -/
  have : Countable (Subtype p) := hv.countable
  rcases isEmpty_or_nonempty (Subtype p) with hp|hp
  · simp [hv.liminf_eq_sSup_iUnion_iInter]
  by_cases H : ∃ (j : Subtype p), s j = ∅
  · simp_rw [hv.liminf_eq_ite, if_pos H, measurable_const]
  simp_rw [hv.liminf_eq_ite, if_neg H]
  have : ∀ i, Countable (s i) := fun i ↦ countable_coe_iff.2 (hs i)
  let m : Subtype p → Set δ := fun j ↦ {x | BddBelow (range (fun (i : s j) ↦ f i x))}
  have m_meas : ∀ j, MeasurableSet (m j) :=
    fun j ↦ measurableSet_bddBelow_range (fun (i : s j) ↦ hf i)
  have mc_meas : MeasurableSet {x | ∀ (j : Subtype p), x ∉ m j} := by
    rw [setOf_forall]
    exact MeasurableSet.iInter (fun j ↦ (m_meas j).compl)
  apply Measurable.piecewise mc_meas measurable_const
  apply measurable_iSup (fun j ↦ ?_)
  let reparam : δ → Subtype p → Subtype p := fun x ↦ liminf_reparam (fun i ↦ f i x) s p
  let F0 : Subtype p → δ → α := fun j x ↦ ⨅ (i : s j), f i x
  have F0_meas : ∀ j, Measurable (F0 j) := fun j ↦ measurable_iInf (fun (i : s j) ↦ hf i)
  set F1 : δ → α := fun x ↦ F0 (reparam x j) x with hF1
  change Measurable F1
  let g : ℕ → Subtype p := Classical.choose (exists_surjective_nat (Subtype p))
  have Z : ∀ x, ∃ n, x ∈ m (g n) ∨ ∀ k, x ∉ m k := by
    intro x
    by_cases H : ∃ k, x ∈ m k
    · rcases H with ⟨k, hk⟩
      rcases Classical.choose_spec (exists_surjective_nat (Subtype p)) k with ⟨n, rfl⟩
      exact ⟨n, Or.inl hk⟩
    · push_neg at H
      exact ⟨0, Or.inr H⟩
  have : F1 = fun x ↦ if x ∈ m j then F0 j x else F0 (g (Nat.find (Z x))) x := by
    ext x
    have A : reparam x j = if x ∈ m j then j else g (Nat.find (Z x)) := rfl
    split_ifs with hjx
    · have : reparam x j = j := by rw [A, if_pos hjx]
      simp only [hF1, this]
    · have : reparam x j = g (Nat.find (Z x)) := by rw [A, if_neg hjx]
      simp only [hF1, this]
  rw [this]
  apply Measurable.piecewise (m_meas j) (F0_meas j)
  apply Measurable.find (fun n ↦ F0_meas (g n)) (fun n ↦ ?_)
  exact (m_meas (g n)).union mc_meas
#align measurable_liminf' measurable_liminf'

/-- `limsup` over a general filter is measurable. See `measurable_limsup` for the version over `ℕ`.
-/
theorem measurable_limsup' {ι ι'} {f : ι → δ → α} {u : Filter ι} (hf : ∀ i, Measurable (f i))
    {p : ι' → Prop} {s : ι' → Set ι} (hu : u.HasCountableBasis p s) (hs : ∀ i, (s i).Countable) :
    Measurable fun x => limsup (fun i => f i x) u :=
  measurable_liminf' (α := αᵒᵈ) hf hu hs
#align measurable_limsup' measurable_limsup'

/-- `liminf` over `ℕ` is measurable. See `measurable_liminf'` for a version with a general filter.
-/
@[measurability]
theorem measurable_liminf {f : ℕ → δ → α} (hf : ∀ i, Measurable (f i)) :
    Measurable fun x => liminf (fun i => f i x) atTop :=
  measurable_liminf' hf atTop_countable_basis fun _ => to_countable _
#align measurable_liminf measurable_liminf

/-- `limsup` over `ℕ` is measurable. See `measurable_limsup'` for a version with a general filter.
-/
@[measurability]
theorem measurable_limsup {f : ℕ → δ → α} (hf : ∀ i, Measurable (f i)) :
    Measurable fun x => limsup (fun i => f i x) atTop :=
  measurable_limsup' hf atTop_countable_basis fun _ => to_countable _
#align measurable_limsup measurable_limsup

end ConditionallyCompleteLinearOrder

/-- Convert a `Homeomorph` to a `MeasurableEquiv`. -/
def Homemorph.toMeasurableEquiv (h : α ≃ₜ β) : α ≃ᵐ β where
  toEquiv := h.toEquiv
  measurable_toFun := h.continuous_toFun.measurable
  measurable_invFun := h.continuous_invFun.measurable
#align homemorph.to_measurable_equiv Homemorph.toMeasurableEquiv

protected theorem IsFiniteMeasureOnCompacts.map (μ : Measure α) [IsFiniteMeasureOnCompacts μ]
    (f : α ≃ₜ β) : IsFiniteMeasureOnCompacts (Measure.map f μ) := by
  refine ⟨fun K hK ↦ ?_⟩
  rw [← Homeomorph.toMeasurableEquiv_coe, MeasurableEquiv.map_apply]
  exact IsCompact.measure_lt_top (f.isCompact_preimage.2 hK)
#align is_finite_measure_on_compacts.map IsFiniteMeasureOnCompacts.map

end BorelSpace

instance Empty.borelSpace : BorelSpace Empty :=
  ⟨borel_eq_top_of_discrete.symm⟩
#align empty.borel_space Empty.borelSpace

instance Unit.borelSpace : BorelSpace Unit :=
  ⟨borel_eq_top_of_discrete.symm⟩
#align unit.borel_space Unit.borelSpace

instance Bool.borelSpace : BorelSpace Bool :=
  ⟨borel_eq_top_of_discrete.symm⟩
#align bool.borel_space Bool.borelSpace

instance Nat.borelSpace : BorelSpace ℕ :=
  ⟨borel_eq_top_of_discrete.symm⟩
#align nat.borel_space Nat.borelSpace

instance Int.borelSpace : BorelSpace ℤ :=
  ⟨borel_eq_top_of_discrete.symm⟩
#align int.borel_space Int.borelSpace

instance Rat.borelSpace : BorelSpace ℚ :=
  ⟨borel_eq_top_of_countable.symm⟩
#align rat.borel_space Rat.borelSpace

/- Instances on `Real` and `Complex` are special cases of `RCLike` but without these instances,
Lean fails to prove `BorelSpace (ι → ℝ)`, so we leave them here. -/
instance Real.measurableSpace : MeasurableSpace ℝ :=
  borel ℝ
#align real.measurable_space Real.measurableSpace

instance Real.borelSpace : BorelSpace ℝ :=
  ⟨rfl⟩
#align real.borel_space Real.borelSpace

instance NNReal.measurableSpace : MeasurableSpace ℝ≥0 :=
  Subtype.instMeasurableSpace
#align nnreal.measurable_space NNReal.measurableSpace

instance NNReal.borelSpace : BorelSpace ℝ≥0 :=
  Subtype.borelSpace _
#align nnreal.borel_space NNReal.borelSpace

instance ENNReal.measurableSpace : MeasurableSpace ℝ≥0∞ :=
  borel ℝ≥0∞
#align ennreal.measurable_space ENNReal.measurableSpace

instance ENNReal.borelSpace : BorelSpace ℝ≥0∞ :=
  ⟨rfl⟩
#align ennreal.borel_space ENNReal.borelSpace

instance EReal.measurableSpace : MeasurableSpace EReal :=
  borel EReal
#align ereal.measurable_space EReal.measurableSpace

instance EReal.borelSpace : BorelSpace EReal :=
  ⟨rfl⟩
#align ereal.borel_space EReal.borelSpace

/-- One can cut out `ℝ≥0∞` into the sets `{0}`, `Ico (t^n) (t^(n+1))` for `n : ℤ` and `{∞}`. This
gives a way to compute the measure of a set in terms of sets on which a given function `f` does not
fluctuate by more than `t`. -/
theorem measure_eq_measure_preimage_add_measure_tsum_Ico_zpow {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f : α → ℝ≥0∞} (hf : Measurable f) {s : Set α} (hs : MeasurableSet s)
    {t : ℝ≥0} (ht : 1 < t) :
    μ s =
      μ (s ∩ f ⁻¹' {0}) + μ (s ∩ f ⁻¹' {∞}) +
      ∑' n : ℤ, μ (s ∩ f ⁻¹' Ico ((t : ℝ≥0∞) ^ n) ((t : ℝ≥0∞) ^ (n + 1))) := by
  have A : μ s = μ (s ∩ f ⁻¹' {0}) + μ (s ∩ f ⁻¹' Ioi 0) := by
    rw [← measure_union]
    · rw [← inter_union_distrib_left, ← preimage_union, singleton_union, Ioi_insert,
        ← _root_.bot_eq_zero, Ici_bot, preimage_univ, inter_univ]
    · exact disjoint_singleton_left.mpr not_mem_Ioi_self
        |>.preimage f |>.inter_right' s |>.inter_left' s
    · exact hs.inter (hf measurableSet_Ioi)
  have B : μ (s ∩ f ⁻¹' Ioi 0) = μ (s ∩ f ⁻¹' {∞}) + μ (s ∩ f ⁻¹' Ioo 0 ∞) := by
    rw [← measure_union]
    · rw [← inter_union_distrib_left]
      congr
      ext x
      simp only [mem_singleton_iff, mem_union, mem_Ioo, mem_Ioi, mem_preimage]
      obtain (H | H) : f x = ∞ ∨ f x < ∞ := eq_or_lt_of_le le_top
      · simp only [H, eq_self_iff_true, or_false_iff, ENNReal.zero_lt_top, not_top_lt, and_false]
      · simp only [H, H.ne, and_true_iff, false_or_iff]
    · refine disjoint_left.2 fun x hx h'x => ?_
      have : f x < ∞ := h'x.2.2
      exact lt_irrefl _ (this.trans_le (le_of_eq hx.2.symm))
    · exact hs.inter (hf measurableSet_Ioo)
  have C : μ (s ∩ f ⁻¹' Ioo 0 ∞) =
      ∑' n : ℤ, μ (s ∩ f ⁻¹' Ico ((t : ℝ≥0∞) ^ n) ((t : ℝ≥0∞) ^ (n + 1))) := by
    rw [← measure_iUnion,
      ENNReal.Ioo_zero_top_eq_iUnion_Ico_zpow (ENNReal.one_lt_coe_iff.2 ht) ENNReal.coe_ne_top,
      preimage_iUnion, inter_iUnion]
    · intro i j hij
      wlog h : i < j generalizing i j
      · exact (this hij.symm (hij.lt_or_lt.resolve_left h)).symm
      refine disjoint_left.2 fun x hx h'x => lt_irrefl (f x) ?_
      calc
        f x < (t : ℝ≥0∞) ^ (i + 1) := hx.2.2
        _ ≤ (t : ℝ≥0∞) ^ j := ENNReal.zpow_le_of_le (ENNReal.one_le_coe_iff.2 ht.le) h
        _ ≤ f x := h'x.2.1
    · intro n
      exact hs.inter (hf measurableSet_Ico)
  rw [A, B, C, add_assoc]
#align measure_eq_measure_preimage_add_measure_tsum_Ico_zpow measure_eq_measure_preimage_add_measure_tsum_Ico_zpow
