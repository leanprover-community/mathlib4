/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! # Functions integrable on a set and at a filter

We define `IntegrableOn f s μ := Integrable f (μ.restrict s)` and prove theorems like
`integrableOn_union : IntegrableOn f (s ∪ t) μ ↔ IntegrableOn f s μ ∧ IntegrableOn f t μ`.

Next we define a predicate `IntegrableAtFilter (f : α → E) (l : Filter α) (μ : Measure α)`
saying that `f` is integrable at some set `s ∈ l` and prove that a measurable function is integrable
at `l` with respect to `μ` provided that `f` is bounded above at `l ⊓ ae μ` and `μ` is finite
at `l`.

-/


noncomputable section

open Set Filter TopologicalSpace MeasureTheory Function

open scoped Topology Interval Filter ENNReal MeasureTheory

variable {α β ε ε' E F : Type*} [MeasurableSpace α]

section

variable [TopologicalSpace β] [ENorm ε] [TopologicalSpace ε]
  {l l' : Filter α} {f g : α → β} {μ ν : Measure α}

/-- A function `f` is strongly measurable at a filter `l` w.r.t. a measure `μ` if it is
ae strongly measurable w.r.t. `μ.restrict s` for some `s ∈ l`. -/
def StronglyMeasurableAtFilter (f : α → β) (l : Filter α) (μ : Measure α := by volume_tac) :=
  ∃ s ∈ l, AEStronglyMeasurable f (μ.restrict s)

@[simp]
theorem stronglyMeasurableAt_bot {f : α → β} : StronglyMeasurableAtFilter f ⊥ μ :=
  ⟨∅, mem_bot, by simp⟩

protected theorem StronglyMeasurableAtFilter.eventually (h : StronglyMeasurableAtFilter f l μ) :
    ∀ᶠ s in l.smallSets, AEStronglyMeasurable f (μ.restrict s) :=
  (eventually_smallSets' fun _ _ => AEStronglyMeasurable.mono_set).2 h

protected theorem StronglyMeasurableAtFilter.filter_mono (h : StronglyMeasurableAtFilter f l μ)
    (h' : l' ≤ l) : StronglyMeasurableAtFilter f l' μ :=
  let ⟨s, hsl, hs⟩ := h
  ⟨s, h' hsl, hs⟩

protected theorem MeasureTheory.AEStronglyMeasurable.stronglyMeasurableAtFilter
    (h : AEStronglyMeasurable f μ) : StronglyMeasurableAtFilter f l μ :=
  ⟨univ, univ_mem, by rwa [Measure.restrict_univ]⟩

theorem AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem {s}
    (h : AEStronglyMeasurable f (μ.restrict s)) (hl : s ∈ l) : StronglyMeasurableAtFilter f l μ :=
  ⟨s, hl, h⟩

@[deprecated (since := "2025-02-12")]
alias AeStronglyMeasurable.stronglyMeasurableAtFilter_of_mem :=
    AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem

protected theorem MeasureTheory.StronglyMeasurable.stronglyMeasurableAtFilter
    (h : StronglyMeasurable f) : StronglyMeasurableAtFilter f l μ :=
  h.aestronglyMeasurable.stronglyMeasurableAtFilter

end

namespace MeasureTheory

section NormedAddCommGroup

theorem HasFiniteIntegral.restrict_of_bounded [NormedAddCommGroup E] {f : α → E} {s : Set α}
    {μ : Measure α} {C} (hs : μ s < ∞) (hf : ∀ᵐ x ∂μ.restrict s, ‖f x‖ ≤ C) :
    HasFiniteIntegral f (μ.restrict s) :=
  haveI : IsFiniteMeasure (μ.restrict s) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  .of_bounded hf

@[deprecated (since := "2025-07-26")]
alias hasFiniteIntegral_restrict_of_bounded := HasFiniteIntegral.restrict_of_bounded

variable [NormedAddCommGroup E] {f g : α → ε} {s t : Set α} {μ ν : Measure α}
  [TopologicalSpace ε] [ContinuousENorm ε]

theorem HasFiniteIntegral.restrict_of_bounded_enorm {C : ℝ≥0∞} (hC : ‖C‖ₑ ≠ ∞ := by finiteness)
    (hs : μ s ≠ ∞ := by finiteness) (hf : ∀ᵐ x ∂μ.restrict s, ‖f x‖ₑ ≤ C) :
    HasFiniteIntegral f (μ.restrict s) :=
  haveI : IsFiniteMeasure (μ.restrict s) := ⟨by rw [Measure.restrict_apply_univ]; exact hs.lt_top⟩
  .of_bounded_enorm hC hf

/-- A function is `IntegrableOn` a set `s` if it is almost everywhere strongly measurable on `s`
and if the integral of its pointwise norm over `s` is less than infinity. -/
def IntegrableOn (f : α → ε) (s : Set α) (μ : Measure α := by volume_tac) : Prop :=
  Integrable f (μ.restrict s)

theorem IntegrableOn.integrable (h : IntegrableOn f s μ) : Integrable f (μ.restrict s) :=
  h

variable [TopologicalSpace ε'] [ENormedAddMonoid ε']

@[simp]
theorem integrableOn_empty : IntegrableOn f ∅ μ := by
  simp [IntegrableOn]

@[simp]
theorem integrableOn_univ : IntegrableOn f univ μ ↔ Integrable f μ := by
  rw [IntegrableOn, Measure.restrict_univ]

theorem integrableOn_zero : IntegrableOn (fun _ => (0 : ε')) s μ :=
  integrable_zero _ _ _

theorem IntegrableOn.of_measure_zero (hs : μ s = 0) : IntegrableOn f s μ := by
  simp [IntegrableOn, Measure.restrict_eq_zero.2 hs]

@[simp]
theorem integrableOn_const_iff {C : ε'} (hC : ‖C‖ₑ ≠ ∞ := by finiteness) :
    IntegrableOn (fun _ ↦ C) s μ ↔ C = 0 ∨ μ s < ∞ := by
  rw [IntegrableOn, ← enorm_eq_zero, integrable_const_iff_enorm hC, isFiniteMeasure_restrict,
    lt_top_iff_ne_top]

theorem integrableOn_const {C : ε'} (hs : μ s ≠ ∞ := by finiteness)
    (hC : ‖C‖ₑ ≠ ∞ := by finiteness) : IntegrableOn (fun _ ↦ C) s μ :=
  (integrableOn_const_iff hC).2 <| Or.inr <| lt_top_iff_ne_top.2 hs

theorem IntegrableOn.mono (h : IntegrableOn f t ν) (hs : s ⊆ t) (hμ : μ ≤ ν) : IntegrableOn f s μ :=
  h.mono_measure <| Measure.restrict_mono hs hμ

theorem IntegrableOn.mono_set (h : IntegrableOn f t μ) (hst : s ⊆ t) : IntegrableOn f s μ :=
  h.mono hst le_rfl

theorem IntegrableOn.mono_measure (h : IntegrableOn f s ν) (hμ : μ ≤ ν) : IntegrableOn f s μ :=
  h.mono (Subset.refl _) hμ

theorem IntegrableOn.mono_set_ae (h : IntegrableOn f t μ) (hst : s ≤ᵐ[μ] t) : IntegrableOn f s μ :=
  h.integrable.mono_measure <| Measure.restrict_mono_ae hst

theorem IntegrableOn.congr_set_ae (h : IntegrableOn f t μ) (hst : s =ᵐ[μ] t) : IntegrableOn f s μ :=
  h.mono_set_ae hst.le

theorem integrableOn_congr_set_ae (hst : s =ᵐ[μ] t) : IntegrableOn f s μ ↔ IntegrableOn f t μ :=
  ⟨fun h ↦ h.congr_set_ae hst.symm, fun h ↦ h.congr_set_ae hst⟩

theorem IntegrableOn.congr_fun_ae (h : IntegrableOn f s μ) (hst : f =ᵐ[μ.restrict s] g) :
    IntegrableOn g s μ :=
  Integrable.congr h hst

theorem integrableOn_congr_fun_ae (hst : f =ᵐ[μ.restrict s] g) :
    IntegrableOn f s μ ↔ IntegrableOn g s μ :=
  ⟨fun h => h.congr_fun_ae hst, fun h => h.congr_fun_ae hst.symm⟩

theorem IntegrableOn.congr_fun (h : IntegrableOn f s μ) (hst : EqOn f g s) (hs : MeasurableSet s) :
    IntegrableOn g s μ :=
  h.congr_fun_ae ((ae_restrict_iff' hs).2 (Eventually.of_forall hst))

theorem integrableOn_congr_fun (hst : EqOn f g s) (hs : MeasurableSet s) :
    IntegrableOn f s μ ↔ IntegrableOn g s μ :=
  ⟨fun h => h.congr_fun hst hs, fun h => h.congr_fun hst.symm hs⟩

theorem Integrable.integrableOn (h : Integrable f μ) : IntegrableOn f s μ := h.restrict

@[simp]
lemma IntegrableOn.of_subsingleton_codomain [Subsingleton ε'] {f : α → ε'} :
    IntegrableOn f s μ :=
  Integrable.of_subsingleton_codomain

theorem IntegrableOn.restrict (h : IntegrableOn f s μ) : IntegrableOn f s (μ.restrict t) := by
  dsimp only [IntegrableOn] at h ⊢
  exact h.mono_measure <| Measure.restrict_mono_measure Measure.restrict_le_self _

theorem IntegrableOn.inter_of_restrict (h : IntegrableOn f s (μ.restrict t)) :
    IntegrableOn f (s ∩ t) μ := by
  have := h.mono_set (inter_subset_left (t := t))
  rwa [IntegrableOn, μ.restrict_restrict_of_subset inter_subset_right] at this

lemma Integrable.piecewise {f g : α → ε'} [DecidablePred (· ∈ s)]
    (hs : MeasurableSet s) (hf : IntegrableOn f s μ) (hg : IntegrableOn g sᶜ μ) :
    Integrable (s.piecewise f g) μ := by
  rw [IntegrableOn] at hf hg
  rw [← memLp_one_iff_integrable] at hf hg ⊢
  exact MemLp.piecewise hs hf hg

theorem IntegrableOn.left_of_union (h : IntegrableOn f (s ∪ t) μ) : IntegrableOn f s μ :=
  h.mono_set subset_union_left

theorem IntegrableOn.right_of_union (h : IntegrableOn f (s ∪ t) μ) : IntegrableOn f t μ :=
  h.mono_set subset_union_right

theorem IntegrableOn.union [PseudoMetrizableSpace ε]
    (hs : IntegrableOn f s μ) (ht : IntegrableOn f t μ) :
    IntegrableOn f (s ∪ t) μ :=
  (hs.add_measure ht).mono_measure <| Measure.restrict_union_le _ _

@[simp]
theorem integrableOn_union [PseudoMetrizableSpace ε] :
    IntegrableOn f (s ∪ t) μ ↔ IntegrableOn f s μ ∧ IntegrableOn f t μ :=
  ⟨fun h => ⟨h.left_of_union, h.right_of_union⟩, fun h => h.1.union h.2⟩

@[simp]
theorem integrableOn_singleton_iff {f : α → ε'} {x : α}
    [MeasurableSingletonClass α] (hfx : ‖f x‖ₑ ≠ ⊤ := by finiteness) :
    IntegrableOn f {x} μ ↔ f x = 0 ∨ μ {x} < ∞ := by
  have : f =ᵐ[μ.restrict {x}] fun _ => f x := by
    filter_upwards [ae_restrict_mem (measurableSet_singleton x)] with _ ha
    simp only [mem_singleton_iff.1 ha]
  rw [IntegrableOn, integrable_congr this, integrable_const_iff_enorm, isFiniteMeasure_restrict,
    lt_top_iff_ne_top, enorm_eq_zero]
  exact hfx

theorem integrableOn_singleton {f : α → ε'} {x : α} [MeasurableSingletonClass α]
    (hfx : ‖f x‖ₑ ≠ ⊤ := by finiteness) (hx : μ {x} < ∞ := by finiteness) : IntegrableOn f {x} μ :=
  (integrableOn_singleton_iff hfx).mpr (Or.inr hx)

@[simp]
theorem integrableOn_finite_biUnion [PseudoMetrizableSpace ε]
    {s : Set β} (hs : s.Finite) {t : β → Set α} :
    IntegrableOn f (⋃ i ∈ s, t i) μ ↔ ∀ i ∈ s, IntegrableOn f (t i) μ := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ hf => simp [hf, or_imp, forall_and]

@[simp]
theorem integrableOn_finset_iUnion [PseudoMetrizableSpace ε] {s : Finset β} {t : β → Set α} :
    IntegrableOn f (⋃ i ∈ s, t i) μ ↔ ∀ i ∈ s, IntegrableOn f (t i) μ :=
  integrableOn_finite_biUnion s.finite_toSet

@[simp]
theorem integrableOn_finite_iUnion [PseudoMetrizableSpace ε] [Finite β] {t : β → Set α} :
    IntegrableOn f (⋃ i, t i) μ ↔ ∀ i, IntegrableOn f (t i) μ := by
  cases nonempty_fintype β
  simpa using integrableOn_finset_iUnion (f := f) (μ := μ) (s := Finset.univ) (t := t)

-- TODO: generalise this lemma and the next to enorm classes; this entails assuming that
-- f is finite on almost every element of `s`
lemma IntegrableOn.finset [MeasurableSingletonClass α] {μ : Measure α} [IsFiniteMeasure μ]
    {s : Finset α} {f : α → E} : IntegrableOn f s μ := by
  rw [← s.toSet.biUnion_of_singleton]
  simp [integrableOn_finset_iUnion, measure_lt_top]

lemma IntegrableOn.of_finite [MeasurableSingletonClass α] {μ : Measure α} [IsFiniteMeasure μ]
    {s : Set α} (hs : s.Finite) {f : α → E} : IntegrableOn f s μ := by
  simpa using IntegrableOn.finset (s := hs.toFinset)

lemma IntegrableOn.of_subsingleton [MeasurableSingletonClass α] {μ : Measure α} [IsFiniteMeasure μ]
    {s : Set α} (hs : s.Subsingleton) {f : α → E} :
    IntegrableOn f s μ :=
  .of_finite hs.finite

theorem IntegrableOn.add_measure [PseudoMetrizableSpace ε]
    (hμ : IntegrableOn f s μ) (hν : IntegrableOn f s ν) :
    IntegrableOn f s (μ + ν) := by
  delta IntegrableOn; rw [Measure.restrict_add]; exact hμ.integrable.add_measure hν

@[simp]
theorem integrableOn_add_measure [PseudoMetrizableSpace ε] :
    IntegrableOn f s (μ + ν) ↔ IntegrableOn f s μ ∧ IntegrableOn f s ν :=
  ⟨fun h =>
    ⟨h.mono_measure (Measure.le_add_right le_rfl), h.mono_measure (Measure.le_add_left le_rfl)⟩,
    fun h => h.1.add_measure h.2⟩

theorem _root_.MeasurableEmbedding.integrableOn_map_iff [MeasurableSpace β] {e : α → β}
    (he : MeasurableEmbedding e) {f : β → ε} {μ : Measure α} {s : Set β} :
    IntegrableOn f s (μ.map e) ↔ IntegrableOn (f ∘ e) (e ⁻¹' s) μ := by
  simp_rw [IntegrableOn, he.restrict_map, he.integrable_map_iff]

theorem _root_.MeasurableEmbedding.integrableOn_iff_comap [MeasurableSpace β] {e : α → β}
    (he : MeasurableEmbedding e) {f : β → ε} {μ : Measure β} {s : Set β} (hs : s ⊆ range e) :
    IntegrableOn f s μ ↔ IntegrableOn (f ∘ e) (e ⁻¹' s) (μ.comap e) := by
  simp_rw [← he.integrableOn_map_iff, he.map_comap, IntegrableOn,
    Measure.restrict_restrict_of_subset hs]

theorem _root_.MeasurableEmbedding.integrableOn_range_iff_comap [MeasurableSpace β] {e : α → β}
    (he : MeasurableEmbedding e) {f : β → ε} {μ : Measure β} :
    IntegrableOn f (range e) μ ↔ Integrable (f ∘ e) (μ.comap e) := by
  rw [he.integrableOn_iff_comap .rfl, preimage_range, integrableOn_univ]

theorem integrableOn_iff_comap_subtypeVal (hs : MeasurableSet s) :
    IntegrableOn f s μ ↔ Integrable (f ∘ (↑) : s → ε) (μ.comap (↑)) := by
  rw [← (MeasurableEmbedding.subtype_coe hs).integrableOn_range_iff_comap, Subtype.range_val]

theorem integrableOn_map_equiv [MeasurableSpace β] (e : α ≃ᵐ β) {f : β → ε} {μ : Measure α}
    {s : Set β} : IntegrableOn f s (μ.map e) ↔ IntegrableOn (f ∘ e) (e ⁻¹' s) μ := by
  simp only [IntegrableOn, e.restrict_map, integrable_map_equiv e]

theorem MeasurePreserving.integrableOn_comp_preimage [MeasurableSpace β] {e : α → β} {ν}
    (h₁ : MeasurePreserving e μ ν) (h₂ : MeasurableEmbedding e) {f : β → ε} {s : Set β} :
    IntegrableOn (f ∘ e) (e ⁻¹' s) μ ↔ IntegrableOn f s ν :=
  (h₁.restrict_preimage_emb h₂ s).integrable_comp_emb h₂

theorem MeasurePreserving.integrableOn_image [MeasurableSpace β] {e : α → β} {ν}
    (h₁ : MeasurePreserving e μ ν) (h₂ : MeasurableEmbedding e) {f : β → ε} {s : Set α} :
    IntegrableOn f (e '' s) ν ↔ IntegrableOn (f ∘ e) s μ :=
  ((h₁.restrict_image_emb h₂ s).integrable_comp_emb h₂).symm

section indicator

-- All results in this section hold for any enormed monoid.
variable {f : α → ε'}

theorem integrable_indicator_iff (hs : MeasurableSet s) :
    Integrable (indicator s f) μ ↔ IntegrableOn f s μ := by
  simp_rw [IntegrableOn, Integrable, hasFiniteIntegral_iff_enorm,
    enorm_indicator_eq_indicator_enorm, lintegral_indicator hs,
    aestronglyMeasurable_indicator_iff hs]

theorem IntegrableOn.integrable_indicator (h : IntegrableOn f s μ) (hs : MeasurableSet s) :
    Integrable (indicator s f) μ :=
  (integrable_indicator_iff hs).2 h

@[fun_prop]
theorem Integrable.indicator (h : Integrable f μ) (hs : MeasurableSet s) :
    Integrable (indicator s f) μ :=
  h.integrableOn.integrable_indicator hs

theorem IntegrableOn.indicator (h : IntegrableOn f s μ) (ht : MeasurableSet t) :
    IntegrableOn (indicator t f) s μ :=
  Integrable.indicator h ht

theorem integrable_indicatorConstLp {E} [NormedAddCommGroup E] {p : ℝ≥0∞} {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) :
    Integrable (indicatorConstLp p hs hμs c) μ := by
  rw [integrable_congr indicatorConstLp_coeFn, integrable_indicator_iff hs, IntegrableOn,
    integrable_const_iff, isFiniteMeasure_restrict]
  exact .inr hμs

end indicator

/-- If a function is integrable on a set `s` and nonzero there, then the measurable hull of `s` is
well behaved: the restriction of the measure to `toMeasurable μ s` coincides with its restriction
to `s`. -/
theorem IntegrableOn.restrict_toMeasurable {f : α → ε'}
    (hf : IntegrableOn f s μ) (h's : ∀ x ∈ s, f x ≠ 0) :
    μ.restrict (toMeasurable μ s) = μ.restrict s := by
  rcases exists_seq_strictAnti_tendsto' ENNReal.zero_lt_top with ⟨u, _, u_pos, u_lim⟩
  let v n := toMeasurable (μ.restrict s) { x | u n ≤ ‖f x‖ₑ }
  have A : ∀ n, μ (s ∩ v n) ≠ ∞ := by
    intro n
    rw [inter_comm, ← Measure.restrict_apply (measurableSet_toMeasurable _ _),
      measure_toMeasurable]
    exact (hf.measure_enorm_ge_lt_top (u_pos n).1 (u_pos n).2.ne).ne
  apply Measure.restrict_toMeasurable_of_cover _ A
  intro x hx
  have : 0 < ‖f x‖ₑ := by simpa only [enorm_pos] using h's _ hx
  obtain ⟨n, hn⟩ : ∃ n, u n < ‖f x‖ₑ := ((tendsto_order.1 u_lim).2 _ this).exists
  exact mem_iUnion.2 ⟨n, subset_toMeasurable _ _ hn.le⟩

/-- If a function is integrable on a set `s`, and vanishes on `t \ s`, then it is integrable on `t`
if `t` is null-measurable. -/
theorem IntegrableOn.of_ae_diff_eq_zero [PseudoMetrizableSpace ε'] {f : α → ε'}
    (hf : IntegrableOn f s μ) (ht : NullMeasurableSet t μ)
    (h't : ∀ᵐ x ∂μ, x ∈ t \ s → f x = 0) : IntegrableOn f t μ := by
  let u := { x ∈ s | f x ≠ 0 }
  have hu : IntegrableOn f u μ := hf.mono_set fun x hx => hx.1
  let v := toMeasurable μ u
  have A : IntegrableOn f v μ := by
    rw [IntegrableOn, hu.restrict_toMeasurable]
    · exact hu
    · intro x hx; exact hx.2
  have B : IntegrableOn f (t \ v) μ := by
    apply integrableOn_zero.congr
    filter_upwards [ae_restrict_of_ae h't,
      ae_restrict_mem₀ (ht.diff (measurableSet_toMeasurable μ u).nullMeasurableSet)] with x hxt hx
    by_cases h'x : x ∈ s
    · by_contra H
      exact hx.2 (subset_toMeasurable μ u ⟨h'x, Ne.symm H⟩)
    · exact (hxt ⟨hx.1, h'x⟩).symm
  apply (A.union B).mono_set _
  rw [union_diff_self]
  exact subset_union_right

/-- If a function is integrable on a set `s`, and vanishes on `t \ s`, then it is integrable on `t`
if `t` is measurable. -/
theorem IntegrableOn.of_forall_diff_eq_zero [PseudoMetrizableSpace ε'] {f : α → ε'}
    (hf : IntegrableOn f s μ) (ht : MeasurableSet t)
    (h't : ∀ x ∈ t \ s, f x = 0) : IntegrableOn f t μ :=
  hf.of_ae_diff_eq_zero ht.nullMeasurableSet (Eventually.of_forall h't)

/-- If a function is integrable on a set `s` and vanishes almost everywhere on its complement,
then it is integrable. -/
theorem IntegrableOn.integrable_of_ae_notMem_eq_zero [PseudoMetrizableSpace ε']
    {f : α → ε'} (hf : IntegrableOn f s μ) (h't : ∀ᵐ x ∂μ, x ∉ s → f x = 0) : Integrable f μ := by
  rw [← integrableOn_univ]
  apply hf.of_ae_diff_eq_zero nullMeasurableSet_univ
  filter_upwards [h't] with x hx h'x using hx h'x.2

@[deprecated (since := "2025-05-23")]
alias IntegrableOn.integrable_of_ae_not_mem_eq_zero := IntegrableOn.integrable_of_ae_notMem_eq_zero

/-- If a function is integrable on a set `s` and vanishes everywhere on its complement,
then it is integrable. -/
theorem IntegrableOn.integrable_of_forall_notMem_eq_zero [PseudoMetrizableSpace ε']
    {f : α → ε'} (hf : IntegrableOn f s μ) (h't : ∀ x, x ∉ s → f x = 0) : Integrable f μ :=
  hf.integrable_of_ae_notMem_eq_zero (Eventually.of_forall fun x hx => h't x hx)

@[deprecated (since := "2025-05-23")]
alias IntegrableOn.integrable_of_forall_not_mem_eq_zero :=
  IntegrableOn.integrable_of_forall_notMem_eq_zero

theorem integrableOn_iff_integrable_of_support_subset [PseudoMetrizableSpace ε']
    {f : α → ε'} (h1s : support f ⊆ s) : IntegrableOn f s μ ↔ Integrable f μ := by
  refine ⟨fun h => ?_, fun h => h.integrableOn⟩
  refine h.integrable_of_forall_notMem_eq_zero fun x hx => ?_
  contrapose! hx
  exact h1s (mem_support.2 hx)

theorem integrableOn_Lp_of_measure_ne_top {E} [NormedAddCommGroup E] {p : ℝ≥0∞} {s : Set α}
    (f : Lp E p μ) (hp : 1 ≤ p) (hμs : μ s ≠ ∞) : IntegrableOn f s μ := by
  refine memLp_one_iff_integrable.mp ?_
  have hμ_restrict_univ : (μ.restrict s) Set.univ < ∞ := by
    simpa only [Set.univ_inter, MeasurableSet.univ, Measure.restrict_apply, lt_top_iff_ne_top]
  haveI hμ_finite : IsFiniteMeasure (μ.restrict s) := ⟨hμ_restrict_univ⟩
  exact ((Lp.memLp _).restrict s).mono_exponent hp

theorem Integrable.lintegral_lt_top {f : α → ℝ} (hf : Integrable f μ) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) < ∞ :=
  calc
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ∫⁻ x, ↑‖f x‖₊ ∂μ := lintegral_ofReal_le_lintegral_enorm f
    _ < ∞ := hf.2

theorem IntegrableOn.setLIntegral_lt_top {f : α → ℝ} {s : Set α} (hf : IntegrableOn f s μ) :
    (∫⁻ x in s, ENNReal.ofReal (f x) ∂μ) < ∞ :=
  Integrable.lintegral_lt_top hf

/-- We say that a function `f` is *integrable at filter* `l` if it is integrable on some
set `s ∈ l`. Equivalently, it is eventually integrable on `s` in `l.smallSets`. -/
def IntegrableAtFilter (f : α → ε) (l : Filter α) (μ : Measure α := by volume_tac) :=
  ∃ s ∈ l, IntegrableOn f s μ

variable {l l' : Filter α}

theorem _root_.MeasurableEmbedding.integrableAtFilter_map_iff [MeasurableSpace β] {e : α → β}
    (he : MeasurableEmbedding e) {f : β → ε} :
    IntegrableAtFilter f (l.map e) (μ.map e) ↔ IntegrableAtFilter (f ∘ e) l μ := by
  simp_rw [IntegrableAtFilter, he.integrableOn_map_iff]
  constructor <;> rintro ⟨s, hs⟩
  · exact ⟨_, hs⟩
  · exact ⟨e '' s, by rwa [mem_map, he.injective.preimage_image]⟩

theorem _root_.MeasurableEmbedding.integrableAtFilter_iff_comap [MeasurableSpace β] {e : α → β}
    (he : MeasurableEmbedding e) {f : β → ε} {μ : Measure β} :
    IntegrableAtFilter f (l.map e) μ ↔ IntegrableAtFilter (f ∘ e) l (μ.comap e) := by
  simp_rw [← he.integrableAtFilter_map_iff, IntegrableAtFilter, he.map_comap]
  constructor <;> rintro ⟨s, hs, int⟩
  · exact ⟨s, hs, int.mono_measure <| μ.restrict_le_self⟩
  · exact ⟨_, inter_mem hs range_mem_map, int.inter_of_restrict⟩

theorem Integrable.integrableAtFilter (h : Integrable f μ) (l : Filter α) :
    IntegrableAtFilter f l μ :=
  ⟨univ, Filter.univ_mem, integrableOn_univ.2 h⟩

protected theorem IntegrableAtFilter.eventually (h : IntegrableAtFilter f l μ) :
    ∀ᶠ s in l.smallSets, IntegrableOn f s μ :=
  Iff.mpr (eventually_smallSets' fun _s _t hst ht => ht.mono_set hst) h

theorem integrableAtFilter_atBot_iff [Preorder α] [IsDirected α fun (x1 x2 : α) => x1 ≥ x2]
    [Nonempty α] :
    IntegrableAtFilter f atBot μ ↔ ∃ a, IntegrableOn f (Iic a) μ := by
  refine ⟨fun ⟨s, hs, hi⟩ ↦ ?_, fun ⟨a, ha⟩ ↦ ⟨Iic a, Iic_mem_atBot a, ha⟩⟩
  obtain ⟨t, ht⟩ := mem_atBot_sets.mp hs
  exact ⟨t, hi.mono_set fun _ hx ↦ ht _ hx⟩

theorem integrableAtFilter_atTop_iff [Preorder α] [IsDirected α fun (x1 x2 : α) => x1 ≤ x2]
    [Nonempty α] :
    IntegrableAtFilter f atTop μ ↔ ∃ a, IntegrableOn f (Ici a) μ :=
  integrableAtFilter_atBot_iff (α := αᵒᵈ)

protected theorem IntegrableAtFilter.add [ContinuousAdd ε'] {f g : α → ε'}
    (hf : IntegrableAtFilter f l μ) (hg : IntegrableAtFilter g l μ) :
    IntegrableAtFilter (f + g) l μ := by
  rcases hf with ⟨s, sl, hs⟩
  rcases hg with ⟨t, tl, ht⟩
  refine ⟨s ∩ t, inter_mem sl tl, ?_⟩
  exact (hs.mono_set inter_subset_left).add (ht.mono_set inter_subset_right)

protected theorem IntegrableAtFilter.neg {f : α → E} (hf : IntegrableAtFilter f l μ) :
    IntegrableAtFilter (-f) l μ := by
  rcases hf with ⟨s, sl, hs⟩
  exact ⟨s, sl, hs.neg⟩

protected theorem IntegrableAtFilter.sub {f g : α → E}
    (hf : IntegrableAtFilter f l μ) (hg : IntegrableAtFilter g l μ) :
    IntegrableAtFilter (f - g) l μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

protected theorem IntegrableAtFilter.smul {𝕜 : Type*} [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 E]
    [IsBoundedSMul 𝕜 E] {f : α → E} (hf : IntegrableAtFilter f l μ) (c : 𝕜) :
    IntegrableAtFilter (c • f) l μ := by
  rcases hf with ⟨s, sl, hs⟩
  exact ⟨s, sl, hs.smul c⟩

protected theorem IntegrableAtFilter.enorm (hf : IntegrableAtFilter f l μ) :
    IntegrableAtFilter (fun x => ‖f x‖ₑ) l μ :=
  Exists.casesOn hf fun s hs ↦ ⟨s, hs.1, hs.2.enorm⟩

protected theorem IntegrableAtFilter.norm {f : α → E} (hf : IntegrableAtFilter f l μ) :
    IntegrableAtFilter (fun x => ‖f x‖) l μ :=
  Exists.casesOn hf fun s hs ↦ ⟨s, hs.1, hs.2.norm⟩

theorem IntegrableAtFilter.filter_mono (hl : l ≤ l') (hl' : IntegrableAtFilter f l' μ) :
    IntegrableAtFilter f l μ :=
  let ⟨s, hs, hsf⟩ := hl'
  ⟨s, hl hs, hsf⟩

theorem IntegrableAtFilter.inf_of_left (hl : IntegrableAtFilter f l μ) :
    IntegrableAtFilter f (l ⊓ l') μ :=
  hl.filter_mono inf_le_left

theorem IntegrableAtFilter.inf_of_right (hl : IntegrableAtFilter f l μ) :
    IntegrableAtFilter f (l' ⊓ l) μ :=
  hl.filter_mono inf_le_right

@[simp]
theorem IntegrableAtFilter.inf_ae_iff {l : Filter α} :
    IntegrableAtFilter f (l ⊓ ae μ) μ ↔ IntegrableAtFilter f l μ := by
  refine ⟨?_, fun h ↦ h.filter_mono inf_le_left⟩
  rintro ⟨s, ⟨t, ht, u, hu, rfl⟩, hf⟩
  refine ⟨t, ht, hf.congr_set_ae <| eventuallyEq_set.2 ?_⟩
  filter_upwards [hu] with x hx using (and_iff_left hx).symm

alias ⟨IntegrableAtFilter.of_inf_ae, _⟩ := IntegrableAtFilter.inf_ae_iff

@[simp]
theorem integrableAtFilter_top {f : α → E} : IntegrableAtFilter f ⊤ μ ↔ Integrable f μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.integrableAtFilter ⊤⟩
  obtain ⟨s, hsf, hs⟩ := h
  exact (integrableOn_iff_integrable_of_support_subset fun _ _ ↦ hsf _).mp hs

theorem IntegrableAtFilter.sup_iff {f : α → E} {l l' : Filter α} :
    IntegrableAtFilter f (l ⊔ l') μ ↔ IntegrableAtFilter f l μ ∧ IntegrableAtFilter f l' μ := by
  constructor
  · exact fun h => ⟨h.filter_mono le_sup_left, h.filter_mono le_sup_right⟩
  · exact fun ⟨⟨s, hsl, hs⟩, ⟨t, htl, ht⟩⟩ ↦ ⟨s ∪ t, union_mem_sup hsl htl, hs.union ht⟩

/-- If `μ` is a measure finite at filter `l` and `f` is a function such that its norm is bounded
above at `l`, then `f` is integrable at `l`. -/
theorem Measure.FiniteAtFilter.integrableAtFilter {f : α → E} {l : Filter α}
    [IsMeasurablyGenerated l] (hfm : StronglyMeasurableAtFilter f l μ) (hμ : μ.FiniteAtFilter l)
    (hf : l.IsBoundedUnder (· ≤ ·) (norm ∘ f)) : IntegrableAtFilter f l μ := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ᶠ s in l.smallSets, ∀ x ∈ s, ‖f x‖ ≤ C :=
    hf.imp fun C hC => eventually_smallSets.2 ⟨_, hC, fun t => id⟩
  rcases (hfm.eventually.and (hμ.eventually.and hC)).exists_measurable_mem_of_smallSets with
    ⟨s, hsl, hsm, hfm, hμ, hC⟩
  refine ⟨s, hsl, ⟨hfm, .restrict_of_bounded hμ (C := C) ?_⟩⟩
  rw [ae_restrict_eq hsm, eventually_inf_principal]
  exact Eventually.of_forall hC

theorem Measure.FiniteAtFilter.integrableAtFilter_of_tendsto_ae {f : α → E} {l : Filter α}
    [IsMeasurablyGenerated l] (hfm : StronglyMeasurableAtFilter f l μ) (hμ : μ.FiniteAtFilter l) {b}
    (hf : Tendsto f (l ⊓ ae μ) (𝓝 b)) : IntegrableAtFilter f l μ :=
  (hμ.inf_of_left.integrableAtFilter (hfm.filter_mono inf_le_left)
      hf.norm.isBoundedUnder_le).of_inf_ae

alias _root_.Filter.Tendsto.integrableAtFilter_ae :=
  Measure.FiniteAtFilter.integrableAtFilter_of_tendsto_ae

theorem Measure.FiniteAtFilter.integrableAtFilter_of_tendsto {f : α → E} {l : Filter α}
    [IsMeasurablyGenerated l] (hfm : StronglyMeasurableAtFilter f l μ) (hμ : μ.FiniteAtFilter l) {b}
    (hf : Tendsto f l (𝓝 b)) : IntegrableAtFilter f l μ :=
  hμ.integrableAtFilter hfm hf.norm.isBoundedUnder_le

alias _root_.Filter.Tendsto.integrableAtFilter :=
  Measure.FiniteAtFilter.integrableAtFilter_of_tendsto

lemma Measure.integrableOn_of_bounded {f : α → E} (s_finite : μ s ≠ ∞)
    (f_mble : AEStronglyMeasurable f μ) {M : ℝ} (f_bdd : ∀ᵐ a ∂(μ.restrict s), ‖f a‖ ≤ M) :
    IntegrableOn f s μ :=
  ⟨f_mble.restrict, .restrict_of_bounded (C := M) s_finite.lt_top f_bdd⟩

theorem integrable_add_of_disjoint {f g : α → E} (h : Disjoint (support f) (support g))
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    Integrable (f + g) μ ↔ Integrable f μ ∧ Integrable g μ := by
  refine ⟨fun hfg => ⟨?_, ?_⟩, fun h => h.1.add h.2⟩
  · rw [← indicator_add_eq_left h]; exact hfg.indicator hf.measurableSet_support
  · rw [← indicator_add_eq_right h]; exact hfg.indicator hg.measurableSet_support

/-- If a function converges along a filter to a limit `a`, is integrable along this filter, and
all elements of the filter have infinite measure, then the limit has to vanish. -/
lemma IntegrableAtFilter.eq_zero_of_tendsto {f : α → E}
    (h : IntegrableAtFilter f l μ) (h' : ∀ s ∈ l, μ s = ∞) {a : E}
    (hf : Tendsto f l (𝓝 a)) : a = 0 := by
  by_contra H
  obtain ⟨ε, εpos, hε⟩ : ∃ (ε : ℝ), 0 < ε ∧ ε < ‖a‖ := exists_between (norm_pos_iff.mpr H)
  rcases h with ⟨u, ul, hu⟩
  let v := u ∩ {b | ε < ‖f b‖}
  have hv : IntegrableOn f v μ := hu.mono_set inter_subset_left
  have vl : v ∈ l := inter_mem ul ((tendsto_order.1 hf.norm).1 _ hε)
  have : μ.restrict v v < ∞ := lt_of_le_of_lt (measure_mono inter_subset_right)
    (Integrable.measure_gt_lt_top hv.norm εpos)
  have : μ v ≠ ∞ := ne_of_lt (by simpa only [Measure.restrict_apply_self])
  exact this (h' v vl)

end NormedAddCommGroup

end MeasureTheory

open MeasureTheory

variable [NormedAddCommGroup E]

/-- A function which is continuous on a set `s` is almost everywhere measurable with respect to
`μ.restrict s`. -/
theorem ContinuousOn.aemeasurable [TopologicalSpace α] [OpensMeasurableSpace α] [MeasurableSpace β]
    [TopologicalSpace β] [BorelSpace β] {f : α → β} {s : Set α} {μ : Measure α}
    (hf : ContinuousOn f s) (hs : MeasurableSet s) : AEMeasurable f (μ.restrict s) := by
  classical
  nontriviality α; inhabit α
  have : (Set.piecewise s f fun _ => f default) =ᵐ[μ.restrict s] f := piecewise_ae_eq_restrict hs
  refine ⟨Set.piecewise s f fun _ => f default, ?_, this.symm⟩
  apply measurable_of_isOpen
  intro t ht
  obtain ⟨u, u_open, hu⟩ : ∃ u : Set α, IsOpen u ∧ f ⁻¹' t ∩ s = u ∩ s :=
    _root_.continuousOn_iff'.1 hf t ht
  rw [piecewise_preimage, Set.ite, hu]
  exact (u_open.measurableSet.inter hs).union ((measurable_const ht.measurableSet).diff hs)

theorem ContinuousOn.aemeasurable₀ [TopologicalSpace α] [OpensMeasurableSpace α] [MeasurableSpace β]
    [TopologicalSpace β] [BorelSpace β] {f : α → β} {s : Set α} {μ : Measure α}
    (hf : ContinuousOn f s) (hs : NullMeasurableSet s μ) : AEMeasurable f (μ.restrict s) := by
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, ts, ht, t_eq_s⟩
  rw [← Measure.restrict_congr_set t_eq_s]
  exact ContinuousOn.aemeasurable (hf.mono ts) ht

/-- A function which is continuous on a separable set `s` is almost everywhere strongly measurable
with respect to `μ.restrict s`. -/
theorem ContinuousOn.aestronglyMeasurable_of_isSeparable [TopologicalSpace α]
    [PseudoMetrizableSpace α] [OpensMeasurableSpace α] [TopologicalSpace β]
    [PseudoMetrizableSpace β] {f : α → β} {s : Set α} {μ : Measure α} (hf : ContinuousOn f s)
    (hs : MeasurableSet s) (h's : TopologicalSpace.IsSeparable s) :
    AEStronglyMeasurable f (μ.restrict s) := by
  letI := pseudoMetrizableSpacePseudoMetric α
  borelize β
  rw [aestronglyMeasurable_iff_aemeasurable_separable]
  refine ⟨hf.aemeasurable hs, f '' s, hf.isSeparable_image h's, ?_⟩
  exact mem_of_superset (self_mem_ae_restrict hs) (subset_preimage_image _ _)

/-- A function which is continuous on a set `s` is almost everywhere strongly measurable with
respect to `μ.restrict s` when either the source space or the target space is second-countable. -/
theorem ContinuousOn.aestronglyMeasurable [TopologicalSpace α] [TopologicalSpace β]
    [h : SecondCountableTopologyEither α β] [OpensMeasurableSpace α] [PseudoMetrizableSpace β]
    {f : α → β} {s : Set α} {μ : Measure α} (hf : ContinuousOn f s) (hs : MeasurableSet s) :
    AEStronglyMeasurable f (μ.restrict s) := by
  borelize β
  refine
    aestronglyMeasurable_iff_aemeasurable_separable.2
      ⟨hf.aemeasurable hs, f '' s, ?_,
        mem_of_superset (self_mem_ae_restrict hs) (subset_preimage_image _ _)⟩
  cases h.out
  · rw [image_eq_range]
    exact isSeparable_range <| continuousOn_iff_continuous_restrict.1 hf
  · exact .of_separableSpace _

/-- A function which is continuous on a compact set `s` is almost everywhere strongly measurable
with respect to `μ.restrict s`. -/
theorem ContinuousOn.aestronglyMeasurable_of_isCompact [TopologicalSpace α] [OpensMeasurableSpace α]
    [TopologicalSpace β] [PseudoMetrizableSpace β] {f : α → β} {s : Set α} {μ : Measure α}
    (hf : ContinuousOn f s) (hs : IsCompact s) (h's : MeasurableSet s) :
    AEStronglyMeasurable f (μ.restrict s) := by
  letI := pseudoMetrizableSpacePseudoMetric β
  borelize β
  rw [aestronglyMeasurable_iff_aemeasurable_separable]
  refine ⟨hf.aemeasurable h's, f '' s, ?_, ?_⟩
  · exact (hs.image_of_continuousOn hf).isSeparable
  · exact mem_of_superset (self_mem_ae_restrict h's) (subset_preimage_image _ _)

theorem ContinuousOn.integrableAt_nhdsWithin_of_isSeparable [TopologicalSpace α]
    [PseudoMetrizableSpace α] [OpensMeasurableSpace α] {μ : Measure α} [IsLocallyFiniteMeasure μ]
    {a : α} {t : Set α} {f : α → E} (hft : ContinuousOn f t) (ht : MeasurableSet t)
    (h't : TopologicalSpace.IsSeparable t) (ha : a ∈ t) : IntegrableAtFilter f (𝓝[t] a) μ :=
  haveI : (𝓝[t] a).IsMeasurablyGenerated := ht.nhdsWithin_isMeasurablyGenerated _
  (hft a ha).integrableAtFilter
    ⟨_, self_mem_nhdsWithin, hft.aestronglyMeasurable_of_isSeparable ht h't⟩
    (μ.finiteAt_nhdsWithin _ _)

theorem ContinuousOn.integrableAt_nhdsWithin [TopologicalSpace α]
    [SecondCountableTopologyEither α E] [OpensMeasurableSpace α] {μ : Measure α}
    [IsLocallyFiniteMeasure μ] {a : α} {t : Set α} {f : α → E} (hft : ContinuousOn f t)
    (ht : MeasurableSet t) (ha : a ∈ t) : IntegrableAtFilter f (𝓝[t] a) μ :=
  haveI : (𝓝[t] a).IsMeasurablyGenerated := ht.nhdsWithin_isMeasurablyGenerated _
  (hft a ha).integrableAtFilter ⟨_, self_mem_nhdsWithin, hft.aestronglyMeasurable ht⟩
    (μ.finiteAt_nhdsWithin _ _)

theorem Continuous.integrableAt_nhds [TopologicalSpace α] [SecondCountableTopologyEither α E]
    [OpensMeasurableSpace α] {μ : Measure α} [IsLocallyFiniteMeasure μ] {f : α → E}
    (hf : Continuous f) (a : α) : IntegrableAtFilter f (𝓝 a) μ := by
  rw [← nhdsWithin_univ]
  exact hf.continuousOn.integrableAt_nhdsWithin MeasurableSet.univ (mem_univ a)

/-- If a function is continuous on an open set `s`, then it is strongly measurable at the filter
`𝓝 x` for all `x ∈ s` if either the source space or the target space is second-countable. -/
theorem ContinuousOn.stronglyMeasurableAtFilter [TopologicalSpace α] [OpensMeasurableSpace α]
    [TopologicalSpace β] [PseudoMetrizableSpace β] [SecondCountableTopologyEither α β] {f : α → β}
    {s : Set α} {μ : Measure α} (hs : IsOpen s) (hf : ContinuousOn f s) :
    ∀ x ∈ s, StronglyMeasurableAtFilter f (𝓝 x) μ := fun _x hx =>
  ⟨s, IsOpen.mem_nhds hs hx, hf.aestronglyMeasurable hs.measurableSet⟩

theorem ContinuousAt.stronglyMeasurableAtFilter [TopologicalSpace α] [OpensMeasurableSpace α]
    [SecondCountableTopologyEither α E] {f : α → E} {s : Set α} {μ : Measure α} (hs : IsOpen s)
    (hf : ∀ x ∈ s, ContinuousAt f x) : ∀ x ∈ s, StronglyMeasurableAtFilter f (𝓝 x) μ :=
  ContinuousOn.stronglyMeasurableAtFilter hs <| continuousOn_of_forall_continuousAt hf

theorem Continuous.stronglyMeasurableAtFilter [TopologicalSpace α] [OpensMeasurableSpace α]
    [TopologicalSpace β] [PseudoMetrizableSpace β] [SecondCountableTopologyEither α β] {f : α → β}
    (hf : Continuous f) (μ : Measure α) (l : Filter α) : StronglyMeasurableAtFilter f l μ :=
  hf.stronglyMeasurable.stronglyMeasurableAtFilter

/-- If a function is continuous on a measurable set `s`, then it is measurable at the filter
  `𝓝[s] x` for all `x`. -/
theorem ContinuousOn.stronglyMeasurableAtFilter_nhdsWithin {α β : Type*} [MeasurableSpace α]
    [TopologicalSpace α] [OpensMeasurableSpace α] [TopologicalSpace β] [PseudoMetrizableSpace β]
    [SecondCountableTopologyEither α β] {f : α → β} {s : Set α} {μ : Measure α}
    (hf : ContinuousOn f s) (hs : MeasurableSet s) (x : α) :
    StronglyMeasurableAtFilter f (𝓝[s] x) μ :=
  ⟨s, self_mem_nhdsWithin, hf.aestronglyMeasurable hs⟩

/-! ### Lemmas about adding and removing interval boundaries

The primed lemmas take explicit arguments about the measure being finite at the endpoint, while
the unprimed ones use `[NoAtoms μ]`.
-/


section PartialOrder

variable [PartialOrder α] [MeasurableSingletonClass α] {f : α → E} {μ : Measure α} {a b : α}

theorem integrableOn_Icc_iff_integrableOn_Ioc' (ha : μ {a} ≠ ∞) :
    IntegrableOn f (Icc a b) μ ↔ IntegrableOn f (Ioc a b) μ := by
  by_cases hab : a ≤ b
  · rw [← Ioc_union_left hab, integrableOn_union, eq_true integrableOn_singleton, and_true]
  · rw [Icc_eq_empty hab, Ioc_eq_empty]
    contrapose! hab
    exact hab.le

theorem integrableOn_Icc_iff_integrableOn_Ico' (hb : μ {b} ≠ ∞) :
    IntegrableOn f (Icc a b) μ ↔ IntegrableOn f (Ico a b) μ := by
  by_cases hab : a ≤ b
  · rw [← Ico_union_right hab, integrableOn_union, eq_true integrableOn_singleton, and_true]
  · rw [Icc_eq_empty hab, Ico_eq_empty]
    contrapose! hab
    exact hab.le

theorem integrableOn_Ico_iff_integrableOn_Ioo' (ha : μ {a} ≠ ∞) :
    IntegrableOn f (Ico a b) μ ↔ IntegrableOn f (Ioo a b) μ := by
  by_cases hab : a < b
  · rw [← Ioo_union_left hab, integrableOn_union,
      eq_true integrableOn_singleton, and_true]
  · rw [Ioo_eq_empty hab, Ico_eq_empty hab]

theorem integrableOn_Ioc_iff_integrableOn_Ioo' (hb : μ {b} ≠ ∞) :
    IntegrableOn f (Ioc a b) μ ↔ IntegrableOn f (Ioo a b) μ := by
  by_cases hab : a < b
  · rw [← Ioo_union_right hab, integrableOn_union, eq_true integrableOn_singleton, and_true]
  · rw [Ioo_eq_empty hab, Ioc_eq_empty hab]

theorem integrableOn_Icc_iff_integrableOn_Ioo' (ha : μ {a} ≠ ∞) (hb : μ {b} ≠ ∞) :
    IntegrableOn f (Icc a b) μ ↔ IntegrableOn f (Ioo a b) μ := by
  rw [integrableOn_Icc_iff_integrableOn_Ioc' ha, integrableOn_Ioc_iff_integrableOn_Ioo' hb]

theorem integrableOn_Ici_iff_integrableOn_Ioi' (hb : μ {b} ≠ ∞) :
    IntegrableOn f (Ici b) μ ↔ IntegrableOn f (Ioi b) μ := by
  rw [← Ioi_union_left, integrableOn_union, eq_true integrableOn_singleton, and_true]

theorem integrableOn_Iic_iff_integrableOn_Iio' (hb : μ {b} ≠ ∞) :
    IntegrableOn f (Iic b) μ ↔ IntegrableOn f (Iio b) μ := by
  rw [← Iio_union_right, integrableOn_union, eq_true integrableOn_singleton, and_true]

variable [NoAtoms μ]

theorem integrableOn_Icc_iff_integrableOn_Ioc :
    IntegrableOn f (Icc a b) μ ↔ IntegrableOn f (Ioc a b) μ :=
  integrableOn_Icc_iff_integrableOn_Ioc' (by rw [measure_singleton]; exact ENNReal.zero_ne_top)

theorem integrableOn_Icc_iff_integrableOn_Ico :
    IntegrableOn f (Icc a b) μ ↔ IntegrableOn f (Ico a b) μ :=
  integrableOn_Icc_iff_integrableOn_Ico' (by rw [measure_singleton]; exact ENNReal.zero_ne_top)

theorem integrableOn_Ico_iff_integrableOn_Ioo :
    IntegrableOn f (Ico a b) μ ↔ IntegrableOn f (Ioo a b) μ :=
  integrableOn_Ico_iff_integrableOn_Ioo' (by rw [measure_singleton]; exact ENNReal.zero_ne_top)

theorem integrableOn_Ioc_iff_integrableOn_Ioo :
    IntegrableOn f (Ioc a b) μ ↔ IntegrableOn f (Ioo a b) μ :=
  integrableOn_Ioc_iff_integrableOn_Ioo' (by rw [measure_singleton]; exact ENNReal.zero_ne_top)

theorem integrableOn_Icc_iff_integrableOn_Ioo :
    IntegrableOn f (Icc a b) μ ↔ IntegrableOn f (Ioo a b) μ := by
  rw [integrableOn_Icc_iff_integrableOn_Ioc, integrableOn_Ioc_iff_integrableOn_Ioo]

theorem integrableOn_Ici_iff_integrableOn_Ioi :
    IntegrableOn f (Ici b) μ ↔ IntegrableOn f (Ioi b) μ :=
  integrableOn_Ici_iff_integrableOn_Ioi' (by rw [measure_singleton]; exact ENNReal.zero_ne_top)

theorem integrableOn_Iic_iff_integrableOn_Iio :
    IntegrableOn f (Iic b) μ ↔ IntegrableOn f (Iio b) μ :=
  integrableOn_Iic_iff_integrableOn_Iio' (by rw [measure_singleton]; exact ENNReal.zero_ne_top)

end PartialOrder
