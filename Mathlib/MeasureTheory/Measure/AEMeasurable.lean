/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.Trim
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

/-!
# Almost everywhere measurable functions

A function is almost everywhere measurable if it coincides almost everywhere with a measurable
function. This property, called `AEMeasurable f μ`, is defined in the file `MeasureSpaceDef`.
We discuss several of its properties that are analogous to properties of measurable functions.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Filter Set Function ENNReal

variable {ι α β γ δ R : Type*} {m0 : MeasurableSpace α} [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ] {f g : α → β} {μ ν : Measure α}

section

@[nontriviality, measurability]
theorem Subsingleton.aemeasurable [Subsingleton α] : AEMeasurable f μ :=
  Subsingleton.measurable.aemeasurable

@[nontriviality, measurability]
theorem aemeasurable_of_subsingleton_codomain [Subsingleton β] : AEMeasurable f μ :=
  (measurable_of_subsingleton_codomain f).aemeasurable

@[simp, fun_prop, measurability]
theorem aemeasurable_zero_measure : AEMeasurable f (0 : Measure α) := by
  nontriviality α; inhabit α
  exact ⟨fun _ => f default, measurable_const, rfl⟩

theorem aemeasurable_id'' (μ : Measure α) {m : MeasurableSpace α} (hm : m ≤ m0) :
    @AEMeasurable α α m m0 id μ :=
  @Measurable.aemeasurable α α m0 m id μ (measurable_id'' hm)

lemma aemeasurable_of_map_neZero {μ : Measure α}
    {f : α → β} (h : NeZero (μ.map f)) :
    AEMeasurable f μ := by
  by_contra h'
  simp [h'] at h

namespace AEMeasurable

lemma mono_ac (hf : AEMeasurable f ν) (hμν : μ ≪ ν) : AEMeasurable f μ :=
  ⟨hf.mk f, hf.measurable_mk, hμν.ae_le hf.ae_eq_mk⟩

theorem mono_measure (h : AEMeasurable f μ) (h' : ν ≤ μ) : AEMeasurable f ν :=
  mono_ac h h'.absolutelyContinuous

theorem mono_set {s t} (h : s ⊆ t) (ht : AEMeasurable f (μ.restrict t)) :
    AEMeasurable f (μ.restrict s) :=
  ht.mono_measure (restrict_mono h le_rfl)

@[fun_prop]
protected theorem mono' (h : AEMeasurable f μ) (h' : ν ≪ μ) : AEMeasurable f ν :=
  ⟨h.mk f, h.measurable_mk, h' h.ae_eq_mk⟩

theorem ae_mem_imp_eq_mk {s} (h : AEMeasurable f (μ.restrict s)) :
    ∀ᵐ x ∂μ, x ∈ s → f x = h.mk f x :=
  ae_imp_of_ae_restrict h.ae_eq_mk

theorem ae_inf_principal_eq_mk {s} (h : AEMeasurable f (μ.restrict s)) : f =ᶠ[ae μ ⊓ 𝓟 s] h.mk f :=
  le_ae_restrict h.ae_eq_mk

@[measurability]
theorem sum_measure [Countable ι] {μ : ι → Measure α} (h : ∀ i, AEMeasurable f (μ i)) :
    AEMeasurable f (sum μ) := by
  classical
  nontriviality β
  inhabit β
  set s : ι → Set α := fun i => toMeasurable (μ i) { x | f x ≠ (h i).mk f x }
  have hsμ : ∀ i, μ i (s i) = 0 := by
    intro i
    rw [measure_toMeasurable]
    exact (h i).ae_eq_mk
  have hsm : MeasurableSet (⋂ i, s i) :=
    MeasurableSet.iInter fun i => measurableSet_toMeasurable _ _
  have hs : ∀ i x, x ∉ s i → f x = (h i).mk f x := by
    intro i x hx
    contrapose! hx
    exact subset_toMeasurable _ _ hx
  set g : α → β := (⋂ i, s i).piecewise (const α default) f
  refine ⟨g, measurable_of_restrict_of_restrict_compl hsm ?_ ?_, ae_sum_iff.mpr fun i => ?_⟩
  · rw [restrict_piecewise]
    simp only [s]
    exact measurable_const
  · rw [restrict_piecewise_compl, compl_iInter]
    intro t ht
    refine ⟨⋃ i, (h i).mk f ⁻¹' t ∩ (s i)ᶜ, MeasurableSet.iUnion fun i ↦
      (measurable_mk _ ht).inter (measurableSet_toMeasurable _ _).compl, ?_⟩
    ext ⟨x, hx⟩
    simp only [mem_preimage, mem_iUnion, Set.restrict, mem_inter_iff,
      mem_compl_iff] at hx ⊢
    constructor
    · rintro ⟨i, hxt, hxs⟩
      rwa [hs _ _ hxs]
    · rcases hx with ⟨i, hi⟩
      rw [hs _ _ hi]
      exact fun h => ⟨i, h, hi⟩
  · refine measure_mono_null (fun x (hx : f x ≠ g x) => ?_) (hsμ i)
    contrapose! hx
    refine (piecewise_eq_of_notMem _ _ _ ?_).symm
    exact fun h => hx (mem_iInter.1 h i)

@[simp]
theorem _root_.aemeasurable_sum_measure_iff [Countable ι] {μ : ι → Measure α} :
    AEMeasurable f (sum μ) ↔ ∀ i, AEMeasurable f (μ i) :=
  ⟨fun h _ => h.mono_measure (le_sum _ _), sum_measure⟩

@[simp]
theorem _root_.aemeasurable_add_measure_iff :
    AEMeasurable f (μ + ν) ↔ AEMeasurable f μ ∧ AEMeasurable f ν := by
  rw [← sum_cond, aemeasurable_sum_measure_iff, Bool.forall_bool, and_comm]
  rfl

@[measurability]
theorem add_measure {f : α → β} (hμ : AEMeasurable f μ) (hν : AEMeasurable f ν) :
    AEMeasurable f (μ + ν) :=
  aemeasurable_add_measure_iff.2 ⟨hμ, hν⟩

protected theorem map_add₀ {μ ν : Measure α} {f : α → β}
    (hμ : AEMeasurable f μ) (hν : AEMeasurable f ν) :
    (μ + ν).map f = μ.map f + ν.map f := by
  rw [Measure.map_congr (hμ.add_measure hν).ae_eq_mk, Measure.map_add _ _ (by fun_prop)]
  congr 1 <;> apply Measure.map_congr
  · exact (AbsolutelyContinuous.rfl.add_right ν) (hμ.add_measure hν).ae_eq_mk.symm
  · exact (AbsolutelyContinuous.rfl.add_right' μ) (hμ.add_measure hν).ae_eq_mk.symm

@[measurability]
protected theorem iUnion [Countable ι] {s : ι → Set α}
    (h : ∀ i, AEMeasurable f (μ.restrict (s i))) : AEMeasurable f (μ.restrict (⋃ i, s i)) :=
  (sum_measure h).mono_measure <| restrict_iUnion_le

@[simp]
theorem _root_.aemeasurable_iUnion_iff [Countable ι] {s : ι → Set α} :
    AEMeasurable f (μ.restrict (⋃ i, s i)) ↔ ∀ i, AEMeasurable f (μ.restrict (s i)) :=
  ⟨fun h _ => h.mono_measure <| restrict_mono (subset_iUnion _ _) le_rfl, AEMeasurable.iUnion⟩

@[simp]
theorem _root_.aemeasurable_union_iff {s t : Set α} :
    AEMeasurable f (μ.restrict (s ∪ t)) ↔
      AEMeasurable f (μ.restrict s) ∧ AEMeasurable f (μ.restrict t) := by
  simp only [union_eq_iUnion, aemeasurable_iUnion_iff, Bool.forall_bool, cond, and_comm]

@[measurability]
theorem smul_measure [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (h : AEMeasurable f μ) (c : R) : AEMeasurable f (c • μ) :=
  ⟨h.mk f, h.measurable_mk, ae_smul_measure h.ae_eq_mk c⟩

theorem comp_aemeasurable {f : α → δ} {g : δ → β} (hg : AEMeasurable g (μ.map f))
    (hf : AEMeasurable f μ) : AEMeasurable (g ∘ f) μ :=
  ⟨hg.mk g ∘ hf.mk f, hg.measurable_mk.comp hf.measurable_mk,
    (ae_eq_comp hf hg.ae_eq_mk).trans (hf.ae_eq_mk.fun_comp (mk g hg))⟩

@[fun_prop]
theorem comp_aemeasurable' {f : α → δ} {g : δ → β} (hg : AEMeasurable g (μ.map f))
    (hf : AEMeasurable f μ) : AEMeasurable (fun x ↦ g (f x)) μ := comp_aemeasurable hg hf

theorem comp_measurable {f : α → δ} {g : δ → β} (hg : AEMeasurable g (μ.map f))
    (hf : Measurable f) : AEMeasurable (g ∘ f) μ :=
  hg.comp_aemeasurable hf.aemeasurable

@[fun_prop]
theorem comp_quasiMeasurePreserving {ν : Measure δ} {f : α → δ} {g : δ → β} (hg : AEMeasurable g ν)
    (hf : QuasiMeasurePreserving f μ ν) : AEMeasurable (g ∘ f) μ :=
  (hg.mono' hf.absolutelyContinuous).comp_measurable hf.measurable

theorem map_map_of_aemeasurable {g : β → γ} {f : α → β} (hg : AEMeasurable g (Measure.map f μ))
    (hf : AEMeasurable f μ) : (μ.map f).map g = μ.map (g ∘ f) := by
  ext1 s hs
  rw [map_apply_of_aemeasurable hg hs, map_apply₀ hf (hg.nullMeasurable hs),
    map_apply_of_aemeasurable (hg.comp_aemeasurable hf) hs, preimage_comp]

@[fun_prop]
protected theorem fst {f : α → β × γ} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x ↦ (f x).1) μ :=
  measurable_fst.comp_aemeasurable hf

@[fun_prop]
protected theorem snd {f : α → β × γ} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x ↦ (f x).2) μ :=
  measurable_snd.comp_aemeasurable hf

@[fun_prop]
theorem prodMk {f : α → β} {g : α → γ} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun x => (f x, g x)) μ :=
  ⟨fun a => (hf.mk f a, hg.mk g a), hf.measurable_mk.prodMk hg.measurable_mk,
    hf.ae_eq_mk.prodMk hg.ae_eq_mk⟩

theorem _root_.nullMeasurableSet_eq_fun [MeasurableEq β]
    {f g : α → β} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    NullMeasurableSet { x | f x = g x } μ :=
  (hf.prodMk hg).nullMeasurableSet_preimage measurableSet_diagonal

theorem exists_ae_eq_range_subset (H : AEMeasurable f μ) {t : Set β} (ht : ∀ᵐ x ∂μ, f x ∈ t)
    (h₀ : t.Nonempty) : ∃ g, Measurable g ∧ range g ⊆ t ∧ f =ᵐ[μ] g := by
  classical
  let s : Set α := toMeasurable μ { x | f x = H.mk f x ∧ f x ∈ t }ᶜ
  let g : α → β := piecewise s (fun _ => h₀.some) (H.mk f)
  refine ⟨g, ?_, ?_, ?_⟩
  · exact Measurable.piecewise (measurableSet_toMeasurable _ _) measurable_const H.measurable_mk
  · rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ s
    · simpa [g, hx] using h₀.some_mem
    · simp only [g, hx, piecewise_eq_of_notMem, not_false_iff]
      contrapose! hx
      apply subset_toMeasurable
      simp +contextual only [hx, mem_compl_iff, mem_setOf_eq, not_and,
        not_false_iff, imp_true_iff]
  · have A : μ (toMeasurable μ { x | f x = H.mk f x ∧ f x ∈ t }ᶜ) = 0 := by
      rw [measure_toMeasurable, ← compl_mem_ae_iff, compl_compl]
      exact H.ae_eq_mk.and ht
    filter_upwards [compl_mem_ae_iff.2 A] with x hx
    rw [mem_compl_iff] at hx
    simp only [s, g, hx, piecewise_eq_of_notMem, not_false_iff]
    contrapose! hx
    apply subset_toMeasurable
    simp only [hx, mem_compl_iff, mem_setOf_eq, false_and, not_false_iff]

theorem exists_measurable_nonneg {β} [Preorder β] [Zero β] {mβ : MeasurableSpace β} {f : α → β}
    (hf : AEMeasurable f μ) (f_nn : ∀ᵐ t ∂μ, 0 ≤ f t) : ∃ g, Measurable g ∧ 0 ≤ g ∧ f =ᵐ[μ] g := by
  obtain ⟨G, hG_meas, hG_mem, hG_ae_eq⟩ := hf.exists_ae_eq_range_subset f_nn ⟨0, le_rfl⟩
  exact ⟨G, hG_meas, fun x => hG_mem (mem_range_self x), hG_ae_eq⟩

theorem subtype_mk (h : AEMeasurable f μ) {s : Set β} {hfs : ∀ x, f x ∈ s} :
    AEMeasurable (codRestrict f s hfs) μ := by
  nontriviality α; inhabit α
  obtain ⟨g, g_meas, hg, fg⟩ : ∃ g : α → β, Measurable g ∧ range g ⊆ s ∧ f =ᵐ[μ] g :=
    h.exists_ae_eq_range_subset (Eventually.of_forall hfs) ⟨_, hfs default⟩
  refine ⟨codRestrict g s fun x => hg (mem_range_self _), Measurable.subtype_mk g_meas, ?_⟩
  filter_upwards [fg] with x hx
  simpa [Subtype.ext_iff]

end AEMeasurable

theorem aemeasurable_const' (h : ∀ᵐ (x) (y) ∂μ, f x = f y) : AEMeasurable f μ := by
  rcases eq_or_ne μ 0 with (rfl | hμ)
  · exact aemeasurable_zero_measure
  · haveI := ae_neBot.2 hμ
    rcases h.exists with ⟨x, hx⟩
    exact ⟨const α (f x), measurable_const, EventuallyEq.symm hx⟩

open scoped Interval in
theorem aemeasurable_uIoc_iff [LinearOrder α] {f : α → β} {a b : α} :
    (AEMeasurable f <| μ.restrict <| Ι a b) ↔
      (AEMeasurable f <| μ.restrict <| Ioc a b) ∧ (AEMeasurable f <| μ.restrict <| Ioc b a) := by
  rw [uIoc_eq_union, aemeasurable_union_iff]

theorem aemeasurable_iff_measurable [μ.IsComplete] : AEMeasurable f μ ↔ Measurable f :=
  ⟨fun h => h.nullMeasurable.measurable_of_complete, fun h => h.aemeasurable⟩

theorem MeasurableEmbedding.aemeasurable_map_iff {g : β → γ} (hf : MeasurableEmbedding f) :
    AEMeasurable g (μ.map f) ↔ AEMeasurable (g ∘ f) μ := by
  refine ⟨fun H => H.comp_measurable hf.measurable, ?_⟩
  rintro ⟨g₁, hgm₁, heq⟩
  rcases hf.exists_measurable_extend hgm₁ fun x => ⟨g x⟩ with ⟨g₂, hgm₂, rfl⟩
  exact ⟨g₂, hgm₂, hf.ae_map_iff.2 heq⟩

theorem MeasurableEmbedding.aemeasurable_comp_iff {g : β → γ} (hg : MeasurableEmbedding g)
    {μ : Measure α} : AEMeasurable (g ∘ f) μ ↔ AEMeasurable f μ := by
  refine ⟨fun H => ?_, hg.measurable.comp_aemeasurable⟩
  suffices AEMeasurable ((rangeSplitting g ∘ rangeFactorization g) ∘ f) μ by
    rwa [(rightInverse_rangeSplitting hg.injective).comp_eq_id] at this
  exact hg.measurable_rangeSplitting.comp_aemeasurable H.subtype_mk

theorem aemeasurable_restrict_iff_comap_subtype {s : Set α} (hs : MeasurableSet s) {μ : Measure α}
    {f : α → β} : AEMeasurable f (μ.restrict s) ↔ AEMeasurable (f ∘ (↑) : s → β) (comap (↑) μ) := by
  rw [← map_comap_subtype_coe hs, (MeasurableEmbedding.subtype_coe hs).aemeasurable_map_iff]

@[to_additive]
theorem aemeasurable_one [One β] : AEMeasurable (fun _ : α => (1 : β)) μ :=
  measurable_one.aemeasurable

@[simp]
theorem aemeasurable_smul_measure_iff {c : ℝ≥0∞} (hc : c ≠ 0) :
    AEMeasurable f (c • μ) ↔ AEMeasurable f μ :=
  ⟨fun h => ⟨h.mk f, h.measurable_mk, (ae_ennreal_smul_measure_iff hc).1 h.ae_eq_mk⟩, fun h =>
    ⟨h.mk f, h.measurable_mk, (ae_ennreal_smul_measure_iff hc).2 h.ae_eq_mk⟩⟩

theorem aemeasurable_of_aemeasurable_trim {α} {m m0 : MeasurableSpace α} {μ : Measure α}
    (hm : m ≤ m0) {f : α → β} (hf : AEMeasurable f (μ.trim hm)) : AEMeasurable f μ :=
  ⟨hf.mk f, Measurable.mono hf.measurable_mk hm le_rfl, ae_eq_of_ae_eq_trim hf.ae_eq_mk⟩

theorem aemeasurable_restrict_of_measurable_subtype {s : Set α} (hs : MeasurableSet s)
    (hf : Measurable fun x : s => f x) : AEMeasurable f (μ.restrict s) :=
  (aemeasurable_restrict_iff_comap_subtype hs).2 hf.aemeasurable

theorem aemeasurable_map_equiv_iff (e : α ≃ᵐ β) {f : β → γ} :
    AEMeasurable f (μ.map e) ↔ AEMeasurable (f ∘ e) μ :=
  e.measurableEmbedding.aemeasurable_map_iff

end

@[fun_prop]
theorem AEMeasurable.restrict (hfm : AEMeasurable f μ) {s} : AEMeasurable f (μ.restrict s) :=
  ⟨AEMeasurable.mk f hfm, hfm.measurable_mk, ae_restrict_of_ae hfm.ae_eq_mk⟩

theorem aemeasurable_Ioi_of_forall_Ioc {β} {mβ : MeasurableSpace β} [LinearOrder α]
    [(atTop : Filter α).IsCountablyGenerated] {x : α} {g : α → β}
    (g_meas : ∀ t > x, AEMeasurable g (μ.restrict (Ioc x t))) :
    AEMeasurable g (μ.restrict (Ioi x)) := by
  haveI : Nonempty α := ⟨x⟩
  obtain ⟨u, hu_tendsto⟩ := exists_seq_tendsto (atTop : Filter α)
  have Ioi_eq_iUnion : Ioi x = ⋃ n : ℕ, Ioc x (u n) := by
    rw [iUnion_Ioc_eq_Ioi_self_iff.mpr _]
    exact fun y _ => (hu_tendsto.eventually (eventually_ge_atTop y)).exists
  rw [Ioi_eq_iUnion, aemeasurable_iUnion_iff]
  intro n
  rcases lt_or_ge x (u n) with h | h
  · exact g_meas (u n) h
  · rw [Ioc_eq_empty (not_lt.mpr h), Measure.restrict_empty]
    exact aemeasurable_zero_measure

section Zero

variable [Zero β]

theorem aemeasurable_indicator_iff {s} (hs : MeasurableSet s) :
    AEMeasurable (indicator s f) μ ↔ AEMeasurable f (μ.restrict s) := by
  constructor
  · intro h
    exact (h.mono_measure Measure.restrict_le_self).congr (indicator_ae_eq_restrict hs)
  · intro h
    refine ⟨indicator s (h.mk f), h.measurable_mk.indicator hs, ?_⟩
    have A : s.indicator f =ᵐ[μ.restrict s] s.indicator (AEMeasurable.mk f h) :=
      (indicator_ae_eq_restrict hs).trans (h.ae_eq_mk.trans <| (indicator_ae_eq_restrict hs).symm)
    have B : s.indicator f =ᵐ[μ.restrict sᶜ] s.indicator (AEMeasurable.mk f h) :=
      (indicator_ae_eq_restrict_compl hs).trans (indicator_ae_eq_restrict_compl hs).symm
    exact ae_of_ae_restrict_of_ae_restrict_compl _ A B

theorem aemeasurable_indicator_iff₀ {s} (hs : NullMeasurableSet s μ) :
    AEMeasurable (indicator s f) μ ↔ AEMeasurable f (μ.restrict s) := by
  rcases hs with ⟨t, ht, hst⟩
  rw [← aemeasurable_congr (indicator_ae_eq_of_ae_eq_set hst.symm), aemeasurable_indicator_iff ht,
      restrict_congr_set hst]

/-- A characterization of the a.e.-measurability of the indicator function which takes a constant
value `b` on a set `A` and `0` elsewhere. -/
lemma aemeasurable_indicator_const_iff {s} [MeasurableSingletonClass β] (b : β) [NeZero b] :
    AEMeasurable (s.indicator (fun _ ↦ b)) μ ↔ NullMeasurableSet s μ := by
  classical
  constructor <;> intro h
  · convert h.nullMeasurable (MeasurableSet.singleton (0 : β)).compl
    rw [indicator_const_preimage_eq_union s {0}ᶜ b]
    simp [NeZero.ne b]
  · exact (aemeasurable_indicator_iff₀ h).mpr aemeasurable_const

@[fun_prop]
theorem AEMeasurable.indicator (hfm : AEMeasurable f μ) {s} (hs : MeasurableSet s) :
    AEMeasurable (s.indicator f) μ :=
  (aemeasurable_indicator_iff hs).mpr hfm.restrict

theorem AEMeasurable.indicator₀ (hfm : AEMeasurable f μ) {s} (hs : NullMeasurableSet s μ) :
    AEMeasurable (s.indicator f) μ :=
  (aemeasurable_indicator_iff₀ hs).mpr hfm.restrict

end Zero

theorem MeasureTheory.Measure.restrict_map_of_aemeasurable {f : α → δ} (hf : AEMeasurable f μ)
    {s : Set δ} (hs : MeasurableSet s) : (μ.map f).restrict s = (μ.restrict <| f ⁻¹' s).map f :=
  calc
    (μ.map f).restrict s = (μ.map (hf.mk f)).restrict s := by
      congr 1
      apply Measure.map_congr hf.ae_eq_mk
    _ = (μ.restrict <| hf.mk f ⁻¹' s).map (hf.mk f) := Measure.restrict_map hf.measurable_mk hs
    _ = (μ.restrict <| hf.mk f ⁻¹' s).map f :=
      (Measure.map_congr (ae_restrict_of_ae hf.ae_eq_mk.symm))
    _ = (μ.restrict <| f ⁻¹' s).map f := by
      apply congr_arg
      ext1 t ht
      simp only [ht, Measure.restrict_apply]
      apply measure_congr
      apply (EventuallyEq.refl _ _).inter (hf.ae_eq_mk.symm.preimage s)

theorem MeasureTheory.Measure.map_mono_of_aemeasurable {f : α → δ} (h : μ ≤ ν)
    (hf : AEMeasurable f ν) : μ.map f ≤ ν.map f :=
  le_iff.2 fun s hs ↦ by simpa [hf, hs, hf.mono_measure h] using h (f ⁻¹' s)

/-- If the `σ`-algebra of the codomain of a null measurable function is countably generated,
then the function is a.e.-measurable. -/
lemma MeasureTheory.NullMeasurable.aemeasurable {f : α → β}
    [hc : MeasurableSpace.CountablyGenerated β] (h : NullMeasurable f μ) : AEMeasurable f μ := by
  classical
  nontriviality β; inhabit β
  rcases hc.1 with ⟨S, hSc, rfl⟩
  choose! T hTf hTm hTeq using fun s hs ↦ (h <| .basic s hs).exists_measurable_subset_ae_eq
  choose! U hUf hUm hUeq using fun s hs ↦ (h <| .basic s hs).exists_measurable_superset_ae_eq
  set v := ⋃ s ∈ S, U s \ T s
  have hvm : MeasurableSet v := .biUnion hSc fun s hs ↦ (hUm s hs).diff (hTm s hs)
  have hvμ : μ v = 0 := (measure_biUnion_null_iff hSc).2 fun s hs ↦ ae_le_set.1 <|
    ((hUeq s hs).trans (hTeq s hs).symm).le
  refine ⟨v.piecewise (fun _ ↦ default) f, ?_, measure_mono_null (fun x ↦
    not_imp_comm.2 fun hxv ↦ (piecewise_eq_of_notMem _ _ _ hxv).symm) hvμ⟩
  refine measurable_of_restrict_of_restrict_compl hvm ?_ ?_
  · rw [restrict_piecewise]
    apply measurable_const
  · rw [restrict_piecewise_compl, restrict_eq]
    refine measurable_generateFrom fun s hs ↦ .of_subtype_image ?_
    rw [preimage_comp, Subtype.image_preimage_coe]
    convert (hTm s hs).diff hvm using 1
    rw [inter_comm]
    refine Set.ext fun x ↦ and_congr_left fun hxv ↦ ⟨fun hx ↦ ?_, fun hx ↦ hTf s hs hx⟩
    exact by_contra fun hx' ↦ hxv <| mem_biUnion hs ⟨hUf s hs hx, hx'⟩

/-- Let `f : α → β` be a null measurable function
such that a.e. all values of `f` belong to a set `t`
such that the restriction of the `σ`-algebra in the codomain to `t` is countably generated,
then `f` is a.e.-measurable. -/
lemma MeasureTheory.NullMeasurable.aemeasurable_of_aerange {f : α → β} {t : Set β}
    [MeasurableSpace.CountablyGenerated t] (h : NullMeasurable f μ) (hft : ∀ᵐ x ∂μ, f x ∈ t) :
    AEMeasurable f μ := by
  rcases eq_empty_or_nonempty t with rfl | hne
  · obtain rfl : μ = 0 := by simpa using hft
    apply aemeasurable_zero_measure
  · rw [← μ.ae_completion] at hft
    obtain ⟨f', hf'm, hf't, hff'⟩ :
        ∃ f' : α → β, NullMeasurable f' μ ∧ range f' ⊆ t ∧ f =ᵐ[μ] f' :=
      h.measurable'.aemeasurable.exists_ae_eq_range_subset hft hne
    rw [range_subset_iff] at hf't
    lift f' to α → t using hf't
    replace hf'm : NullMeasurable f' μ := hf'm.measurable'.subtype_mk
    exact (measurable_subtype_coe.comp_aemeasurable hf'm.aemeasurable).congr hff'.symm

namespace MeasureTheory
namespace Measure

lemma map_sum {ι : Type*} {m : ι → Measure α} {f : α → β} (hf : AEMeasurable f (Measure.sum m)) :
    Measure.map f (Measure.sum m) = Measure.sum (fun i ↦ Measure.map f (m i)) := by
  ext s hs
  rw [map_apply_of_aemeasurable hf hs, sum_apply₀ _ (hf.nullMeasurable hs), sum_apply _ hs]
  have M i : AEMeasurable f (m i) := hf.mono_measure (le_sum m i)
  simp_rw [map_apply_of_aemeasurable (M _) hs]

instance (μ : Measure α) (f : α → β) [SFinite μ] : SFinite (μ.map f) := by
  by_cases H : AEMeasurable f μ
  · rw [← sum_sfiniteSeq μ] at H ⊢
    rw [map_sum H]
    infer_instance
  · rw [map_of_not_aemeasurable H]
    infer_instance

end Measure
end MeasureTheory
