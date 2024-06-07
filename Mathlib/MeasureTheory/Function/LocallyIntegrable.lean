/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn

#align_import measure_theory.function.locally_integrable from "leanprover-community/mathlib"@"08a4542bec7242a5c60f179e4e49de8c0d677b1b"

/-!
# Locally integrable functions

A function is called *locally integrable* (`MeasureTheory.LocallyIntegrable`) if it is integrable
on a neighborhood of every point. More generally, it is *locally integrable on `s`* if it is
locally integrable on a neighbourhood within `s` of any point of `s`.

This file contains properties of locally integrable functions, and integrability results
on compact sets.

## Main statements

* `Continuous.locallyIntegrable`: A continuous function is locally integrable.
* `ContinuousOn.locallyIntegrableOn`: A function which is continuous on `s` is locally
  integrable on `s`.
-/

open MeasureTheory MeasureTheory.Measure Set Function TopologicalSpace Bornology

open scoped Topology Interval ENNReal

variable {X Y E F R : Type*} [MeasurableSpace X] [TopologicalSpace X]
variable [MeasurableSpace Y] [TopologicalSpace Y]
variable [NormedAddCommGroup E] [NormedAddCommGroup F] {f g : X → E} {μ : Measure X} {s : Set X}

namespace MeasureTheory

section LocallyIntegrableOn

/-- A function `f : X → E` is *locally integrable on s*, for `s ⊆ X`, if for every `x ∈ s` there is
a neighbourhood of `x` within `s` on which `f` is integrable. (Note this is, in general, strictly
weaker than local integrability with respect to `μ.restrict s`.) -/
def LocallyIntegrableOn (f : X → E) (s : Set X) (μ : Measure X := by volume_tac) : Prop :=
  ∀ x : X, x ∈ s → IntegrableAtFilter f (𝓝[s] x) μ
#align measure_theory.locally_integrable_on MeasureTheory.LocallyIntegrableOn

theorem LocallyIntegrableOn.mono_set (hf : LocallyIntegrableOn f s μ) {t : Set X}
    (hst : t ⊆ s) : LocallyIntegrableOn f t μ := fun x hx =>
  (hf x <| hst hx).filter_mono (nhdsWithin_mono x hst)
#align measure_theory.locally_integrable_on.mono MeasureTheory.LocallyIntegrableOn.mono_set

theorem LocallyIntegrableOn.norm (hf : LocallyIntegrableOn f s μ) :
    LocallyIntegrableOn (fun x => ‖f x‖) s μ := fun t ht =>
  let ⟨U, hU_nhd, hU_int⟩ := hf t ht
  ⟨U, hU_nhd, hU_int.norm⟩
#align measure_theory.locally_integrable_on.norm MeasureTheory.LocallyIntegrableOn.norm

theorem LocallyIntegrableOn.mono (hf : LocallyIntegrableOn f s μ) {g : X → F}
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖f x‖) :
    LocallyIntegrableOn g s μ := by
  intro x hx
  rcases hf x hx with ⟨t, t_mem, ht⟩
  exact ⟨t, t_mem, Integrable.mono ht hg.restrict (ae_restrict_of_ae h)⟩

theorem IntegrableOn.locallyIntegrableOn (hf : IntegrableOn f s μ) : LocallyIntegrableOn f s μ :=
  fun _ _ => ⟨s, self_mem_nhdsWithin, hf⟩
#align measure_theory.integrable_on.locally_integrable_on MeasureTheory.IntegrableOn.locallyIntegrableOn

/-- If a function is locally integrable on a compact set, then it is integrable on that set. -/
theorem LocallyIntegrableOn.integrableOn_isCompact (hf : LocallyIntegrableOn f s μ)
    (hs : IsCompact s) : IntegrableOn f s μ :=
  IsCompact.induction_on hs integrableOn_empty (fun _u _v huv hv => hv.mono_set huv)
    (fun _u _v hu hv => integrableOn_union.mpr ⟨hu, hv⟩) hf
#align measure_theory.locally_integrable_on.integrable_on_is_compact MeasureTheory.LocallyIntegrableOn.integrableOn_isCompact

theorem LocallyIntegrableOn.integrableOn_compact_subset (hf : LocallyIntegrableOn f s μ) {t : Set X}
    (hst : t ⊆ s) (ht : IsCompact t) : IntegrableOn f t μ :=
  (hf.mono_set hst).integrableOn_isCompact ht
#align measure_theory.locally_integrable_on.integrable_on_compact_subset MeasureTheory.LocallyIntegrableOn.integrableOn_compact_subset

/-- If a function `f` is locally integrable on a set `s` in a second countable topological space,
then there exist countably many open sets `u` covering `s` such that `f` is integrable on each
set `u ∩ s`. -/
theorem LocallyIntegrableOn.exists_countable_integrableOn [SecondCountableTopology X]
    (hf : LocallyIntegrableOn f s μ) : ∃ T : Set (Set X), T.Countable ∧
    (∀ u ∈ T, IsOpen u) ∧ (s ⊆ ⋃ u ∈ T, u) ∧ (∀ u ∈ T, IntegrableOn f (u ∩ s) μ) := by
  have : ∀ x : s, ∃ u, IsOpen u ∧ x.1 ∈ u ∧ IntegrableOn f (u ∩ s) μ := by
    rintro ⟨x, hx⟩
    rcases hf x hx with ⟨t, ht, h't⟩
    rcases mem_nhdsWithin.1 ht with ⟨u, u_open, x_mem, u_sub⟩
    exact ⟨u, u_open, x_mem, h't.mono_set u_sub⟩
  choose u u_open xu hu using this
  obtain ⟨T, T_count, hT⟩ : ∃ T : Set s, T.Countable ∧ s ⊆ ⋃ i ∈ T, u i := by
    have : s ⊆ ⋃ x : s, u x := fun y hy => mem_iUnion_of_mem ⟨y, hy⟩ (xu ⟨y, hy⟩)
    obtain ⟨T, hT_count, hT_un⟩ := isOpen_iUnion_countable u u_open
    exact ⟨T, hT_count, by rwa [hT_un]⟩
  refine ⟨u '' T, T_count.image _, ?_, by rwa [biUnion_image], ?_⟩
  · rintro v ⟨w, -, rfl⟩
    exact u_open _
  · rintro v ⟨w, -, rfl⟩
    exact hu _

/-- If a function `f` is locally integrable on a set `s` in a second countable topological space,
then there exists a sequence of open sets `u n` covering `s` such that `f` is integrable on each
set `u n ∩ s`. -/
theorem LocallyIntegrableOn.exists_nat_integrableOn [SecondCountableTopology X]
    (hf : LocallyIntegrableOn f s μ) : ∃ u : ℕ → Set X,
    (∀ n, IsOpen (u n)) ∧ (s ⊆ ⋃ n, u n) ∧ (∀ n, IntegrableOn f (u n ∩ s) μ) := by
  rcases hf.exists_countable_integrableOn with ⟨T, T_count, T_open, sT, hT⟩
  let T' : Set (Set X) := insert ∅ T
  have T'_count : T'.Countable := Countable.insert ∅ T_count
  have T'_ne : T'.Nonempty := by simp only [T', insert_nonempty]
  rcases T'_count.exists_eq_range T'_ne with ⟨u, hu⟩
  refine ⟨u, ?_, ?_, ?_⟩
  · intro n
    have : u n ∈ T' := by rw [hu]; exact mem_range_self n
    rcases mem_insert_iff.1 this with h|h
    · rw [h]
      exact isOpen_empty
    · exact T_open _ h
  · intro x hx
    obtain ⟨v, hv, h'v⟩ : ∃ v, v ∈ T ∧ x ∈ v := by simpa only [mem_iUnion, exists_prop] using sT hx
    have : v ∈ range u := by rw [← hu]; exact subset_insert ∅ T hv
    obtain ⟨n, rfl⟩ : ∃ n, u n = v := by simpa only [mem_range] using this
    exact mem_iUnion_of_mem _ h'v
  · intro n
    have : u n ∈ T' := by rw [hu]; exact mem_range_self n
    rcases mem_insert_iff.1 this with h|h
    · simp only [h, empty_inter, integrableOn_empty]
    · exact hT _ h

theorem LocallyIntegrableOn.aestronglyMeasurable [SecondCountableTopology X]
    (hf : LocallyIntegrableOn f s μ) : AEStronglyMeasurable f (μ.restrict s) := by
  rcases hf.exists_nat_integrableOn with ⟨u, -, su, hu⟩
  have : s = ⋃ n, u n ∩ s := by rw [← iUnion_inter]; exact (inter_eq_right.mpr su).symm
  rw [this, aestronglyMeasurable_iUnion_iff]
  exact fun i : ℕ => (hu i).aestronglyMeasurable
#align measure_theory.locally_integrable_on.ae_strongly_measurable MeasureTheory.LocallyIntegrableOn.aestronglyMeasurable

/-- If `s` is either open, or closed, then `f` is locally integrable on `s` iff it is integrable on
every compact subset contained in `s`. -/
theorem locallyIntegrableOn_iff [LocallyCompactSpace X] [T2Space X] (hs : IsClosed s ∨ IsOpen s) :
    LocallyIntegrableOn f s μ ↔ ∀ (k : Set X), k ⊆ s → (IsCompact k → IntegrableOn f k μ) := by
  -- The correct condition is that `s` be *locally closed*, i.e. for every `x ∈ s` there is some
  -- `U ∈ 𝓝 x` such that `U ∩ s` is closed. But mathlib doesn't have locally closed sets yet.
  refine ⟨fun hf k hk => hf.integrableOn_compact_subset hk, fun hf x hx => ?_⟩
  cases hs with
  | inl hs =>
    exact
      let ⟨K, hK, h2K⟩ := exists_compact_mem_nhds x
      ⟨_, inter_mem_nhdsWithin s h2K,
        hf _ (inter_subset_left _ _)
          (hK.of_isClosed_subset (hs.inter hK.isClosed) (inter_subset_right _ _))⟩
  | inr hs =>
    obtain ⟨K, hK, h2K, h3K⟩ := exists_compact_subset hs hx
    refine ⟨K, ?_, hf K h3K hK⟩
    simpa only [IsOpen.nhdsWithin_eq hs hx, interior_eq_nhds'] using h2K
#align measure_theory.locally_integrable_on_iff MeasureTheory.locallyIntegrableOn_iff

protected theorem LocallyIntegrableOn.add
    (hf : LocallyIntegrableOn f s μ) (hg : LocallyIntegrableOn g s μ) :
    LocallyIntegrableOn (f + g) s μ := fun x hx ↦ (hf x hx).add (hg x hx)

protected theorem LocallyIntegrableOn.sub
    (hf : LocallyIntegrableOn f s μ) (hg : LocallyIntegrableOn g s μ) :
    LocallyIntegrableOn (f - g) s μ := fun x hx ↦ (hf x hx).sub (hg x hx)

protected theorem LocallyIntegrableOn.neg (hf : LocallyIntegrableOn f s μ) :
    LocallyIntegrableOn (-f) s μ := fun x hx ↦ (hf x hx).neg

end LocallyIntegrableOn

/-- A function `f : X → E` is *locally integrable* if it is integrable on a neighborhood of every
point. In particular, it is integrable on all compact sets,
see `LocallyIntegrable.integrableOn_isCompact`. -/
def LocallyIntegrable (f : X → E) (μ : Measure X := by volume_tac) : Prop :=
  ∀ x : X, IntegrableAtFilter f (𝓝 x) μ
#align measure_theory.locally_integrable MeasureTheory.LocallyIntegrable

theorem locallyIntegrable_comap (hs : MeasurableSet s) :
    LocallyIntegrable (fun x : s ↦ f x) (μ.comap Subtype.val) ↔ LocallyIntegrableOn f s μ := by
  simp_rw [LocallyIntegrableOn, Subtype.forall', ← map_nhds_subtype_val]
  exact forall_congr' fun _ ↦ (MeasurableEmbedding.subtype_coe hs).integrableAtFilter_iff_comap.symm

theorem locallyIntegrableOn_univ : LocallyIntegrableOn f univ μ ↔ LocallyIntegrable f μ := by
  simp only [LocallyIntegrableOn, nhdsWithin_univ, mem_univ, true_imp_iff]; rfl
#align measure_theory.locally_integrable_on_univ MeasureTheory.locallyIntegrableOn_univ

theorem LocallyIntegrable.locallyIntegrableOn (hf : LocallyIntegrable f μ) (s : Set X) :
    LocallyIntegrableOn f s μ := fun x _ => (hf x).filter_mono nhdsWithin_le_nhds
#align measure_theory.locally_integrable.locally_integrable_on MeasureTheory.LocallyIntegrable.locallyIntegrableOn

theorem Integrable.locallyIntegrable (hf : Integrable f μ) : LocallyIntegrable f μ := fun _ =>
  hf.integrableAtFilter _
#align measure_theory.integrable.locally_integrable MeasureTheory.Integrable.locallyIntegrable

theorem LocallyIntegrable.mono (hf : LocallyIntegrable f μ) {g : X → F}
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖f x‖) :
    LocallyIntegrable g μ := by
  rw [← locallyIntegrableOn_univ] at hf ⊢
  exact hf.mono hg h

/-- If `f` is locally integrable with respect to `μ.restrict s`, it is locally integrable on `s`.
(See `locallyIntegrableOn_iff_locallyIntegrable_restrict` for an iff statement when `s` is
closed.) -/
theorem locallyIntegrableOn_of_locallyIntegrable_restrict [OpensMeasurableSpace X]
    (hf : LocallyIntegrable f (μ.restrict s)) : LocallyIntegrableOn f s μ := by
  intro x _
  obtain ⟨t, ht_mem, ht_int⟩ := hf x
  obtain ⟨u, hu_sub, hu_o, hu_mem⟩ := mem_nhds_iff.mp ht_mem
  refine ⟨_, inter_mem_nhdsWithin s (hu_o.mem_nhds hu_mem), ?_⟩
  simpa only [IntegrableOn, Measure.restrict_restrict hu_o.measurableSet, inter_comm] using
    ht_int.mono_set hu_sub
#align measure_theory.locally_integrable_on_of_locally_integrable_restrict MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict

/-- If `s` is closed, being locally integrable on `s` wrt `μ` is equivalent to being locally
integrable with respect to `μ.restrict s`. For the one-way implication without assuming `s` closed,
see `locallyIntegrableOn_of_locallyIntegrable_restrict`. -/
theorem locallyIntegrableOn_iff_locallyIntegrable_restrict [OpensMeasurableSpace X]
    (hs : IsClosed s) : LocallyIntegrableOn f s μ ↔ LocallyIntegrable f (μ.restrict s) := by
  refine ⟨fun hf x => ?_, locallyIntegrableOn_of_locallyIntegrable_restrict⟩
  by_cases h : x ∈ s
  · obtain ⟨t, ht_nhds, ht_int⟩ := hf x h
    obtain ⟨u, hu_o, hu_x, hu_sub⟩ := mem_nhdsWithin.mp ht_nhds
    refine ⟨u, hu_o.mem_nhds hu_x, ?_⟩
    rw [IntegrableOn, restrict_restrict hu_o.measurableSet]
    exact ht_int.mono_set hu_sub
  · rw [← isOpen_compl_iff] at hs
    refine ⟨sᶜ, hs.mem_nhds h, ?_⟩
    rw [IntegrableOn, restrict_restrict, inter_comm, inter_compl_self, ← IntegrableOn]
    exacts [integrableOn_empty, hs.measurableSet]
#align measure_theory.locally_integrable_on_iff_locally_integrable_restrict MeasureTheory.locallyIntegrableOn_iff_locallyIntegrable_restrict

/-- If a function is locally integrable, then it is integrable on any compact set. -/
theorem LocallyIntegrable.integrableOn_isCompact {k : Set X} (hf : LocallyIntegrable f μ)
    (hk : IsCompact k) : IntegrableOn f k μ :=
  (hf.locallyIntegrableOn k).integrableOn_isCompact hk
#align measure_theory.locally_integrable.integrable_on_is_compact MeasureTheory.LocallyIntegrable.integrableOn_isCompact

/-- If a function is locally integrable, then it is integrable on an open neighborhood of any
compact set. -/
theorem LocallyIntegrable.integrableOn_nhds_isCompact (hf : LocallyIntegrable f μ) {k : Set X}
    (hk : IsCompact k) : ∃ u, IsOpen u ∧ k ⊆ u ∧ IntegrableOn f u μ := by
  refine IsCompact.induction_on hk ?_ ?_ ?_ ?_
  · refine ⟨∅, isOpen_empty, Subset.rfl, integrableOn_empty⟩
  · rintro s t hst ⟨u, u_open, tu, hu⟩
    exact ⟨u, u_open, hst.trans tu, hu⟩
  · rintro s t ⟨u, u_open, su, hu⟩ ⟨v, v_open, tv, hv⟩
    exact ⟨u ∪ v, u_open.union v_open, union_subset_union su tv, hu.union hv⟩
  · intro x _
    rcases hf x with ⟨u, ux, hu⟩
    rcases mem_nhds_iff.1 ux with ⟨v, vu, v_open, xv⟩
    exact ⟨v, nhdsWithin_le_nhds (v_open.mem_nhds xv), v, v_open, Subset.rfl, hu.mono_set vu⟩
#align measure_theory.locally_integrable.integrable_on_nhds_is_compact MeasureTheory.LocallyIntegrable.integrableOn_nhds_isCompact

theorem locallyIntegrable_iff [LocallyCompactSpace X] :
    LocallyIntegrable f μ ↔ ∀ k : Set X, IsCompact k → IntegrableOn f k μ :=
  ⟨fun hf _k hk => hf.integrableOn_isCompact hk, fun hf x =>
    let ⟨K, hK, h2K⟩ := exists_compact_mem_nhds x
    ⟨K, h2K, hf K hK⟩⟩
#align measure_theory.locally_integrable_iff MeasureTheory.locallyIntegrable_iff

theorem LocallyIntegrable.aestronglyMeasurable [SecondCountableTopology X]
    (hf : LocallyIntegrable f μ) : AEStronglyMeasurable f μ := by
  simpa only [restrict_univ] using (locallyIntegrableOn_univ.mpr hf).aestronglyMeasurable
#align measure_theory.locally_integrable.ae_strongly_measurable MeasureTheory.LocallyIntegrable.aestronglyMeasurable

/-- If a function is locally integrable in a second countable topological space,
then there exists a sequence of open sets covering the space on which it is integrable. -/
theorem LocallyIntegrable.exists_nat_integrableOn [SecondCountableTopology X]
    (hf : LocallyIntegrable f μ) : ∃ u : ℕ → Set X,
    (∀ n, IsOpen (u n)) ∧ ((⋃ n, u n) = univ) ∧ (∀ n, IntegrableOn f (u n) μ) := by
  rcases (hf.locallyIntegrableOn univ).exists_nat_integrableOn with ⟨u, u_open, u_union, hu⟩
  refine ⟨u, u_open, eq_univ_of_univ_subset u_union, fun n ↦ ?_⟩
  simpa only [inter_univ] using hu n

theorem Memℒp.locallyIntegrable [IsLocallyFiniteMeasure μ] {f : X → E} {p : ℝ≥0∞}
    (hf : Memℒp f p μ) (hp : 1 ≤ p) : LocallyIntegrable f μ := by
  intro x
  rcases μ.finiteAt_nhds x with ⟨U, hU, h'U⟩
  have : Fact (μ U < ⊤) := ⟨h'U⟩
  refine ⟨U, hU, ?_⟩
  rw [IntegrableOn, ← memℒp_one_iff_integrable]
  apply (hf.restrict U).memℒp_of_exponent_le hp

theorem locallyIntegrable_const [IsLocallyFiniteMeasure μ] (c : E) :
    LocallyIntegrable (fun _ => c) μ :=
  (memℒp_top_const c).locallyIntegrable le_top
#align measure_theory.locally_integrable_const MeasureTheory.locallyIntegrable_const

theorem locallyIntegrableOn_const [IsLocallyFiniteMeasure μ] (c : E) :
    LocallyIntegrableOn (fun _ => c) s μ :=
  (locallyIntegrable_const c).locallyIntegrableOn s
#align measure_theory.locally_integrable_on_const MeasureTheory.locallyIntegrableOn_const

theorem locallyIntegrable_zero : LocallyIntegrable (fun _ ↦ (0 : E)) μ :=
  (integrable_zero X E μ).locallyIntegrable

theorem locallyIntegrableOn_zero : LocallyIntegrableOn (fun _ ↦ (0 : E)) s μ :=
  locallyIntegrable_zero.locallyIntegrableOn s

theorem LocallyIntegrable.indicator (hf : LocallyIntegrable f μ) {s : Set X}
    (hs : MeasurableSet s) : LocallyIntegrable (s.indicator f) μ := by
  intro x
  rcases hf x with ⟨U, hU, h'U⟩
  exact ⟨U, hU, h'U.indicator hs⟩
#align measure_theory.locally_integrable.indicator MeasureTheory.LocallyIntegrable.indicator

theorem locallyIntegrable_map_homeomorph [BorelSpace X] [BorelSpace Y] (e : X ≃ₜ Y) {f : Y → E}
    {μ : Measure X} : LocallyIntegrable f (Measure.map e μ) ↔ LocallyIntegrable (f ∘ e) μ := by
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · rcases h (e x) with ⟨U, hU, h'U⟩
    refine ⟨e ⁻¹' U, e.continuous.continuousAt.preimage_mem_nhds hU, ?_⟩
    exact (integrableOn_map_equiv e.toMeasurableEquiv).1 h'U
  · rcases h (e.symm x) with ⟨U, hU, h'U⟩
    refine ⟨e.symm ⁻¹' U, e.symm.continuous.continuousAt.preimage_mem_nhds hU, ?_⟩
    apply (integrableOn_map_equiv e.toMeasurableEquiv).2
    simp only [Homeomorph.toMeasurableEquiv_coe]
    convert h'U
    ext x
    simp only [mem_preimage, Homeomorph.symm_apply_apply]
#align measure_theory.locally_integrable_map_homeomorph MeasureTheory.locallyIntegrable_map_homeomorph

protected theorem LocallyIntegrable.add (hf : LocallyIntegrable f μ) (hg : LocallyIntegrable g μ) :
    LocallyIntegrable (f + g) μ := fun x ↦ (hf x).add (hg x)

protected theorem LocallyIntegrable.sub (hf : LocallyIntegrable f μ) (hg : LocallyIntegrable g μ) :
    LocallyIntegrable (f - g) μ := fun x ↦ (hf x).sub (hg x)

protected theorem LocallyIntegrable.neg (hf : LocallyIntegrable f μ) :
    LocallyIntegrable (-f) μ := fun x ↦ (hf x).neg

protected theorem LocallyIntegrable.smul {𝕜 : Type*} [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 E]
    [BoundedSMul 𝕜 E] (hf : LocallyIntegrable f μ) (c : 𝕜) :
    LocallyIntegrable (c • f) μ := fun x ↦ (hf x).smul c

theorem locallyIntegrable_finset_sum' {ι} (s : Finset ι) {f : ι → X → E}
    (hf : ∀ i ∈ s, LocallyIntegrable (f i) μ) : LocallyIntegrable (∑ i ∈ s, f i) μ :=
  Finset.sum_induction f (fun g => LocallyIntegrable g μ) (fun _ _ => LocallyIntegrable.add)
    locallyIntegrable_zero hf

theorem locallyIntegrable_finset_sum {ι} (s : Finset ι) {f : ι → X → E}
    (hf : ∀ i ∈ s, LocallyIntegrable (f i) μ) : LocallyIntegrable (fun a ↦ ∑ i ∈ s, f i a) μ := by
  simpa only [← Finset.sum_apply] using locallyIntegrable_finset_sum' s hf

/-- If `f` is locally integrable and `g` is continuous with compact support,
then `g • f` is integrable. -/
theorem LocallyIntegrable.integrable_smul_left_of_hasCompactSupport
    [NormedSpace ℝ E] [OpensMeasurableSpace X] [T2Space X]
    (hf : LocallyIntegrable f μ) {g : X → ℝ} (hg : Continuous g) (h'g : HasCompactSupport g) :
    Integrable (fun x ↦ g x • f x) μ := by
  let K := tsupport g
  have hK : IsCompact K := h'g
  have : K.indicator (fun x ↦ g x • f x) = (fun x ↦ g x • f x) := by
    apply indicator_eq_self.2
    apply support_subset_iff'.2
    intros x hx
    simp [image_eq_zero_of_nmem_tsupport hx]
  rw [← this, indicator_smul]
  apply Integrable.smul_of_top_right
  · rw [integrable_indicator_iff hK.measurableSet]
    exact hf.integrableOn_isCompact hK
  · exact hg.memℒp_top_of_hasCompactSupport h'g μ

/-- If `f` is locally integrable and `g` is continuous with compact support,
then `f • g` is integrable. -/
theorem LocallyIntegrable.integrable_smul_right_of_hasCompactSupport
    [NormedSpace ℝ E] [OpensMeasurableSpace X] [T2Space X] {f : X → ℝ} (hf : LocallyIntegrable f μ)
    {g : X → E} (hg : Continuous g) (h'g : HasCompactSupport g) :
    Integrable (fun x ↦ f x • g x) μ := by
  let K := tsupport g
  have hK : IsCompact K := h'g
  have : K.indicator (fun x ↦ f x • g x) = (fun x ↦ f x • g x) := by
    apply indicator_eq_self.2
    apply support_subset_iff'.2
    intros x hx
    simp [image_eq_zero_of_nmem_tsupport hx]
  rw [← this, indicator_smul_left]
  apply Integrable.smul_of_top_left
  · rw [integrable_indicator_iff hK.measurableSet]
    exact hf.integrableOn_isCompact hK
  · exact hg.memℒp_top_of_hasCompactSupport h'g μ

open Filter

theorem integrable_iff_integrableAtFilter_cocompact :
    Integrable f μ ↔ (IntegrableAtFilter f (cocompact X) μ ∧ LocallyIntegrable f μ) := by
  refine ⟨fun hf ↦ ⟨hf.integrableAtFilter _, hf.locallyIntegrable⟩, fun ⟨⟨s, hsc, hs⟩, hloc⟩ ↦ ?_⟩
  obtain ⟨t, htc, ht⟩ := mem_cocompact'.mp hsc
  rewrite [← integrableOn_univ, ← compl_union_self s, integrableOn_union]
  exact ⟨(hloc.integrableOn_isCompact htc).mono ht le_rfl, hs⟩

theorem integrable_iff_integrableAtFilter_atBot_atTop [LinearOrder X] [CompactIccSpace X] :
    Integrable f μ ↔
    (IntegrableAtFilter f atBot μ ∧ IntegrableAtFilter f atTop μ) ∧ LocallyIntegrable f μ := by
  constructor
  · exact fun hf ↦ ⟨⟨hf.integrableAtFilter _, hf.integrableAtFilter _⟩, hf.locallyIntegrable⟩
  · refine fun h ↦ integrable_iff_integrableAtFilter_cocompact.mpr ⟨?_, h.2⟩
    exact (IntegrableAtFilter.sup_iff.mpr h.1).filter_mono cocompact_le_atBot_atTop

theorem integrable_iff_integrableAtFilter_atBot [LinearOrder X] [OrderTop X] [CompactIccSpace X] :
    Integrable f μ ↔ IntegrableAtFilter f atBot μ ∧ LocallyIntegrable f μ := by
  constructor
  · exact fun hf ↦ ⟨hf.integrableAtFilter _, hf.locallyIntegrable⟩
  · refine fun h ↦ integrable_iff_integrableAtFilter_cocompact.mpr ⟨?_, h.2⟩
    exact h.1.filter_mono cocompact_le_atBot

theorem integrable_iff_integrableAtFilter_atTop [LinearOrder X] [OrderBot X] [CompactIccSpace X] :
    Integrable f μ ↔ IntegrableAtFilter f atTop μ ∧ LocallyIntegrable f μ :=
  integrable_iff_integrableAtFilter_atBot (X := Xᵒᵈ)

variable {a : X}

theorem integrableOn_Iic_iff_integrableAtFilter_atBot [LinearOrder X] [CompactIccSpace X] :
    IntegrableOn f (Iic a) μ ↔ IntegrableAtFilter f atBot μ ∧ LocallyIntegrableOn f (Iic a) μ := by
  refine ⟨fun h ↦ ⟨⟨Iic a, Iic_mem_atBot a, h⟩, h.locallyIntegrableOn⟩, fun ⟨⟨s, hsl, hs⟩, h⟩ ↦ ?_⟩
  haveI : Nonempty X := Nonempty.intro a
  obtain ⟨a', ha'⟩ := mem_atBot_sets.mp hsl
  refine (integrableOn_union.mpr ⟨hs.mono ha' le_rfl, ?_⟩).mono Iic_subset_Iic_union_Icc le_rfl
  exact h.integrableOn_compact_subset Icc_subset_Iic_self isCompact_Icc

theorem integrableOn_Ici_iff_integrableAtFilter_atTop [LinearOrder X] [CompactIccSpace X] :
    IntegrableOn f (Ici a) μ ↔ IntegrableAtFilter f atTop μ ∧ LocallyIntegrableOn f (Ici a) μ :=
  integrableOn_Iic_iff_integrableAtFilter_atBot (X := Xᵒᵈ)

theorem integrableOn_Iio_iff_integrableAtFilter_atBot_nhdsWithin
    [LinearOrder X] [CompactIccSpace X] [NoMinOrder X] [OrderTopology X] :
    IntegrableOn f (Iio a) μ ↔ IntegrableAtFilter f atBot μ ∧
    IntegrableAtFilter f (𝓝[<] a) μ ∧ LocallyIntegrableOn f (Iio a) μ := by
  constructor
  · intro h
    exact ⟨⟨Iio a, Iio_mem_atBot a, h⟩, ⟨Iio a, self_mem_nhdsWithin, h⟩, h.locallyIntegrableOn⟩
  · intro ⟨hbot, ⟨s, hsl, hs⟩, hlocal⟩
    obtain ⟨s', ⟨hs'_mono, hs'⟩⟩ := mem_nhdsWithin_Iio_iff_exists_Ioo_subset.mp hsl
    refine (integrableOn_union.mpr ⟨?_, hs.mono hs' le_rfl⟩).mono Iio_subset_Iic_union_Ioo le_rfl
    exact integrableOn_Iic_iff_integrableAtFilter_atBot.mpr
      ⟨hbot, hlocal.mono_set (Iic_subset_Iio.mpr hs'_mono)⟩

theorem integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin
    [LinearOrder X] [CompactIccSpace X] [NoMaxOrder X] [OrderTopology X] :
    IntegrableOn f (Ioi a) μ ↔ IntegrableAtFilter f atTop μ ∧
    IntegrableAtFilter f (𝓝[>] a) μ ∧ LocallyIntegrableOn f (Ioi a) μ :=
  integrableOn_Iio_iff_integrableAtFilter_atBot_nhdsWithin (X := Xᵒᵈ)

end MeasureTheory

open MeasureTheory

section borel

variable [OpensMeasurableSpace X]
variable {K : Set X} {a b : X}

/-- A continuous function `f` is locally integrable with respect to any locally finite measure. -/
theorem Continuous.locallyIntegrable [IsLocallyFiniteMeasure μ] [SecondCountableTopologyEither X E]
    (hf : Continuous f) : LocallyIntegrable f μ :=
  hf.integrableAt_nhds
#align continuous.locally_integrable Continuous.locallyIntegrable

/-- A function `f` continuous on a set `K` is locally integrable on this set with respect
to any locally finite measure. -/
theorem ContinuousOn.locallyIntegrableOn [IsLocallyFiniteMeasure μ]
    [SecondCountableTopologyEither X E] (hf : ContinuousOn f K)
    (hK : MeasurableSet K) : LocallyIntegrableOn f K μ := fun _x hx =>
  hf.integrableAt_nhdsWithin hK hx
#align continuous_on.locally_integrable_on ContinuousOn.locallyIntegrableOn

variable [IsFiniteMeasureOnCompacts μ]

/-- A function `f` continuous on a compact set `K` is integrable on this set with respect to any
locally finite measure. -/
theorem ContinuousOn.integrableOn_compact'
    (hK : IsCompact K) (h'K : MeasurableSet K) (hf : ContinuousOn f K) :
    IntegrableOn f K μ := by
  refine ⟨ContinuousOn.aestronglyMeasurable_of_isCompact hf hK h'K, ?_⟩
  have : Fact (μ K < ∞) := ⟨hK.measure_lt_top⟩
  obtain ⟨C, hC⟩ : ∃ C, ∀ x ∈ f '' K, ‖x‖ ≤ C :=
    IsBounded.exists_norm_le (hK.image_of_continuousOn hf).isBounded
  apply hasFiniteIntegral_of_bounded (C := C)
  filter_upwards [ae_restrict_mem h'K] with x hx using hC _ (mem_image_of_mem f hx)

theorem ContinuousOn.integrableOn_compact [T2Space X]
    (hK : IsCompact K) (hf : ContinuousOn f K) : IntegrableOn f K μ :=
  hf.integrableOn_compact' hK hK.measurableSet
#align continuous_on.integrable_on_compact ContinuousOn.integrableOn_compact

theorem ContinuousOn.integrableOn_Icc [Preorder X] [CompactIccSpace X] [T2Space X]
    (hf : ContinuousOn f (Icc a b)) : IntegrableOn f (Icc a b) μ :=
  hf.integrableOn_compact isCompact_Icc
#align continuous_on.integrable_on_Icc ContinuousOn.integrableOn_Icc

theorem Continuous.integrableOn_Icc [Preorder X] [CompactIccSpace X] [T2Space X]
    (hf : Continuous f) : IntegrableOn f (Icc a b) μ :=
  hf.continuousOn.integrableOn_Icc
#align continuous.integrable_on_Icc Continuous.integrableOn_Icc

theorem Continuous.integrableOn_Ioc [Preorder X] [CompactIccSpace X] [T2Space X]
    (hf : Continuous f) : IntegrableOn f (Ioc a b) μ :=
  hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self
#align continuous.integrable_on_Ioc Continuous.integrableOn_Ioc

theorem ContinuousOn.integrableOn_uIcc [LinearOrder X] [CompactIccSpace X] [T2Space X]
    (hf : ContinuousOn f [[a, b]]) : IntegrableOn f [[a, b]] μ :=
  hf.integrableOn_Icc
#align continuous_on.integrable_on_uIcc ContinuousOn.integrableOn_uIcc

theorem Continuous.integrableOn_uIcc [LinearOrder X] [CompactIccSpace X] [T2Space X]
    (hf : Continuous f) : IntegrableOn f [[a, b]] μ :=
  hf.integrableOn_Icc
#align continuous.integrable_on_uIcc Continuous.integrableOn_uIcc

theorem Continuous.integrableOn_uIoc [LinearOrder X] [CompactIccSpace X] [T2Space X]
    (hf : Continuous f) : IntegrableOn f (Ι a b) μ :=
  hf.integrableOn_Ioc
#align continuous.integrable_on_uIoc Continuous.integrableOn_uIoc

/-- A continuous function with compact support is integrable on the whole space. -/
theorem Continuous.integrable_of_hasCompactSupport (hf : Continuous f) (hcf : HasCompactSupport f) :
    Integrable f μ :=
  (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).mp <|
    hf.continuousOn.integrableOn_compact' hcf (isClosed_tsupport _).measurableSet
#align continuous.integrable_of_has_compact_support Continuous.integrable_of_hasCompactSupport

end borel

open scoped ENNReal

section Monotone

variable [BorelSpace X] [ConditionallyCompleteLinearOrder X] [ConditionallyCompleteLinearOrder E]
  [OrderTopology X] [OrderTopology E] [SecondCountableTopology E]

theorem MonotoneOn.integrableOn_of_measure_ne_top (hmono : MonotoneOn f s) {a b : X}
    (ha : IsLeast s a) (hb : IsGreatest s b) (hs : μ s ≠ ∞) (h's : MeasurableSet s) :
    IntegrableOn f s μ := by
  borelize E
  obtain rfl | _ := s.eq_empty_or_nonempty
  · exact integrableOn_empty
  have hbelow : BddBelow (f '' s) := ⟨f a, fun x ⟨y, hy, hyx⟩ => hyx ▸ hmono ha.1 hy (ha.2 hy)⟩
  have habove : BddAbove (f '' s) := ⟨f b, fun x ⟨y, hy, hyx⟩ => hyx ▸ hmono hy hb.1 (hb.2 hy)⟩
  have : IsBounded (f '' s) := Metric.isBounded_of_bddAbove_of_bddBelow habove hbelow
  rcases isBounded_iff_forall_norm_le.mp this with ⟨C, hC⟩
  have A : IntegrableOn (fun _ => C) s μ := by
    simp only [hs.lt_top, integrableOn_const, or_true_iff]
  exact
    Integrable.mono' A (aemeasurable_restrict_of_monotoneOn h's hmono).aestronglyMeasurable
      ((ae_restrict_iff' h's).mpr <| ae_of_all _ fun y hy => hC (f y) (mem_image_of_mem f hy))
#align monotone_on.integrable_on_of_measure_ne_top MonotoneOn.integrableOn_of_measure_ne_top

theorem MonotoneOn.integrableOn_isCompact [IsFiniteMeasureOnCompacts μ] (hs : IsCompact s)
    (hmono : MonotoneOn f s) : IntegrableOn f s μ := by
  obtain rfl | h := s.eq_empty_or_nonempty
  · exact integrableOn_empty
  · exact
      hmono.integrableOn_of_measure_ne_top (hs.isLeast_sInf h) (hs.isGreatest_sSup h)
        hs.measure_lt_top.ne hs.measurableSet
#align monotone_on.integrable_on_is_compact MonotoneOn.integrableOn_isCompact

theorem AntitoneOn.integrableOn_of_measure_ne_top (hanti : AntitoneOn f s) {a b : X}
    (ha : IsLeast s a) (hb : IsGreatest s b) (hs : μ s ≠ ∞) (h's : MeasurableSet s) :
    IntegrableOn f s μ :=
  hanti.dual_right.integrableOn_of_measure_ne_top ha hb hs h's
#align antitone_on.integrable_on_of_measure_ne_top AntitoneOn.integrableOn_of_measure_ne_top

theorem AntioneOn.integrableOn_isCompact [IsFiniteMeasureOnCompacts μ] (hs : IsCompact s)
    (hanti : AntitoneOn f s) : IntegrableOn f s μ :=
  hanti.dual_right.integrableOn_isCompact (E := Eᵒᵈ) hs
#align antione_on.integrable_on_is_compact AntioneOn.integrableOn_isCompact

theorem Monotone.locallyIntegrable [IsLocallyFiniteMeasure μ] (hmono : Monotone f) :
    LocallyIntegrable f μ := by
  intro x
  rcases μ.finiteAt_nhds x with ⟨U, hU, h'U⟩
  obtain ⟨a, b, xab, hab, abU⟩ : ∃ a b : X, x ∈ Icc a b ∧ Icc a b ∈ 𝓝 x ∧ Icc a b ⊆ U :=
    exists_Icc_mem_subset_of_mem_nhds hU
  have ab : a ≤ b := xab.1.trans xab.2
  refine ⟨Icc a b, hab, ?_⟩
  exact
    (hmono.monotoneOn _).integrableOn_of_measure_ne_top (isLeast_Icc ab) (isGreatest_Icc ab)
      ((measure_mono abU).trans_lt h'U).ne measurableSet_Icc
#align monotone.locally_integrable Monotone.locallyIntegrable

theorem Antitone.locallyIntegrable [IsLocallyFiniteMeasure μ] (hanti : Antitone f) :
    LocallyIntegrable f μ :=
  hanti.dual_right.locallyIntegrable
#align antitone.locally_integrable Antitone.locallyIntegrable

end Monotone

namespace MeasureTheory

variable [OpensMeasurableSpace X] {A K : Set X}

section Mul

variable [NormedRing R] [SecondCountableTopologyEither X R] {g g' : X → R}

theorem IntegrableOn.mul_continuousOn_of_subset (hg : IntegrableOn g A μ) (hg' : ContinuousOn g' K)
    (hA : MeasurableSet A) (hK : IsCompact K) (hAK : A ⊆ K) :
    IntegrableOn (fun x => g x * g' x) A μ := by
  rcases IsCompact.exists_bound_of_continuousOn hK hg' with ⟨C, hC⟩
  rw [IntegrableOn, ← memℒp_one_iff_integrable] at hg ⊢
  have : ∀ᵐ x ∂μ.restrict A, ‖g x * g' x‖ ≤ C * ‖g x‖ := by
    filter_upwards [ae_restrict_mem hA] with x hx
    refine (norm_mul_le _ _).trans ?_
    rw [mul_comm]
    gcongr
    exact hC x (hAK hx)
  exact
    Memℒp.of_le_mul hg (hg.aestronglyMeasurable.mul <| (hg'.mono hAK).aestronglyMeasurable hA) this
#align measure_theory.integrable_on.mul_continuous_on_of_subset MeasureTheory.IntegrableOn.mul_continuousOn_of_subset

theorem IntegrableOn.mul_continuousOn [T2Space X] (hg : IntegrableOn g K μ)
    (hg' : ContinuousOn g' K) (hK : IsCompact K) : IntegrableOn (fun x => g x * g' x) K μ :=
  hg.mul_continuousOn_of_subset hg' hK.measurableSet hK (Subset.refl _)
#align measure_theory.integrable_on.mul_continuous_on MeasureTheory.IntegrableOn.mul_continuousOn

theorem IntegrableOn.continuousOn_mul_of_subset (hg : ContinuousOn g K) (hg' : IntegrableOn g' A μ)
    (hK : IsCompact K) (hA : MeasurableSet A) (hAK : A ⊆ K) :
    IntegrableOn (fun x => g x * g' x) A μ := by
  rcases IsCompact.exists_bound_of_continuousOn hK hg with ⟨C, hC⟩
  rw [IntegrableOn, ← memℒp_one_iff_integrable] at hg' ⊢
  have : ∀ᵐ x ∂μ.restrict A, ‖g x * g' x‖ ≤ C * ‖g' x‖ := by
    filter_upwards [ae_restrict_mem hA] with x hx
    refine (norm_mul_le _ _).trans ?_
    gcongr
    exact hC x (hAK hx)
  exact
    Memℒp.of_le_mul hg' (((hg.mono hAK).aestronglyMeasurable hA).mul hg'.aestronglyMeasurable) this
#align measure_theory.integrable_on.continuous_on_mul_of_subset MeasureTheory.IntegrableOn.continuousOn_mul_of_subset

theorem IntegrableOn.continuousOn_mul [T2Space X] (hg : ContinuousOn g K)
    (hg' : IntegrableOn g' K μ) (hK : IsCompact K) : IntegrableOn (fun x => g x * g' x) K μ :=
  hg'.continuousOn_mul_of_subset hg hK hK.measurableSet Subset.rfl
#align measure_theory.integrable_on.continuous_on_mul MeasureTheory.IntegrableOn.continuousOn_mul

end Mul

section SMul

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]

theorem IntegrableOn.continuousOn_smul [T2Space X] [SecondCountableTopologyEither X 𝕜] {g : X → E}
    (hg : IntegrableOn g K μ) {f : X → 𝕜} (hf : ContinuousOn f K) (hK : IsCompact K) :
    IntegrableOn (fun x => f x • g x) K μ := by
  rw [IntegrableOn, ← integrable_norm_iff]
  · simp_rw [norm_smul]
    refine IntegrableOn.continuousOn_mul ?_ hg.norm hK
    exact continuous_norm.comp_continuousOn hf
  · exact (hf.aestronglyMeasurable hK.measurableSet).smul hg.1
#align measure_theory.integrable_on.continuous_on_smul MeasureTheory.IntegrableOn.continuousOn_smul

theorem IntegrableOn.smul_continuousOn [T2Space X] [SecondCountableTopologyEither X E] {f : X → 𝕜}
    (hf : IntegrableOn f K μ) {g : X → E} (hg : ContinuousOn g K) (hK : IsCompact K) :
    IntegrableOn (fun x => f x • g x) K μ := by
  rw [IntegrableOn, ← integrable_norm_iff]
  · simp_rw [norm_smul]
    refine IntegrableOn.mul_continuousOn hf.norm ?_ hK
    exact continuous_norm.comp_continuousOn hg
  · exact hf.1.smul (hg.aestronglyMeasurable hK.measurableSet)
#align measure_theory.integrable_on.smul_continuous_on MeasureTheory.IntegrableOn.smul_continuousOn

end SMul

namespace LocallyIntegrableOn

theorem continuousOn_mul [LocallyCompactSpace X] [T2Space X] [NormedRing R]
    [SecondCountableTopologyEither X R] {f g : X → R} {s : Set X} (hf : LocallyIntegrableOn f s μ)
    (hg : ContinuousOn g s) (hs : IsOpen s) : LocallyIntegrableOn (fun x => g x * f x) s μ := by
  rw [MeasureTheory.locallyIntegrableOn_iff (Or.inr hs)] at hf ⊢
  exact fun k hk_sub hk_c => (hf k hk_sub hk_c).continuousOn_mul (hg.mono hk_sub) hk_c
#align measure_theory.locally_integrable_on.continuous_on_mul MeasureTheory.LocallyIntegrableOn.continuousOn_mul

theorem mul_continuousOn [LocallyCompactSpace X] [T2Space X] [NormedRing R]
    [SecondCountableTopologyEither X R] {f g : X → R} {s : Set X} (hf : LocallyIntegrableOn f s μ)
    (hg : ContinuousOn g s) (hs : IsOpen s) : LocallyIntegrableOn (fun x => f x * g x) s μ := by
  rw [MeasureTheory.locallyIntegrableOn_iff (Or.inr hs)] at hf ⊢
  exact fun k hk_sub hk_c => (hf k hk_sub hk_c).mul_continuousOn (hg.mono hk_sub) hk_c
#align measure_theory.locally_integrable_on.mul_continuous_on MeasureTheory.LocallyIntegrableOn.mul_continuousOn

theorem continuousOn_smul [LocallyCompactSpace X] [T2Space X] {𝕜 : Type*} [NormedField 𝕜]
    [SecondCountableTopologyEither X 𝕜] [NormedSpace 𝕜 E] {f : X → E} {g : X → 𝕜} {s : Set X}
    (hs : IsOpen s) (hf : LocallyIntegrableOn f s μ) (hg : ContinuousOn g s) :
    LocallyIntegrableOn (fun x => g x • f x) s μ := by
  rw [MeasureTheory.locallyIntegrableOn_iff (Or.inr hs)] at hf ⊢
  exact fun k hk_sub hk_c => (hf k hk_sub hk_c).continuousOn_smul (hg.mono hk_sub) hk_c
#align measure_theory.locally_integrable_on.continuous_on_smul MeasureTheory.LocallyIntegrableOn.continuousOn_smul

theorem smul_continuousOn [LocallyCompactSpace X] [T2Space X] {𝕜 : Type*} [NormedField 𝕜]
    [SecondCountableTopologyEither X E] [NormedSpace 𝕜 E] {f : X → 𝕜} {g : X → E} {s : Set X}
    (hs : IsOpen s) (hf : LocallyIntegrableOn f s μ) (hg : ContinuousOn g s) :
    LocallyIntegrableOn (fun x => f x • g x) s μ := by
  rw [MeasureTheory.locallyIntegrableOn_iff (Or.inr hs)] at hf ⊢
  exact fun k hk_sub hk_c => (hf k hk_sub hk_c).smul_continuousOn (hg.mono hk_sub) hk_c
#align measure_theory.locally_integrable_on.smul_continuous_on MeasureTheory.LocallyIntegrableOn.smul_continuousOn

end LocallyIntegrableOn

end MeasureTheory
