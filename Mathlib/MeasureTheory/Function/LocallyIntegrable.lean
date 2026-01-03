/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Integral.IntegrableOn

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

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Function TopologicalSpace Bornology

open scoped Topology Interval ENNReal

variable {X Y ε ε' ε'' E F R : Type*} [MeasurableSpace X] [TopologicalSpace X]
variable [MeasurableSpace Y] [TopologicalSpace Y]
variable [TopologicalSpace ε] [ContinuousENorm ε] [TopologicalSpace ε'] [ContinuousENorm ε']
  [TopologicalSpace ε''] [ESeminormedAddMonoid ε'']
  [NormedAddCommGroup E] [NormedAddCommGroup F] {f g : X → ε} {μ : Measure X} {s : Set X}

namespace MeasureTheory

section LocallyIntegrableOn

/-- A function `f : X → E` is *locally integrable on s*, for `s ⊆ X`, if for every `x ∈ s` there is
a neighbourhood of `x` within `s` on which `f` is integrable.

Note that this is, in general, strictly weaker than local integrability with respect to
`μ.restrict s`. For example, `fun (x : ℝ) ↦ 1/x` is locally integrable on `Set.Ioo 0 1` with
respect to the Lebesgue measure, but it is *not* locally integrable with respect to the
Lebesgue measure restricted to `Set.Ioo 0 1`. -/
def LocallyIntegrableOn (f : X → ε) (s : Set X) (μ : Measure X := by volume_tac) : Prop :=
  ∀ x : X, x ∈ s → IntegrableAtFilter f (𝓝[s] x) μ

theorem LocallyIntegrableOn.mono_set (hf : LocallyIntegrableOn f s μ) {t : Set X}
    (hst : t ⊆ s) : LocallyIntegrableOn f t μ := fun x hx =>
  (hf x <| hst hx).filter_mono (nhdsWithin_mono x hst)

theorem LocallyIntegrableOn.enorm (hf : LocallyIntegrableOn f s μ) :
    LocallyIntegrableOn (‖f ·‖ₑ) s μ := fun t ht ↦
  let ⟨U, hU_nhd, hU_int⟩ := hf t ht
  ⟨U, hU_nhd, hU_int.enorm⟩

theorem LocallyIntegrableOn.norm {f : X → E} (hf : LocallyIntegrableOn f s μ) :
    LocallyIntegrableOn (fun x => ‖f x‖) s μ := fun t ht =>
  let ⟨U, hU_nhd, hU_int⟩ := hf t ht
  ⟨U, hU_nhd, hU_int.norm⟩

theorem LocallyIntegrableOn.mono_enorm (hf : LocallyIntegrableOn f s μ) {g : X → ε'}
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ x ∂μ, ‖g x‖ₑ ≤ ‖f x‖ₑ) :
    LocallyIntegrableOn g s μ := by
  intro x hx
  rcases hf x hx with ⟨t, t_mem, ht⟩
  exact ⟨t, t_mem, ht.mono_enorm hg.restrict (ae_restrict_of_ae h)⟩

theorem LocallyIntegrableOn.mono {f : X → E} (hf : LocallyIntegrableOn f s μ) {g : X → F}
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖f x‖) :
    LocallyIntegrableOn g s μ := by
  intro x hx
  rcases hf x hx with ⟨t, t_mem, ht⟩
  exact ⟨t, t_mem, Integrable.mono ht hg.restrict (ae_restrict_of_ae h)⟩

theorem IntegrableOn.locallyIntegrableOn (hf : IntegrableOn f s μ) : LocallyIntegrableOn f s μ :=
  fun _ _ => ⟨s, self_mem_nhdsWithin, hf⟩

/-- If a function is locally integrable on a compact set, then it is integrable on that set. -/
theorem LocallyIntegrableOn.integrableOn_isCompact [PseudoMetrizableSpace ε]
    (hf : LocallyIntegrableOn f s μ) (hs : IsCompact s) : IntegrableOn f s μ :=
  IsCompact.induction_on hs integrableOn_empty (fun _u _v huv hv => hv.mono_set huv)
    (fun _u _v hu hv => integrableOn_union.mpr ⟨hu, hv⟩) hf

theorem LocallyIntegrableOn.integrableOn_compact_subset [PseudoMetrizableSpace ε]
    (hf : LocallyIntegrableOn f s μ) {t : Set X} (hst : t ⊆ s) (ht : IsCompact t) :
    IntegrableOn f t μ :=
  (hf.mono_set hst).integrableOn_isCompact ht

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
    rcases mem_insert_iff.1 this with h | h
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
    rcases mem_insert_iff.1 this with h | h
    · simp only [h, empty_inter, integrableOn_empty]
    · exact hT _ h

theorem LocallyIntegrableOn.aestronglyMeasurable [PseudoMetrizableSpace ε]
    [SecondCountableTopology X] (hf : LocallyIntegrableOn f s μ) :
    AEStronglyMeasurable f (μ.restrict s) := by
  rcases hf.exists_nat_integrableOn with ⟨u, -, su, hu⟩
  have : s = ⋃ n, u n ∩ s := by rw [← iUnion_inter]; exact (inter_eq_right.mpr su).symm
  rw [this, aestronglyMeasurable_iUnion_iff]
  exact fun i : ℕ => (hu i).aestronglyMeasurable

/-- If `s` is locally closed (e.g. open or closed), then `f` is locally integrable on `s` iff it is
integrable on every compact subset contained in `s`. -/
theorem locallyIntegrableOn_iff [PseudoMetrizableSpace ε]
    [LocallyCompactSpace X] (hs : IsLocallyClosed s) :
    LocallyIntegrableOn f s μ ↔ ∀ (k : Set X), k ⊆ s → IsCompact k → IntegrableOn f k μ := by
  refine ⟨fun hf k hk ↦ hf.integrableOn_compact_subset hk, fun hf x hx ↦ ?_⟩
  rcases hs with ⟨U, Z, hU, hZ, rfl⟩
  rcases exists_compact_subset hU hx.1 with ⟨K, hK, hxK, hKU⟩
  rw [nhdsWithin_inter_of_mem (nhdsWithin_le_nhds <| hU.mem_nhds hx.1)]
  refine ⟨Z ∩ K, inter_mem_nhdsWithin _ (mem_interior_iff_mem_nhds.1 hxK), ?_⟩
  exact hf (Z ∩ K) (fun y hy ↦ ⟨hKU hy.2, hy.1⟩) (.inter_left hK hZ)

protected theorem LocallyIntegrableOn.add [ContinuousAdd ε''] {f g : X → ε''}
    (hf : LocallyIntegrableOn f s μ) (hg : LocallyIntegrableOn g s μ) :
    LocallyIntegrableOn (f + g) s μ := fun x hx ↦ (hf x hx).add (hg x hx)

-- TODO: once mathlib has an ENormedAddCommSubMonoid, generalise this lemma also
protected theorem LocallyIntegrableOn.sub
    {f g : X → E} (hf : LocallyIntegrableOn f s μ) (hg : LocallyIntegrableOn g s μ) :
    LocallyIntegrableOn (f - g) s μ := fun x hx ↦ (hf x hx).sub (hg x hx)

protected theorem LocallyIntegrableOn.neg {f : X → E} (hf : LocallyIntegrableOn f s μ) :
    LocallyIntegrableOn (-f) s μ := fun x hx ↦ (hf x hx).neg

@[simp] theorem _root_.locallyIntegrableOn_neg_iff {f : X → E} :
    LocallyIntegrableOn (-f) s μ ↔ LocallyIntegrableOn f s μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.neg⟩
  convert h.neg; simp

-- TODO: generalise this to ENormed spaces, once there are suitable typeclasses
protected theorem LocallyIntegrableOn.smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    {f : X → E} (hf : LocallyIntegrableOn f s μ) (c : 𝕜) :
    LocallyIntegrableOn (c • f) s μ := fun x hx ↦ (hf x hx).smul c

-- See `locallyIntegrableOn_smul_iff` below for the fully general version.
-- It is placed below to make use of `locallyIntegrableOn_zero`.
theorem _root_.locallyIntegrableOn_smul_iff' {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    {f : X → E} {c : 𝕜} (hc : c ≠ 0) :
    LocallyIntegrableOn (c • f) s μ ↔ LocallyIntegrableOn f s μ := by
  refine ⟨fun hf ↦ ?_, fun h ↦ h.smul c⟩
  convert hf.smul c⁻¹
  simp [← smul_assoc, inv_mul_cancel₀ hc]

end LocallyIntegrableOn

/-- A function `f : X → ε` is *locally integrable* if it is integrable on a neighborhood of every
point. In particular, it is integrable on all compact sets,
see `LocallyIntegrable.integrableOn_isCompact`. -/
def LocallyIntegrable (f : X → ε) (μ : Measure X := by volume_tac) : Prop :=
  ∀ x : X, IntegrableAtFilter f (𝓝 x) μ

theorem locallyIntegrable_comap (hs : MeasurableSet s) :
    LocallyIntegrable (fun x : s ↦ f x) (μ.comap Subtype.val) ↔ LocallyIntegrableOn f s μ := by
  simp_rw [LocallyIntegrableOn, Subtype.forall', ← map_nhds_subtype_val]
  exact forall_congr' fun _ ↦ (MeasurableEmbedding.subtype_coe hs).integrableAtFilter_iff_comap.symm

theorem locallyIntegrableOn_univ : LocallyIntegrableOn f univ μ ↔ LocallyIntegrable f μ := by
  simp only [LocallyIntegrableOn, nhdsWithin_univ, mem_univ, true_imp_iff]; rfl

theorem LocallyIntegrable.locallyIntegrableOn (hf : LocallyIntegrable f μ) (s : Set X) :
    LocallyIntegrableOn f s μ := fun x _ => (hf x).filter_mono nhdsWithin_le_nhds

theorem Integrable.locallyIntegrable (hf : Integrable f μ) : LocallyIntegrable f μ := fun _ =>
  hf.integrableAtFilter _

theorem LocallyIntegrable.mono_enorm (hf : LocallyIntegrable f μ) {g : X → ε'}
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ x ∂μ, ‖g x‖ₑ ≤ ‖f x‖ₑ) :
    LocallyIntegrable g μ := by
  rw [← locallyIntegrableOn_univ] at hf ⊢
  exact hf.mono_enorm hg h

theorem LocallyIntegrable.mono {f : X → E} (hf : LocallyIntegrable f μ) {g : X → F}
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

/-- If `s` is closed, being locally integrable on `s` w.r.t. `μ` is equivalent to being locally
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

/-- If a function is locally integrable, then it is integrable on any compact set. -/
theorem LocallyIntegrable.integrableOn_isCompact [PseudoMetrizableSpace ε]
    {k : Set X} (hf : LocallyIntegrable f μ) (hk : IsCompact k) : IntegrableOn f k μ :=
  (hf.locallyIntegrableOn k).integrableOn_isCompact hk

/-- If a function is locally integrable, then it is integrable on an open neighborhood of any
compact set. -/
theorem LocallyIntegrable.integrableOn_nhds_isCompact [PseudoMetrizableSpace ε]
    (hf : LocallyIntegrable f μ) {k : Set X} (hk : IsCompact k) :
    ∃ u, IsOpen u ∧ k ⊆ u ∧ IntegrableOn f u μ := by
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

theorem locallyIntegrable_iff [PseudoMetrizableSpace ε] [LocallyCompactSpace X] :
    LocallyIntegrable f μ ↔ ∀ k : Set X, IsCompact k → IntegrableOn f k μ :=
  ⟨fun hf _k hk => hf.integrableOn_isCompact hk, fun hf x =>
    let ⟨K, hK, h2K⟩ := exists_compact_mem_nhds x
    ⟨K, h2K, hf K hK⟩⟩

theorem LocallyIntegrable.aestronglyMeasurable [PseudoMetrizableSpace ε] [SecondCountableTopology X]
    (hf : LocallyIntegrable f μ) : AEStronglyMeasurable f μ := by
  simpa only [restrict_univ] using (locallyIntegrableOn_univ.mpr hf).aestronglyMeasurable

/-- If a function is locally integrable in a second countable topological space,
then there exists a sequence of open sets covering the space on which it is integrable. -/
theorem LocallyIntegrable.exists_nat_integrableOn [SecondCountableTopology X]
    (hf : LocallyIntegrable f μ) : ∃ u : ℕ → Set X,
    (∀ n, IsOpen (u n)) ∧ ((⋃ n, u n) = univ) ∧ (∀ n, IntegrableOn f (u n) μ) := by
  rcases (hf.locallyIntegrableOn univ).exists_nat_integrableOn with ⟨u, u_open, u_union, hu⟩
  refine ⟨u, u_open, eq_univ_of_univ_subset u_union, fun n ↦ ?_⟩
  simpa only [inter_univ] using hu n

theorem MemLp.locallyIntegrable [IsLocallyFiniteMeasure μ] {p : ℝ≥0∞}
    (hf : MemLp f p μ) (hp : 1 ≤ p) : LocallyIntegrable f μ := by
  intro x
  rcases μ.finiteAt_nhds x with ⟨U, hU, h'U⟩
  have : Fact (μ U < ⊤) := ⟨h'U⟩
  refine ⟨U, hU, ?_⟩
  rw [IntegrableOn, ← memLp_one_iff_integrable]
  apply (hf.restrict U).mono_exponent hp

theorem locallyIntegrable_const_enorm [IsLocallyFiniteMeasure μ] {c : ε} (hc : ‖c‖ₑ ≠ ∞) :
    LocallyIntegrable (fun _ => c) μ :=
  (memLp_top_const_enorm hc).locallyIntegrable le_top

theorem locallyIntegrable_const [IsLocallyFiniteMeasure μ] (c : E) :
    LocallyIntegrable (fun _ => c) μ :=
  locallyIntegrable_const_enorm enorm_ne_top

theorem locallyIntegrableOn_const_enorm [IsLocallyFiniteMeasure μ] {c : ε} (hc : ‖c‖ₑ ≠ ∞) :
    LocallyIntegrableOn (fun _ => c) s μ :=
  (locallyIntegrable_const_enorm hc).locallyIntegrableOn s

theorem locallyIntegrableOn_const [IsLocallyFiniteMeasure μ] (c : E) :
    LocallyIntegrableOn (fun _ => c) s μ :=
  locallyIntegrableOn_const_enorm enorm_ne_top

theorem locallyIntegrable_zero : LocallyIntegrable (fun _ ↦ (0 : ε'')) μ :=
  (integrable_zero X ε'' μ).locallyIntegrable

theorem locallyIntegrableOn_zero : LocallyIntegrableOn (fun _ ↦ (0 : ε'')) s μ :=
  locallyIntegrable_zero.locallyIntegrableOn s

@[simp]
theorem _root_.locallyIntegrableOn_smul_iff {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    {f : X → E} (c : 𝕜) :
    LocallyIntegrableOn (c • f) s μ ↔ c = 0 ∨ LocallyIntegrableOn f s μ := by
  by_cases hc : c = 0
  · simpa [hc] using locallyIntegrableOn_zero
  · simpa [hc] using locallyIntegrableOn_smul_iff' hc

theorem LocallyIntegrable.indicator {f : X → ε''} (hf : LocallyIntegrable f μ) {s : Set X}
    (hs : MeasurableSet s) : LocallyIntegrable (s.indicator f) μ := by
  intro x
  rcases hf x with ⟨U, hU, h'U⟩
  exact ⟨U, hU, h'U.indicator hs⟩

theorem locallyIntegrable_map_homeomorph [BorelSpace X] [BorelSpace Y] (e : X ≃ₜ Y) {f : Y → ε''}
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

protected theorem LocallyIntegrable.add [ContinuousAdd ε''] {f g : X → ε''}
    (hf : LocallyIntegrable f μ) (hg : LocallyIntegrable g μ) : LocallyIntegrable (f + g) μ :=
  fun x ↦ (hf x).add (hg x)

protected theorem LocallyIntegrable.sub {f g : X → E}
    (hf : LocallyIntegrable f μ) (hg : LocallyIntegrable g μ) : LocallyIntegrable (f - g) μ :=
  fun x ↦ (hf x).sub (hg x)

protected theorem LocallyIntegrable.neg {f : X → E} (hf : LocallyIntegrable f μ) :
    LocallyIntegrable (-f) μ := fun x ↦ (hf x).neg

protected theorem LocallyIntegrable.smul {f : X → E} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    [SMulZeroClass 𝕜 E] [IsBoundedSMul 𝕜 E] (hf : LocallyIntegrable f μ) (c : 𝕜) :
    LocallyIntegrable (c • f) μ := fun x ↦ (hf x).smul c

variable {ε''' : Type*} [TopologicalSpace ε'''] [ESeminormedAddCommMonoid ε''']
  [ContinuousAdd ε'''] in
theorem locallyIntegrable_finset_sum' {ι} (s : Finset ι) {f : ι → X → ε'''}
    (hf : ∀ i ∈ s, LocallyIntegrable (f i) μ) : LocallyIntegrable (∑ i ∈ s, f i) μ :=
  Finset.sum_induction f (fun g => LocallyIntegrable g μ) (fun _ _ => LocallyIntegrable.add)
    locallyIntegrable_zero hf

variable {ε''' : Type*} [TopologicalSpace ε'''] [ESeminormedAddCommMonoid ε''']
  [ContinuousAdd ε'''] in
theorem locallyIntegrable_finset_sum {ι} (s : Finset ι) {f : ι → X → ε'''}
    (hf : ∀ i ∈ s, LocallyIntegrable (f i) μ) : LocallyIntegrable (fun a ↦ ∑ i ∈ s, f i a) μ := by
  simpa only [← Finset.sum_apply] using locallyIntegrable_finset_sum' s hf

/-- If `f` is locally integrable and `g` is continuous with compact support,
then `g • f` is integrable. -/
theorem LocallyIntegrable.integrable_smul_left_of_hasCompactSupport
    {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    [OpensMeasurableSpace X] [T2Space X] {f : X → E} (hf : LocallyIntegrable f μ)
    {g : X → 𝕜} (hg : Continuous g) (h'g : HasCompactSupport g) :
    Integrable (fun x ↦ g x • f x) μ := by
  let K := tsupport g
  have hK : IsCompact K := h'g
  have : K.indicator (fun x ↦ g x • f x) = (fun x ↦ g x • f x) := by
    apply indicator_eq_self.2
    apply support_subset_iff'.2
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  rw [← this, indicator_smul]
  apply Integrable.smul_of_top_right
  · rw [integrable_indicator_iff hK.measurableSet]
    exact hf.integrableOn_isCompact hK
  · exact hg.memLp_top_of_hasCompactSupport h'g μ

/-- If `f` is locally integrable and `g` is continuous with compact support,
then `f • g` is integrable. -/
theorem LocallyIntegrable.integrable_smul_right_of_hasCompactSupport
     {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
     [OpensMeasurableSpace X] [T2Space X] {f : X → 𝕜} (hf : LocallyIntegrable f μ)
     {g : X → E} (hg : Continuous g) (h'g : HasCompactSupport g) :
    Integrable (fun x ↦ f x • g x) μ := by
  let K := tsupport g
  have hK : IsCompact K := h'g
  have : K.indicator (fun x ↦ f x • g x) = (fun x ↦ f x • g x) := by
    apply indicator_eq_self.2
    apply support_subset_iff'.2
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  rw [← this, indicator_smul_left]
  apply Integrable.smul_of_top_left
  · rw [integrable_indicator_iff hK.measurableSet]
    exact hf.integrableOn_isCompact hK
  · exact hg.memLp_top_of_hasCompactSupport h'g μ

open Filter

variable [PseudoMetrizableSpace ε]

theorem integrable_iff_integrableAtFilter_cocompact :
    Integrable f μ ↔ (IntegrableAtFilter f (cocompact X) μ ∧ LocallyIntegrable f μ) := by
  refine ⟨fun hf ↦ ⟨hf.integrableAtFilter _, hf.locallyIntegrable⟩, fun ⟨⟨s, hsc, hs⟩, hloc⟩ ↦ ?_⟩
  obtain ⟨t, htc, ht⟩ := mem_cocompact'.mp hsc
  rewrite [← integrableOn_univ, ← compl_union_self s, integrableOn_union]
  exact ⟨(hloc.integrableOn_isCompact htc).mono ht le_rfl, hs⟩

theorem integrable_iff_integrableAtFilter_atBot_atTop
    [PseudoMetrizableSpace ε''] {f : X → ε''} [LinearOrder X] [CompactIccSpace X] :
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
    obtain ⟨s', ⟨hs'_mono, hs'⟩⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hsl
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
variable {K : Set X} {f : X → E} {a b : X}

/-- A continuous function `f` is locally integrable with respect to any locally finite measure. -/
theorem Continuous.locallyIntegrable [IsLocallyFiniteMeasure μ] [SecondCountableTopologyEither X E]
    (hf : Continuous f) : LocallyIntegrable f μ :=
  hf.integrableAt_nhds

/-- A function `f` continuous on a set `K` is locally integrable on this set with respect
to any locally finite measure. -/
theorem ContinuousOn.locallyIntegrableOn [IsLocallyFiniteMeasure μ]
    [SecondCountableTopologyEither X E] (hf : ContinuousOn f K)
    (hK : MeasurableSet K) : LocallyIntegrableOn f K μ := fun _x hx =>
  hf.integrableAt_nhdsWithin hK hx

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
  apply HasFiniteIntegral.of_bounded (C := C)
  filter_upwards [ae_restrict_mem h'K] with x hx using hC _ (mem_image_of_mem f hx)

theorem ContinuousOn.integrableOn_compact [T2Space X]
    (hK : IsCompact K) (hf : ContinuousOn f K) : IntegrableOn f K μ :=
  hf.integrableOn_compact' hK hK.measurableSet

theorem ContinuousOn.integrableOn_Icc [Preorder X] [CompactIccSpace X] [T2Space X]
    (hf : ContinuousOn f (Icc a b)) : IntegrableOn f (Icc a b) μ :=
  hf.integrableOn_compact isCompact_Icc

theorem Continuous.integrableOn_Icc [Preorder X] [CompactIccSpace X] [T2Space X]
    (hf : Continuous f) : IntegrableOn f (Icc a b) μ :=
  hf.continuousOn.integrableOn_Icc

theorem Continuous.integrableOn_Ioc [Preorder X] [CompactIccSpace X] [T2Space X]
    (hf : Continuous f) : IntegrableOn f (Ioc a b) μ :=
  hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem ContinuousOn.integrableOn_uIcc [LinearOrder X] [CompactIccSpace X] [T2Space X]
    (hf : ContinuousOn f [[a, b]]) : IntegrableOn f [[a, b]] μ :=
  hf.integrableOn_Icc

theorem Continuous.integrableOn_uIcc [LinearOrder X] [CompactIccSpace X] [T2Space X]
    (hf : Continuous f) : IntegrableOn f [[a, b]] μ :=
  hf.integrableOn_Icc

open scoped Interval in
theorem Continuous.integrableOn_uIoc [LinearOrder X] [CompactIccSpace X] [T2Space X]
    (hf : Continuous f) : IntegrableOn f (Ι a b) μ :=
  hf.integrableOn_Ioc

/-- A continuous function with compact support is integrable on the whole space. -/
theorem Continuous.integrable_of_hasCompactSupport (hf : Continuous f) (hcf : HasCompactSupport f) :
    Integrable f μ :=
  (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).mp <|
    hf.continuousOn.integrableOn_compact' hcf (isClosed_tsupport _).measurableSet

end borel

open scoped ENNReal

section Monotone

variable [BorelSpace X] [ConditionallyCompleteLinearOrder X] [ConditionallyCompleteLinearOrder E]
  [OrderTopology X] [OrderTopology E] [SecondCountableTopology E] {p : ℝ≥0∞}
  {f : X → E}

theorem MonotoneOn.memLp_top (hmono : MonotoneOn f s) {a b : X}
    (ha : IsLeast s a) (hb : IsGreatest s b) (h's : MeasurableSet s) :
    MemLp f ∞ (μ.restrict s) := by
  borelize E
  have hbelow : BddBelow (f '' s) := ⟨f a, fun x ⟨y, hy, hyx⟩ => hyx ▸ hmono ha.1 hy (ha.2 hy)⟩
  have habove : BddAbove (f '' s) := ⟨f b, fun x ⟨y, hy, hyx⟩ => hyx ▸ hmono hy hb.1 (hb.2 hy)⟩
  have : IsBounded (f '' s) := Metric.isBounded_of_bddAbove_of_bddBelow habove hbelow
  rcases isBounded_iff_forall_norm_le.mp this with ⟨C, hC⟩
  have A : MemLp (fun _ => C) ⊤ (μ.restrict s) := memLp_top_const _
  apply MemLp.mono A (aemeasurable_restrict_of_monotoneOn h's hmono).aestronglyMeasurable
  apply (ae_restrict_iff' h's).mpr
  apply ae_of_all _ fun y hy ↦ ?_
  exact (hC _ (mem_image_of_mem f hy)).trans (le_abs_self _)

theorem MonotoneOn.memLp_of_measure_ne_top (hmono : MonotoneOn f s) {a b : X}
    (ha : IsLeast s a) (hb : IsGreatest s b) (hs : μ s ≠ ∞) (h's : MeasurableSet s) :
    MemLp f p (μ.restrict s) :=
  (hmono.memLp_top ha hb h's).mono_exponent_of_measure_support_ne_top (s := univ)
    (by simp) (by simpa using hs) le_top

theorem MonotoneOn.memLp_isCompact [IsFiniteMeasureOnCompacts μ] (hs : IsCompact s)
    (hmono : MonotoneOn f s) : MemLp f p (μ.restrict s) := by
  obtain rfl | h := s.eq_empty_or_nonempty
  · simp
  · exact hmono.memLp_of_measure_ne_top (hs.isLeast_sInf h) (hs.isGreatest_sSup h)
      hs.measure_lt_top.ne hs.measurableSet

theorem AntitoneOn.memLp_top (hanti : AntitoneOn f s) {a b : X}
    (ha : IsLeast s a) (hb : IsGreatest s b) (h's : MeasurableSet s) :
    MemLp f ∞ (μ.restrict s) :=
  MonotoneOn.memLp_top (E := Eᵒᵈ) hanti ha hb h's

theorem AntitoneOn.memLp_of_measure_ne_top (hanti : AntitoneOn f s) {a b : X}
    (ha : IsLeast s a) (hb : IsGreatest s b) (hs : μ s ≠ ∞) (h's : MeasurableSet s) :
    MemLp f p (μ.restrict s) :=
  MonotoneOn.memLp_of_measure_ne_top (E := Eᵒᵈ) hanti ha hb hs h's

theorem AntitoneOn.memLp_isCompact [IsFiniteMeasureOnCompacts μ] (hs : IsCompact s)
    (hanti : AntitoneOn f s) : MemLp f p (μ.restrict s) :=
  MonotoneOn.memLp_isCompact (E := Eᵒᵈ) hs hanti

theorem MonotoneOn.integrableOn_of_measure_ne_top (hmono : MonotoneOn f s) {a b : X}
    (ha : IsLeast s a) (hb : IsGreatest s b) (hs : μ s ≠ ∞) (h's : MeasurableSet s) :
    IntegrableOn f s μ :=
  memLp_one_iff_integrable.1 (hmono.memLp_of_measure_ne_top ha hb hs h's)

theorem MonotoneOn.integrableOn_isCompact [IsFiniteMeasureOnCompacts μ] (hs : IsCompact s)
    (hmono : MonotoneOn f s) : IntegrableOn f s μ :=
  memLp_one_iff_integrable.1 (hmono.memLp_isCompact hs)

theorem AntitoneOn.integrableOn_of_measure_ne_top (hanti : AntitoneOn f s) {a b : X}
    (ha : IsLeast s a) (hb : IsGreatest s b) (hs : μ s ≠ ∞) (h's : MeasurableSet s) :
    IntegrableOn f s μ :=
  memLp_one_iff_integrable.1 (hanti.memLp_of_measure_ne_top ha hb hs h's)

theorem AntitoneOn.integrableOn_isCompact [IsFiniteMeasureOnCompacts μ] (hs : IsCompact s)
    (hanti : AntitoneOn f s) : IntegrableOn f s μ :=
  memLp_one_iff_integrable.1 (hanti.memLp_isCompact hs)

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

theorem Antitone.locallyIntegrable [IsLocallyFiniteMeasure μ] (hanti : Antitone f) :
    LocallyIntegrable f μ :=
  hanti.dual_right.locallyIntegrable

end Monotone

namespace MeasureTheory

variable [OpensMeasurableSpace X] {A K : Set X}

section Mul

variable [NormedRing R] [SecondCountableTopologyEither X R] {g g' : X → R}

theorem IntegrableOn.mul_continuousOn_of_subset (hg : IntegrableOn g A μ) (hg' : ContinuousOn g' K)
    (hA : MeasurableSet A) (hK : IsCompact K) (hAK : A ⊆ K) :
    IntegrableOn (fun x => g x * g' x) A μ := by
  rcases IsCompact.exists_bound_of_continuousOn hK hg' with ⟨C, hC⟩
  rw [IntegrableOn, ← memLp_one_iff_integrable] at hg ⊢
  have : ∀ᵐ x ∂μ.restrict A, ‖g x * g' x‖ ≤ C * ‖g x‖ := by
    filter_upwards [ae_restrict_mem hA] with x hx
    refine (norm_mul_le _ _).trans ?_
    rw [mul_comm]
    gcongr
    exact hC x (hAK hx)
  exact
    MemLp.of_le_mul hg (hg.aestronglyMeasurable.mul <| (hg'.mono hAK).aestronglyMeasurable hA) this

theorem IntegrableOn.mul_continuousOn [T2Space X] (hg : IntegrableOn g K μ)
    (hg' : ContinuousOn g' K) (hK : IsCompact K) : IntegrableOn (fun x => g x * g' x) K μ :=
  hg.mul_continuousOn_of_subset hg' hK.measurableSet hK (Subset.refl _)

theorem IntegrableOn.continuousOn_mul_of_subset (hg : ContinuousOn g K) (hg' : IntegrableOn g' A μ)
    (hK : IsCompact K) (hA : MeasurableSet A) (hAK : A ⊆ K) :
    IntegrableOn (fun x => g x * g' x) A μ := by
  rcases IsCompact.exists_bound_of_continuousOn hK hg with ⟨C, hC⟩
  rw [IntegrableOn, ← memLp_one_iff_integrable] at hg' ⊢
  have : ∀ᵐ x ∂μ.restrict A, ‖g x * g' x‖ ≤ C * ‖g' x‖ := by
    filter_upwards [ae_restrict_mem hA] with x hx
    refine (norm_mul_le _ _).trans ?_
    gcongr
    exact hC x (hAK hx)
  exact
    MemLp.of_le_mul hg' (((hg.mono hAK).aestronglyMeasurable hA).mul hg'.aestronglyMeasurable) this

theorem IntegrableOn.continuousOn_mul [T2Space X] (hg : ContinuousOn g K)
    (hg' : IntegrableOn g' K μ) (hK : IsCompact K) : IntegrableOn (fun x => g x * g' x) K μ :=
  hg'.continuousOn_mul_of_subset hg hK hK.measurableSet Subset.rfl

end Mul

section SMul

variable {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E]

theorem IntegrableOn.continuousOn_smul_of_subset [SecondCountableTopologyEither X 𝕜] {f : X → 𝕜}
    (hf : ContinuousOn f K) {g : X → E} (hg : IntegrableOn g A μ)
    (hK : IsCompact K) (hA : MeasurableSet A) (hAK : A ⊆ K) :
    IntegrableOn (fun x => f x • g x) A μ := by
  rcases IsCompact.exists_bound_of_continuousOn hK hf with ⟨C, hC⟩
  rw [IntegrableOn, ← memLp_one_iff_integrable] at hg ⊢
  have : ∀ᵐ x ∂μ.restrict A, ‖f x • g x‖ ≤ C * ‖g x‖ := by
    filter_upwards [ae_restrict_mem hA] with x hx
    refine (norm_smul_le _ _).trans ?_
    gcongr
    exact hC x (hAK hx)
  exact
    MemLp.of_le_mul hg (((hf.mono hAK).aestronglyMeasurable hA).smul hg.aestronglyMeasurable) this

theorem IntegrableOn.continuousOn_smul [T2Space X] [SecondCountableTopologyEither X 𝕜] {g : X → E}
    (hg : IntegrableOn g K μ) {f : X → 𝕜} (hf : ContinuousOn f K) (hK : IsCompact K) :
    IntegrableOn (fun x => f x • g x) K μ :=
  hg.continuousOn_smul_of_subset hf hK hK.measurableSet Subset.rfl

theorem IntegrableOn.smul_continuousOn_of_subset [SecondCountableTopologyEither X E] {f : X → 𝕜}
    (hf : IntegrableOn f A μ) {g : X → E} (hg : ContinuousOn g K)
    (hA : MeasurableSet A) (hK : IsCompact K) (hAK : A ⊆ K) :
    IntegrableOn (fun x => f x • g x) A μ := by
  rcases IsCompact.exists_bound_of_continuousOn hK hg with ⟨C, hC⟩
  rw [IntegrableOn, ← memLp_one_iff_integrable] at hf ⊢
  have : ∀ᵐ x ∂μ.restrict A, ‖f x • g x‖ ≤ C * ‖f x‖ := by
    filter_upwards [ae_restrict_mem hA] with x hx
    refine (norm_smul_le _ _).trans ?_
    rw [mul_comm]
    gcongr
    exact hC x (hAK hx)
  exact
    MemLp.of_le_mul hf (hf.aestronglyMeasurable.smul <| (hg.mono hAK).aestronglyMeasurable hA) this

theorem IntegrableOn.smul_continuousOn [T2Space X] [SecondCountableTopologyEither X E] {f : X → 𝕜}
    (hf : IntegrableOn f K μ) {g : X → E} (hg : ContinuousOn g K) (hK : IsCompact K) :
    IntegrableOn (fun x => f x • g x) K μ :=
  hf.smul_continuousOn_of_subset hg hK.measurableSet hK (Subset.refl _)

end SMul

namespace LocallyIntegrableOn

theorem continuousOn_mul [LocallyCompactSpace X] [T2Space X] [NormedRing R]
    [SecondCountableTopologyEither X R] {f g : X → R} {s : Set X} (hf : LocallyIntegrableOn f s μ)
    (hg : ContinuousOn g s) (hs : IsLocallyClosed s) :
    LocallyIntegrableOn (fun x => g x * f x) s μ := by
  rw [MeasureTheory.locallyIntegrableOn_iff hs] at hf ⊢
  exact fun k hk_sub hk_c => (hf k hk_sub hk_c).continuousOn_mul (hg.mono hk_sub) hk_c

theorem mul_continuousOn [LocallyCompactSpace X] [T2Space X] [NormedRing R]
    [SecondCountableTopologyEither X R] {f g : X → R} {s : Set X} (hf : LocallyIntegrableOn f s μ)
    (hg : ContinuousOn g s) (hs : IsLocallyClosed s) :
    LocallyIntegrableOn (fun x => f x * g x) s μ := by
  rw [MeasureTheory.locallyIntegrableOn_iff hs] at hf ⊢
  exact fun k hk_sub hk_c => (hf k hk_sub hk_c).mul_continuousOn (hg.mono hk_sub) hk_c

theorem continuousOn_smul [LocallyCompactSpace X] [T2Space X] {𝕜 : Type*} [NormedRing 𝕜]
    [SecondCountableTopologyEither X 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E] {f : X → E} {g : X → 𝕜}
    {s : Set X} (hs : IsLocallyClosed s) (hf : LocallyIntegrableOn f s μ) (hg : ContinuousOn g s) :
    LocallyIntegrableOn (fun x => g x • f x) s μ := by
  rw [MeasureTheory.locallyIntegrableOn_iff hs] at hf ⊢
  exact fun k hk_sub hk_c => (hf k hk_sub hk_c).continuousOn_smul (hg.mono hk_sub) hk_c

theorem smul_continuousOn [LocallyCompactSpace X] [T2Space X] {𝕜 : Type*} [NormedRing 𝕜]
    [SecondCountableTopologyEither X E] [Module 𝕜 E] [NormSMulClass 𝕜 E] {f : X → 𝕜} {g : X → E}
    {s : Set X} (hs : IsLocallyClosed s) (hf : LocallyIntegrableOn f s μ) (hg : ContinuousOn g s) :
    LocallyIntegrableOn (fun x => f x • g x) s μ := by
  rw [MeasureTheory.locallyIntegrableOn_iff hs] at hf ⊢
  exact fun k hk_sub hk_c => (hf k hk_sub hk_c).smul_continuousOn (hg.mono hk_sub) hk_c

end LocallyIntegrableOn

end MeasureTheory
