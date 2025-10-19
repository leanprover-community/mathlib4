/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.Order.Filter.EventuallyConst

/-!
# Measure-preserving maps

We say that `f : α → β` is a measure-preserving map w.r.t. measures `μ : Measure α` and
`ν : Measure β` if `f` is measurable and `map f μ = ν`. In this file we define the predicate
`MeasureTheory.MeasurePreserving` and prove its basic properties.

We use the term "measure preserving" because in many applications `α = β` and `μ = ν`.

## References

Partially based on
[this](https://www.isa-afp.org/browser_info/current/AFP/Ergodic_Theory/Measure_Preserving_Transformations.html)
Isabelle formalization.

## Tags

measure-preserving map, measure
-/

open MeasureTheory.Measure Function Set
open scoped ENNReal

variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ]

namespace MeasureTheory

variable {μa : Measure α} {μb : Measure β} {μc : Measure γ} {μd : Measure δ}

/-- `f` is a measure-preserving map w.r.t. measures `μa` and `μb` if `f` is measurable
and `map f μa = μb`. -/
structure MeasurePreserving (f : α → β)
  (μa : Measure α := by volume_tac) (μb : Measure β := by volume_tac) : Prop where
  protected measurable : Measurable f
  protected map_eq : map f μa = μb

protected theorem _root_.Measurable.measurePreserving
    {f : α → β} (h : Measurable f) (μa : Measure α) : MeasurePreserving f μa (map f μa) :=
  ⟨h, rfl⟩

namespace MeasurePreserving

protected theorem id (μ : Measure α) : MeasurePreserving id μ μ :=
  ⟨measurable_id, map_id⟩

protected theorem aemeasurable {f : α → β} (hf : MeasurePreserving f μa μb) : AEMeasurable f μa :=
  hf.1.aemeasurable

@[nontriviality]
theorem of_isEmpty [IsEmpty β] (f : α → β) (μa : Measure α) (μb : Measure β) :
    MeasurePreserving f μa μb :=
  ⟨measurable_of_subsingleton_codomain _, Subsingleton.elim _ _⟩

theorem symm (e : α ≃ᵐ β) {μa : Measure α} {μb : Measure β} (h : MeasurePreserving e μa μb) :
    MeasurePreserving e.symm μb μa :=
  ⟨e.symm.measurable, by
    rw [← h.map_eq, map_map e.symm.measurable e.measurable, e.symm_comp_self, map_id]⟩

theorem restrict_preimage {f : α → β} (hf : MeasurePreserving f μa μb) {s : Set β}
    (hs : MeasurableSet s) : MeasurePreserving f (μa.restrict (f ⁻¹' s)) (μb.restrict s) :=
  ⟨hf.measurable, by rw [← hf.map_eq, restrict_map hf.measurable hs]⟩

theorem restrict_preimage_emb {f : α → β} (hf : MeasurePreserving f μa μb)
    (h₂ : MeasurableEmbedding f) (s : Set β) :
    MeasurePreserving f (μa.restrict (f ⁻¹' s)) (μb.restrict s) :=
  ⟨hf.measurable, by rw [← hf.map_eq, h₂.restrict_map]⟩

theorem restrict_image_emb {f : α → β} (hf : MeasurePreserving f μa μb) (h₂ : MeasurableEmbedding f)
    (s : Set α) : MeasurePreserving f (μa.restrict s) (μb.restrict (f '' s)) := by
  simpa only [Set.preimage_image_eq _ h₂.injective] using hf.restrict_preimage_emb h₂ (f '' s)

theorem aemeasurable_comp_iff {f : α → β} (hf : MeasurePreserving f μa μb)
    (h₂ : MeasurableEmbedding f) {g : β → γ} : AEMeasurable (g ∘ f) μa ↔ AEMeasurable g μb := by
  rw [← hf.map_eq, h₂.aemeasurable_map_iff]

protected theorem quasiMeasurePreserving {f : α → β} (hf : MeasurePreserving f μa μb) :
    QuasiMeasurePreserving f μa μb :=
  ⟨hf.1, hf.2.absolutelyContinuous⟩

protected theorem comp {g : β → γ} {f : α → β} (hg : MeasurePreserving g μb μc)
    (hf : MeasurePreserving f μa μb) : MeasurePreserving (g ∘ f) μa μc :=
  ⟨hg.1.comp hf.1, by rw [← map_map hg.1 hf.1, hf.2, hg.2]⟩

/-- An alias of `MeasureTheory.MeasurePreserving.comp` with a convenient defeq and argument order
for `MeasurableEquiv` -/
protected theorem trans {e : α ≃ᵐ β} {e' : β ≃ᵐ γ}
    {μa : Measure α} {μb : Measure β} {μc : Measure γ}
    (h : MeasurePreserving e μa μb) (h' : MeasurePreserving e' μb μc) :
    MeasurePreserving (e.trans e') μa μc :=
  h'.comp h

protected theorem comp_left_iff {g : α → β} {e : β ≃ᵐ γ} (h : MeasurePreserving e μb μc) :
    MeasurePreserving (e ∘ g) μa μc ↔ MeasurePreserving g μa μb := by
  refine ⟨fun hg => ?_, fun hg => h.comp hg⟩
  convert (MeasurePreserving.symm e h).comp hg
  simp [← Function.comp_assoc e.symm e g]

protected theorem comp_right_iff {g : α → β} {e : γ ≃ᵐ α} (h : MeasurePreserving e μc μa) :
    MeasurePreserving (g ∘ e) μc μb ↔ MeasurePreserving g μa μb := by
  refine ⟨fun hg => ?_, fun hg => hg.comp h⟩
  convert hg.comp (MeasurePreserving.symm e h)
  simp [Function.comp_assoc g e e.symm]

protected theorem sigmaFinite {f : α → β} (hf : MeasurePreserving f μa μb) [SigmaFinite μb] :
    SigmaFinite μa :=
  SigmaFinite.of_map μa hf.aemeasurable (by rwa [hf.map_eq])

protected theorem sfinite {f : α → β} (hf : MeasurePreserving f μa μb) [SFinite μa] :
    SFinite μb := by
  rw [← hf.map_eq]
  infer_instance

theorem measure_preimage {f : α → β} (hf : MeasurePreserving f μa μb) {s : Set β}
    (hs : NullMeasurableSet s μb) : μa (f ⁻¹' s) = μb s := by
  rw [← hf.map_eq] at hs ⊢
  rw [map_apply₀ hf.1.aemeasurable hs]

theorem measureReal_preimage {f : α → β} (hf : MeasurePreserving f μa μb) {s : Set β}
    (hs : NullMeasurableSet s μb) : μa.real (f ⁻¹' s) = μb.real s := by
  simp [measureReal_def, measure_preimage hf hs]

theorem measure_preimage_emb {f : α → β} (hf : MeasurePreserving f μa μb)
    (hfe : MeasurableEmbedding f) (s : Set β) : μa (f ⁻¹' s) = μb s := by
  rw [← hf.map_eq, hfe.map_apply]

theorem measure_preimage_equiv {f : α ≃ᵐ β} (hf : MeasurePreserving f μa μb) (s : Set β) :
    μa (f ⁻¹' s) = μb s :=
  measure_preimage_emb hf f.measurableEmbedding s

theorem measure_preimage_le {f : α → β} (hf : MeasurePreserving f μa μb) (s : Set β) :
    μa (f ⁻¹' s) ≤ μb s := by
  rw [← hf.map_eq]
  exact le_map_apply hf.aemeasurable _

theorem preimage_null {f : α → β} (hf : MeasurePreserving f μa μb) {s : Set β}
    (hs : μb s = 0) : μa (f ⁻¹' s) = 0 :=
  hf.quasiMeasurePreserving.preimage_null hs

theorem aeconst_comp [MeasurableSingletonClass γ] {f : α → β} (hf : MeasurePreserving f μa μb)
    {g : β → γ} (hg : NullMeasurable g μb) :
    Filter.EventuallyConst (g ∘ f) (ae μa) ↔ Filter.EventuallyConst g (ae μb) :=
  exists_congr fun s ↦ and_congr_left fun hs ↦ by
    simp only [Filter.mem_map, mem_ae_iff, ← hf.measure_preimage (hg hs.measurableSet).compl,
      preimage_comp, preimage_compl]

theorem aeconst_preimage {f : α → β} (hf : MeasurePreserving f μa μb) {s : Set β}
    (hs : NullMeasurableSet s μb) :
    Filter.EventuallyConst (f ⁻¹' s) (ae μa) ↔ Filter.EventuallyConst s (ae μb) :=
  aeconst_comp hf hs.mem

theorem add_measure {f μa' μb'} (hf : MeasurePreserving f μa μb)
    (hf' : MeasurePreserving f μa' μb') : MeasurePreserving f (μa + μa') (μb + μb') where
  measurable := hf.measurable
  map_eq := by rw [Measure.map_add _ _ hf.measurable, hf.map_eq, hf'.map_eq]

theorem smul_measure {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] {f : α → β}
    (hf : MeasurePreserving f μa μb) (c : R) : MeasurePreserving f (c • μa) (c • μb) where
  measurable := hf.measurable
  map_eq := by rw [Measure.map_smul, hf.map_eq]

variable {μ : Measure α} {f : α → α} {s : Set α}

protected theorem iterate (hf : MeasurePreserving f μ μ) :
    ∀ n, MeasurePreserving f^[n] μ μ
  | 0 => .id μ
  | n + 1 => (MeasurePreserving.iterate hf n).comp hf

open scoped symmDiff in
lemma measure_symmDiff_preimage_iterate_le
    (hf : MeasurePreserving f μ μ) (hs : NullMeasurableSet s μ) (n : ℕ) :
    μ (s ∆ (f^[n] ⁻¹' s)) ≤ n • μ (s ∆ (f ⁻¹' s)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [add_smul, one_smul]
    grw [← ih, measure_symmDiff_le s (f^[n] ⁻¹' s) (f^[n+1] ⁻¹' s)]
    replace hs : NullMeasurableSet (s ∆ (f ⁻¹' s)) μ :=
      hs.symmDiff <| hs.preimage hf.quasiMeasurePreserving
    rw [iterate_succ', preimage_comp, ← preimage_symmDiff, (hf.iterate n).measure_preimage hs]

/-- If `μ univ < n * μ s` and `f` is a map preserving measure `μ`,
then for some `x ∈ s` and `0 < m < n`, `f^[m] x ∈ s`. -/
theorem exists_mem_iterate_mem_of_measure_univ_lt_mul_measure (hf : MeasurePreserving f μ μ)
    (hs : NullMeasurableSet s μ) {n : ℕ} (hvol : μ (Set.univ : Set α) < n * μ s) :
    ∃ x ∈ s, ∃ m ∈ Set.Ioo 0 n, f^[m] x ∈ s := by
  have A : ∀ m, NullMeasurableSet (f^[m] ⁻¹' s) μ := fun m ↦
    hs.preimage (hf.iterate m).quasiMeasurePreserving
  have B : ∀ m, μ (f^[m] ⁻¹' s) = μ s := fun m ↦ (hf.iterate m).measure_preimage hs
  have : μ (univ : Set α) < ∑ m ∈ Finset.range n, μ (f^[m] ⁻¹' s) := by simpa [B]
  obtain ⟨i, hi, j, hj, hij, x, hxi : f^[i] x ∈ s, hxj : f^[j] x ∈ s⟩ :
      ∃ i < n, ∃ j < n, i ≠ j ∧ (f^[i] ⁻¹' s ∩ f^[j] ⁻¹' s).Nonempty := by
    simpa using exists_nonempty_inter_of_measure_univ_lt_sum_measure μ (fun m _ ↦ A m) this
  wlog hlt : i < j generalizing i j
  · exact this j hj i hi hij.symm hxj hxi (hij.lt_or_gt.resolve_left hlt)
  refine ⟨f^[i] x, hxi, j - i, ⟨tsub_pos_of_lt hlt, lt_of_le_of_lt (j.sub_le i) hj⟩, ?_⟩
  rwa [← iterate_add_apply, tsub_add_cancel_of_le hlt.le]

/-- A self-map preserving a finite measure is conservative: if `μ s ≠ 0`, then at least one point
`x ∈ s` comes back to `s` under iterations of `f`. Actually, a.e. point of `s` comes back to `s`
infinitely many times, see `MeasureTheory.MeasurePreserving.conservative` and theorems about
`MeasureTheory.Conservative`. -/
theorem exists_mem_iterate_mem [IsFiniteMeasure μ] (hf : MeasurePreserving f μ μ)
    (hs : NullMeasurableSet s μ) (hs' : μ s ≠ 0) : ∃ x ∈ s, ∃ m ≠ 0, f^[m] x ∈ s := by
  rcases ENNReal.exists_nat_mul_gt hs' (measure_ne_top μ (Set.univ : Set α)) with ⟨N, hN⟩
  rcases hf.exists_mem_iterate_mem_of_measure_univ_lt_mul_measure hs hN with ⟨x, hx, m, hm, hmx⟩
  exact ⟨x, hx, m, hm.1.ne', hmx⟩

end MeasurePreserving

lemma measurePreserving_subtype_coe {s : Set α} (hs : MeasurableSet s) :
    MeasurePreserving (Subtype.val : s → α) (μa.comap Subtype.val) (μa.restrict s) where
  measurable := measurable_subtype_coe
  map_eq := map_comap_subtype_coe hs _

namespace MeasurableEquiv

theorem measurePreserving_symm (μ : Measure α) (e : α ≃ᵐ β) :
    MeasurePreserving e.symm (map e μ) μ :=
  (e.measurable.measurePreserving μ).symm _

end MeasurableEquiv

end MeasureTheory
