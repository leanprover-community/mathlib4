/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
# Integrable functions

In this file, the predicate `Integrable` is defined and basic properties of
integrable functions are proved.

Such a predicate is already available under the name `MemLp 1`. We give a direct definition which
is easier to use, and show that it is equivalent to `MemLp 1`.

## Main definition

* Let `f : α → β` be a function, where `α` is a `MeasureSpace` and `β` a `NormedAddCommGroup`
  which also a `MeasurableSpace`. Then `f` is called `Integrable` if
  `f` is `Measurable` and `HasFiniteIntegral f` holds.

## Implementation notes

To prove something for an arbitrary integrable function, a useful theorem is
`Integrable.induction` in the file `SetIntegral`.

## Tags

integrable

-/


noncomputable section

open EMetric ENNReal Filter MeasureTheory NNReal Set TopologicalSpace

open scoped Topology

variable {α β γ δ ε ε' ε'' : Type*} {m : MeasurableSpace α} {μ ν : Measure α} [MeasurableSpace δ]
variable [NormedAddCommGroup β] [NormedAddCommGroup γ]
  [TopologicalSpace ε] [ContinuousENorm ε] [TopologicalSpace ε'] [ContinuousENorm ε'] [ENorm ε'']

namespace MeasureTheory

/-! ### The predicate `Integrable` -/

/-- `Integrable f μ` means that `f` is measurable and that the integral `∫⁻ a, ‖f a‖ ∂μ` is finite.
  `Integrable f` means `Integrable f volume`. -/
@[fun_prop]
def Integrable {α} {_ : MeasurableSpace α} (f : α → ε)
    (μ : Measure α := by volume_tac) : Prop :=
  AEStronglyMeasurable f μ ∧ HasFiniteIntegral f μ

/-- Notation for `Integrable` with respect to a non-standard σ-algebra. -/
scoped notation "Integrable[" mα "]" => @Integrable _ _ _ _ mα

theorem memLp_one_iff_integrable {f : α → ε} : MemLp f 1 μ ↔ Integrable f μ := by
  simp_rw [Integrable, hasFiniteIntegral_iff_enorm, MemLp, eLpNorm_one_eq_lintegral_enorm]

@[fun_prop]
theorem Integrable.aestronglyMeasurable {f : α → ε} (hf : Integrable f μ) :
    AEStronglyMeasurable f μ :=
  hf.1

@[fun_prop]
theorem Integrable.aemeasurable [MeasurableSpace ε] [BorelSpace ε] [PseudoMetrizableSpace ε]
    {f : α → ε} (hf : Integrable f μ) : AEMeasurable f μ :=
  hf.aestronglyMeasurable.aemeasurable

@[fun_prop]
theorem Integrable.hasFiniteIntegral {f : α → ε} (hf : Integrable f μ) : HasFiniteIntegral f μ :=
  hf.2

theorem Integrable.mono_enorm {f : α → ε} {g : α → ε'} (hg : Integrable g μ)
    (hf : AEStronglyMeasurable f μ) (h : ∀ᵐ a ∂μ, ‖f a‖ₑ ≤ ‖g a‖ₑ) : Integrable f μ :=
  ⟨hf, hg.hasFiniteIntegral.mono_enorm h⟩

theorem Integrable.mono {f : α → β} {g : α → γ} (hg : Integrable g μ)
    (hf : AEStronglyMeasurable f μ) (h : ∀ᵐ a ∂μ, ‖f a‖ ≤ ‖g a‖) : Integrable f μ :=
  ⟨hf, hg.hasFiniteIntegral.mono h⟩

theorem Integrable.mono'_enorm {f : α → ε} {g : α → ℝ≥0∞} (hg : Integrable g μ)
    (hf : AEStronglyMeasurable f μ) (h : ∀ᵐ a ∂μ, ‖f a‖ₑ ≤ g a) : Integrable f μ :=
  ⟨hf, hg.hasFiniteIntegral.mono_enorm h⟩

theorem Integrable.mono' {f : α → β} {g : α → ℝ} (hg : Integrable g μ)
    (hf : AEStronglyMeasurable f μ) (h : ∀ᵐ a ∂μ, ‖f a‖ ≤ g a) : Integrable f μ :=
  ⟨hf, hg.hasFiniteIntegral.mono' h⟩

theorem Integrable.congr'_enorm {f : α → ε} {g : α → ε'} (hf : Integrable f μ)
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) : Integrable g μ :=
  ⟨hg, hf.hasFiniteIntegral.congr'_enorm h⟩

theorem Integrable.congr' {f : α → β} {g : α → γ} (hf : Integrable f μ)
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ a ∂μ, ‖f a‖ = ‖g a‖) : Integrable g μ :=
  ⟨hg, hf.hasFiniteIntegral.congr' h⟩

theorem integrable_congr'_enorm {f : α → ε} {g : α → ε'}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) :
    Integrable f μ ↔ Integrable g μ :=
  ⟨fun h2f => h2f.congr'_enorm hg h, fun h2g => h2g.congr'_enorm hf <| EventuallyEq.symm h⟩

theorem integrable_congr' {f : α → β} {g : α → γ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ a ∂μ, ‖f a‖ = ‖g a‖) :
    Integrable f μ ↔ Integrable g μ :=
  integrable_congr'_enorm hf hg <| h.mono fun _x hx ↦ enorm_eq_iff_norm_eq.mpr hx

theorem Integrable.congr {f g : α → ε} (hf : Integrable f μ) (h : f =ᵐ[μ] g) : Integrable g μ :=
  ⟨hf.1.congr h, hf.2.congr h⟩

theorem integrable_congr {f g : α → ε} (h : f =ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ :=
  ⟨fun hf => hf.congr h, fun hg => hg.congr h.symm⟩

theorem integrable_const_iff_enorm {c : ε} (hc : ‖c‖ₑ ≠ ∞) :
    Integrable (fun _ : α => c) μ ↔ ‖c‖ₑ = 0 ∨ IsFiniteMeasure μ := by
  have : AEStronglyMeasurable (fun _ : α => c) μ := aestronglyMeasurable_const
  rw [Integrable, and_iff_right this, hasFiniteIntegral_const_iff_enorm hc]

lemma integrable_const_iff {c : β} : Integrable (fun _ : α => c) μ ↔ c = 0 ∨ IsFiniteMeasure μ := by
  rw [integrable_const_iff_enorm enorm_ne_top]
  simp

lemma integrable_const_iff_isFiniteMeasure_enorm {c : ε} (hc : ‖c‖ₑ ≠ 0) (hc' : ‖c‖ₑ ≠ ∞) :
    Integrable (fun _ ↦ c) μ ↔ IsFiniteMeasure μ := by
  simp [integrable_const_iff_enorm hc', hc, isFiniteMeasure_iff]

lemma integrable_const_iff_isFiniteMeasure {c : β} (hc : c ≠ 0) :
    Integrable (fun _ ↦ c) μ ↔ IsFiniteMeasure μ := by
  simp [integrable_const_iff, hc, isFiniteMeasure_iff]

theorem Integrable.of_mem_Icc_enorm [IsFiniteMeasure μ]
    {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) {X : α → ℝ≥0∞} (hX : AEMeasurable X μ)
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    Integrable X μ :=
  ⟨hX.aestronglyMeasurable, .of_mem_Icc_of_ne_top ha hb h⟩

theorem Integrable.of_mem_Icc [IsFiniteMeasure μ] (a b : ℝ) {X : α → ℝ} (hX : AEMeasurable X μ)
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    Integrable X μ :=
  ⟨hX.aestronglyMeasurable, .of_mem_Icc a b h⟩

@[simp, fun_prop]
theorem integrable_const_enorm [IsFiniteMeasure μ] {c : ε} (hc : ‖c‖ₑ ≠ ∞) :
    Integrable (fun _ : α ↦ c) μ :=
  (integrable_const_iff_enorm hc).2 <| .inr ‹_›

@[fun_prop]
theorem integrable_const [IsFiniteMeasure μ] (c : β) : Integrable (fun _ : α => c) μ :=
  integrable_const_iff.2 <| .inr ‹_›

-- TODO: an `ENorm`-version of this lemma requires `HasFiniteIntegral.of_finite`
@[fun_prop, simp]
lemma Integrable.of_finite [Finite α] [MeasurableSingletonClass α] [IsFiniteMeasure μ] {f : α → β} :
    Integrable f μ := ⟨.of_discrete, .of_finite⟩

/-- This lemma is a special case of `Integrable.of_finite`. -/
lemma Integrable.of_isEmpty [IsEmpty α] {f : α → β} : Integrable f μ := .of_finite

/-- This lemma is a special case of `Integrable.of_finite`. -/
lemma Integrable.of_subsingleton [Subsingleton α] [IsFiniteMeasure μ] {f : α → β} :
    Integrable f μ :=
  .of_finite

theorem MemLp.integrable_enorm_rpow {f : α → ε} {p : ℝ≥0∞} (hf : MemLp f p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) : Integrable (fun x : α => ‖f x‖ₑ ^ p.toReal) μ := by
  rw [← memLp_one_iff_integrable]
  exact hf.enorm_rpow hp_ne_zero hp_ne_top

theorem MemLp.integrable_norm_rpow {f : α → β} {p : ℝ≥0∞} (hf : MemLp f p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) : Integrable (fun x : α => ‖f x‖ ^ p.toReal) μ := by
  rw [← memLp_one_iff_integrable]
  exact hf.norm_rpow hp_ne_zero hp_ne_top

theorem MemLp.integrable_enorm_rpow' [IsFiniteMeasure μ] {f : α → ε} {p : ℝ≥0∞} (hf : MemLp f p μ) :
    Integrable (fun x : α => ‖f x‖ₑ ^ p.toReal) μ := by
  by_cases h_zero : p = 0
  · simp [h_zero]
  by_cases h_top : p = ∞
  · simp [h_top]
  exact hf.integrable_enorm_rpow h_zero h_top

theorem MemLp.integrable_norm_rpow' [IsFiniteMeasure μ] {f : α → β} {p : ℝ≥0∞} (hf : MemLp f p μ) :
    Integrable (fun x : α => ‖f x‖ ^ p.toReal) μ := by
  by_cases h_zero : p = 0
  · simp [h_zero]
  by_cases h_top : p = ∞
  · simp [h_top]
  exact hf.integrable_norm_rpow h_zero h_top

lemma MemLp.integrable_enorm_pow {f : α → ε} {p : ℕ} (hf : MemLp f p μ) (hp : p ≠ 0) :
    Integrable (fun x : α ↦ ‖f x‖ₑ ^ p) μ := by
  simpa using hf.integrable_enorm_rpow (mod_cast hp) (by simp)

lemma MemLp.integrable_norm_pow {f : α → β} {p : ℕ} (hf : MemLp f p μ) (hp : p ≠ 0) :
    Integrable (fun x : α => ‖f x‖ ^ p) μ := by
  simpa using hf.integrable_norm_rpow (mod_cast hp) (by simp)

lemma MemLp.integrable_enorm_pow' [IsFiniteMeasure μ] {f : α → ε} {p : ℕ} (hf : MemLp f p μ) :
    Integrable (fun x : α ↦ ‖f x‖ₑ ^ p) μ := by simpa using hf.integrable_enorm_rpow'

lemma MemLp.integrable_norm_pow' [IsFiniteMeasure μ] {f : α → β} {p : ℕ} (hf : MemLp f p μ) :
    Integrable (fun x : α => ‖f x‖ ^ p) μ := by simpa using hf.integrable_norm_rpow'

lemma integrable_enorm_rpow_iff {f : α → ε} {p : ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ) (p_zero : p ≠ 0) (p_top : p ≠ ∞) :
    Integrable (fun x : α => ‖f x‖ₑ ^ p.toReal) μ ↔ MemLp f p μ := by
  rw [← memLp_enorm_rpow_iff (q := p) hf p_zero p_top, ← memLp_one_iff_integrable,
    ENNReal.div_self p_zero p_top]

lemma integrable_norm_rpow_iff {f : α → β} {p : ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ) (p_zero : p ≠ 0) (p_top : p ≠ ∞) :
    Integrable (fun x : α => ‖f x‖ ^ p.toReal) μ ↔ MemLp f p μ := by
  rw [← memLp_norm_rpow_iff (q := p) hf p_zero p_top, ← memLp_one_iff_integrable,
    ENNReal.div_self p_zero p_top]

theorem Integrable.mono_measure {f : α → ε} (h : Integrable f ν) (hμ : μ ≤ ν) : Integrable f μ :=
  ⟨h.aestronglyMeasurable.mono_measure hμ, h.hasFiniteIntegral.mono_measure hμ⟩

theorem Integrable.of_measure_le_smul {ε} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
    {μ' : Measure α} {c : ℝ≥0∞} (hc : c ≠ ∞) (hμ'_le : μ' ≤ c • μ)
    {f : α → ε} (hf : Integrable f μ) : Integrable f μ' := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.of_measure_le_smul hc hμ'_le

@[fun_prop]
theorem Integrable.add_measure [PseudoMetrizableSpace ε]
    {f : α → ε} (hμ : Integrable f μ) (hν : Integrable f ν) :
    Integrable f (μ + ν) := by
  simp_rw [← memLp_one_iff_integrable] at hμ hν ⊢
  refine ⟨hμ.aestronglyMeasurable.add_measure hν.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_one_add_measure, ENNReal.add_lt_top]
  exact ⟨hμ.eLpNorm_lt_top, hν.eLpNorm_lt_top⟩

theorem Integrable.left_of_add_measure {f : α → ε} (h : Integrable f (μ + ν)) : Integrable f μ := by
  rw [← memLp_one_iff_integrable] at h ⊢
  exact h.left_of_add_measure

theorem Integrable.right_of_add_measure {f : α → ε} (h : Integrable f (μ + ν)) :
    Integrable f ν := by
  rw [← memLp_one_iff_integrable] at h ⊢
  exact h.right_of_add_measure

@[simp]
theorem integrable_add_measure [PseudoMetrizableSpace ε] {f : α → ε} :
    Integrable f (μ + ν) ↔ Integrable f μ ∧ Integrable f ν :=
  ⟨fun h => ⟨h.left_of_add_measure, h.right_of_add_measure⟩, fun h => h.1.add_measure h.2⟩

@[simp]
theorem integrable_zero_measure {f : α → ε} : Integrable f (0 : Measure α) := by
  constructor <;> fun_prop

/-- In a measurable space with measurable singletons, every function is integrable with respect to
a Dirac measure.
See `integrable_dirac'` for a version which requires `f` to be strongly measurable but does not
need singletons to be measurable. -/
@[fun_prop]
lemma integrable_dirac [MeasurableSingletonClass α] {a : α} {f : α → ε} (hfa : ‖f a‖ₑ < ∞) :
    Integrable f (Measure.dirac a) :=
  ⟨aestronglyMeasurable_dirac, by simpa [HasFiniteIntegral]⟩

/-- Every strongly measurable function is integrable with respect to a Dirac measure.
See `integrable_dirac` for a version which requires that singletons are measurable sets but has no
hypothesis on `f`. -/
@[fun_prop]
lemma integrable_dirac' {a : α} {f : α → ε} (hf : StronglyMeasurable f) (hfa : ‖f a‖ₑ < ∞) :
    Integrable f (Measure.dirac a) :=
  ⟨hf.aestronglyMeasurable, by simpa [HasFiniteIntegral, lintegral_dirac' _ hf.enorm]⟩

theorem integrable_finset_sum_measure [PseudoMetrizableSpace ε]
    {ι} {m : MeasurableSpace α} {f : α → ε} {μ : ι → Measure α}
    {s : Finset ι} : Integrable f (∑ i ∈ s, μ i) ↔ ∀ i ∈ s, Integrable f (μ i) := by
  classical
  induction s using Finset.induction_on <;> simp [*]

section

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]

@[fun_prop]
theorem Integrable.smul_measure {f : α → ε} (h : Integrable f μ) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    Integrable f (c • μ) := by
  rw [← memLp_one_iff_integrable] at h ⊢
  exact h.smul_measure hc

@[fun_prop]
theorem Integrable.smul_measure_nnreal {f : α → ε} (h : Integrable f μ) {c : ℝ≥0} :
    Integrable f (c • μ) := by
  apply h.smul_measure
  simp

theorem integrable_smul_measure {f : α → ε} {c : ℝ≥0∞} (h₁ : c ≠ 0) (h₂ : c ≠ ∞) :
    Integrable f (c • μ) ↔ Integrable f μ :=
  ⟨fun h => by
    simpa only [smul_smul, ENNReal.inv_mul_cancel h₁ h₂, one_smul] using
      h.smul_measure (ENNReal.inv_ne_top.2 h₁),
    fun h => h.smul_measure h₂⟩

theorem integrable_inv_smul_measure {f : α → ε} {c : ℝ≥0∞} (h₁ : c ≠ 0) (h₂ : c ≠ ∞) :
    Integrable f (c⁻¹ • μ) ↔ Integrable f μ :=
  integrable_smul_measure (by simpa using h₂) (by simpa using h₁)

theorem Integrable.to_average {f : α → ε} (h : Integrable f μ) : Integrable f ((μ univ)⁻¹ • μ) := by
  rcases eq_or_ne μ 0 with (rfl | hne)
  · rwa [smul_zero]
  · apply h.smul_measure
    simpa

open scoped Classical in
theorem integrable_average [IsFiniteMeasure μ] {f : α → ε} :
    Integrable f ((μ univ)⁻¹ • μ) ↔ Integrable f μ :=
  (eq_or_ne μ 0).by_cases (fun h => by simp [h]) fun h =>
    integrable_smul_measure (ENNReal.inv_ne_zero.2 <| measure_ne_top _ _)
      (ENNReal.inv_ne_top.2 <| mt Measure.measure_univ_eq_zero.1 h)

end

section

variable {α' : Type*} [MeasurableSpace α']

theorem integrable_map_measure {f : α → α'} {g : α' → ε}
    (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) :
    Integrable g (Measure.map f μ) ↔ Integrable (g ∘ f) μ := by
  simp_rw [← memLp_one_iff_integrable]
  exact memLp_map_measure_iff hg hf

theorem Integrable.comp_aemeasurable {f : α → α'} {g : α' → ε}
    (hg : Integrable g (Measure.map f μ)) (hf : AEMeasurable f μ) : Integrable (g ∘ f) μ :=
  (integrable_map_measure hg.aestronglyMeasurable hf).mp hg

theorem Integrable.comp_measurable {f : α → α'} {g : α' → ε} (hg : Integrable g (Measure.map f μ))
    (hf : Measurable f) : Integrable (g ∘ f) μ :=
  hg.comp_aemeasurable hf.aemeasurable

end

theorem _root_.MeasurableEmbedding.integrable_map_iff {f : α → δ} (hf : MeasurableEmbedding f)
    {g : δ → ε} : Integrable g (Measure.map f μ) ↔ Integrable (g ∘ f) μ := by
  simp_rw [← memLp_one_iff_integrable]
  exact hf.memLp_map_measure_iff

theorem integrable_map_equiv (f : α ≃ᵐ δ) (g : δ → ε) :
    Integrable g (Measure.map f μ) ↔ Integrable (g ∘ f) μ := by
  simp_rw [← memLp_one_iff_integrable]
  exact f.memLp_map_measure_iff

theorem MeasurePreserving.integrable_comp {ν : Measure δ} {g : δ → ε} {f : α → δ}
    (hf : MeasurePreserving f μ ν) (hg : AEStronglyMeasurable g ν) :
    Integrable (g ∘ f) μ ↔ Integrable g ν := by
  rw [← hf.map_eq] at hg ⊢
  exact (integrable_map_measure hg hf.measurable.aemeasurable).symm

theorem MeasurePreserving.integrable_comp_of_integrable {ν : Measure δ} {g : δ → ε} {f : α → δ}
    (hf : MeasurePreserving f μ ν) (hg : Integrable g ν) :
    Integrable (g ∘ f) μ :=
  hf.integrable_comp hg.aestronglyMeasurable |>.mpr hg

theorem MeasurePreserving.integrable_comp_emb {f : α → δ} {ν} (h₁ : MeasurePreserving f μ ν)
    (h₂ : MeasurableEmbedding f) {g : δ → ε} : Integrable (g ∘ f) μ ↔ Integrable g ν :=
  h₁.map_eq ▸ Iff.symm h₂.integrable_map_iff

theorem lintegral_edist_lt_top {f g : α → β} (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫⁻ a, edist (f a) (g a) ∂μ) < ∞ :=
  lt_of_le_of_lt (lintegral_edist_triangle hf.aestronglyMeasurable aestronglyMeasurable_zero)
    (ENNReal.add_lt_top.2 <| by
      simp_rw [Pi.zero_apply, ← hasFiniteIntegral_iff_edist]
      exact ⟨hf.hasFiniteIntegral, hg.hasFiniteIntegral⟩)

section ESeminormedAddMonoid

variable {ε' : Type*} [TopologicalSpace ε'] [ESeminormedAddMonoid ε']

variable (α ε') in
@[simp]
theorem integrable_zero (μ : Measure α) : Integrable (fun _ => (0 : ε')) μ := by
  simp [Integrable, aestronglyMeasurable_const]

theorem Integrable.add' {f g : α → ε'} (hf : Integrable f μ) (hg : Integrable g μ) :
    HasFiniteIntegral (f + g) μ :=
  calc
    ∫⁻ a, ‖f a + g a‖ₑ ∂μ ≤ ∫⁻ a, ‖f a‖ₑ + ‖g a‖ₑ ∂μ := lintegral_mono fun _ ↦ enorm_add_le _ _
    _ = _ := lintegral_enorm_add_left hf.aestronglyMeasurable _
    _ < ∞ := add_lt_top.2 ⟨hf.hasFiniteIntegral, hg.hasFiniteIntegral⟩

@[fun_prop]
theorem Integrable.add [ContinuousAdd ε']
    {f g : α → ε'} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (f + g) μ :=
  ⟨hf.aestronglyMeasurable.add hg.aestronglyMeasurable, hf.add' hg⟩

@[fun_prop]
theorem Integrable.add'' [ContinuousAdd ε']
    {f g : α → ε'} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun x ↦ f x + g x) μ := hf.add hg

@[simp]
lemma Integrable.of_subsingleton_codomain [Subsingleton ε'] {f : α → ε'} :
    Integrable f μ :=
  integrable_zero _ _ _ |>.congr <| .of_forall fun _ ↦ Subsingleton.elim _ _

end ESeminormedAddMonoid

section ESeminormedAddCommMonoid

variable {ε' : Type*} [TopologicalSpace ε'] [ESeminormedAddCommMonoid ε'] [ContinuousAdd ε']

@[fun_prop]
theorem integrable_finset_sum' {ι} (s : Finset ι) {f : ι → α → ε'}
    (hf : ∀ i ∈ s, Integrable (f i) μ) : Integrable (∑ i ∈ s, f i) μ :=
  Finset.sum_induction f (fun g => Integrable g μ) (fun _ _ => Integrable.add)
    (integrable_zero _ _ _) hf

@[fun_prop]
theorem integrable_finset_sum {ι} (s : Finset ι) {f : ι → α → ε'}
    (hf : ∀ i ∈ s, Integrable (f i) μ) : Integrable (fun a => ∑ i ∈ s, f i a) μ := by
  simpa only [← Finset.sum_apply] using integrable_finset_sum' s hf

end ESeminormedAddCommMonoid

/-- If `f` is integrable, then so is `-f`.
See `Integrable.neg'` for the same statement, but formulated with `x ↦ - f x` instead of `-f`. -/
@[fun_prop]
theorem Integrable.neg {f : α → β} (hf : Integrable f μ) : Integrable (-f) μ :=
  ⟨hf.aestronglyMeasurable.neg, by fun_prop⟩

/-- If `f` is integrable, then so is `fun x ↦ - f x`.
See `Integrable.neg` for the same statement, but formulated with `-f` instead of `fun x ↦ - f x`. -/
@[fun_prop]
theorem Integrable.neg' {f : α → β} (hf : Integrable f μ) : Integrable (fun x ↦ - f x) μ :=
  ⟨hf.aestronglyMeasurable.neg, hf.hasFiniteIntegral.neg⟩

@[simp]
theorem integrable_neg_iff {f : α → β} : Integrable (-f) μ ↔ Integrable f μ :=
  ⟨fun h => neg_neg f ▸ h.neg, Integrable.neg⟩

/-- if `f` is integrable, then `f + g` is integrable iff `g` is.
See `integrable_add_iff_integrable_right'` for the same statement with `fun x ↦ f x + g x` instead
of `f + g`. -/
@[simp]
lemma integrable_add_iff_integrable_right {f g : α → β} (hf : Integrable f μ) :
    Integrable (f + g) μ ↔ Integrable g μ :=
  ⟨fun h ↦ show g = f + g + (-f) by simp only [add_neg_cancel_comm] ▸ h.add hf.neg,
    fun h ↦ hf.add h⟩

/-- if `f` is integrable, then `fun x ↦ f x + g x` is integrable iff `g` is.
See `integrable_add_iff_integrable_right` for the same statement with `f + g` instead
of `fun x ↦ f x + g x`. -/
@[simp]
lemma integrable_add_iff_integrable_right' {f g : α → β} (hf : Integrable f μ) :
    Integrable (fun x ↦ f x + g x) μ ↔ Integrable g μ :=
  integrable_add_iff_integrable_right hf

/-- if `f` is integrable, then `g + f` is integrable iff `g` is.
See `integrable_add_iff_integrable_left'` for the same statement with `fun x ↦ g x + f x` instead
of `g + f`. -/
@[simp]
lemma integrable_add_iff_integrable_left {f g : α → β} (hf : Integrable f μ) :
    Integrable (g + f) μ ↔ Integrable g μ := by
  rw [add_comm, integrable_add_iff_integrable_right hf]

/-- if `f` is integrable, then `fun x ↦ g x + f x` is integrable iff `g` is.
See `integrable_add_iff_integrable_left'` for the same statement with `g + f` instead
of `fun x ↦ g x + f x`. -/
@[simp]
lemma integrable_add_iff_integrable_left' {f g : α → β} (hf : Integrable f μ) :
    Integrable (fun x ↦ g x + f x) μ ↔ Integrable g μ :=
  integrable_add_iff_integrable_left hf

lemma integrable_left_of_integrable_add_of_nonneg {f g : α → ℝ}
    (h_meas : AEStronglyMeasurable f μ) (hf : 0 ≤ᵐ[μ] f) (hg : 0 ≤ᵐ[μ] g)
    (h_int : Integrable (f + g) μ) : Integrable f μ := by
  refine h_int.mono' h_meas ?_
  filter_upwards [hf, hg] with a haf hag
  exact (Real.norm_of_nonneg haf).symm ▸ le_add_of_nonneg_right hag

lemma integrable_right_of_integrable_add_of_nonneg {f g : α → ℝ}
    (h_meas : AEStronglyMeasurable f μ) (hf : 0 ≤ᵐ[μ] f) (hg : 0 ≤ᵐ[μ] g)
    (h_int : Integrable (f + g) μ) : Integrable g μ :=
  integrable_left_of_integrable_add_of_nonneg
    ((AEStronglyMeasurable.add_iff_right h_meas).mp h_int.aestronglyMeasurable)
      hg hf (add_comm f g ▸ h_int)

lemma integrable_add_iff_of_nonneg {f g : α → ℝ} (h_meas : AEStronglyMeasurable f μ)
    (hf : 0 ≤ᵐ[μ] f) (hg : 0 ≤ᵐ[μ] g) :
    Integrable (f + g) μ ↔ Integrable f μ ∧ Integrable g μ :=
  ⟨fun h ↦ ⟨integrable_left_of_integrable_add_of_nonneg h_meas hf hg h,
    integrable_right_of_integrable_add_of_nonneg h_meas hf hg h⟩, fun ⟨hf, hg⟩ ↦ hf.add hg⟩

lemma integrable_add_iff_of_nonpos {f g : α → ℝ} (h_meas : AEStronglyMeasurable f μ)
    (hf : f ≤ᵐ[μ] 0) (hg : g ≤ᵐ[μ] 0) :
    Integrable (f + g) μ ↔ Integrable f μ ∧ Integrable g μ := by
  rw [← integrable_neg_iff, ← integrable_neg_iff (f := f), ← integrable_neg_iff (f := g), neg_add]
  exact integrable_add_iff_of_nonneg h_meas.neg (hf.mono (fun _ ↦ neg_nonneg_of_nonpos))
    (hg.mono (fun _ ↦ neg_nonneg_of_nonpos))

lemma integrable_add_const_iff [IsFiniteMeasure μ] {f : α → β} {c : β} :
    Integrable (fun x ↦ f x + c) μ ↔ Integrable f μ :=
  integrable_add_iff_integrable_left (integrable_const _)

lemma integrable_const_add_iff [IsFiniteMeasure μ] {f : α → β} {c : β} :
    Integrable (fun x ↦ c + f x) μ ↔ Integrable f μ :=
  integrable_add_iff_integrable_right (integrable_const _)

-- TODO: generalise these lemmas to an `ENormedAddCommSubMonoid`
@[fun_prop]
theorem Integrable.sub {f g : α → β} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (f - g) μ := by simpa only [sub_eq_add_neg] using hf.add hg.neg

@[fun_prop]
theorem Integrable.sub' {f g : α → β} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun a ↦ f a - g a) μ := by simpa only [sub_eq_add_neg] using hf.add hg.neg

@[fun_prop]
theorem Integrable.enorm {f : α → ε} (hf : Integrable f μ) : Integrable (‖f ·‖ₑ) μ := by
  constructor <;> fun_prop

@[fun_prop]
theorem Integrable.norm {f : α → β} (hf : Integrable f μ) : Integrable (fun a => ‖f a‖) μ := by
  constructor <;> fun_prop

@[fun_prop]
theorem Integrable.inf {β}
    [NormedAddCommGroup β] [Lattice β] [HasSolidNorm β] [IsOrderedAddMonoid β]
    {f g : α → β} (hf : Integrable f μ)
    (hg : Integrable g μ) : Integrable (f ⊓ g) μ := by
  rw [← memLp_one_iff_integrable] at hf hg ⊢
  exact hf.inf hg

@[fun_prop]
theorem Integrable.sup {β}
    [NormedAddCommGroup β] [Lattice β] [HasSolidNorm β] [IsOrderedAddMonoid β]
    {f g : α → β} (hf : Integrable f μ)
    (hg : Integrable g μ) : Integrable (f ⊔ g) μ := by
  rw [← memLp_one_iff_integrable] at hf hg ⊢
  exact hf.sup hg

@[fun_prop]
theorem Integrable.abs {β}
    [NormedAddCommGroup β] [Lattice β] [HasSolidNorm β] [IsOrderedAddMonoid β]
    {f : α → β} (hf : Integrable f μ) :
    Integrable (fun a => |f a|) μ := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.abs

-- TODO: generalise this to enorms, once there is an `ENormedDivisionRing` class
theorem Integrable.bdd_mul {F : Type*} [NormedDivisionRing F] {f g : α → F} (hint : Integrable g μ)
    (hm : AEStronglyMeasurable f μ) (hfbdd : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    Integrable (fun x => f x * g x) μ := by
  rcases isEmpty_or_nonempty α with hα | hα
  · rw [μ.eq_zero_of_isEmpty]
    exact integrable_zero_measure
  · refine ⟨hm.mul hint.1, ?_⟩
    obtain ⟨C, hC⟩ := hfbdd
    have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC hα.some)
    have : (fun x => ‖f x * g x‖₊) ≤ fun x => ⟨C, hCnonneg⟩ * ‖g x‖₊ := by
      intro x
      simp only [nnnorm_mul]
      exact mul_le_mul_of_nonneg_right (hC x) (zero_le _)
    refine lt_of_le_of_lt (lintegral_mono_nnreal this) ?_
    simp only [ENNReal.coe_mul]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top hint.2

-- TODO: generalise the following lemmas to enorm classes

/-- **Hölder's inequality for integrable functions**: the scalar multiplication of an integrable
vector-valued function by a scalar function with finite essential supremum is integrable. -/
theorem Integrable.essSup_smul {R : Type*} [NormedRing R] [Module R β] [IsBoundedSMul R β]
    {f : α → β} (hf : Integrable f μ) {g : α → R}
    (g_aestronglyMeasurable : AEStronglyMeasurable g μ) (ess_sup_g : essSup (‖g ·‖ₑ) μ ≠ ∞) :
    Integrable (fun x : α => g x • f x) μ := by
  rw [← memLp_one_iff_integrable] at *
  refine ⟨g_aestronglyMeasurable.smul hf.1, ?_⟩
  have hg' : eLpNorm g ∞ μ ≠ ∞ := by rwa [eLpNorm_exponent_top]
  calc
    eLpNorm (fun x : α => g x • f x) 1 μ ≤ _ := by
      simpa using MeasureTheory.eLpNorm_smul_le_mul_eLpNorm hf.1 g_aestronglyMeasurable
        (p := ∞) (q := 1)
    _ < ∞ := ENNReal.mul_lt_top hg'.lt_top hf.2

/-- Hölder's inequality for integrable functions: the scalar multiplication of an integrable
scalar-valued function by a vector-value function with finite essential supremum is integrable. -/
theorem Integrable.smul_essSup {𝕜 : Type*} [NormedRing 𝕜] [MulActionWithZero 𝕜 β]
    [IsBoundedSMul 𝕜 β] {f : α → 𝕜} (hf : Integrable f μ) {g : α → β}
    (g_aestronglyMeasurable : AEStronglyMeasurable g μ) (ess_sup_g : essSup (‖g ·‖ₑ) μ ≠ ∞) :
    Integrable (fun x : α => f x • g x) μ := by
  rw [← memLp_one_iff_integrable] at *
  refine ⟨hf.1.smul g_aestronglyMeasurable, ?_⟩
  have hg' : eLpNorm g ∞ μ ≠ ∞ := by rwa [eLpNorm_exponent_top]
  calc
    eLpNorm (fun x : α => f x • g x) 1 μ ≤ _ := by
      simpa using MeasureTheory.eLpNorm_smul_le_mul_eLpNorm g_aestronglyMeasurable hf.1
        (p := 1) (q := ∞)
    _ < ∞ := ENNReal.mul_lt_top hf.2 hg'.lt_top

theorem integrable_enorm_iff {f : α → ε} (hf : AEStronglyMeasurable f μ) :
    Integrable (‖f ·‖ₑ) μ ↔ Integrable f μ := by
  simp_rw [Integrable, and_iff_right hf, and_iff_right hf.enorm.aestronglyMeasurable,
    hasFiniteIntegral_enorm_iff]

theorem integrable_norm_iff {f : α → β} (hf : AEStronglyMeasurable f μ) :
    Integrable (fun a => ‖f a‖) μ ↔ Integrable f μ := by
  simp_rw [Integrable, and_iff_right hf, and_iff_right hf.norm, hasFiniteIntegral_norm_iff]

-- TODO: generalise this lemma to an `ENormedAddCommSubMonoid`
theorem integrable_of_norm_sub_le {f₀ f₁ : α → β} {g : α → ℝ} (hf₁_m : AEStronglyMeasurable f₁ μ)
    (hf₀_i : Integrable f₀ μ) (hg_i : Integrable g μ) (h : ∀ᵐ a ∂μ, ‖f₀ a - f₁ a‖ ≤ g a) :
    Integrable f₁ μ :=
  haveI : ∀ᵐ a ∂μ, ‖f₁ a‖ ≤ ‖f₀ a‖ + g a := by
    apply h.mono
    intro a ha
    calc
      ‖f₁ a‖ ≤ ‖f₀ a‖ + ‖f₀ a - f₁ a‖ := norm_le_insert _ _
      _ ≤ ‖f₀ a‖ + g a := by gcongr
  Integrable.mono' (hf₀_i.norm.add hg_i) hf₁_m this

lemma integrable_of_le_of_le {f g₁ g₂ : α → ℝ} (hf : AEStronglyMeasurable f μ)
    (h_le₁ : g₁ ≤ᵐ[μ] f) (h_le₂ : f ≤ᵐ[μ] g₂)
    (h_int₁ : Integrable g₁ μ) (h_int₂ : Integrable g₂ μ) :
    Integrable f μ := by
  have : ∀ᵐ x ∂μ, ‖f x‖ ≤ max ‖g₁ x‖ ‖g₂ x‖ := by
    filter_upwards [h_le₁, h_le₂] with x hx1 hx2
    simp only [Real.norm_eq_abs]
    exact abs_le_max_abs_abs hx1 hx2
  have h_le_add : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖‖g₁ x‖ + ‖g₂ x‖‖ := by
    filter_upwards [this] with x hx
    refine hx.trans ?_
    conv_rhs => rw [Real.norm_of_nonneg (by positivity)]
    exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
  exact Integrable.mono (by fun_prop) hf h_le_add

-- TODO: generalising this to enorms requires defining a product instance for enormed monoids first
@[fun_prop]
theorem Integrable.prodMk {f : α → β} {g : α → γ} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun x => (f x, g x)) μ :=
  ⟨by fun_prop,
    (hf.norm.add' hg.norm).mono <|
      Eventually.of_forall fun x =>
        calc
          max ‖f x‖ ‖g x‖ ≤ ‖f x‖ + ‖g x‖ := max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
          _ ≤ ‖‖f x‖ + ‖g x‖‖ := le_abs_self _⟩

@[deprecated (since := "2025-03-05")]
alias Integrable.prod_mk := Integrable.prodMk

theorem MemLp.integrable {q : ℝ≥0∞} (hq1 : 1 ≤ q) {f : α → ε} [IsFiniteMeasure μ]
    (hfq : MemLp f q μ) : Integrable f μ :=
  memLp_one_iff_integrable.mp (hfq.mono_exponent hq1)

/-- A non-quantitative version of Markov inequality for integrable functions: the measure of points
where `‖f x‖ₑ ≥ ε` is finite for all positive `ε`. -/
theorem Integrable.measure_enorm_ge_lt_top {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    {f : α → E} (hf : Integrable f μ) {ε : ℝ≥0∞} (hε : 0 < ε) (hε' : ε ≠ ∞) :
    μ { x | ε ≤ ‖f x‖ₑ } < ∞ := by
  refine meas_ge_le_mul_pow_eLpNorm_enorm μ one_ne_zero one_ne_top hf.1 hε.ne' (by simp [hε'])
    |>.trans_lt ?_
  apply ENNReal.mul_lt_top
  · simpa only [ENNReal.toReal_one, ENNReal.rpow_one, ENNReal.inv_lt_top, ENNReal.ofReal_pos]
      using hε
  · simpa only [ENNReal.toReal_one, ENNReal.rpow_one] using
      (memLp_one_iff_integrable.2 hf).eLpNorm_lt_top

/-- A non-quantitative version of Markov inequality for integrable functions: the measure of points
where `‖f x‖ ≥ ε` is finite for all positive `ε`. -/
theorem Integrable.measure_norm_ge_lt_top {f : α → β} (hf : Integrable f μ) {ε : ℝ} (hε : 0 < ε) :
    μ { x | ε ≤ ‖f x‖ } < ∞ := by
  convert Integrable.measure_enorm_ge_lt_top hf (ofReal_pos.mpr hε) ofReal_ne_top with x
  rw [← Real.enorm_of_nonneg hε.le, enorm_le_iff_norm_le, Real.norm_of_nonneg hε.le]

/-- A non-quantitative version of Markov inequality for integrable functions: the measure of points
where `‖f x‖ₑ > ε` is finite for all positive `ε`. -/
lemma Integrable.measure_norm_gt_lt_top_enorm {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    {f : α → E} (hf : Integrable f μ) {ε : ℝ≥0∞} (hε : 0 < ε) : μ {x | ε < ‖f x‖ₑ} < ∞ := by
  by_cases hε' : ε = ∞
  · simp [hε']
  exact lt_of_le_of_lt (measure_mono (fun _ h ↦ (Set.mem_setOf_eq ▸ h).le))
    (hf.measure_enorm_ge_lt_top hε hε')

/-- A non-quantitative version of Markov inequality for integrable functions: the measure of points
where `‖f x‖ > ε` is finite for all positive `ε`. -/
lemma Integrable.measure_norm_gt_lt_top {f : α → β} (hf : Integrable f μ) {ε : ℝ} (hε : 0 < ε) :
    μ {x | ε < ‖f x‖} < ∞ :=
  lt_of_le_of_lt (measure_mono (fun _ h ↦ (Set.mem_setOf_eq ▸ h).le)) (hf.measure_norm_ge_lt_top hε)

-- TODO: try generalising all lemmas below to enorm classes

/-- If `f` is `ℝ`-valued and integrable, then for any `c > 0` the set `{x | f x ≥ c}` has finite
measure. -/
lemma Integrable.measure_ge_lt_top {f : α → ℝ} (hf : Integrable f μ) {ε : ℝ} (ε_pos : 0 < ε) :
    μ {a : α | ε ≤ f a} < ∞ := by
  refine lt_of_le_of_lt (measure_mono ?_) (hf.measure_norm_ge_lt_top ε_pos)
  intro x hx
  simp only [Real.norm_eq_abs, Set.mem_setOf_eq] at hx ⊢
  exact hx.trans (le_abs_self _)

/-- If `f` is `ℝ`-valued and integrable, then for any `c < 0` the set `{x | f x ≤ c}` has finite
measure. -/
lemma Integrable.measure_le_lt_top {f : α → ℝ} (hf : Integrable f μ) {c : ℝ} (c_neg : c < 0) :
    μ {a : α | f a ≤ c} < ∞ := by
  refine lt_of_le_of_lt (measure_mono ?_) (hf.measure_norm_ge_lt_top (show 0 < -c by linarith))
  intro x hx
  simp only [Real.norm_eq_abs, Set.mem_setOf_eq] at hx ⊢
  exact (show -c ≤ - f x by linarith).trans (neg_le_abs _)

/-- If `f` is `ℝ`-valued and integrable, then for any `c > 0` the set `{x | f x > c}` has finite
measure. -/
lemma Integrable.measure_gt_lt_top {f : α → ℝ} (hf : Integrable f μ) {ε : ℝ} (ε_pos : 0 < ε) :
    μ {a : α | ε < f a} < ∞ :=
  lt_of_le_of_lt (measure_mono (fun _ hx ↦ (Set.mem_setOf_eq ▸ hx).le))
    (Integrable.measure_ge_lt_top hf ε_pos)

/-- If `f` is `ℝ`-valued and integrable, then for any `c < 0` the set `{x | f x < c}` has finite
measure. -/
lemma Integrable.measure_lt_lt_top {f : α → ℝ} (hf : Integrable f μ) {c : ℝ} (c_neg : c < 0) :
    μ {a : α | f a < c} < ∞ :=
  lt_of_le_of_lt (measure_mono (fun _ hx ↦ (Set.mem_setOf_eq ▸ hx).le))
    (Integrable.measure_le_lt_top hf c_neg)

theorem LipschitzWith.integrable_comp_iff_of_antilipschitz {K K'} {f : α → β} {g : β → γ}
    (hg : LipschitzWith K g) (hg' : AntilipschitzWith K' g) (g0 : g 0 = 0) :
    Integrable (g ∘ f) μ ↔ Integrable f μ := by
  simp [← memLp_one_iff_integrable, hg.memLp_comp_iff_of_antilipschitz hg' g0]

@[fun_prop]
theorem Integrable.real_toNNReal {f : α → ℝ} (hf : Integrable f μ) :
    Integrable (fun x => ((f x).toNNReal : ℝ)) μ := by
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  refine lt_of_le_of_lt ?_ ((hasFiniteIntegral_iff_norm _).1 hf.hasFiniteIntegral)
  apply lintegral_mono
  intro x
  simp [abs_le, le_abs_self]

theorem ofReal_toReal_ae_eq {f : α → ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x < ∞) :
    (fun x => ENNReal.ofReal (f x).toReal) =ᵐ[μ] f := by
  filter_upwards [hf]
  intro x hx
  simp only [hx.ne, ofReal_toReal, Ne, not_false_iff]

theorem coe_toNNReal_ae_eq {f : α → ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x < ∞) :
    (fun x => ((f x).toNNReal : ℝ≥0∞)) =ᵐ[μ] f := by
  filter_upwards [hf]
  intro x hx
  simp only [hx.ne, Ne, not_false_iff, coe_toNNReal]

section count

variable [MeasurableSingletonClass α] {f : α → β}

/-- A function is integrable for the counting measure iff its norm is summable. -/
lemma integrable_count_iff :
    Integrable f Measure.count ↔ Summable (‖f ·‖) := by
  -- Note: this proof would be much easier if we assumed `SecondCountableTopology G`. Without
  -- this we have to justify the claim that `f` lands a.e. in a separable subset, which is true
  -- (because summable functions have countable range) but slightly tedious to check.
  rw [Integrable, hasFiniteIntegral_count_iff, and_iff_right_iff_imp]
  intro hs
  have hs' : (Function.support f).Countable := by
    simpa only [Ne, Pi.zero_apply, eq_comm, Function.support, norm_eq_zero]
      using hs.countable_support
  letI : MeasurableSpace β := borel β
  haveI : BorelSpace β := ⟨rfl⟩
  refine aestronglyMeasurable_iff_aemeasurable_separable.mpr ⟨?_, ?_⟩
  · refine (measurable_zero.measurable_of_countable_ne ?_).aemeasurable
    simpa only [Ne, Pi.zero_apply, eq_comm, Function.support] using hs'
  · refine ⟨f '' univ, ?_, ae_of_all _ fun a ↦ ⟨a, ⟨mem_univ _, rfl⟩⟩⟩
    suffices f '' univ ⊆ (f '' f.support) ∪ {0} from
      (((hs'.image f).union (countable_singleton 0)).mono this).isSeparable
    grind [Function.mem_support]

end count

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integrable_withDensity_iff_integrable_coe_smul {f : α → ℝ≥0} (hf : Measurable f)
    {g : α → E} :
    Integrable g (μ.withDensity fun x => f x) ↔ Integrable (fun x => (f x : ℝ) • g x) μ := by
  by_cases H : AEStronglyMeasurable (fun x : α => (f x : ℝ) • g x) μ
  · simp only [Integrable, aestronglyMeasurable_withDensity_iff hf, hasFiniteIntegral_iff_enorm, H,
      true_and]
    rw [lintegral_withDensity_eq_lintegral_mul₀' hf.coe_nnreal_ennreal.aemeasurable]
    · simp [enorm_smul]
    · simpa [aemeasurable_withDensity_ennreal_iff hf, enorm_smul] using H.enorm
  · simp only [Integrable, aestronglyMeasurable_withDensity_iff hf, H, false_and]

theorem integrable_withDensity_iff_integrable_smul {f : α → ℝ≥0} (hf : Measurable f) {g : α → E} :
    Integrable g (μ.withDensity fun x => f x) ↔ Integrable (fun x => f x • g x) μ :=
  integrable_withDensity_iff_integrable_coe_smul hf

theorem integrable_withDensity_iff_integrable_smul' {f : α → ℝ≥0∞} (hf : Measurable f)
    (hflt : ∀ᵐ x ∂μ, f x < ∞) {g : α → E} :
    Integrable g (μ.withDensity f) ↔ Integrable (fun x => (f x).toReal • g x) μ := by
  rw [← withDensity_congr_ae (coe_toNNReal_ae_eq hflt),
    integrable_withDensity_iff_integrable_smul]
  · simp_rw [NNReal.smul_def, ENNReal.toReal]
  · exact hf.ennreal_toNNReal

theorem integrable_withDensity_iff_integrable_coe_smul₀ {f : α → ℝ≥0} (hf : AEMeasurable f μ)
    {g : α → E} :
    Integrable g (μ.withDensity fun x => f x) ↔ Integrable (fun x => (f x : ℝ) • g x) μ :=
  calc
    Integrable g (μ.withDensity fun x => f x) ↔
        Integrable g (μ.withDensity fun x => (hf.mk f x : ℝ≥0)) := by
      suffices (fun x => (f x : ℝ≥0∞)) =ᵐ[μ] (fun x => (hf.mk f x : ℝ≥0)) by
        rw [withDensity_congr_ae this]
      filter_upwards [hf.ae_eq_mk] with x hx
      simp [hx]
    _ ↔ Integrable (fun x => ((hf.mk f x : ℝ≥0) : ℝ) • g x) μ :=
      integrable_withDensity_iff_integrable_coe_smul hf.measurable_mk
    _ ↔ Integrable (fun x => (f x : ℝ) • g x) μ := by
      apply integrable_congr
      filter_upwards [hf.ae_eq_mk] with x hx
      simp [hx]

theorem integrable_withDensity_iff_integrable_smul₀' {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hflt : ∀ᵐ x ∂μ, f x < ∞) {g : α → E} :
    Integrable g (μ.withDensity f) ↔ Integrable (fun x => (f x).toReal • g x) μ := by
  rw [← withDensity_congr_ae (coe_toNNReal_ae_eq hflt),
    integrable_withDensity_iff_integrable_coe_smul₀]
  · congr!
  · exact hf.ennreal_toNNReal

theorem integrable_withDensity_iff_integrable_smul₀ {f : α → ℝ≥0} (hf : AEMeasurable f μ)
    {g : α → E} : Integrable g (μ.withDensity fun x => f x) ↔ Integrable (fun x => f x • g x) μ :=
  integrable_withDensity_iff_integrable_coe_smul₀ hf

end

theorem integrable_withDensity_iff {f : α → ℝ≥0∞} (hf : Measurable f) (hflt : ∀ᵐ x ∂μ, f x < ∞)
    {g : α → ℝ} : Integrable g (μ.withDensity f) ↔ Integrable (fun x => g x * (f x).toReal) μ := by
  have : (fun x => g x * (f x).toReal) = fun x => (f x).toReal • g x := by simp [mul_comm]
  rw [this]
  exact integrable_withDensity_iff_integrable_smul' hf hflt

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem memL1_smul_of_L1_withDensity {f : α → ℝ≥0} (f_meas : Measurable f)
    (u : Lp E 1 (μ.withDensity fun x => f x)) : MemLp (fun x => f x • u x) 1 μ :=
  memLp_one_iff_integrable.2 <|
    (integrable_withDensity_iff_integrable_smul f_meas).1 <| memLp_one_iff_integrable.1 (Lp.memLp u)

variable (μ)

/-- The map `u ↦ f • u` is an isometry between the `L^1` spaces for `μ.withDensity f` and `μ`. -/
noncomputable def withDensitySMulLI {f : α → ℝ≥0} (f_meas : Measurable f) :
    Lp E 1 (μ.withDensity fun x => f x) →ₗᵢ[ℝ] Lp E 1 μ where
  toFun u := (memL1_smul_of_L1_withDensity f_meas u).toLp _
  map_add' := by
    intro u v
    ext1
    filter_upwards [(memL1_smul_of_L1_withDensity f_meas u).coeFn_toLp,
      (memL1_smul_of_L1_withDensity f_meas v).coeFn_toLp,
      (memL1_smul_of_L1_withDensity f_meas (u + v)).coeFn_toLp,
      Lp.coeFn_add ((memL1_smul_of_L1_withDensity f_meas u).toLp _)
        ((memL1_smul_of_L1_withDensity f_meas v).toLp _),
      (ae_withDensity_iff f_meas.coe_nnreal_ennreal).1 (Lp.coeFn_add u v)]
    intro x hu hv huv h' h''
    rw [huv, h', Pi.add_apply, hu, hv]
    rcases eq_or_ne (f x) 0 with (hx | hx)
    · simp only [hx, zero_smul, add_zero]
    · rw [h'' _, Pi.add_apply, smul_add]
      simpa only [Ne, ENNReal.coe_eq_zero] using hx
  map_smul' := by
    intro r u
    ext1
    filter_upwards [(ae_withDensity_iff f_meas.coe_nnreal_ennreal).1 (Lp.coeFn_smul r u),
      (memL1_smul_of_L1_withDensity f_meas (r • u)).coeFn_toLp,
      Lp.coeFn_smul r ((memL1_smul_of_L1_withDensity f_meas u).toLp _),
      (memL1_smul_of_L1_withDensity f_meas u).coeFn_toLp]
    intro x h h' h'' h'''
    rw [RingHom.id_apply, h', h'', Pi.smul_apply, h''']
    rcases eq_or_ne (f x) 0 with (hx | hx)
    · simp only [hx, zero_smul, smul_zero]
    · rw [h _, smul_comm, Pi.smul_apply]
      simpa only [Ne, ENNReal.coe_eq_zero] using hx
  norm_map' := by
    intro u
    simp only [eLpNorm, LinearMap.coe_mk, AddHom.coe_mk,
      one_ne_zero, ENNReal.one_ne_top, ENNReal.toReal_one, if_false, eLpNorm', ENNReal.rpow_one,
      _root_.div_one, Lp.norm_def]
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ f_meas.coe_nnreal_ennreal
        (Filter.Eventually.of_forall fun x => ENNReal.coe_lt_top)]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [(memL1_smul_of_L1_withDensity f_meas u).coeFn_toLp] with x hx
    rw [hx]
    simp [NNReal.smul_def, enorm_smul]

@[simp]
theorem withDensitySMulLI_apply {f : α → ℝ≥0} (f_meas : Measurable f)
    (u : Lp E 1 (μ.withDensity fun x => f x)) :
    withDensitySMulLI μ (E := E) f_meas u =
      (memL1_smul_of_L1_withDensity f_meas u).toLp fun x => f x • u x :=
  rfl

end

section ENNReal

theorem mem_L1_toReal_of_lintegral_ne_top {f : α → ℝ≥0∞} (hfm : AEMeasurable f μ)
    (hfi : ∫⁻ x, f x ∂μ ≠ ∞) : MemLp (fun x ↦ (f x).toReal) 1 μ := by
  rw [MemLp, eLpNorm_one_eq_lintegral_enorm]
  exact ⟨(AEMeasurable.ennreal_toReal hfm).aestronglyMeasurable,
    hasFiniteIntegral_toReal_of_lintegral_ne_top hfi⟩

theorem integrable_toReal_of_lintegral_ne_top {f : α → ℝ≥0∞} (hfm : AEMeasurable f μ)
    (hfi : ∫⁻ x, f x ∂μ ≠ ∞) : Integrable (fun x ↦ (f x).toReal) μ :=
  memLp_one_iff_integrable.1 <| mem_L1_toReal_of_lintegral_ne_top hfm hfi

lemma integrable_toReal_iff {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf_ne_top : ∀ᵐ x ∂μ, f x ≠ ∞) :
    Integrable (fun x ↦ (f x).toReal) μ ↔ ∫⁻ x, f x ∂μ ≠ ∞ := by
  rw [Integrable, hasFiniteIntegral_toReal_iff hf_ne_top]
  simp only [hf.ennreal_toReal.aestronglyMeasurable, ne_eq, true_and]

lemma lintegral_ofReal_ne_top_iff_integrable {f : α → ℝ}
    (hfm : AEStronglyMeasurable f μ) (hf : 0 ≤ᵐ[μ] f) :
    ∫⁻ a, ENNReal.ofReal (f a) ∂μ ≠ ∞ ↔ Integrable f μ := by
  rw [Integrable, hasFiniteIntegral_iff_ofReal hf]
  simp [hfm]

end ENNReal

section PosPart

/-! ### Lemmas used for defining the positive part of an `L¹` function -/


@[fun_prop]
theorem Integrable.pos_part {f : α → ℝ} (hf : Integrable f μ) :
    Integrable (fun a => max (f a) 0) μ := by
  constructor <;> fun_prop

@[fun_prop]
theorem Integrable.neg_part {f : α → ℝ} (hf : Integrable f μ) :
    Integrable (fun a => max (-f a) 0) μ :=
  hf.neg.pos_part

end PosPart

section IsBoundedSMul

variable {𝕜 : Type*}
  {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]

@[fun_prop]
theorem Integrable.smul [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 β] [IsBoundedSMul 𝕜 β] (c : 𝕜)
    {f : α → β} (hf : Integrable f μ) : Integrable (c • f) μ := by
  constructor <;> fun_prop

@[fun_prop]
theorem Integrable.fun_smul [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 β] [IsBoundedSMul 𝕜 β] (c : 𝕜)
    {f : α → β} (hf : Integrable f μ) : Integrable (fun x ↦ c • f x) μ :=
  hf.smul c

@[fun_prop]
theorem Integrable.smul_enorm
    [NormedAddCommGroup 𝕜] [SMul 𝕜 ε] [ContinuousConstSMul 𝕜 ε] [ENormSMulClass 𝕜 ε] (c : 𝕜)
    {f : α → ε} (hf : Integrable f μ) : Integrable (c • f) μ := by
  constructor <;> fun_prop

theorem Integrable.fun_smul_enorm
    [NormedAddCommGroup 𝕜] [SMul 𝕜 ε] [ContinuousConstSMul 𝕜 ε] [ENormSMulClass 𝕜 ε] (c : 𝕜)
    {f : α → ε} (hf : Integrable f μ) : Integrable (fun x ↦ c • f x) μ :=
  hf.smul_enorm c

theorem _root_.IsUnit.integrable_smul_iff [NormedRing 𝕜] [MulActionWithZero 𝕜 β]
    [IsBoundedSMul 𝕜 β] {c : 𝕜} (hc : IsUnit c) (f : α → β) :
    Integrable (c • f) μ ↔ Integrable f μ :=
  and_congr hc.aestronglyMeasurable_const_smul_iff (hasFiniteIntegral_smul_iff hc f)

theorem integrable_smul_iff [NormedDivisionRing 𝕜] [MulActionWithZero 𝕜 β]
    [IsBoundedSMul 𝕜 β] {c : 𝕜} (hc : c ≠ 0) (f : α → β) :
    Integrable (c • f) μ ↔ Integrable f μ :=
  (IsUnit.mk0 _ hc).integrable_smul_iff f

theorem integrable_fun_smul_iff [NormedDivisionRing 𝕜] [MulActionWithZero 𝕜 β] [IsBoundedSMul 𝕜 β]
    {c : 𝕜} (hc : c ≠ 0) (f : α → β) :
    Integrable (fun x ↦ c • f x) μ ↔ Integrable f μ :=
  integrable_smul_iff hc f

variable [NormedRing 𝕜] [Module 𝕜 β] [IsBoundedSMul 𝕜 β]

theorem Integrable.smul_of_top_right {f : α → β} {φ : α → 𝕜} (hf : Integrable f μ)
    (hφ : MemLp φ ∞ μ) : Integrable (φ • f) μ := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact MemLp.smul hf hφ

theorem Integrable.smul_of_top_left {f : α → β} {φ : α → 𝕜} (hφ : Integrable φ μ)
    (hf : MemLp f ∞ μ) : Integrable (φ • f) μ := by
  rw [← memLp_one_iff_integrable] at hφ ⊢
  exact MemLp.smul hf hφ

@[fun_prop]
theorem Integrable.smul_const {f : α → 𝕜} (hf : Integrable f μ) (c : β) :
    Integrable (fun x => f x • c) μ :=
  hf.smul_of_top_left (memLp_top_const c)

end IsBoundedSMul

section NormedSpaceOverCompleteField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem integrable_smul_const {f : α → 𝕜} {c : E} (hc : c ≠ 0) :
    Integrable (fun x => f x • c) μ ↔ Integrable f μ := by
  simp_rw [Integrable, aestronglyMeasurable_smul_const_iff (f := f) hc, and_congr_right_iff,
    hasFiniteIntegral_iff_enorm, enorm_smul]
  intro _; rw [lintegral_mul_const' _ _ enorm_ne_top, ENNReal.mul_lt_top_iff]
  have : ∀ x : ℝ≥0∞, x = 0 → x < ∞ := by simp
  simp [hc, or_iff_left_of_imp (this _)]

end NormedSpaceOverCompleteField

section NormedRing

variable {𝕜 : Type*} [NormedRing 𝕜] {f : α → 𝕜}

@[fun_prop]
theorem Integrable.const_mul {f : α → 𝕜} (h : Integrable f μ) (c : 𝕜) :
    Integrable (fun x => c * f x) μ :=
  h.smul c

theorem Integrable.const_mul' {f : α → 𝕜} (h : Integrable f μ) (c : 𝕜) :
    Integrable ((fun _ : α => c) * f) μ :=
  Integrable.const_mul h c

@[fun_prop]
theorem Integrable.mul_const {f : α → 𝕜} (h : Integrable f μ) (c : 𝕜) :
    Integrable (fun x => f x * c) μ :=
  h.smul (MulOpposite.op c)

theorem Integrable.mul_const' {f : α → 𝕜} (h : Integrable f μ) (c : 𝕜) :
    Integrable (f * fun _ : α => c) μ :=
  Integrable.mul_const h c

theorem integrable_const_mul_iff {c : 𝕜} (hc : IsUnit c) (f : α → 𝕜) :
    Integrable (fun x => c * f x) μ ↔ Integrable f μ :=
  hc.integrable_smul_iff f

theorem integrable_mul_const_iff {c : 𝕜} (hc : IsUnit c) (f : α → 𝕜) :
    Integrable (fun x => f x * c) μ ↔ Integrable f μ :=
  hc.op.integrable_smul_iff f

theorem Integrable.bdd_mul' {f g : α → 𝕜} {c : ℝ} (hg : Integrable g μ)
    (hf : AEStronglyMeasurable f μ) (hf_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ c) :
    Integrable (fun x => f x * g x) μ := by
  refine Integrable.mono' (hg.norm.smul c) (hf.mul hg.1) ?_
  filter_upwards [hf_bound] with x hx
  rw [Pi.smul_apply, smul_eq_mul]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

theorem Integrable.mul_of_top_right {f : α → 𝕜} {φ : α → 𝕜} (hf : Integrable f μ)
    (hφ : MemLp φ ∞ μ) : Integrable (φ * f) μ :=
  hf.smul_of_top_right hφ

theorem Integrable.mul_of_top_left {f : α → 𝕜} {φ : α → 𝕜} (hφ : Integrable φ μ)
    (hf : MemLp f ∞ μ) : Integrable (φ * f) μ :=
  hφ.smul_of_top_left hf

lemma MemLp.integrable_mul {p q : ℝ≥0∞} {f g : α → 𝕜} (hf : MemLp f p μ) (hg : MemLp g q μ)
    [HolderTriple p q 1] :
    Integrable (f * g) μ :=
  memLp_one_iff_integrable.1 <| hg.mul hf

end NormedRing

section NormedDivisionRing

variable {𝕜 : Type*} [NormedDivisionRing 𝕜] {f : α → 𝕜}

@[fun_prop]
theorem Integrable.div_const {f : α → 𝕜} (h : Integrable f μ) (c : 𝕜) :
    Integrable (fun x => f x / c) μ := by simp_rw [div_eq_mul_inv, h.mul_const]

end NormedDivisionRing

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {f : α → 𝕜}

@[fun_prop]
theorem Integrable.ofReal {f : α → ℝ} (hf : Integrable f μ) :
    Integrable (fun x => (f x : 𝕜)) μ := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.ofReal

theorem Integrable.re_im_iff :
    Integrable (fun x => RCLike.re (f x)) μ ∧ Integrable (fun x => RCLike.im (f x)) μ ↔
      Integrable f μ := by
  simp_rw [← memLp_one_iff_integrable]
  exact memLp_re_im_iff

@[fun_prop]
theorem Integrable.re (hf : Integrable f μ) : Integrable (fun x => RCLike.re (f x)) μ := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.re

@[fun_prop]
theorem Integrable.im (hf : Integrable f μ) : Integrable (fun x => RCLike.im (f x)) μ := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.im

end RCLike

section Trim

variable {H : Type*} [NormedAddCommGroup H] {m0 : MeasurableSpace α} {μ' : Measure α} {f : α → H}

theorem Integrable.trim (hm : m ≤ m0) (hf_int : Integrable f μ') (hf : StronglyMeasurable[m] f) :
    Integrable f (μ'.trim hm) := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_trim hm _]
  · exact hf_int.2
  · fun_prop

theorem integrable_of_integrable_trim (hm : m ≤ m0) (hf_int : Integrable f (μ'.trim hm)) :
    Integrable f μ' := by
  obtain ⟨hf_meas_ae, hf⟩ := hf_int
  refine ⟨aestronglyMeasurable_of_aestronglyMeasurable_trim hm hf_meas_ae, ?_⟩
  simpa [HasFiniteIntegral, lintegral_trim_ae hm hf_meas_ae.enorm] using hf

end Trim

section SigmaFinite

variable {E : Type*} {m0 : MeasurableSpace α} [NormedAddCommGroup E]
  {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]

theorem integrable_of_forall_fin_meas_le' {μ : Measure α} (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (C : ℝ≥0∞) (hC : C < ∞) {f : α → ε} (hf_meas : AEStronglyMeasurable f μ)
    (hf : ∀ s, MeasurableSet[m] s → μ s ≠ ∞ → ∫⁻ x in s, ‖f x‖ₑ ∂μ ≤ C) : Integrable f μ :=
  ⟨hf_meas, (lintegral_le_of_forall_fin_meas_trim_le hm C hf).trans_lt hC⟩

theorem integrable_of_forall_fin_meas_le [SigmaFinite μ] (C : ℝ≥0∞) (hC : C < ∞) {f : α → ε}
    (hf_meas : AEStronglyMeasurable[m] f μ)
    (hf : ∀ s : Set α, MeasurableSet[m] s → μ s ≠ ∞ → ∫⁻ x in s, ‖f x‖ₑ ∂μ ≤ C) :
    Integrable f μ :=
  have : SigmaFinite (μ.trim le_rfl) := by rwa [@trim_eq_self _ m]
  integrable_of_forall_fin_meas_le' le_rfl C hC hf_meas hf

end SigmaFinite

section restrict

variable {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε] {f : α → ε}

/-- One should usually use `MeasureTheory.Integrable.integrableOn` instead. -/
lemma Integrable.restrict (hf : Integrable f μ) {s : Set α} : Integrable f (μ.restrict s) :=
  hf.mono_measure Measure.restrict_le_self

end restrict

end MeasureTheory

section ContinuousLinearMap

open MeasureTheory

variable {E H : Type*} [NormedAddCommGroup E] [NormedAddCommGroup H]
  {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedSpace 𝕜' E] [NormedSpace 𝕜 H]

variable {σ : 𝕜 →+* 𝕜'} {σ' : 𝕜' →+* 𝕜} [RingHomIsometric σ] [RingHomIsometric σ']
  [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

@[fun_prop]
theorem ContinuousLinearMap.integrable_comp {φ : α → H} (L : H →SL[σ] E) (φ_int : Integrable φ μ) :
    Integrable (fun a : α => L (φ a)) μ :=
  ((Integrable.norm φ_int).const_mul ‖L‖).mono'
    (by fun_prop)
    (Eventually.of_forall fun a => L.le_opNorm (φ a))

@[simp]
theorem ContinuousLinearEquiv.integrable_comp_iff {φ : α → H} (L : H ≃SL[σ] E) :
    Integrable (fun a : α ↦ L (φ a)) μ ↔ Integrable φ μ :=
  ⟨fun h ↦ by simpa using ContinuousLinearMap.integrable_comp (L.symm : E →SL[σ'] H) h,
  fun h ↦ ContinuousLinearMap.integrable_comp (L : H →SL[σ] E) h⟩

@[simp]
theorem LinearIsometryEquiv.integrable_comp_iff {φ : α → H} (L : H ≃ₛₗᵢ[σ] E) :
    Integrable (fun a : α ↦ L (φ a)) μ ↔ Integrable φ μ :=
  ContinuousLinearEquiv.integrable_comp_iff (L : H ≃SL[σ] E)

theorem MeasureTheory.Integrable.apply_continuousLinearMap {φ : α → H →SL[σ] E}
    (φ_int : Integrable φ μ) (v : H) : Integrable (fun a => φ a v) μ :=
  (ContinuousLinearMap.apply' E σ v).integrable_comp φ_int

end ContinuousLinearMap

namespace MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

@[fun_prop]
lemma Integrable.fst {f : α → E × F} (hf : Integrable f μ) : Integrable (fun x ↦ (f x).1) μ :=
  (ContinuousLinearMap.fst ℝ E F).integrable_comp hf

@[fun_prop]
lemma Integrable.snd {f : α → E × F} (hf : Integrable f μ) : Integrable (fun x ↦ (f x).2) μ :=
  (ContinuousLinearMap.snd ℝ E F).integrable_comp hf

lemma integrable_prod {f : α → E × F} :
    Integrable f μ ↔ Integrable (fun x ↦ (f x).1) μ ∧ Integrable (fun x ↦ (f x).2) μ :=
  ⟨fun h ↦ ⟨h.fst, h.snd⟩, fun h ↦ h.1.prodMk h.2⟩

section Limit

/-- If `G n` tends to `f` a.e. and each `‖G n ·‖ₑ` is `AEMeasurable`, then the lower Lebesgue
integral of `‖f ·‖ₑ` is at most the liminf of the lower Lebesgue integral of `‖G n ·‖ₑ`. -/
theorem lintegral_enorm_le_liminf_of_tendsto
    {G : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {μ : Measure ℝ}
    (hGf : ∀ᵐ x ∂μ, Tendsto (fun (n : ℕ) ↦ G n x) atTop (𝓝 (f x)))
    (hG : ∀ (n : ℕ), AEMeasurable (fun x ↦ ‖G n x‖ₑ) μ) :
    ∫⁻ x, ‖f x‖ₑ ∂μ ≤ liminf (fun n ↦ ∫⁻ x, ‖G n x‖ₑ ∂μ) atTop :=
  lintegral_congr_ae (by filter_upwards [hGf] with x hx using hx.enorm.liminf_eq) ▸
    (MeasureTheory.lintegral_liminf_le' hG)

/-- If `G n` tends to `f` a.e. and each `G n` is `AEStronglyMeasurable`, then the lower Lebesgue
integral of `‖f ·‖ₑ` is at most the liminf of the lower Lebesgue integral of `‖G n ·‖ₑ`. -/
theorem lintegral_enorm_le_liminf_of_tendsto'
    {G : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {μ : Measure ℝ}
    (hGf : ∀ᵐ x ∂μ, Tendsto (fun (n : ℕ) ↦ G n x) atTop (𝓝 (f x)))
    (hG : ∀ (n : ℕ), AEStronglyMeasurable (G n) μ) :
    ∫⁻ x, ‖f x‖ₑ ∂μ ≤ liminf (fun n ↦ ∫⁻ x, ‖G n x‖ₑ ∂μ) atTop :=
  lintegral_enorm_le_liminf_of_tendsto hGf (fun n ↦ (hG n).aemeasurable.enorm)

/-- If `G n` tends to `f` a.e., each `G n` is `AEStronglyMeasurable` and the liminf of the lower
Lebesgue integral of `‖G n ·‖ₑ` is finite, then `f` is Lebesgue integrable. -/
theorem integrable_of_tendsto
    {G : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {μ : Measure ℝ}
    (hGf : ∀ᵐ x ∂μ, Tendsto (fun (n : ℕ) ↦ G n x) atTop (𝓝 (f x)))
    (hG : ∀ (n : ℕ), AEStronglyMeasurable (G n) μ)
    (hG' : liminf (fun n ↦ ∫⁻ x, ‖G n x‖ₑ ∂μ) atTop ≠ ⊤) :
    Integrable f μ :=
  ⟨aestronglyMeasurable_of_tendsto_ae _ hG hGf,
   lt_of_le_of_lt (lintegral_enorm_le_liminf_of_tendsto' hGf hG) hG'.lt_top⟩

end Limit

end MeasureTheory
