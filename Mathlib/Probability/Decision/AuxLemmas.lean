/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Posterior

/-!
# AuxLemmas
-/

open MeasureTheory
open scoped ENNReal NNReal

lemma ENNReal.add_sub_add_eq_sub_right {a c b : ℝ≥0∞} (hc : c ≠ ∞) :
    (a + c) - (b + c) = a - b := by
  lift c to ℝ≥0 using hc
  cases a <;> cases b
  · simp
  · simp
  · simp
  · norm_cast
    rw [add_tsub_add_eq_tsub_right]

lemma ENNReal.add_sub_add_eq_sub_left {a c b : ℝ≥0∞} (hc : c ≠ ∞) :
    (c + a) - (c + b) = a - b := by
  simp_rw [add_comm c]
  exact ENNReal.add_sub_add_eq_sub_right hc

lemma ENNReal.mul_min (a b c : ℝ≥0∞) : a * min b c = min (a * b) (a * c) := mul_left_mono.map_min

lemma iInf_mul_le_lintegral {α : Type*} {_ : MeasurableSpace α} (μ : Measure α) (f : α → ℝ≥0∞) :
    (⨅ x, f x) * μ .univ ≤ ∫⁻ x, f x ∂μ := by
  have : (⨅ x, f x) * μ .univ = ∫⁻ y, ⨅ x, f x ∂μ := by simp
  rw [this]
  gcongr
  exact iInf_le _ _

lemma iInf_le_lintegral {α : Type*} {_ : MeasurableSpace α} (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ≥0∞) :
    ⨅ x, f x ≤ ∫⁻ x, f x ∂μ :=
  le_trans (by simp) (iInf_mul_le_lintegral μ f)

lemma lintegral_le_iSup {α : Type*} {_ : MeasurableSpace α} (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ ≤ ⨆ x, f x := sorry

-- from BrownianMotion
theorem Set.Finite.lt_iInf_iff {α ι : Type*} [CompleteLinearOrder α]
    {s : Set ι} {f : ι → α} (h : s.Nonempty) (hs : s.Finite) {a : α} :
    a < ⨅ i ∈ s, f i ↔ ∀ x ∈ s, a < f x := sorry

lemma iInf_eq_bot_iff_of_finite {α ι : Type*} [CompleteLinearOrder α] [Finite ι] [Nonempty ι]
    {f : ι → α} : (⨅ i, f i) = ⊥ ↔ ∃ i, f i = ⊥ := by
  refine ⟨fun h ↦ ?_, fun ⟨i, hi⟩ ↦ le_antisymm ((iInf_le _ i).trans_eq hi) bot_le⟩
  by_contra! h'
  simp_rw [← bot_lt_iff_ne_bot] at h'
  have h'' : ∀ i ∈ (Set.univ : Set ι), ⊥ < f i := by simpa
  rw [← Set.Finite.lt_iInf_iff (by simp) Set.finite_univ] at h''
  simp only [Set.mem_univ, iInf_pos] at h''
  exact h''.ne' h

lemma _root_.Measurable.smul_measure {α β : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    {f : α → ℝ≥0∞}
    (hf : Measurable f) (μ : Measure β) :
    Measurable (fun x ↦ f x • μ) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  fun_prop

instance {α : Type*} [MeasurableSpace α] [Countable α] [DiscreteMeasurableSpace α]
    {μ : Measure α} : SFinite μ := by
  rw [← Measure.sum_smul_dirac μ]
  infer_instance

namespace ProbabilityTheory

@[simp]
lemma Kernel.comp_const {α β γ : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    {_ : MeasurableSpace γ}
    (κ : Kernel β γ) (μ : Measure β) : κ ∘ₖ Kernel.const α μ = Kernel.const α (κ ∘ₘ μ) := by
  ext x s hs
  rw [Kernel.comp_apply, Measure.bind_apply hs (by fun_prop), Kernel.const_apply,
    Kernel.const_apply, Measure.bind_apply hs (by fun_prop)]

@[simp]
lemma Kernel.comp_discard' {α β : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    (κ : Kernel α β) :
    discard β ∘ₖ κ =
      { toFun a := κ a .univ • Measure.dirac ()
        measurable' := (κ.measurable_coe .univ).smul_measure _ } := by
  ext a s hs
  simp [comp_apply' _ _ _ hs, mul_comm]

@[simp]
lemma _root_.MeasureTheory.Measure.discard_comp {α : Type*} {_ : MeasurableSpace α}
    (μ : Measure α) :
    (Kernel.discard α) ∘ₘ μ = μ .univ • (Measure.dirac ()) := by
  ext s hs; simp [Measure.bind_apply hs (Kernel.aemeasurable _), mul_comm]

variable {Θ Θ' 𝓧 𝓧' 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {mΘ' : MeasurableSpace Θ'}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓧' : MeasurableSpace 𝓧'} {m𝓨 : MeasurableSpace 𝓨}
  {ℓ : Θ → 𝓨 → ℝ≥0∞} {P : Kernel Θ 𝓧} {κ : Kernel 𝓧 𝓨} {π : Measure Θ}

instance [Nonempty 𝓨] : Nonempty (Subtype (@IsMarkovKernel 𝓧 𝓨 m𝓧 m𝓨)) := by
  simp only [nonempty_subtype]
  let y : 𝓨 := Classical.ofNonempty
  exact ⟨Kernel.const _ (Measure.dirac y), inferInstance⟩

end ProbabilityTheory

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

lemma Measure.eq_of_le_of_measure_univ_eq [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≤ ν) (h_univ : μ .univ = ν .univ) : μ = ν := by
  ext s hs
  refine le_antisymm (hμν s) ?_
  by_contra! h_lt
  have : Set.univ = s ∪ sᶜ := by simp
  have h_disj : Disjoint s sᶜ := Set.disjoint_compl_right_iff_subset.mpr subset_rfl
  replace h_univ : ν .univ ≤ μ .univ := h_univ.symm.le
  rw [this, measure_union h_disj hs.compl, measure_union h_disj hs.compl] at h_univ
  refine absurd h_univ ?_
  push_neg
  refine ENNReal.add_lt_add_of_lt_of_le (by finiteness) h_lt (hμν sᶜ)

lemma Measure.eq_of_le_of_isProbabilityMeasure [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≤ ν) : μ = ν :=
  eq_of_le_of_measure_univ_eq hμν (by simp)

lemma isFiniteMeasure_smul {c : ℝ≥0∞} (hc : c ≠ ∞) (μ : Measure α) [IsFiniteMeasure μ] :
    IsFiniteMeasure (c • μ) := by
  lift c to ℝ≥0 using hc
  have : (c : ℝ≥0∞) • μ = c • μ := rfl
  rw [this]
  infer_instance

end MeasureTheory

namespace MeasurableEmbedding
-- PRed by Gaëtan

open Set
variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α → β}

lemma equivRange_apply (hf : MeasurableEmbedding f) (x : α) :
    hf.equivRange x = ⟨f x, mem_range_self x⟩ := by
  suffices f x = (hf.equivRange x).1 by simp [this]
  simp [MeasurableEmbedding.equivRange, MeasurableEquiv.cast, MeasurableEquiv.Set.univ,
    MeasurableEmbedding.equivImage]

lemma equivRange_symm_apply_mk (hf : MeasurableEmbedding f) (x : α) :
    hf.equivRange.symm ⟨f x, mem_range_self x⟩ = x := by
  have : x = hf.equivRange.symm (hf.equivRange x) := EquivLike.inv_apply_eq.mp rfl
  conv_rhs => rw [this, hf.equivRange_apply]

/-- The left-inverse of a MeasurableEmbedding -/
protected noncomputable
def invFun [Nonempty α] (hf : MeasurableEmbedding f) [∀ x, Decidable (x ∈ range f)] (x : β) : α :=
  if hx : x ∈ range f then hf.equivRange.symm ⟨x, hx⟩ else (Nonempty.some inferInstance)

@[fun_prop]
lemma measurable_invFun [Nonempty α] [∀ x, Decidable (x ∈ range f)]
    (hf : MeasurableEmbedding f) :
    Measurable (hf.invFun : β → α) :=
  Measurable.dite (by fun_prop) measurable_const hf.measurableSet_range

lemma leftInverse_invFun [Nonempty α] [∀ x, Decidable (x ∈ range f)]
    (hf : MeasurableEmbedding f) :
    Function.LeftInverse hf.invFun f := by
  intro x
  simp only [MeasurableEmbedding.invFun, mem_range, exists_apply_eq_apply, ↓reduceDIte]
  exact hf.equivRange_symm_apply_mk x

end MeasurableEmbedding

lemma measurable_encode {α : Type*} {_ : MeasurableSpace α} [Encodable α]
    [MeasurableSingletonClass α] :
    Measurable (Encodable.encode (α := α)) := by
  refine measurable_to_nat fun a ↦ ?_
  have : Encodable.encode ⁻¹' {Encodable.encode a} = {a} := by ext; simp
  rw [this]
  exact measurableSet_singleton _

lemma measurableEmbedding_encode (α : Type*) {_ : MeasurableSpace α} [Encodable α]
    [MeasurableSingletonClass α] :
    MeasurableEmbedding (Encodable.encode (α := α)) where
  injective := Encodable.encode_injective
  measurable := measurable_encode
  measurableSet_image' _ _ := .of_discrete
