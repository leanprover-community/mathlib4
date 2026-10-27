/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.Measure.OuterMeasure

/-!
# The `ℝ≥0∞`-module of measures

This file provides an `ℝ≥0∞`-module structure on the space of measures.

## Tags

measure, module
-/

@[expose] public section

open Set Function
open scoped NNReal ENNReal

namespace MeasureTheory.Measure

variable {α ι R R' : Type*} {mα : MeasurableSpace α}
  {μ ν : Measure α} {s t : Set α} {c : ℝ≥0∞}

instance : Zero (Measure α) :=
  ⟨{  toOuterMeasure := 0
      m_iUnion := fun _f _hf _hd => tsum_zero.symm
      trim_le := OuterMeasure.trim_zero.le }⟩

@[simp]
theorem zero_toOuterMeasure : (0 : Measure α).toOuterMeasure = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_zero : ⇑(0 : Measure α) = 0 :=
  rfl

variable [mα] in
@[simp] lemma _root_.MeasureTheory.OuterMeasure.toMeasure_zero
    (h : mα ≤ (0 : OuterMeasure α).caratheodory) :
    (0 : OuterMeasure α).toMeasure h = 0 := by
  ext s hs
  simp [hs]

@[simp] lemma _root_.MeasureTheory.OuterMeasure.toMeasure_eq_zero
    {μ : OuterMeasure α} (h : mα ≤ μ.caratheodory) : μ.toMeasure h = 0 ↔ μ = 0 where
  mp hμ := by ext s; exact le_bot_iff.1 <| (le_toMeasure_apply _ _ _).trans_eq congr($hμ s)
  mpr := by rintro rfl; simp

@[nontriviality]
lemma apply_eq_zero_of_isEmpty [IsEmpty α] (μ : Measure α) (s : Set α) :
    μ s = 0 := by
  rw [eq_empty_of_isEmpty s, measure_empty]

instance [IsEmpty α] : Subsingleton (Measure α) :=
  ⟨fun μ ν => by ext1 s _; rw [apply_eq_zero_of_isEmpty, apply_eq_zero_of_isEmpty]⟩

theorem eq_zero_of_isEmpty [IsEmpty α] (μ : Measure α) : μ = 0 :=
  Subsingleton.elim μ 0

@[simp]
theorem ofMeasurable_zero : ofMeasurable (α := α) (fun _ _ => 0) rfl (by simp) = 0 := by
  ext s
  simp [ofMeasurable, ← toOuterMeasure_apply, inducedOuterMeasure_zero MeasurableSet.iUnion]

instance : Inhabited (Measure α) :=
  ⟨0⟩

instance : Add (Measure α) :=
  ⟨fun μ₁ μ₂ =>
    { toOuterMeasure := μ₁.toOuterMeasure + μ₂.toOuterMeasure
      m_iUnion := fun s hs hd =>
        show μ₁ (⋃ i, s i) + μ₂ (⋃ i, s i) = ∑' i, (μ₁ (s i) + μ₂ (s i)) by
          rw [ENNReal.tsum_add, measure_iUnion hd hs, measure_iUnion hd hs]
      trim_le := by rw [OuterMeasure.trim_add, μ₁.trimmed, μ₂.trimmed] }⟩

@[simp]
theorem add_toOuterMeasure (μ₁ μ₂ : Measure α) :
    (μ₁ + μ₂).toOuterMeasure = μ₁.toOuterMeasure + μ₂.toOuterMeasure :=
  rfl

@[simp, norm_cast]
theorem coe_add (μ₁ μ₂ : Measure α) : ⇑(μ₁ + μ₂) = μ₁ + μ₂ :=
  rfl

theorem add_apply (μ₁ μ₂ : Measure α) (s : Set α) :
    (μ₁ + μ₂) s = μ₁ s + μ₂ s :=
  rfl

section SMul

variable [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] [SMul R' ℝ≥0∞] [IsScalarTower R' ℝ≥0∞ ℝ≥0∞]

instance : SMul R (Measure α) :=
  ⟨fun c μ =>
    { toOuterMeasure := c • μ.toOuterMeasure
      m_iUnion := fun s hs hd => by
        simp only [smul_apply, coe_toOuterMeasure, ENNReal.tsum_const_smul,
          measure_iUnion hd hs]
      trim_le := by rw [OuterMeasure.trim_smul, μ.trimmed] }⟩

@[simp]
theorem smul_toOuterMeasure (c : R) (μ : Measure α) :
    (c • μ).toOuterMeasure = c • μ.toOuterMeasure :=
  rfl

@[simp, norm_cast]
theorem coe_smul (c : R) (μ : Measure α) : ⇑(c • μ) = c • ⇑μ :=
  rfl

@[simp]
lemma coe_nnreal_smul (c : ℝ≥0) (μ : Measure α) : (c : ℝ≥0∞) • μ = c • μ := rfl

@[simp]
theorem smul_apply (c : R) (μ : Measure α) (s : Set α) :
    (c • μ) s = c • μ s :=
  rfl

instance [SMulCommClass R R' ℝ≥0∞] :
    SMulCommClass R R' (Measure α) :=
  ⟨fun _ _ _ => ext fun _ _ => smul_comm _ _ _⟩

instance [SMul R R'] [IsScalarTower R R' ℝ≥0∞] :
    IsScalarTower R R' (Measure α) :=
  ⟨fun _ _ _ => ext fun _ _ => smul_assoc _ _ _⟩

instance [SMul Rᵐᵒᵖ ℝ≥0∞] [IsCentralScalar R ℝ≥0∞] :
    IsCentralScalar R (Measure α) :=
  ⟨fun _ _ => ext fun _ _ => op_smul_eq_smul _ _⟩

end SMul

instance [Monoid R] [MulAction R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] : MulAction R (Measure α) :=
  Injective.mulAction _ toOuterMeasure_injective smul_toOuterMeasure

instance : AddCommMonoid (Measure α) :=
  toOuterMeasure_injective.addCommMonoid toOuterMeasure zero_toOuterMeasure add_toOuterMeasure
    fun _ _ => smul_toOuterMeasure _ _

/-- Coercion to function as an additive monoid homomorphism. -/
def coeAddHom : Measure α →+ Set α → ℝ≥0∞ where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]
theorem coeAddHom_apply (μ : Measure α) : coeAddHom μ = ⇑μ := rfl

@[simp]
theorem coe_finsetSum (I : Finset ι) (μ : ι → Measure α) :
    ⇑(∑ i ∈ I, μ i) = ∑ i ∈ I, ⇑(μ i) := map_sum coeAddHom μ I

@[deprecated (since := "2026-04-08")] alias coe_finset_sum := coe_finsetSum

theorem finsetSum_apply (I : Finset ι) (μ : ι → Measure α) (s : Set α) :
    (∑ i ∈ I, μ i) s = ∑ i ∈ I, μ i s := by rw [coe_finsetSum, Finset.sum_apply]

@[deprecated (since := "2026-04-08")] alias finset_sum_apply := finsetSum_apply

instance [Monoid R] [DistribMulAction R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] :
    DistribMulAction R (Measure α) :=
  Injective.distribMulAction ⟨⟨toOuterMeasure, zero_toOuterMeasure⟩, add_toOuterMeasure⟩
    toOuterMeasure_injective smul_toOuterMeasure

instance [Semiring R] [Module R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] : Module R (Measure α) :=
  Injective.module R ⟨⟨toOuterMeasure, zero_toOuterMeasure⟩, add_toOuterMeasure⟩
    toOuterMeasure_injective smul_toOuterMeasure

instance [Semiring R] [Module R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    [Module.IsTorsionFree R ℝ≥0∞] : Module.IsTorsionFree R (Measure α) :=
  DFunLike.coe_injective.moduleIsTorsionFree _ (by simp)

@[simp] lemma ennreal_smul_eq_zero : c • μ = 0 ↔ c = 0 ∨ μ = 0 := by
  simp [Measure.ext_iff', forall_or_left]

@[simp]
theorem coe_nnreal_smul_apply (c : ℝ≥0) (μ : Measure α) (s : Set α) :
    (c • μ) s = c * μ s :=
  rfl

@[simp]
theorem nnreal_smul_coe_apply (c : ℝ≥0) (μ : Measure α) (s : Set α) :
    c • μ s = c * μ s :=
  rfl

theorem ae_smul_measure {p : α → Prop} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (h : ∀ᵐ x ∂μ, p x) (c : R) : ∀ᵐ x ∂c • μ, p x :=
  ae_iff.2 <| by rw [smul_apply, ae_iff.1 h, ← smul_one_smul ℝ≥0∞, smul_zero]

theorem ae_smul_measure_le [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (c : R) :
    ae (c • μ) ≤ ae μ := fun _ h ↦ ae_smul_measure h c

lemma ae_ennreal_smul_measure_iff {p : α → Prop} (hc : c ≠ 0) :
    (∀ᵐ x ∂c • μ, p x) ↔ ∀ᵐ x ∂μ, p x := by simp [ae_iff, hc]

@[simp] lemma ae_ennreal_smul_measure_eq (hc : c ≠ 0) (μ : Measure α) :
    ae (c • μ) = ae μ := by ext; exact ae_ennreal_smul_measure_iff hc

lemma ae_smul_measure_iff [Semiring R] [IsDomain R] [Module R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    [Module.IsTorsionFree R ℝ≥0∞] {c : R} {p : α → Prop} (hc : c ≠ 0) :
    (∀ᵐ x ∂c • μ, p x) ↔ ∀ᵐ x ∂μ, p x := by
  simp [ae_iff, hc]

@[simp] lemma ae_smul_measure_eq [Semiring R] [IsDomain R] [Module R ℝ≥0∞]
    [IsScalarTower R ℝ≥0∞ ℝ≥0∞] [Module.IsTorsionFree R ℝ≥0∞] {c : R} (hc : c ≠ 0) (μ : Measure α) :
    ae (c • μ) = ae μ := by
  ext; exact ae_smul_measure_iff hc

theorem measure_eq_left_of_subset_of_measure_add_eq (h : (μ + ν) t ≠ ∞) (h' : s ⊆ t)
    (h'' : (μ + ν) s = (μ + ν) t) : μ s = μ t := by
  refine le_antisymm (measure_mono h') ?_
  have : μ t + ν t ≤ μ s + ν t :=
    calc
      μ t + ν t = μ s + ν s := h''.symm
      _ ≤ μ s + ν t := by gcongr
  apply ENNReal.le_of_add_le_add_right _ this
  exact ne_top_of_le_ne_top h (le_add_left le_rfl)

theorem measure_eq_right_of_subset_of_measure_add_eq (h : (μ + ν) t ≠ ∞) (h' : s ⊆ t)
    (h'' : (μ + ν) s = (μ + ν) t) : ν s = ν t := by
  rw [add_comm] at h'' h
  exact measure_eq_left_of_subset_of_measure_add_eq h h' h''

theorem measure_toMeasurable_add_inter_left (hs : MeasurableSet s) (ht : (μ + ν) t ≠ ∞) :
    μ (toMeasurable (μ + ν) t ∩ s) = μ (t ∩ s) := by
  refine (measure_inter_eq_of_measure_eq hs ?_ (subset_toMeasurable _ _) ?_).symm
  · refine
      measure_eq_left_of_subset_of_measure_add_eq ?_ (subset_toMeasurable _ _)
        (measure_toMeasurable t).symm
    rwa [measure_toMeasurable t]
  · simp only [not_or, ENNReal.add_eq_top, Pi.add_apply, Ne, coe_add] at ht
    exact ht.1

theorem measure_toMeasurable_add_inter_right (hs : MeasurableSet s) (ht : (μ + ν) t ≠ ∞) :
    ν (toMeasurable (μ + ν) t ∩ s) = ν (t ∩ s) := by
  rw [add_comm] at ht ⊢
  exact measure_toMeasurable_add_inter_left hs ht

end MeasureTheory.Measure
