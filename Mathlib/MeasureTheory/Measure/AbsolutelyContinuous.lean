/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.Measure.Map

/-!
# Absolute Continuity of Measures

We say that `μ` is absolutely continuous with respect to `ν`, or that `μ` is dominated by `ν`,
if `ν(A) = 0` implies that `μ(A) = 0`. We denote that by `μ ≪ ν`.

It is equivalent to an inequality of the almost everywhere filters of the measures:
`μ ≪ ν ↔ ae μ ≤ ae ν`.

## Main definitions

* `MeasureTheory.Measure.AbsolutelyContinuous μ ν`: `μ` is absolutely continuous with respect to `ν`

## Main statements

* `ae_le_iff_absolutelyContinuous`: `ae μ ≤ ae ν ↔ μ ≪ ν`

## Notation

* `μ ≪ ν`: `MeasureTheory.Measure.AbsolutelyContinuous μ ν`. That is: `μ` is absolutely continuous
  with respect to `ν`

-/

@[expose] public section

variable {α β δ ι R : Type*}

namespace MeasureTheory

open Set ENNReal NNReal

variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ μ₁ μ₂ μ₃ ν ν' : Measure α} {s t : Set α}

namespace Measure

/-- We say that `μ` is absolutely continuous with respect to `ν`, or that `μ` is dominated by `ν`,
  if `ν(A) = 0` implies that `μ(A) = 0`. -/
def AbsolutelyContinuous {_m0 : MeasurableSpace α} (μ ν : Measure α) : Prop :=
  ∀ ⦃s : Set α⦄, ν s = 0 → μ s = 0

@[inherit_doc MeasureTheory.Measure.AbsolutelyContinuous]
scoped[MeasureTheory] infixl:50 " ≪ " => MeasureTheory.Measure.AbsolutelyContinuous

theorem absolutelyContinuous_of_le (h : μ ≤ ν) : μ ≪ ν := fun s hs =>
  nonpos_iff_eq_zero.1 <| hs ▸ le_iff'.1 h s

alias _root_.LE.le.absolutelyContinuous := absolutelyContinuous_of_le

theorem absolutelyContinuous_of_eq (h : μ = ν) : μ ≪ ν :=
  h.le.absolutelyContinuous

alias _root_.Eq.absolutelyContinuous := absolutelyContinuous_of_eq

namespace AbsolutelyContinuous

theorem mk (h : ∀ ⦃s : Set α⦄, MeasurableSet s → ν s = 0 → μ s = 0) : μ ≪ ν := by
  intro s hs
  rcases exists_measurable_superset_of_null hs with ⟨t, h1t, h2t, h3t⟩
  exact measure_mono_null h1t (h h2t h3t)

@[refl]
protected theorem refl {_m0 : MeasurableSpace α} (μ : Measure α) : μ ≪ μ :=
  rfl.absolutelyContinuous

protected theorem rfl : μ ≪ μ := fun _s hs => hs

instance instRefl {_ : MeasurableSpace α} : @Std.Refl (Measure α) (· ≪ ·) :=
  ⟨fun _ => AbsolutelyContinuous.rfl⟩

@[simp]
protected lemma zero (μ : Measure α) : 0 ≪ μ := fun _ _ ↦ by simp

@[trans]
protected theorem trans (h1 : μ₁ ≪ μ₂) (h2 : μ₂ ≪ μ₃) : μ₁ ≪ μ₃ := fun _s hs => h1 <| h2 hs

@[mono]
protected theorem map (h : μ ≪ ν) {f : α → β} (hf : Measurable f) : μ.map f ≪ ν.map f :=
  AbsolutelyContinuous.mk fun s hs => by simpa [hf, hs] using @h _

protected theorem smul_left [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (h : μ ≪ ν) (c : R) :
    c • μ ≪ ν := fun s hνs => by
  simp only [h hνs, smul_apply, smul_zero, ← smul_one_smul ℝ≥0∞ c (0 : ℝ≥0∞)]

/-- If `μ ≪ ν`, then `c • μ ≪ c • ν`.

Earlier, this name was used for what's now called `AbsolutelyContinuous.smul_left`. -/
protected theorem smul [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (h : μ ≪ ν) (c : R) :
    c • μ ≪ c • ν := by
  intro s hνs
  rw [smul_apply, ← smul_one_smul ℝ≥0∞, smul_eq_mul, mul_eq_zero] at hνs ⊢
  exact hνs.imp_right fun hs ↦ h hs

protected lemma add (h1 : μ₁ ≪ ν) (h2 : μ₂ ≪ ν') : μ₁ + μ₂ ≪ ν + ν' := by
  intro s hs
  simp only [coe_add, Pi.add_apply, add_eq_zero] at hs ⊢
  exact ⟨h1 hs.1, h2 hs.2⟩

lemma add_left_iff {μ₁ μ₂ ν : Measure α} :
    μ₁ + μ₂ ≪ ν ↔ μ₁ ≪ ν ∧ μ₂ ≪ ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ (h.1.add h.2).trans ?_⟩
  · have : ∀ s, ν s = 0 → μ₁ s = 0 ∧ μ₂ s = 0 := by intro s hs0; simpa using h hs0
    exact ⟨fun s hs0 ↦ (this s hs0).1, fun s hs0 ↦ (this s hs0).2⟩
  · rw [← two_smul ℝ≥0]
    exact AbsolutelyContinuous.rfl.smul_left 2

lemma add_left {μ₁ μ₂ ν : Measure α} (h₁ : μ₁ ≪ ν) (h₂ : μ₂ ≪ ν) : μ₁ + μ₂ ≪ ν :=
  Measure.AbsolutelyContinuous.add_left_iff.mpr ⟨h₁, h₂⟩

lemma add_right (h1 : μ ≪ ν) (ν' : Measure α) : μ ≪ ν + ν' := by
  intro s hs
  simp only [coe_add, Pi.add_apply, add_eq_zero] at hs ⊢
  exact h1 hs.1

lemma null_mono {μ ν : Measure α} (hμν : μ ≪ ν) ⦃t : Set α⦄
    (ht : ν t = 0) : μ t = 0 :=
  hμν ht

lemma pos_mono {μ ν : Measure α} (hμν : μ ≪ ν) ⦃t : Set α⦄
    (ht : 0 < μ t) : 0 < ν t := by
  contrapose! ht
  simp_all [hμν.null_mono]

end AbsolutelyContinuous

@[simp]
lemma absolutelyContinuous_zero_iff : μ ≪ 0 ↔ μ = 0 :=
  ⟨fun h ↦ measure_univ_eq_zero.mp (h rfl), fun h ↦ h.symm ▸ AbsolutelyContinuous.zero _⟩

alias absolutelyContinuous_refl := AbsolutelyContinuous.refl
alias absolutelyContinuous_rfl := AbsolutelyContinuous.rfl

lemma absolutelyContinuous_sum_left {μs : ι → Measure α} (hμs : ∀ i, μs i ≪ ν) :
    Measure.sum μs ≪ ν :=
  AbsolutelyContinuous.mk fun s hs hs0 ↦ by simp [sum_apply _ hs, fun i ↦ hμs i hs0]

lemma absolutelyContinuous_sum_right {μs : ι → Measure α} (i : ι) (hνμ : ν ≪ μs i) :
    ν ≪ Measure.sum μs := by
  refine AbsolutelyContinuous.mk fun s hs hs0 ↦ ?_
  simp only [sum_apply _ hs, ENNReal.tsum_eq_zero] at hs0
  exact hνμ (hs0 i)

lemma smul_absolutelyContinuous {c : ℝ≥0∞} : c • μ ≪ μ := .smul_left .rfl _

theorem absolutelyContinuous_of_le_smul {μ' : Measure α} {c : ℝ≥0∞} (hμ'_le : μ' ≤ c • μ) :
    μ' ≪ μ :=
  (Measure.absolutelyContinuous_of_le hμ'_le).trans smul_absolutelyContinuous

lemma absolutelyContinuous_smul {c : ℝ≥0∞} (hc : c ≠ 0) : μ ≪ c • μ := by
  simp [AbsolutelyContinuous, hc]

theorem ae_le_iff_absolutelyContinuous : ae μ ≤ ae ν ↔ μ ≪ ν :=
  ⟨fun h s => by
    rw [measure_eq_zero_iff_ae_notMem, measure_eq_zero_iff_ae_notMem]
    exact fun hs => h hs, fun h _ hs => h hs⟩

alias ⟨_root_.LE.le.absolutelyContinuous_of_ae, AbsolutelyContinuous.ae_le⟩ :=
  ae_le_iff_absolutelyContinuous

alias ae_mono' := AbsolutelyContinuous.ae_le

theorem AbsolutelyContinuous.ae_eq (h : μ ≪ ν) {f g : α → δ} (h' : f =ᵐ[ν] g) : f =ᵐ[μ] g :=
  h.ae_le h'

end Measure

protected theorem AEDisjoint.of_absolutelyContinuous
    (h : AEDisjoint μ s t) {ν : Measure α} (h' : ν ≪ μ) :
    AEDisjoint ν s t := h' h

protected theorem AEDisjoint.of_le
    (h : AEDisjoint μ s t) {ν : Measure α} (h' : ν ≤ μ) :
    AEDisjoint ν s t :=
  h.of_absolutelyContinuous (Measure.absolutelyContinuous_of_le h')

@[gcongr, mono]
theorem ae_mono (h : μ ≤ ν) : ae μ ≤ ae ν :=
  h.absolutelyContinuous.ae_le

end MeasureTheory

namespace MeasurableEmbedding

open MeasureTheory Measure

variable {m0 : MeasurableSpace α} {m1 : MeasurableSpace β} {f : α → β} {μ ν : Measure α}

lemma absolutelyContinuous_map (hf : MeasurableEmbedding f) (hμν : μ ≪ ν) :
    μ.map f ≪ ν.map f := by
  intro t ht
  rw [hf.map_apply] at ht ⊢
  exact hμν ht

end MeasurableEmbedding
