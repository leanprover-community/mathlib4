/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# The `ℝ≥0∞`-module of measures

We define addition of measures, and scalar multiplication with `ℝ≥0∞`.

## References

* <https://en.wikipedia.org/wiki/Measure_(mathematics)>
* <https://en.wikipedia.org/wiki/Complete_measure>
* <https://en.wikipedia.org/wiki/Almost_everywhere>

## Tags

measure, almost everywhere, measure space, completion, null set, null measurable set
-/

@[expose] public section

noncomputable section

open Set Function ENNReal NNReal

variable {α β γ ι R R' : Type*}

namespace MeasureTheory

variable {m0 : MeasurableSpace α} {mβ : MeasurableSpace β} [MeasurableSpace γ]
variable {μ μ₁ μ₂ ν ν' : Measure α} {s t : Set α}

namespace Measure

instance instZero {_ : MeasurableSpace α} : Zero (Measure α) :=
  ⟨{  toOuterMeasure := 0
      m_iUnion := fun _f _hf _hd => tsum_zero.symm
      trim_le := OuterMeasure.trim_zero.le }⟩

@[simp]
theorem zero_toOuterMeasure {_m : MeasurableSpace α} : (0 : Measure α).toOuterMeasure = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_zero {_m : MeasurableSpace α} : ⇑(0 : Measure α) = 0 :=
  rfl

@[simp] lemma _root_.MeasureTheory.OuterMeasure.toMeasure_zero
    [ms : MeasurableSpace α] (h : ms ≤ (0 : OuterMeasure α).caratheodory) :
    (0 : OuterMeasure α).toMeasure h = 0 := by
  ext s hs
  simp [hs]

@[simp] lemma _root_.MeasureTheory.OuterMeasure.toMeasure_eq_zero {ms : MeasurableSpace α}
    {μ : OuterMeasure α} (h : ms ≤ μ.caratheodory) : μ.toMeasure h = 0 ↔ μ = 0 where
  mp hμ := by ext s; exact le_bot_iff.1 <| (le_toMeasure_apply _ _ _).trans_eq congr($hμ s)
  mpr := by rintro rfl; simp

@[nontriviality]
lemma apply_eq_zero_of_isEmpty [IsEmpty α] {_ : MeasurableSpace α} (μ : Measure α) (s : Set α) :
    μ s = 0 := by
  rw [eq_empty_of_isEmpty s, measure_empty]

instance instSubsingleton [IsEmpty α] {m : MeasurableSpace α} : Subsingleton (Measure α) :=
  ⟨fun μ ν => by ext1 s _; rw [apply_eq_zero_of_isEmpty, apply_eq_zero_of_isEmpty]⟩

theorem eq_zero_of_isEmpty [IsEmpty α] {_m : MeasurableSpace α} (μ : Measure α) : μ = 0 :=
  Subsingleton.elim μ 0

@[simp]
theorem ofMeasurable_zero : ofMeasurable (α := α) (fun _ _ => 0) rfl (by simp) = 0 := by
  ext s
  simp [ofMeasurable, ← toOuterMeasure_apply, inducedOuterMeasure_zero MeasurableSet.iUnion]

instance instInhabited {_ : MeasurableSpace α} : Inhabited (Measure α) :=
  ⟨0⟩

instance instAdd {_ : MeasurableSpace α} : Add (Measure α) :=
  ⟨fun μ₁ μ₂ =>
    { toOuterMeasure := μ₁.toOuterMeasure + μ₂.toOuterMeasure
      m_iUnion := fun s hs hd =>
        show μ₁ (⋃ i, s i) + μ₂ (⋃ i, s i) = ∑' i, (μ₁ (s i) + μ₂ (s i)) by
          rw [ENNReal.tsum_add, measure_iUnion hd hs, measure_iUnion hd hs]
      trim_le := by rw [OuterMeasure.trim_add, μ₁.trimmed, μ₂.trimmed] }⟩

@[simp]
theorem add_toOuterMeasure {_m : MeasurableSpace α} (μ₁ μ₂ : Measure α) :
    (μ₁ + μ₂).toOuterMeasure = μ₁.toOuterMeasure + μ₂.toOuterMeasure :=
  rfl

@[simp, norm_cast]
theorem coe_add {_m : MeasurableSpace α} (μ₁ μ₂ : Measure α) : ⇑(μ₁ + μ₂) = μ₁ + μ₂ :=
  rfl

theorem add_apply {_m : MeasurableSpace α} (μ₁ μ₂ : Measure α) (s : Set α) :
    (μ₁ + μ₂) s = μ₁ s + μ₂ s :=
  rfl

section SMul

variable [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
variable [SMul R' ℝ≥0∞] [IsScalarTower R' ℝ≥0∞ ℝ≥0∞]

instance instSMul {_ : MeasurableSpace α} : SMul R (Measure α) :=
  ⟨fun c μ =>
    { toOuterMeasure := c • μ.toOuterMeasure
      m_iUnion := fun s hs hd => by
        simp only [smul_apply, coe_toOuterMeasure, ENNReal.tsum_const_smul,
          measure_iUnion hd hs]
      trim_le := by rw [OuterMeasure.trim_smul, μ.trimmed] }⟩

@[simp]
theorem smul_toOuterMeasure {_m : MeasurableSpace α} (c : R) (μ : Measure α) :
    (c • μ).toOuterMeasure = c • μ.toOuterMeasure :=
  rfl

@[simp, norm_cast]
theorem coe_smul {_m : MeasurableSpace α} (c : R) (μ : Measure α) : ⇑(c • μ) = c • ⇑μ :=
  rfl

@[simp]
lemma coe_nnreal_smul (c : ℝ≥0) (μ : Measure α) : (c : ℝ≥0∞) • μ = c • μ := rfl

@[simp]
theorem smul_apply {_m : MeasurableSpace α} (c : R) (μ : Measure α) (s : Set α) :
    (c • μ) s = c • μ s :=
  rfl

instance instSMulCommClass [SMulCommClass R R' ℝ≥0∞] {_ : MeasurableSpace α} :
    SMulCommClass R R' (Measure α) :=
  ⟨fun _ _ _ => ext fun _ _ => smul_comm _ _ _⟩

instance instIsScalarTower [SMul R R'] [IsScalarTower R R' ℝ≥0∞] {_ : MeasurableSpace α} :
    IsScalarTower R R' (Measure α) :=
  ⟨fun _ _ _ => ext fun _ _ => smul_assoc _ _ _⟩

instance instIsCentralScalar [SMul Rᵐᵒᵖ ℝ≥0∞] [IsCentralScalar R ℝ≥0∞] {_ : MeasurableSpace α} :
    IsCentralScalar R (Measure α) :=
  ⟨fun _ _ => ext fun _ _ => op_smul_eq_smul _ _⟩

end SMul

instance instMulAction [Monoid R] [MulAction R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    {_ : MeasurableSpace α} : MulAction R (Measure α) :=
  Injective.mulAction _ toOuterMeasure_injective smul_toOuterMeasure

instance instAddCommMonoid {_ : MeasurableSpace α} : AddCommMonoid (Measure α) :=
  toOuterMeasure_injective.addCommMonoid toOuterMeasure zero_toOuterMeasure add_toOuterMeasure
    fun _ _ => smul_toOuterMeasure _ _

/-- Coercion to function as an additive monoid homomorphism. -/
def coeAddHom {_ : MeasurableSpace α} : Measure α →+ Set α → ℝ≥0∞ where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]
theorem coeAddHom_apply {_ : MeasurableSpace α} (μ : Measure α) : coeAddHom μ = ⇑μ := rfl

@[simp]
theorem coe_finsetSum {_m : MeasurableSpace α} (I : Finset ι) (μ : ι → Measure α) :
    ⇑(∑ i ∈ I, μ i) = ∑ i ∈ I, ⇑(μ i) := map_sum coeAddHom μ I

@[deprecated (since := "2026-04-08")] alias coe_finset_sum := coe_finsetSum

theorem finsetSum_apply {m : MeasurableSpace α} (I : Finset ι) (μ : ι → Measure α) (s : Set α) :
    (∑ i ∈ I, μ i) s = ∑ i ∈ I, μ i s := by rw [coe_finsetSum, Finset.sum_apply]

@[deprecated (since := "2026-04-08")] alias finset_sum_apply := finsetSum_apply

instance instDistribMulAction [Monoid R] [DistribMulAction R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    {_ : MeasurableSpace α} : DistribMulAction R (Measure α) :=
  Injective.distribMulAction ⟨⟨toOuterMeasure, zero_toOuterMeasure⟩, add_toOuterMeasure⟩
    toOuterMeasure_injective smul_toOuterMeasure

instance instModule [Semiring R] [Module R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    {_ : MeasurableSpace α} : Module R (Measure α) :=
  Injective.module R ⟨⟨toOuterMeasure, zero_toOuterMeasure⟩, add_toOuterMeasure⟩
    toOuterMeasure_injective smul_toOuterMeasure

instance instModuleIsTorsionFree [Semiring R] [Module R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    [Module.IsTorsionFree R ℝ≥0∞] : Module.IsTorsionFree R (Measure α) :=
  DFunLike.coe_injective.moduleIsTorsionFree _ (by simp)

@[simp] lemma ennreal_smul_eq_zero {c : ℝ≥0∞} {μ : Measure α} : c • μ = 0 ↔ c = 0 ∨ μ = 0 := by
  simp [Measure.ext_iff', forall_or_left]

@[simp]
theorem coe_nnreal_smul_apply {_m : MeasurableSpace α} (c : ℝ≥0) (μ : Measure α) (s : Set α) :
    (c • μ) s = c * μ s :=
  rfl

@[simp]
theorem nnreal_smul_coe_apply {_m : MeasurableSpace α} (c : ℝ≥0) (μ : Measure α) (s : Set α) :
    c • μ s = c * μ s :=
  rfl

theorem ae_smul_measure {p : α → Prop} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (h : ∀ᵐ x ∂μ, p x) (c : R) : ∀ᵐ x ∂c • μ, p x :=
  ae_iff.2 <| by rw [smul_apply, ae_iff.1 h, ← smul_one_smul ℝ≥0∞, smul_zero]

theorem ae_smul_measure_le [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (c : R) :
    ae (c • μ) ≤ ae μ := fun _ h ↦ ae_smul_measure h c

section Module

variable {R : Type*} [Semiring R] [IsDomain R] [Module R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
  [Module.IsTorsionFree R ℝ≥0∞] {c : R} {p : α → Prop}

lemma ae_smul_measure_iff (hc : c ≠ 0) {μ : Measure α} : (∀ᵐ x ∂c • μ, p x) ↔ ∀ᵐ x ∂μ, p x := by
  simp [ae_iff, hc]

@[simp] lemma ae_smul_measure_eq (hc : c ≠ 0) (μ : Measure α) : ae (c • μ) = ae μ := by
  ext; exact ae_smul_measure_iff hc

end Module

lemma ae_ennreal_smul_measure_iff {c : ℝ≥0∞} {p : α → Prop} (hc : c ≠ 0) {μ : Measure α} :
    (∀ᵐ x ∂c • μ, p x) ↔ ∀ᵐ x ∂μ, p x := by simp [ae_iff, hc]

@[simp] lemma ae_ennreal_smul_measure_eq {c : ℝ≥0∞} (hc : c ≠ 0) (μ : Measure α) :
    ae (c • μ) = ae μ := by ext; exact ae_ennreal_smul_measure_iff hc

theorem measure_eq_left_of_subset_of_measure_add_eq {s t : Set α} (h : (μ + ν) t ≠ ∞) (h' : s ⊆ t)
    (h'' : (μ + ν) s = (μ + ν) t) : μ s = μ t := by
  refine le_antisymm (measure_mono h') ?_
  have : μ t + ν t ≤ μ s + ν t :=
    calc
      μ t + ν t = μ s + ν s := h''.symm
      _ ≤ μ s + ν t := by gcongr
  apply ENNReal.le_of_add_le_add_right _ this
  exact ne_top_of_le_ne_top h (le_add_left le_rfl)

theorem measure_eq_right_of_subset_of_measure_add_eq {s t : Set α} (h : (μ + ν) t ≠ ∞) (h' : s ⊆ t)
    (h'' : (μ + ν) s = (μ + ν) t) : ν s = ν t := by
  rw [add_comm] at h'' h
  exact measure_eq_left_of_subset_of_measure_add_eq h h' h''

theorem measure_toMeasurable_add_inter_left {s t : Set α} (hs : MeasurableSet s)
    (ht : (μ + ν) t ≠ ∞) : μ (toMeasurable (μ + ν) t ∩ s) = μ (t ∩ s) := by
  refine (measure_inter_eq_of_measure_eq hs ?_ (subset_toMeasurable _ _) ?_).symm
  · refine
      measure_eq_left_of_subset_of_measure_add_eq ?_ (subset_toMeasurable _ _)
        (measure_toMeasurable t).symm
    rwa [measure_toMeasurable t]
  · simp only [not_or, ENNReal.add_eq_top, Pi.add_apply, Ne, coe_add] at ht
    exact ht.1

theorem measure_toMeasurable_add_inter_right {s t : Set α} (hs : MeasurableSet s)
    (ht : (μ + ν) t ≠ ∞) : ν (toMeasurable (μ + ν) t ∩ s) = ν (t ∩ s) := by
  rw [add_comm] at ht ⊢
  exact measure_toMeasurable_add_inter_left hs ht

theorem measure_support_eq_zero_iff {E : Type*} [Zero E] (μ : Measure α := by volume_tac)
    {f : α → E} : μ f.support = 0 ↔ f =ᵐ[μ] 0 := by
  rfl


section Sum

variable {f : ι → Measure α}

/-- Sum of an indexed family of measures. -/
noncomputable def sum (f : ι → Measure α) : Measure α :=
  (OuterMeasure.sum fun i => (f i).toOuterMeasure).toMeasure <|
    le_trans (le_iInf fun _ => le_toOuterMeasure_caratheodory _)
      (OuterMeasure.le_sum_caratheodory _)

theorem le_sum_apply (f : ι → Measure α) (s : Set α) : ∑' i, f i s ≤ sum f s :=
  le_toMeasure_apply _ _ _

@[simp]
theorem sum_apply (f : ι → Measure α) {s : Set α} (hs : MeasurableSet s) :
    sum f s = ∑' i, f i s :=
  toMeasure_apply _ _ hs

theorem sum_apply₀ (f : ι → Measure α) {s : Set α} (hs : NullMeasurableSet s (sum f)) :
    sum f s = ∑' i, f i s := by
  apply le_antisymm ?_ (le_sum_apply _ _)
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, ts, t_meas, ht⟩
  calc
  sum f s = sum f t := measure_congr ht.symm
  _ = ∑' i, f i t := sum_apply _ t_meas
  _ ≤ ∑' i, f i s := ENNReal.tsum_le_tsum fun i ↦ measure_mono ts

/-! For the next theorem, the countability assumption is necessary. For a counterexample, consider
an uncountable space, with a distinguished point `x₀`, and the sigma-algebra made of countable sets
not containing `x₀`, and their complements. All points but `x₀` are measurable.
Consider the sum of the Dirac masses at points different from `x₀`, and `s = {x₀}`. For any Dirac
mass `δ_x`, we have `δ_x (x₀) = 0`, so `∑' x, δ_x (x₀) = 0`. On the other hand, the measure
`sum δ_x` gives mass one to each point different from `x₀`, so it gives infinite mass to any
measurable set containing `x₀` (as such a set is uncountable), and by outer regularity one gets
`sum δ_x {x₀} = ∞`.
-/
theorem sum_apply_of_countable [Countable ι] (f : ι → Measure α) (s : Set α) :
    sum f s = ∑' i, f i s := by
  apply le_antisymm ?_ (le_sum_apply _ _)
  rcases exists_measurable_superset_forall_eq f s with ⟨t, hst, htm, ht⟩
  calc
  sum f s ≤ sum f t := measure_mono hst
  _ = ∑' i, f i t := sum_apply _ htm
  _ = ∑' i, f i s := by simp [ht]

@[simp]
theorem sum_apply_eq_zero [Countable ι] {μ : ι → Measure α} {s : Set α} :
    sum μ s = 0 ↔ ∀ i, μ i s = 0 := by
  simp [sum_apply_of_countable]

theorem sum_apply_eq_zero' {μ : ι → Measure α} {s : Set α} (hs : MeasurableSet s) :
    sum μ s = 0 ↔ ∀ i, μ i s = 0 := by simp [hs]

@[simp] lemma sum_eq_zero : sum f = 0 ↔ ∀ i, f i = 0 := by
  simp +contextual [Measure.ext_iff, forall_comm (α := ι)]

@[simp]
lemma sum_zero : Measure.sum (fun (_ : ι) ↦ (0 : Measure α)) = 0 := by
  ext s hs
  simp [Measure.sum_apply _ hs]

theorem sum_sum {ι' : Type*} (μ : ι → ι' → Measure α) :
    (sum fun n => sum (μ n)) = sum (fun (p : ι × ι') ↦ μ p.1 p.2) := by
  ext1 s hs
  simp [sum_apply _ hs, ENNReal.tsum_prod']

theorem sum_comm {ι' : Type*} (μ : ι → ι' → Measure α) :
    (sum fun n => sum (μ n)) = sum fun m => sum fun n => μ n m := by
  ext1 s hs
  simp_rw [sum_apply _ hs]
  rw [ENNReal.tsum_comm]

theorem ae_sum_iff [Countable ι] {μ : ι → Measure α} {p : α → Prop} :
    (∀ᵐ x ∂sum μ, p x) ↔ ∀ i, ∀ᵐ x ∂μ i, p x :=
  sum_apply_eq_zero

theorem ae_sum_iff' {μ : ι → Measure α} {p : α → Prop} (h : MeasurableSet { x | p x }) :
    (∀ᵐ x ∂sum μ, p x) ↔ ∀ i, ∀ᵐ x ∂μ i, p x :=
  sum_apply_eq_zero' h.compl

@[simp]
theorem sum_fintype [Fintype ι] (μ : ι → Measure α) : sum μ = ∑ i, μ i := by
  ext1 s hs
  simp only [sum_apply, finsetSum_apply, hs, tsum_fintype]

theorem sum_coe_finset (s : Finset ι) (μ : ι → Measure α) :
    (sum fun i : s => μ i) = ∑ i ∈ s, μ i := by rw [sum_fintype, Finset.sum_coe_sort s μ]

theorem sum_bool (f : Bool → Measure α) : sum f = f true + f false := by
  rw [sum_fintype, Fintype.sum_bool]

theorem sum_cond (μ ν : Measure α) : (sum fun b => cond b μ ν) = μ + ν :=
  sum_bool _

theorem sum_add_sum_compl (s : Set ι) (μ : ι → Measure α) :
    ((sum fun i : s => μ i) + sum fun i : ↥sᶜ => μ i) = sum μ := by
  ext1 t ht
  simp only [add_apply, sum_apply _ ht]
  exact ENNReal.summable.tsum_add_tsum_compl (f := fun i => μ i t) ENNReal.summable

theorem sum_congr {μ ν : ℕ → Measure α} (h : ∀ n, μ n = ν n) : sum μ = sum ν :=
  congr_arg sum (funext h)

theorem sum_add_sum {ι : Type*} (μ ν : ι → Measure α) : sum μ + sum ν = sum fun n => μ n + ν n := by
  ext1 s hs
  simp only [add_apply, sum_apply _ hs,
    ENNReal.summable.tsum_add ENNReal.summable]

@[simp] lemma sum_comp_equiv {ι ι' : Type*} (e : ι' ≃ ι) (m : ι → Measure α) :
    sum (m ∘ e) = sum m := by
  ext s hs
  simpa [hs, sum_apply] using e.tsum_eq (fun n ↦ m n s)

@[simp] lemma sum_extend_zero {ι ι' : Type*} {f : ι → ι'} (hf : Injective f) (m : ι → Measure α) :
    sum (Function.extend f m 0) = sum m := by
  ext s hs
  simp [*, Function.apply_extend (fun μ : Measure α ↦ μ s)]

end Sum

end Measure

open Measure

open MeasureTheory

lemma NullMeasurableSet.smul_measure (h : NullMeasurableSet s μ) (c : ℝ≥0∞) :
    NullMeasurableSet s (c • μ) := by
  obtain ⟨t, ht, hst⟩ := h
  exact ⟨t, ht, hst.filter_mono (ae_smul_measure_le c)⟩

lemma nullMeasurableSet_smul_measure_iff {c : ℝ≥0∞} (hc : c ≠ 0) :
    NullMeasurableSet s (c • μ) ↔ NullMeasurableSet s μ := by
  simp only [nullMeasurableSet_iff_eventuallyMeasurableSet, μ.ae_ennreal_smul_measure_eq hc]

end MeasureTheory

end
