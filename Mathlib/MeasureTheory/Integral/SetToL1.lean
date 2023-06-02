/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne

! This file was ported from Lean 3 source module measure_theory.integral.set_to_l1
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Extension of a linear function from indicators to L1

Let `T : set α → E →L[ℝ] F` be additive for measurable sets with finite measure, in the sense that
for `s, t` two such sets, `s ∩ t = ∅ → T (s ∪ t) = T s + T t`. `T` is akin to a bilinear map on
`set α × E`, or a linear map on indicator functions.

This file constructs an extension of `T` to integrable simple functions, which are finite sums of
indicators of measurable sets with finite measure, then to integrable functions, which are limits of
integrable simple functions.

The main result is a continuous linear map `(α →₁[μ] E) →L[ℝ] F`. This extension process is used to
define the Bochner integral in the `measure_theory.integral.bochner` file and the conditional
expectation of an integrable function in `measure_theory.function.conditional_expectation`.

## Main Definitions

- `fin_meas_additive μ T`: the property that `T` is additive on measurable sets with finite measure.
  For two such sets, `s ∩ t = ∅ → T (s ∪ t) = T s + T t`.
- `dominated_fin_meas_additive μ T C`: `fin_meas_additive μ T ∧ ∀ s, ‖T s‖ ≤ C * (μ s).to_real`.
  This is the property needed to perform the extension from indicators to L1.
- `set_to_L1 (hT : dominated_fin_meas_additive μ T C) : (α →₁[μ] E) →L[ℝ] F`: the extension of `T`
  from indicators to L1.
- `set_to_fun μ T (hT : dominated_fin_meas_additive μ T C) (f : α → E) : F`: a version of the
  extension which applies to functions (with value 0 if the function is not integrable).

## Properties

For most properties of `set_to_fun`, we provide two lemmas. One version uses hypotheses valid on
all sets, like `T = T'`, and a second version which uses a primed name uses hypotheses on
measurable sets with finite measure, like `∀ s, measurable_set s → μ s < ∞ → T s = T' s`.

The lemmas listed here don't show all hypotheses. Refer to the actual lemmas for details.

Linearity:
- `set_to_fun_zero_left : set_to_fun μ 0 hT f = 0`
- `set_to_fun_add_left : set_to_fun μ (T + T') _ f = set_to_fun μ T hT f + set_to_fun μ T' hT' f`
- `set_to_fun_smul_left : set_to_fun μ (λ s, c • (T s)) (hT.smul c) f = c • set_to_fun μ T hT f`
- `set_to_fun_zero : set_to_fun μ T hT (0 : α → E) = 0`
- `set_to_fun_neg : set_to_fun μ T hT (-f) = - set_to_fun μ T hT f`
If `f` and `g` are integrable:
- `set_to_fun_add : set_to_fun μ T hT (f + g) = set_to_fun μ T hT f + set_to_fun μ T hT g`
- `set_to_fun_sub : set_to_fun μ T hT (f - g) = set_to_fun μ T hT f - set_to_fun μ T hT g`
If `T` is verifies `∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x`:
- `set_to_fun_smul : set_to_fun μ T hT (c • f) = c • set_to_fun μ T hT f`

Other:
- `set_to_fun_congr_ae (h : f =ᵐ[μ] g) : set_to_fun μ T hT f = set_to_fun μ T hT g`
- `set_to_fun_measure_zero (h : μ = 0) : set_to_fun μ T hT f = 0`

If the space is a `normed_lattice_add_comm_group` and `T` is such that `0 ≤ T s x` for `0 ≤ x`, we
also prove order-related properties:
- `set_to_fun_mono_left (h : ∀ s x, T s x ≤ T' s x) : set_to_fun μ T hT f ≤ set_to_fun μ T' hT' f`
- `set_to_fun_nonneg (hf : 0 ≤ᵐ[μ] f) : 0 ≤ set_to_fun μ T hT f`
- `set_to_fun_mono (hfg : f ≤ᵐ[μ] g) : set_to_fun μ T hT f ≤ set_to_fun μ T hT g`

## Implementation notes

The starting object `T : set α → E →L[ℝ] F` matters only through its restriction on measurable sets
with finite measure. Its value on other sets is ignored.
-/


noncomputable section

open scoped Classical Topology BigOperators NNReal ENNReal MeasureTheory Pointwise

open Set Filter TopologicalSpace ENNReal Emetric

namespace MeasureTheory

variable {α E F F' G 𝕜 : Type _} {p : ℝ≥0∞} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [NormedAddCommGroup G] {m : MeasurableSpace α} {μ : Measure α}

-- mathport name: «expr →ₛ »
local infixr:25 " →ₛ " => SimpleFunc

open Finset

section FinMeasAdditive

/-- A set function is `fin_meas_additive` if its value on the union of two disjoint measurable
sets with finite measure is the sum of its values on each set. -/
def FinMeasAdditive {β} [AddMonoid β] {m : MeasurableSpace α} (μ : Measure α) (T : Set α → β) :
    Prop :=
  ∀ s t, MeasurableSet s → MeasurableSet t → μ s ≠ ∞ → μ t ≠ ∞ → s ∩ t = ∅ → T (s ∪ t) = T s + T t
#align measure_theory.fin_meas_additive MeasureTheory.FinMeasAdditive

namespace FinMeasAdditive

variable {β : Type _} [AddCommMonoid β] {T T' : Set α → β}

theorem zero : FinMeasAdditive μ (0 : Set α → β) := fun s t hs ht hμs hμt hst => by simp
#align measure_theory.fin_meas_additive.zero MeasureTheory.FinMeasAdditive.zero

theorem add (hT : FinMeasAdditive μ T) (hT' : FinMeasAdditive μ T') : FinMeasAdditive μ (T + T') :=
  by
  intro s t hs ht hμs hμt hst
  simp only [hT s t hs ht hμs hμt hst, hT' s t hs ht hμs hμt hst, Pi.add_apply]
  abel
#align measure_theory.fin_meas_additive.add MeasureTheory.FinMeasAdditive.add

theorem smul [Monoid 𝕜] [DistribMulAction 𝕜 β] (hT : FinMeasAdditive μ T) (c : 𝕜) :
    FinMeasAdditive μ fun s => c • T s := fun s t hs ht hμs hμt hst => by
  simp [hT s t hs ht hμs hμt hst]
#align measure_theory.fin_meas_additive.smul MeasureTheory.FinMeasAdditive.smul

theorem of_eq_top_imp_eq_top {μ' : Measure α} (h : ∀ s, MeasurableSet s → μ s = ∞ → μ' s = ∞)
    (hT : FinMeasAdditive μ T) : FinMeasAdditive μ' T := fun s t hs ht hμ's hμ't hst =>
  hT s t hs ht (mt (h s hs) hμ's) (mt (h t ht) hμ't) hst
#align measure_theory.fin_meas_additive.of_eq_top_imp_eq_top MeasureTheory.FinMeasAdditive.of_eq_top_imp_eq_top

theorem of_smul_measure (c : ℝ≥0∞) (hc_ne_top : c ≠ ∞) (hT : FinMeasAdditive (c • μ) T) :
    FinMeasAdditive μ T :=
  by
  refine' of_eq_top_imp_eq_top (fun s hs hμs => _) hT
  rw [measure.smul_apply, smul_eq_mul, WithTop.mul_eq_top_iff] at hμs 
  simp only [hc_ne_top, or_false_iff, Ne.def, false_and_iff] at hμs 
  exact hμs.2
#align measure_theory.fin_meas_additive.of_smul_measure MeasureTheory.FinMeasAdditive.of_smul_measure

theorem smul_measure (c : ℝ≥0∞) (hc_ne_zero : c ≠ 0) (hT : FinMeasAdditive μ T) :
    FinMeasAdditive (c • μ) T :=
  by
  refine' of_eq_top_imp_eq_top (fun s hs hμs => _) hT
  rw [measure.smul_apply, smul_eq_mul, WithTop.mul_eq_top_iff]
  simp only [hc_ne_zero, true_and_iff, Ne.def, not_false_iff]
  exact Or.inl hμs
#align measure_theory.fin_meas_additive.smul_measure MeasureTheory.FinMeasAdditive.smul_measure

theorem smul_measure_iff (c : ℝ≥0∞) (hc_ne_zero : c ≠ 0) (hc_ne_top : c ≠ ∞) :
    FinMeasAdditive (c • μ) T ↔ FinMeasAdditive μ T :=
  ⟨fun hT => of_smul_measure c hc_ne_top hT, fun hT => smul_measure c hc_ne_zero hT⟩
#align measure_theory.fin_meas_additive.smul_measure_iff MeasureTheory.FinMeasAdditive.smul_measure_iff

theorem map_empty_eq_zero {β} [AddCancelMonoid β] {T : Set α → β} (hT : FinMeasAdditive μ T) :
    T ∅ = 0 :=
  by
  have h_empty : μ ∅ ≠ ∞ := (measure_empty.le.trans_lt ENNReal.coe_lt_top).Ne
  specialize hT ∅ ∅ MeasurableSet.empty MeasurableSet.empty h_empty h_empty (Set.inter_empty ∅)
  rw [Set.union_empty] at hT 
  nth_rw 1 [← add_zero (T ∅)] at hT 
  exact (add_left_cancel hT).symm
#align measure_theory.fin_meas_additive.map_empty_eq_zero MeasureTheory.FinMeasAdditive.map_empty_eq_zero

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (i j «expr ∈ » sι) -/
theorem map_iUnion_fin_meas_set_eq_sum (T : Set α → β) (T_empty : T ∅ = 0)
    (h_add : FinMeasAdditive μ T) {ι} (S : ι → Set α) (sι : Finset ι)
    (hS_meas : ∀ i, MeasurableSet (S i)) (hSp : ∀ i ∈ sι, μ (S i) ≠ ∞)
    (h_disj : ∀ (i) (_ : i ∈ sι) (j) (_ : j ∈ sι), i ≠ j → Disjoint (S i) (S j)) :
    T (⋃ i ∈ sι, S i) = ∑ i in sι, T (S i) :=
  by
  revert hSp h_disj
  refine' Finset.induction_on sι _ _
  ·
    simp only [Finset.not_mem_empty, IsEmpty.forall_iff, Union_false, Union_empty, sum_empty,
      forall₂_true_iff, imp_true_iff, forall_true_left, not_false_iff, T_empty]
  intro a s has h hps h_disj
  rw [Finset.sum_insert has, ← h]
  swap; · exact fun i hi => hps i (Finset.mem_insert_of_mem hi)
  swap;
  ·
    exact fun i hi j hj hij =>
      h_disj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
  rw [←
    h_add (S a) (⋃ i ∈ s, S i) (hS_meas a) (measurable_set_bUnion _ fun i _ => hS_meas i)
      (hps a (Finset.mem_insert_self a s))]
  · congr; convert Finset.iSup_insert a s S
  ·
    exact
      ((measure_bUnion_finset_le _ _).trans_lt <|
          ENNReal.sum_lt_top fun i hi => hps i <| Finset.mem_insert_of_mem hi).Ne
  · simp_rw [Set.inter_iUnion]
    refine' Union_eq_empty.mpr fun i => Union_eq_empty.mpr fun hi => _
    rw [← Set.disjoint_iff_inter_eq_empty]
    refine' h_disj a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi) fun hai => _
    rw [← hai] at hi 
    exact has hi
#align measure_theory.fin_meas_additive.map_Union_fin_meas_set_eq_sum MeasureTheory.FinMeasAdditive.map_iUnion_fin_meas_set_eq_sum

end FinMeasAdditive

/-- A `fin_meas_additive` set function whose norm on every set is less than the measure of the
set (up to a multiplicative constant). -/
def DominatedFinMeasAdditive {β} [SeminormedAddCommGroup β] {m : MeasurableSpace α} (μ : Measure α)
    (T : Set α → β) (C : ℝ) : Prop :=
  FinMeasAdditive μ T ∧ ∀ s, MeasurableSet s → μ s < ∞ → ‖T s‖ ≤ C * (μ s).toReal
#align measure_theory.dominated_fin_meas_additive MeasureTheory.DominatedFinMeasAdditive

namespace DominatedFinMeasAdditive

variable {β : Type _} [SeminormedAddCommGroup β] {T T' : Set α → β} {C C' : ℝ}

theorem zero {m : MeasurableSpace α} (μ : Measure α) (hC : 0 ≤ C) :
    DominatedFinMeasAdditive μ (0 : Set α → β) C :=
  by
  refine' ⟨fin_meas_additive.zero, fun s hs hμs => _⟩
  rw [Pi.zero_apply, norm_zero]
  exact mul_nonneg hC to_real_nonneg
#align measure_theory.dominated_fin_meas_additive.zero MeasureTheory.DominatedFinMeasAdditive.zero

theorem eq_zero_of_measure_zero {β : Type _} [NormedAddCommGroup β] {T : Set α → β} {C : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) {s : Set α} (hs : MeasurableSet s) (hs_zero : μ s = 0) :
    T s = 0 := by
  refine' norm_eq_zero.mp _
  refine' ((hT.2 s hs (by simp [hs_zero])).trans (le_of_eq _)).antisymm (norm_nonneg _)
  rw [hs_zero, ENNReal.zero_toReal, MulZeroClass.mul_zero]
#align measure_theory.dominated_fin_meas_additive.eq_zero_of_measure_zero MeasureTheory.DominatedFinMeasAdditive.eq_zero_of_measure_zero

theorem eq_zero {β : Type _} [NormedAddCommGroup β] {T : Set α → β} {C : ℝ} {m : MeasurableSpace α}
    (hT : DominatedFinMeasAdditive (0 : Measure α) T C) {s : Set α} (hs : MeasurableSet s) :
    T s = 0 :=
  eq_zero_of_measure_zero hT hs (by simp only [measure.coe_zero, Pi.zero_apply])
#align measure_theory.dominated_fin_meas_additive.eq_zero MeasureTheory.DominatedFinMeasAdditive.eq_zero

theorem add (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C') :
    DominatedFinMeasAdditive μ (T + T') (C + C') :=
  by
  refine' ⟨hT.1.add hT'.1, fun s hs hμs => _⟩
  rw [Pi.add_apply, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hT.2 s hs hμs) (hT'.2 s hs hμs))
#align measure_theory.dominated_fin_meas_additive.add MeasureTheory.DominatedFinMeasAdditive.add

theorem smul [NormedField 𝕜] [NormedSpace 𝕜 β] (hT : DominatedFinMeasAdditive μ T C) (c : 𝕜) :
    DominatedFinMeasAdditive μ (fun s => c • T s) (‖c‖ * C) :=
  by
  refine' ⟨hT.1.smul c, fun s hs hμs => _⟩
  dsimp only
  rw [norm_smul, mul_assoc]
  exact mul_le_mul le_rfl (hT.2 s hs hμs) (norm_nonneg _) (norm_nonneg _)
#align measure_theory.dominated_fin_meas_additive.smul MeasureTheory.DominatedFinMeasAdditive.smul

theorem of_measure_le {μ' : Measure α} (h : μ ≤ μ') (hT : DominatedFinMeasAdditive μ T C)
    (hC : 0 ≤ C) : DominatedFinMeasAdditive μ' T C :=
  by
  have h' : ∀ s, MeasurableSet s → μ s = ∞ → μ' s = ∞ := by intro s hs hμs; rw [eq_top_iff, ← hμs];
    exact h s hs
  refine' ⟨hT.1.of_eq_top_imp_eq_top h', fun s hs hμ's => _⟩
  have hμs : μ s < ∞ := (h s hs).trans_lt hμ's
  refine' (hT.2 s hs hμs).trans (mul_le_mul le_rfl _ ENNReal.toReal_nonneg hC)
  rw [to_real_le_to_real hμs.ne hμ's.ne]
  exact h s hs
#align measure_theory.dominated_fin_meas_additive.of_measure_le MeasureTheory.DominatedFinMeasAdditive.of_measure_le

theorem add_measure_right {m : MeasurableSpace α} (μ ν : Measure α)
    (hT : DominatedFinMeasAdditive μ T C) (hC : 0 ≤ C) : DominatedFinMeasAdditive (μ + ν) T C :=
  of_measure_le (Measure.le_add_right le_rfl) hT hC
#align measure_theory.dominated_fin_meas_additive.add_measure_right MeasureTheory.DominatedFinMeasAdditive.add_measure_right

theorem add_measure_left {m : MeasurableSpace α} (μ ν : Measure α)
    (hT : DominatedFinMeasAdditive ν T C) (hC : 0 ≤ C) : DominatedFinMeasAdditive (μ + ν) T C :=
  of_measure_le (Measure.le_add_left le_rfl) hT hC
#align measure_theory.dominated_fin_meas_additive.add_measure_left MeasureTheory.DominatedFinMeasAdditive.add_measure_left

theorem of_smul_measure (c : ℝ≥0∞) (hc_ne_top : c ≠ ∞) (hT : DominatedFinMeasAdditive (c • μ) T C) :
    DominatedFinMeasAdditive μ T (c.toReal * C) :=
  by
  have h : ∀ s, MeasurableSet s → c • μ s = ∞ → μ s = ∞ :=
    by
    intro s hs hcμs
    simp only [hc_ne_top, Algebra.id.smul_eq_mul, WithTop.mul_eq_top_iff, or_false_iff, Ne.def,
      false_and_iff] at hcμs 
    exact hcμs.2
  refine' ⟨hT.1.of_eq_top_imp_eq_top h, fun s hs hμs => _⟩
  have hcμs : c • μ s ≠ ∞ := mt (h s hs) hμs.ne
  rw [smul_eq_mul] at hcμs 
  simp_rw [dominated_fin_meas_additive, measure.smul_apply, smul_eq_mul, to_real_mul] at hT 
  refine' (hT.2 s hs hcμs.lt_top).trans (le_of_eq _)
  ring
#align measure_theory.dominated_fin_meas_additive.of_smul_measure MeasureTheory.DominatedFinMeasAdditive.of_smul_measure

theorem of_measure_le_smul {μ' : Measure α} (c : ℝ≥0∞) (hc : c ≠ ∞) (h : μ ≤ c • μ')
    (hT : DominatedFinMeasAdditive μ T C) (hC : 0 ≤ C) :
    DominatedFinMeasAdditive μ' T (c.toReal * C) :=
  (hT.of_measure_le h hC).of_smul_measure c hc
#align measure_theory.dominated_fin_meas_additive.of_measure_le_smul MeasureTheory.DominatedFinMeasAdditive.of_measure_le_smul

end DominatedFinMeasAdditive

end FinMeasAdditive

namespace SimpleFunc

/-- Extend `set α → (F →L[ℝ] F')` to `(α →ₛ F) → F'`. -/
def setToSimpleFunc {m : MeasurableSpace α} (T : Set α → F →L[ℝ] F') (f : α →ₛ F) : F' :=
  ∑ x in f.range, T (f ⁻¹' {x}) x
#align measure_theory.simple_func.set_to_simple_func MeasureTheory.SimpleFunc.setToSimpleFunc

@[simp]
theorem setToSimpleFunc_zero {m : MeasurableSpace α} (f : α →ₛ F) :
    setToSimpleFunc (0 : Set α → F →L[ℝ] F') f = 0 := by simp [set_to_simple_func]
#align measure_theory.simple_func.set_to_simple_func_zero MeasureTheory.SimpleFunc.setToSimpleFunc_zero

theorem setToSimpleFunc_zero' {T : Set α → E →L[ℝ] F'}
    (h_zero : ∀ s, MeasurableSet s → μ s < ∞ → T s = 0) (f : α →ₛ E) (hf : Integrable f μ) :
    setToSimpleFunc T f = 0 := by
  simp_rw [set_to_simple_func]
  refine' sum_eq_zero fun x hx => _
  by_cases hx0 : x = 0
  · simp [hx0]
  rw [h_zero (f ⁻¹' ({x} : Set E)) (measurable_set_fiber _ _)
      (measure_preimage_lt_top_of_integrable f hf hx0),
    ContinuousLinearMap.zero_apply]
#align measure_theory.simple_func.set_to_simple_func_zero' MeasureTheory.SimpleFunc.setToSimpleFunc_zero'

@[simp]
theorem setToSimpleFunc_zero_apply {m : MeasurableSpace α} (T : Set α → F →L[ℝ] F') :
    setToSimpleFunc T (0 : α →ₛ F) = 0 := by
  cases isEmpty_or_nonempty α <;> simp [set_to_simple_func]
#align measure_theory.simple_func.set_to_simple_func_zero_apply MeasureTheory.SimpleFunc.setToSimpleFunc_zero_apply

theorem setToSimpleFunc_eq_sum_filter {m : MeasurableSpace α} (T : Set α → F →L[ℝ] F')
    (f : α →ₛ F) : setToSimpleFunc T f = ∑ x in f.range.filterₓ fun x => x ≠ 0, (T (f ⁻¹' {x})) x :=
  by
  symm
  refine' sum_filter_of_ne fun x hx => mt fun hx0 => _
  rw [hx0]
  exact ContinuousLinearMap.map_zero _
#align measure_theory.simple_func.set_to_simple_func_eq_sum_filter MeasureTheory.SimpleFunc.setToSimpleFunc_eq_sum_filter

theorem map_setToSimpleFunc (T : Set α → F →L[ℝ] F') (h_add : FinMeasAdditive μ T) {f : α →ₛ G}
    (hf : Integrable f μ) {g : G → F} (hg : g 0 = 0) :
    (f.map g).setToSimpleFunc T = ∑ x in f.range, T (f ⁻¹' {x}) (g x) :=
  by
  have T_empty : T ∅ = 0 := h_add.map_empty_eq_zero
  have hfp : ∀ x ∈ f.range, x ≠ 0 → μ (f ⁻¹' {x}) ≠ ∞ := fun x hx hx0 =>
    (measure_preimage_lt_top_of_integrable f hf hx0).Ne
  simp only [set_to_simple_func, range_map]
  refine' Finset.sum_image' _ fun b hb => _
  rcases mem_range.1 hb with ⟨a, rfl⟩
  by_cases h0 : g (f a) = 0
  · simp_rw [h0]
    rw [ContinuousLinearMap.map_zero, Finset.sum_eq_zero fun x hx => _]
    rw [mem_filter] at hx 
    rw [hx.2, ContinuousLinearMap.map_zero]
  have h_left_eq :
    T (map g f ⁻¹' {g (f a)}) (g (f a)) =
      T (f ⁻¹' ↑(f.range.filter fun b => g b = g (f a))) (g (f a)) :=
    by congr; rw [map_preimage_singleton]
  rw [h_left_eq]
  have h_left_eq' :
    T (f ⁻¹' ↑(Filter (fun b : G => g b = g (f a)) f.range)) (g (f a)) =
      T (⋃ y ∈ Filter (fun b : G => g b = g (f a)) f.range, f ⁻¹' {y}) (g (f a)) :=
    by congr; rw [← Finset.set_biUnion_preimage_singleton]
  rw [h_left_eq']
  rw [h_add.map_Union_fin_meas_set_eq_sum T T_empty]
  · simp only [filter_congr_decidable, sum_apply, ContinuousLinearMap.coe_sum']
    refine' Finset.sum_congr rfl fun x hx => _
    rw [mem_filter] at hx 
    rw [hx.2]
  · exact fun i => measurable_set_fiber _ _
  · intro i hi
    rw [mem_filter] at hi 
    refine' hfp i hi.1 fun hi0 => _
    rw [hi0, hg] at hi 
    exact h0 hi.2.symm
  · intro i j hi hj hij
    rw [Set.disjoint_iff]
    intro x hx
    rw [Set.mem_inter_iff, Set.mem_preimage, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_singleton_iff] at hx 
    rw [← hx.1, ← hx.2] at hij 
    exact absurd rfl hij
#align measure_theory.simple_func.map_set_to_simple_func MeasureTheory.SimpleFunc.map_setToSimpleFunc

theorem setToSimpleFunc_congr' (T : Set α → E →L[ℝ] F) (h_add : FinMeasAdditive μ T) {f g : α →ₛ E}
    (hf : Integrable f μ) (hg : Integrable g μ) (h : ∀ x y, x ≠ y → T (f ⁻¹' {x} ∩ g ⁻¹' {y}) = 0) :
    f.setToSimpleFunc T = g.setToSimpleFunc T :=
  show ((pair f g).map Prod.fst).setToSimpleFunc T = ((pair f g).map Prod.snd).setToSimpleFunc T
    by
    have h_pair : integrable (f.pair g) μ := integrable_pair hf hg
    rw [map_set_to_simple_func T h_add h_pair Prod.fst_zero]
    rw [map_set_to_simple_func T h_add h_pair Prod.snd_zero]
    refine' Finset.sum_congr rfl fun p hp => _
    rcases mem_range.1 hp with ⟨a, rfl⟩
    by_cases eq : f a = g a
    · dsimp only [pair_apply]; rw [Eq]
    · have : T (pair f g ⁻¹' {(f a, g a)}) = 0 :=
        by
        have h_eq : T (⇑(f.pair g) ⁻¹' {(f a, g a)}) = T (f ⁻¹' {f a} ∩ g ⁻¹' {g a}) := by congr;
          rw [pair_preimage_singleton f g]
        rw [h_eq]
        exact h (f a) (g a) Eq
      simp only [this, ContinuousLinearMap.zero_apply, pair_apply]
#align measure_theory.simple_func.set_to_simple_func_congr' MeasureTheory.SimpleFunc.setToSimpleFunc_congr'

theorem setToSimpleFunc_congr (T : Set α → E →L[ℝ] F)
    (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0) (h_add : FinMeasAdditive μ T) {f g : α →ₛ E}
    (hf : Integrable f μ) (h : f =ᵐ[μ] g) : f.setToSimpleFunc T = g.setToSimpleFunc T :=
  by
  refine' set_to_simple_func_congr' T h_add hf ((integrable_congr h).mp hf) _
  refine' fun x y hxy => h_zero _ ((measurable_set_fiber f x).inter (measurable_set_fiber g y)) _
  rw [eventually_eq, ae_iff] at h 
  refine' measure_mono_null (fun z => _) h
  simp_rw [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
  intro h
  rwa [h.1, h.2]
#align measure_theory.simple_func.set_to_simple_func_congr MeasureTheory.SimpleFunc.setToSimpleFunc_congr

theorem setToSimpleFunc_congr_left (T T' : Set α → E →L[ℝ] F)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → T s = T' s) (f : α →ₛ E) (hf : Integrable f μ) :
    setToSimpleFunc T f = setToSimpleFunc T' f :=
  by
  simp_rw [set_to_simple_func]
  refine' sum_congr rfl fun x hx => _
  by_cases hx0 : x = 0
  · simp [hx0]
  ·
    rw [h (f ⁻¹' {x}) (simple_func.measurable_set_fiber _ _)
        (simple_func.measure_preimage_lt_top_of_integrable _ hf hx0)]
#align measure_theory.simple_func.set_to_simple_func_congr_left MeasureTheory.SimpleFunc.setToSimpleFunc_congr_left

theorem setToSimpleFunc_add_left {m : MeasurableSpace α} (T T' : Set α → F →L[ℝ] F') {f : α →ₛ F} :
    setToSimpleFunc (T + T') f = setToSimpleFunc T f + setToSimpleFunc T' f :=
  by
  simp_rw [set_to_simple_func, Pi.add_apply]
  push_cast
  simp_rw [Pi.add_apply, sum_add_distrib]
#align measure_theory.simple_func.set_to_simple_func_add_left MeasureTheory.SimpleFunc.setToSimpleFunc_add_left

theorem setToSimpleFunc_add_left' (T T' T'' : Set α → E →L[ℝ] F)
    (h_add : ∀ s, MeasurableSet s → μ s < ∞ → T'' s = T s + T' s) {f : α →ₛ E}
    (hf : Integrable f μ) : setToSimpleFunc T'' f = setToSimpleFunc T f + setToSimpleFunc T' f :=
  by
  simp_rw [set_to_simple_func_eq_sum_filter]
  suffices
    ∀ x ∈ Filter (fun x : E => x ≠ 0) f.range, T'' (f ⁻¹' {x}) = T (f ⁻¹' {x}) + T' (f ⁻¹' {x})
    by
    rw [← sum_add_distrib]
    refine' Finset.sum_congr rfl fun x hx => _
    rw [this x hx]
    push_cast
    rw [Pi.add_apply]
  intro x hx
  refine'
    h_add (f ⁻¹' {x}) (measurableSet_preimage _ _) (measure_preimage_lt_top_of_integrable _ hf _)
  rw [mem_filter] at hx 
  exact hx.2
#align measure_theory.simple_func.set_to_simple_func_add_left' MeasureTheory.SimpleFunc.setToSimpleFunc_add_left'

theorem setToSimpleFunc_smul_left {m : MeasurableSpace α} (T : Set α → F →L[ℝ] F') (c : ℝ)
    (f : α →ₛ F) : setToSimpleFunc (fun s => c • T s) f = c • setToSimpleFunc T f := by
  simp_rw [set_to_simple_func, ContinuousLinearMap.smul_apply, smul_sum]
#align measure_theory.simple_func.set_to_simple_func_smul_left MeasureTheory.SimpleFunc.setToSimpleFunc_smul_left

theorem setToSimpleFunc_smul_left' (T T' : Set α → E →L[ℝ] F') (c : ℝ)
    (h_smul : ∀ s, MeasurableSet s → μ s < ∞ → T' s = c • T s) {f : α →ₛ E} (hf : Integrable f μ) :
    setToSimpleFunc T' f = c • setToSimpleFunc T f :=
  by
  simp_rw [set_to_simple_func_eq_sum_filter]
  suffices ∀ x ∈ Filter (fun x : E => x ≠ 0) f.range, T' (f ⁻¹' {x}) = c • T (f ⁻¹' {x})
    by
    rw [smul_sum]
    refine' Finset.sum_congr rfl fun x hx => _
    rw [this x hx]
    rfl
  intro x hx
  refine'
    h_smul (f ⁻¹' {x}) (measurableSet_preimage _ _) (measure_preimage_lt_top_of_integrable _ hf _)
  rw [mem_filter] at hx 
  exact hx.2
#align measure_theory.simple_func.set_to_simple_func_smul_left' MeasureTheory.SimpleFunc.setToSimpleFunc_smul_left'

theorem setToSimpleFunc_add (T : Set α → E →L[ℝ] F) (h_add : FinMeasAdditive μ T) {f g : α →ₛ E}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    setToSimpleFunc T (f + g) = setToSimpleFunc T f + setToSimpleFunc T g :=
  have hp_pair : Integrable (f.pair g) μ := integrable_pair hf hg
  calc
    setToSimpleFunc T (f + g) = ∑ x in (pair f g).range, T (pair f g ⁻¹' {x}) (x.fst + x.snd) := by
      rw [add_eq_map₂, map_set_to_simple_func T h_add hp_pair]; simp
    _ = ∑ x in (pair f g).range, T (pair f g ⁻¹' {x}) x.fst + T (pair f g ⁻¹' {x}) x.snd :=
      (Finset.sum_congr rfl fun a ha => ContinuousLinearMap.map_add _ _ _)
    _ =
        (∑ x in (pair f g).range, T (pair f g ⁻¹' {x}) x.fst) +
          ∑ x in (pair f g).range, T (pair f g ⁻¹' {x}) x.snd :=
      by rw [Finset.sum_add_distrib]
    _ = ((pair f g).map Prod.fst).setToSimpleFunc T + ((pair f g).map Prod.snd).setToSimpleFunc T :=
      by
      rw [map_set_to_simple_func T h_add hp_pair Prod.snd_zero,
        map_set_to_simple_func T h_add hp_pair Prod.fst_zero]
    
#align measure_theory.simple_func.set_to_simple_func_add MeasureTheory.SimpleFunc.setToSimpleFunc_add

theorem setToSimpleFunc_neg (T : Set α → E →L[ℝ] F) (h_add : FinMeasAdditive μ T) {f : α →ₛ E}
    (hf : Integrable f μ) : setToSimpleFunc T (-f) = -setToSimpleFunc T f :=
  calc
    setToSimpleFunc T (-f) = setToSimpleFunc T (f.map Neg.neg) := rfl
    _ = -setToSimpleFunc T f :=
      by
      rw [map_set_to_simple_func T h_add hf neg_zero, set_to_simple_func, ← sum_neg_distrib]
      exact Finset.sum_congr rfl fun x h => ContinuousLinearMap.map_neg _ _
    
#align measure_theory.simple_func.set_to_simple_func_neg MeasureTheory.SimpleFunc.setToSimpleFunc_neg

theorem setToSimpleFunc_sub (T : Set α → E →L[ℝ] F) (h_add : FinMeasAdditive μ T) {f g : α →ₛ E}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    setToSimpleFunc T (f - g) = setToSimpleFunc T f - setToSimpleFunc T g :=
  by
  rw [sub_eq_add_neg, set_to_simple_func_add T h_add hf, set_to_simple_func_neg T h_add hg,
    sub_eq_add_neg]
  rw [integrable_iff] at hg ⊢
  intro x hx_ne
  change μ (Neg.neg ∘ g ⁻¹' {x}) < ∞
  rw [preimage_comp, neg_preimage, Set.neg_singleton]
  refine' hg (-x) _
  simp [hx_ne]
#align measure_theory.simple_func.set_to_simple_func_sub MeasureTheory.SimpleFunc.setToSimpleFunc_sub

theorem setToSimpleFunc_smul_real (T : Set α → E →L[ℝ] F) (h_add : FinMeasAdditive μ T) (c : ℝ)
    {f : α →ₛ E} (hf : Integrable f μ) : setToSimpleFunc T (c • f) = c • setToSimpleFunc T f :=
  calc
    setToSimpleFunc T (c • f) = ∑ x in f.range, T (f ⁻¹' {x}) (c • x) := by
      rw [smul_eq_map c f, map_set_to_simple_func T h_add hf]; rw [smul_zero]
    _ = ∑ x in f.range, c • T (f ⁻¹' {x}) x :=
      (Finset.sum_congr rfl fun b hb => by rw [ContinuousLinearMap.map_smul (T (f ⁻¹' {b})) c b])
    _ = c • setToSimpleFunc T f := by simp only [set_to_simple_func, smul_sum, smul_smul, mul_comm]
    
#align measure_theory.simple_func.set_to_simple_func_smul_real MeasureTheory.SimpleFunc.setToSimpleFunc_smul_real

theorem setToSimpleFunc_smul {E} [NormedAddCommGroup E] [NormedField 𝕜] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [NormedSpace 𝕜 F] (T : Set α → E →L[ℝ] F) (h_add : FinMeasAdditive μ T)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (c : 𝕜) {f : α →ₛ E} (hf : Integrable f μ) :
    setToSimpleFunc T (c • f) = c • setToSimpleFunc T f :=
  calc
    setToSimpleFunc T (c • f) = ∑ x in f.range, T (f ⁻¹' {x}) (c • x) :=
      by
      rw [smul_eq_map c f, map_set_to_simple_func T h_add hf]
      rw [smul_zero]
    _ = ∑ x in f.range, c • T (f ⁻¹' {x}) x := (Finset.sum_congr rfl fun b hb => by rw [h_smul])
    _ = c • setToSimpleFunc T f := by simp only [set_to_simple_func, smul_sum, smul_smul, mul_comm]
    
#align measure_theory.simple_func.set_to_simple_func_smul MeasureTheory.SimpleFunc.setToSimpleFunc_smul

section Order

variable {G' G'' : Type _} [NormedLatticeAddCommGroup G''] [NormedSpace ℝ G'']
  [NormedLatticeAddCommGroup G'] [NormedSpace ℝ G']

theorem setToSimpleFunc_mono_left {m : MeasurableSpace α} (T T' : Set α → F →L[ℝ] G'')
    (hTT' : ∀ s x, T s x ≤ T' s x) (f : α →ₛ F) : setToSimpleFunc T f ≤ setToSimpleFunc T' f := by
  simp_rw [set_to_simple_func]; exact sum_le_sum fun i hi => hTT' _ i
#align measure_theory.simple_func.set_to_simple_func_mono_left MeasureTheory.SimpleFunc.setToSimpleFunc_mono_left

theorem setToSimpleFunc_mono_left' (T T' : Set α → E →L[ℝ] G'')
    (hTT' : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, T s x ≤ T' s x) (f : α →ₛ E)
    (hf : Integrable f μ) : setToSimpleFunc T f ≤ setToSimpleFunc T' f :=
  by
  refine' sum_le_sum fun i hi => _
  by_cases h0 : i = 0
  · simp [h0]
  · exact hTT' _ (measurable_set_fiber _ _) (measure_preimage_lt_top_of_integrable _ hf h0) i
#align measure_theory.simple_func.set_to_simple_func_mono_left' MeasureTheory.SimpleFunc.setToSimpleFunc_mono_left'

theorem setToSimpleFunc_nonneg {m : MeasurableSpace α} (T : Set α → G' →L[ℝ] G'')
    (hT_nonneg : ∀ s x, 0 ≤ x → 0 ≤ T s x) (f : α →ₛ G') (hf : 0 ≤ f) : 0 ≤ setToSimpleFunc T f :=
  by
  refine' sum_nonneg fun i hi => hT_nonneg _ i _
  rw [mem_range] at hi 
  obtain ⟨y, hy⟩ := set.mem_range.mp hi
  rw [← hy]
  refine' le_trans _ (hf y)
  simp
#align measure_theory.simple_func.set_to_simple_func_nonneg MeasureTheory.SimpleFunc.setToSimpleFunc_nonneg

theorem setToSimpleFunc_nonneg' (T : Set α → G' →L[ℝ] G'')
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) (f : α →ₛ G') (hf : 0 ≤ f)
    (hfi : Integrable f μ) : 0 ≤ setToSimpleFunc T f :=
  by
  refine' sum_nonneg fun i hi => _
  by_cases h0 : i = 0
  · simp [h0]
  refine'
    hT_nonneg _ (measurable_set_fiber _ _) (measure_preimage_lt_top_of_integrable _ hfi h0) i _
  rw [mem_range] at hi 
  obtain ⟨y, hy⟩ := set.mem_range.mp hi
  rw [← hy]
  convert hf y
#align measure_theory.simple_func.set_to_simple_func_nonneg' MeasureTheory.SimpleFunc.setToSimpleFunc_nonneg'

theorem setToSimpleFunc_mono {T : Set α → G' →L[ℝ] G''} (h_add : FinMeasAdditive μ T)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f g : α →ₛ G'}
    (hfi : Integrable f μ) (hgi : Integrable g μ) (hfg : f ≤ g) :
    setToSimpleFunc T f ≤ setToSimpleFunc T g :=
  by
  rw [← sub_nonneg, ← set_to_simple_func_sub T h_add hgi hfi]
  refine' set_to_simple_func_nonneg' T hT_nonneg _ _ (hgi.sub hfi)
  intro x
  simp only [coe_sub, sub_nonneg, coe_zero, Pi.zero_apply, Pi.sub_apply]
  exact hfg x
#align measure_theory.simple_func.set_to_simple_func_mono MeasureTheory.SimpleFunc.setToSimpleFunc_mono

end Order

theorem norm_setToSimpleFunc_le_sum_op_norm {m : MeasurableSpace α} (T : Set α → F' →L[ℝ] F)
    (f : α →ₛ F') : ‖f.setToSimpleFunc T‖ ≤ ∑ x in f.range, ‖T (f ⁻¹' {x})‖ * ‖x‖ :=
  calc
    ‖∑ x in f.range, T (f ⁻¹' {x}) x‖ ≤ ∑ x in f.range, ‖T (f ⁻¹' {x}) x‖ := norm_sum_le _ _
    _ ≤ ∑ x in f.range, ‖T (f ⁻¹' {x})‖ * ‖x‖ := by refine' Finset.sum_le_sum fun b hb => _;
      simp_rw [ContinuousLinearMap.le_op_norm]
    
#align measure_theory.simple_func.norm_set_to_simple_func_le_sum_op_norm MeasureTheory.SimpleFunc.norm_setToSimpleFunc_le_sum_op_norm

theorem norm_setToSimpleFunc_le_sum_mul_norm (T : Set α → F →L[ℝ] F') {C : ℝ}
    (hT_norm : ∀ s, MeasurableSet s → ‖T s‖ ≤ C * (μ s).toReal) (f : α →ₛ F) :
    ‖f.setToSimpleFunc T‖ ≤ C * ∑ x in f.range, (μ (f ⁻¹' {x})).toReal * ‖x‖ :=
  calc
    ‖f.setToSimpleFunc T‖ ≤ ∑ x in f.range, ‖T (f ⁻¹' {x})‖ * ‖x‖ :=
      norm_setToSimpleFunc_le_sum_op_norm T f
    _ ≤ ∑ x in f.range, C * (μ (f ⁻¹' {x})).toReal * ‖x‖ :=
      (sum_le_sum fun b hb =>
        mul_le_mul_of_nonneg_right (hT_norm _ <| SimpleFunc.measurableSet_fiber _ _) <|
          norm_nonneg _)
    _ ≤ C * ∑ x in f.range, (μ (f ⁻¹' {x})).toReal * ‖x‖ := by simp_rw [mul_sum, ← mul_assoc]
    
#align measure_theory.simple_func.norm_set_to_simple_func_le_sum_mul_norm MeasureTheory.SimpleFunc.norm_setToSimpleFunc_le_sum_mul_norm

theorem norm_setToSimpleFunc_le_sum_mul_norm_of_integrable (T : Set α → E →L[ℝ] F') {C : ℝ}
    (hT_norm : ∀ s, MeasurableSet s → μ s < ∞ → ‖T s‖ ≤ C * (μ s).toReal) (f : α →ₛ E)
    (hf : Integrable f μ) :
    ‖f.setToSimpleFunc T‖ ≤ C * ∑ x in f.range, (μ (f ⁻¹' {x})).toReal * ‖x‖ :=
  calc
    ‖f.setToSimpleFunc T‖ ≤ ∑ x in f.range, ‖T (f ⁻¹' {x})‖ * ‖x‖ :=
      norm_setToSimpleFunc_le_sum_op_norm T f
    _ ≤ ∑ x in f.range, C * (μ (f ⁻¹' {x})).toReal * ‖x‖ :=
      by
      refine' Finset.sum_le_sum fun b hb => _
      obtain rfl | hb := eq_or_ne b 0
      · simp
      exact
        mul_le_mul_of_nonneg_right
          (hT_norm _ (simple_func.measurable_set_fiber _ _) <|
            simple_func.measure_preimage_lt_top_of_integrable _ hf hb)
          (norm_nonneg _)
    _ ≤ C * ∑ x in f.range, (μ (f ⁻¹' {x})).toReal * ‖x‖ := by simp_rw [mul_sum, ← mul_assoc]
    
#align measure_theory.simple_func.norm_set_to_simple_func_le_sum_mul_norm_of_integrable MeasureTheory.SimpleFunc.norm_setToSimpleFunc_le_sum_mul_norm_of_integrable

theorem setToSimpleFunc_indicator (T : Set α → F →L[ℝ] F') (hT_empty : T ∅ = 0)
    {m : MeasurableSpace α} {s : Set α} (hs : MeasurableSet s) (x : F) :
    SimpleFunc.setToSimpleFunc T
        (SimpleFunc.piecewise s hs (SimpleFunc.const α x) (SimpleFunc.const α 0)) =
      T s x :=
  by
  obtain rfl | hs_empty := s.eq_empty_or_nonempty
  ·
    simp only [hT_empty, ContinuousLinearMap.zero_apply, piecewise_empty, const_zero,
      set_to_simple_func_zero_apply]
  simp_rw [set_to_simple_func]
  obtain rfl | hs_univ := eq_or_ne s univ
  · haveI hα := hs_empty.to_type
    simp
  rw [range_indicator hs hs_empty hs_univ]
  by_cases hx0 : x = 0
  · simp_rw [hx0]; simp
  rw [sum_insert]
  swap; · rw [Finset.mem_singleton]; exact hx0
  rw [sum_singleton, (T _).map_zero, add_zero]
  congr
  simp only [coe_piecewise, piecewise_eq_indicator, coe_const, Pi.const_zero,
    piecewise_eq_indicator]
  rw [indicator_preimage, preimage_const_of_mem]
  swap; · exact Set.mem_singleton x
  rw [← Pi.const_zero, preimage_const_of_not_mem]
  swap; · rw [Set.mem_singleton_iff]; exact Ne.symm hx0
  simp
#align measure_theory.simple_func.set_to_simple_func_indicator MeasureTheory.SimpleFunc.setToSimpleFunc_indicator

theorem setToSimpleFunc_const' [Nonempty α] (T : Set α → F →L[ℝ] F') (x : F)
    {m : MeasurableSpace α} : SimpleFunc.setToSimpleFunc T (SimpleFunc.const α x) = T univ x := by
  simp only [set_to_simple_func, range_const, Set.mem_singleton, preimage_const_of_mem,
    sum_singleton, coe_const]
#align measure_theory.simple_func.set_to_simple_func_const' MeasureTheory.SimpleFunc.setToSimpleFunc_const'

theorem setToSimpleFunc_const (T : Set α → F →L[ℝ] F') (hT_empty : T ∅ = 0) (x : F)
    {m : MeasurableSpace α} : SimpleFunc.setToSimpleFunc T (SimpleFunc.const α x) = T univ x :=
  by
  cases hα : isEmpty_or_nonempty α
  · have h_univ_empty : (univ : Set α) = ∅ := Subsingleton.elim _ _
    rw [h_univ_empty, hT_empty]
    simp only [set_to_simple_func, ContinuousLinearMap.zero_apply, sum_empty,
      range_eq_empty_of_is_empty]
  · exact set_to_simple_func_const' T x
#align measure_theory.simple_func.set_to_simple_func_const MeasureTheory.SimpleFunc.setToSimpleFunc_const

end SimpleFunc

namespace L1

open AeEqFun Lp.SimpleFunc Lp

variable {α E μ}

namespace SimpleFunc

theorem norm_eq_sum_mul (f : α →₁ₛ[μ] G) :
    ‖f‖ = ∑ x in (toSimpleFunc f).range, (μ (toSimpleFunc f ⁻¹' {x})).toReal * ‖x‖ :=
  by
  rw [norm_to_simple_func, snorm_one_eq_lintegral_nnnorm]
  have h_eq := simple_func.map_apply (fun x => (‖x‖₊ : ℝ≥0∞)) (to_simple_func f)
  dsimp only at h_eq 
  simp_rw [← h_eq]
  rw [simple_func.lintegral_eq_lintegral, simple_func.map_lintegral, ENNReal.toReal_sum]
  · congr
    ext1 x
    rw [ENNReal.toReal_mul, mul_comm, ← ofReal_norm_eq_coe_nnnorm,
      ENNReal.toReal_ofReal (norm_nonneg _)]
  · intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]; simp
    ·
      exact
        ENNReal.mul_ne_top ENNReal.coe_ne_top
          (simple_func.measure_preimage_lt_top_of_integrable _ (simple_func.integrable f) hx0).Ne
#align measure_theory.L1.simple_func.norm_eq_sum_mul MeasureTheory.L1.SimpleFunc.norm_eq_sum_mul

section SetToL1s

variable [NormedField 𝕜] [NormedSpace 𝕜 E]

attribute [local instance] Lp.simple_func.module

attribute [local instance] Lp.simple_func.normed_space

/-- Extend `set α → (E →L[ℝ] F')` to `(α →₁ₛ[μ] E) → F'`. -/
def setToL1s (T : Set α → E →L[ℝ] F) (f : α →₁ₛ[μ] E) : F :=
  (toSimpleFunc f).setToSimpleFunc T
#align measure_theory.L1.simple_func.set_to_L1s MeasureTheory.L1.SimpleFunc.setToL1s

theorem setToL1s_eq_setToSimpleFunc (T : Set α → E →L[ℝ] F) (f : α →₁ₛ[μ] E) :
    setToL1s T f = (toSimpleFunc f).setToSimpleFunc T :=
  rfl
#align measure_theory.L1.simple_func.set_to_L1s_eq_set_to_simple_func MeasureTheory.L1.SimpleFunc.setToL1s_eq_setToSimpleFunc

@[simp]
theorem setToL1s_zero_left (f : α →₁ₛ[μ] E) : setToL1s (0 : Set α → E →L[ℝ] F) f = 0 :=
  SimpleFunc.setToSimpleFunc_zero _
#align measure_theory.L1.simple_func.set_to_L1s_zero_left MeasureTheory.L1.SimpleFunc.setToL1s_zero_left

theorem setToL1s_zero_left' {T : Set α → E →L[ℝ] F}
    (h_zero : ∀ s, MeasurableSet s → μ s < ∞ → T s = 0) (f : α →₁ₛ[μ] E) : setToL1s T f = 0 :=
  SimpleFunc.setToSimpleFunc_zero' h_zero _ (SimpleFunc.integrable f)
#align measure_theory.L1.simple_func.set_to_L1s_zero_left' MeasureTheory.L1.SimpleFunc.setToL1s_zero_left'

theorem setToL1s_congr (T : Set α → E →L[ℝ] F) (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0)
    (h_add : FinMeasAdditive μ T) {f g : α →₁ₛ[μ] E} (h : toSimpleFunc f =ᵐ[μ] toSimpleFunc g) :
    setToL1s T f = setToL1s T g :=
  SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable f) h
#align measure_theory.L1.simple_func.set_to_L1s_congr MeasureTheory.L1.SimpleFunc.setToL1s_congr

theorem setToL1s_congr_left (T T' : Set α → E →L[ℝ] F)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → T s = T' s) (f : α →₁ₛ[μ] E) :
    setToL1s T f = setToL1s T' f :=
  SimpleFunc.setToSimpleFunc_congr_left T T' h (simpleFunc.toSimpleFunc f) (SimpleFunc.integrable f)
#align measure_theory.L1.simple_func.set_to_L1s_congr_left MeasureTheory.L1.SimpleFunc.setToL1s_congr_left

/-- `set_to_L1s` does not change if we replace the measure `μ` by `μ'` with `μ ≪ μ'`. The statement
uses two functions `f` and `f'` because they have to belong to different types, but morally these
are the same function (we have `f =ᵐ[μ] f'`). -/
theorem setToL1s_congr_measure {μ' : Measure α} (T : Set α → E →L[ℝ] F)
    (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0) (h_add : FinMeasAdditive μ T) (hμ : μ ≪ μ')
    (f : α →₁ₛ[μ] E) (f' : α →₁ₛ[μ'] E) (h : f =ᵐ[μ] f') : setToL1s T f = setToL1s T f' :=
  by
  refine' simple_func.set_to_simple_func_congr T h_zero h_add (simple_func.integrable f) _
  refine' (to_simple_func_eq_to_fun f).trans _
  suffices : f' =ᵐ[μ] ⇑(simple_func.to_simple_func f'); exact h.trans this
  have goal' : f' =ᵐ[μ'] simple_func.to_simple_func f' := (to_simple_func_eq_to_fun f').symm
  exact hμ.ae_eq goal'
#align measure_theory.L1.simple_func.set_to_L1s_congr_measure MeasureTheory.L1.SimpleFunc.setToL1s_congr_measure

theorem setToL1s_add_left (T T' : Set α → E →L[ℝ] F) (f : α →₁ₛ[μ] E) :
    setToL1s (T + T') f = setToL1s T f + setToL1s T' f :=
  SimpleFunc.setToSimpleFunc_add_left T T'
#align measure_theory.L1.simple_func.set_to_L1s_add_left MeasureTheory.L1.SimpleFunc.setToL1s_add_left

theorem setToL1s_add_left' (T T' T'' : Set α → E →L[ℝ] F)
    (h_add : ∀ s, MeasurableSet s → μ s < ∞ → T'' s = T s + T' s) (f : α →₁ₛ[μ] E) :
    setToL1s T'' f = setToL1s T f + setToL1s T' f :=
  SimpleFunc.setToSimpleFunc_add_left' T T' T'' h_add (SimpleFunc.integrable f)
#align measure_theory.L1.simple_func.set_to_L1s_add_left' MeasureTheory.L1.SimpleFunc.setToL1s_add_left'

theorem setToL1s_smul_left (T : Set α → E →L[ℝ] F) (c : ℝ) (f : α →₁ₛ[μ] E) :
    setToL1s (fun s => c • T s) f = c • setToL1s T f :=
  SimpleFunc.setToSimpleFunc_smul_left T c _
#align measure_theory.L1.simple_func.set_to_L1s_smul_left MeasureTheory.L1.SimpleFunc.setToL1s_smul_left

theorem setToL1s_smul_left' (T T' : Set α → E →L[ℝ] F) (c : ℝ)
    (h_smul : ∀ s, MeasurableSet s → μ s < ∞ → T' s = c • T s) (f : α →₁ₛ[μ] E) :
    setToL1s T' f = c • setToL1s T f :=
  SimpleFunc.setToSimpleFunc_smul_left' T T' c h_smul (SimpleFunc.integrable f)
#align measure_theory.L1.simple_func.set_to_L1s_smul_left' MeasureTheory.L1.SimpleFunc.setToL1s_smul_left'

theorem setToL1s_add (T : Set α → E →L[ℝ] F) (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0)
    (h_add : FinMeasAdditive μ T) (f g : α →₁ₛ[μ] E) :
    setToL1s T (f + g) = setToL1s T f + setToL1s T g :=
  by
  simp_rw [set_to_L1s]
  rw [←
    simple_func.set_to_simple_func_add T h_add (simple_func.integrable f)
      (simple_func.integrable g)]
  exact
    simple_func.set_to_simple_func_congr T h_zero h_add (simple_func.integrable _)
      (add_to_simple_func f g)
#align measure_theory.L1.simple_func.set_to_L1s_add MeasureTheory.L1.SimpleFunc.setToL1s_add

theorem setToL1s_neg {T : Set α → E →L[ℝ] F} (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0)
    (h_add : FinMeasAdditive μ T) (f : α →₁ₛ[μ] E) : setToL1s T (-f) = -setToL1s T f :=
  by
  simp_rw [set_to_L1s]
  have : simple_func.to_simple_func (-f) =ᵐ[μ] ⇑(-simple_func.to_simple_func f) :=
    neg_to_simple_func f
  rw [simple_func.set_to_simple_func_congr T h_zero h_add (simple_func.integrable _) this]
  exact simple_func.set_to_simple_func_neg T h_add (simple_func.integrable f)
#align measure_theory.L1.simple_func.set_to_L1s_neg MeasureTheory.L1.SimpleFunc.setToL1s_neg

theorem setToL1s_sub {T : Set α → E →L[ℝ] F} (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0)
    (h_add : FinMeasAdditive μ T) (f g : α →₁ₛ[μ] E) :
    setToL1s T (f - g) = setToL1s T f - setToL1s T g := by
  rw [sub_eq_add_neg, set_to_L1s_add T h_zero h_add, set_to_L1s_neg h_zero h_add, sub_eq_add_neg]
#align measure_theory.L1.simple_func.set_to_L1s_sub MeasureTheory.L1.SimpleFunc.setToL1s_sub

theorem setToL1s_smul_real (T : Set α → E →L[ℝ] F)
    (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0) (h_add : FinMeasAdditive μ T) (c : ℝ)
    (f : α →₁ₛ[μ] E) : setToL1s T (c • f) = c • setToL1s T f :=
  by
  simp_rw [set_to_L1s]
  rw [← simple_func.set_to_simple_func_smul_real T h_add c (simple_func.integrable f)]
  refine' simple_func.set_to_simple_func_congr T h_zero h_add (simple_func.integrable _) _
  exact smul_to_simple_func c f
#align measure_theory.L1.simple_func.set_to_L1s_smul_real MeasureTheory.L1.SimpleFunc.setToL1s_smul_real

theorem setToL1s_smul {E} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
    [NormedSpace 𝕜 F] (T : Set α → E →L[ℝ] F) (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0)
    (h_add : FinMeasAdditive μ T) (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (c : 𝕜)
    (f : α →₁ₛ[μ] E) : setToL1s T (c • f) = c • setToL1s T f :=
  by
  simp_rw [set_to_L1s]
  rw [← simple_func.set_to_simple_func_smul T h_add h_smul c (simple_func.integrable f)]
  refine' simple_func.set_to_simple_func_congr T h_zero h_add (simple_func.integrable _) _
  exact smul_to_simple_func c f
#align measure_theory.L1.simple_func.set_to_L1s_smul MeasureTheory.L1.SimpleFunc.setToL1s_smul

theorem norm_setToL1s_le (T : Set α → E →L[ℝ] F) {C : ℝ}
    (hT_norm : ∀ s, MeasurableSet s → μ s < ∞ → ‖T s‖ ≤ C * (μ s).toReal) (f : α →₁ₛ[μ] E) :
    ‖setToL1s T f‖ ≤ C * ‖f‖ := by
  rw [set_to_L1s, norm_eq_sum_mul f]
  exact
    simple_func.norm_set_to_simple_func_le_sum_mul_norm_of_integrable T hT_norm _
      (simple_func.integrable f)
#align measure_theory.L1.simple_func.norm_set_to_L1s_le MeasureTheory.L1.SimpleFunc.norm_setToL1s_le

theorem setToL1s_indicatorConst {T : Set α → E →L[ℝ] F} {s : Set α}
    (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0) (h_add : FinMeasAdditive μ T)
    (hs : MeasurableSet s) (hμs : μ s < ∞) (x : E) :
    setToL1s T (simpleFunc.indicatorConst 1 hs hμs.Ne x) = T s x :=
  by
  have h_empty : T ∅ = 0 := h_zero _ MeasurableSet.empty measure_empty
  rw [set_to_L1s_eq_set_to_simple_func]
  refine' Eq.trans _ (simple_func.set_to_simple_func_indicator T h_empty hs x)
  refine' simple_func.set_to_simple_func_congr T h_zero h_add (simple_func.integrable _) _
  exact to_simple_func_indicator_const hs hμs.ne x
#align measure_theory.L1.simple_func.set_to_L1s_indicator_const MeasureTheory.L1.SimpleFunc.setToL1s_indicatorConst

theorem setToL1s_const [FiniteMeasure μ] {T : Set α → E →L[ℝ] F}
    (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0) (h_add : FinMeasAdditive μ T) (x : E) :
    setToL1s T (simpleFunc.indicatorConst 1 MeasurableSet.univ (measure_ne_top μ _) x) = T univ x :=
  setToL1s_indicatorConst h_zero h_add MeasurableSet.univ (measure_lt_top _ _) x
#align measure_theory.L1.simple_func.set_to_L1s_const MeasureTheory.L1.SimpleFunc.setToL1s_const

section Order

variable {G'' G' : Type _} [NormedLatticeAddCommGroup G'] [NormedSpace ℝ G']
  [NormedLatticeAddCommGroup G''] [NormedSpace ℝ G''] {T : Set α → G'' →L[ℝ] G'}

theorem setToL1s_mono_left {T T' : Set α → E →L[ℝ] G''} (hTT' : ∀ s x, T s x ≤ T' s x)
    (f : α →₁ₛ[μ] E) : setToL1s T f ≤ setToL1s T' f :=
  SimpleFunc.setToSimpleFunc_mono_left T T' hTT' _
#align measure_theory.L1.simple_func.set_to_L1s_mono_left MeasureTheory.L1.SimpleFunc.setToL1s_mono_left

theorem setToL1s_mono_left' {T T' : Set α → E →L[ℝ] G''}
    (hTT' : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, T s x ≤ T' s x) (f : α →₁ₛ[μ] E) :
    setToL1s T f ≤ setToL1s T' f :=
  SimpleFunc.setToSimpleFunc_mono_left' T T' hTT' _ (SimpleFunc.integrable f)
#align measure_theory.L1.simple_func.set_to_L1s_mono_left' MeasureTheory.L1.SimpleFunc.setToL1s_mono_left'

theorem setToL1s_nonneg (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0)
    (h_add : FinMeasAdditive μ T)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f : α →₁ₛ[μ] G''}
    (hf : 0 ≤ f) : 0 ≤ setToL1s T f := by
  simp_rw [set_to_L1s]
  obtain ⟨f', hf', hff'⟩ : ∃ f' : α →ₛ G'', 0 ≤ f' ∧ simple_func.to_simple_func f =ᵐ[μ] f' :=
    by
    obtain ⟨f'', hf'', hff''⟩ := exists_simple_func_nonneg_ae_eq hf
    exact ⟨f'', hf'', (Lp.simple_func.to_simple_func_eq_to_fun f).trans hff''⟩
  rw [simple_func.set_to_simple_func_congr _ h_zero h_add (simple_func.integrable _) hff']
  exact
    simple_func.set_to_simple_func_nonneg' T hT_nonneg _ hf' ((simple_func.integrable f).congr hff')
#align measure_theory.L1.simple_func.set_to_L1s_nonneg MeasureTheory.L1.SimpleFunc.setToL1s_nonneg

theorem setToL1s_mono (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0)
    (h_add : FinMeasAdditive μ T)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f g : α →₁ₛ[μ] G''}
    (hfg : f ≤ g) : setToL1s T f ≤ setToL1s T g :=
  by
  rw [← sub_nonneg] at hfg ⊢
  rw [← set_to_L1s_sub h_zero h_add]
  exact set_to_L1s_nonneg h_zero h_add hT_nonneg hfg
#align measure_theory.L1.simple_func.set_to_L1s_mono MeasureTheory.L1.SimpleFunc.setToL1s_mono

end Order

variable [NormedSpace 𝕜 F]

variable (α E μ 𝕜)

/-- Extend `set α → E →L[ℝ] F` to `(α →₁ₛ[μ] E) →L[𝕜] F`. -/
def setToL1sClm' {T : Set α → E →L[ℝ] F} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) : (α →₁ₛ[μ] E) →L[𝕜] F :=
  LinearMap.mkContinuous
    ⟨setToL1s T, setToL1s_add T (fun _ => hT.eq_zero_of_measure_zero) hT.1,
      setToL1s_smul T (fun _ => hT.eq_zero_of_measure_zero) hT.1 h_smul⟩
    C fun f => norm_setToL1s_le T hT.2 f
#align measure_theory.L1.simple_func.set_to_L1s_clm' MeasureTheory.L1.SimpleFunc.setToL1sClm'

/-- Extend `set α → E →L[ℝ] F` to `(α →₁ₛ[μ] E) →L[ℝ] F`. -/
def setToL1sClm {T : Set α → E →L[ℝ] F} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C) :
    (α →₁ₛ[μ] E) →L[ℝ] F :=
  LinearMap.mkContinuous
    ⟨setToL1s T, setToL1s_add T (fun _ => hT.eq_zero_of_measure_zero) hT.1,
      setToL1s_smul_real T (fun _ => hT.eq_zero_of_measure_zero) hT.1⟩
    C fun f => norm_setToL1s_le T hT.2 f
#align measure_theory.L1.simple_func.set_to_L1s_clm MeasureTheory.L1.SimpleFunc.setToL1sClm

variable {α E μ 𝕜}

variable {T T' T'' : Set α → E →L[ℝ] F} {C C' C'' : ℝ}

@[simp]
theorem setToL1sClm_zero_left (hT : DominatedFinMeasAdditive μ (0 : Set α → E →L[ℝ] F) C)
    (f : α →₁ₛ[μ] E) : setToL1sClm α E μ hT f = 0 :=
  setToL1s_zero_left _
#align measure_theory.L1.simple_func.set_to_L1s_clm_zero_left MeasureTheory.L1.SimpleFunc.setToL1sClm_zero_left

theorem setToL1sClm_zero_left' (hT : DominatedFinMeasAdditive μ T C)
    (h_zero : ∀ s, MeasurableSet s → μ s < ∞ → T s = 0) (f : α →₁ₛ[μ] E) :
    setToL1sClm α E μ hT f = 0 :=
  setToL1s_zero_left' h_zero f
#align measure_theory.L1.simple_func.set_to_L1s_clm_zero_left' MeasureTheory.L1.SimpleFunc.setToL1sClm_zero_left'

theorem setToL1sClm_congr_left (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (h : T = T') (f : α →₁ₛ[μ] E) :
    setToL1sClm α E μ hT f = setToL1sClm α E μ hT' f :=
  setToL1s_congr_left T T' (fun _ _ _ => by rw [h]) f
#align measure_theory.L1.simple_func.set_to_L1s_clm_congr_left MeasureTheory.L1.SimpleFunc.setToL1sClm_congr_left

theorem setToL1sClm_congr_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (h : ∀ s, MeasurableSet s → μ s < ∞ → T s = T' s)
    (f : α →₁ₛ[μ] E) : setToL1sClm α E μ hT f = setToL1sClm α E μ hT' f :=
  setToL1s_congr_left T T' h f
#align measure_theory.L1.simple_func.set_to_L1s_clm_congr_left' MeasureTheory.L1.SimpleFunc.setToL1sClm_congr_left'

theorem setToL1sClm_congr_measure {μ' : Measure α} (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ' T C') (hμ : μ ≪ μ') (f : α →₁ₛ[μ] E) (f' : α →₁ₛ[μ'] E)
    (h : f =ᵐ[μ] f') : setToL1sClm α E μ hT f = setToL1sClm α E μ' hT' f' :=
  setToL1s_congr_measure T (fun s => hT.eq_zero_of_measure_zero) hT.1 hμ _ _ h
#align measure_theory.L1.simple_func.set_to_L1s_clm_congr_measure MeasureTheory.L1.SimpleFunc.setToL1sClm_congr_measure

theorem setToL1sClm_add_left (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (f : α →₁ₛ[μ] E) :
    setToL1sClm α E μ (hT.add hT') f = setToL1sClm α E μ hT f + setToL1sClm α E μ hT' f :=
  setToL1s_add_left T T' f
#align measure_theory.L1.simple_func.set_to_L1s_clm_add_left MeasureTheory.L1.SimpleFunc.setToL1sClm_add_left

theorem setToL1sClm_add_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (hT'' : DominatedFinMeasAdditive μ T'' C'')
    (h_add : ∀ s, MeasurableSet s → μ s < ∞ → T'' s = T s + T' s) (f : α →₁ₛ[μ] E) :
    setToL1sClm α E μ hT'' f = setToL1sClm α E μ hT f + setToL1sClm α E μ hT' f :=
  setToL1s_add_left' T T' T'' h_add f
#align measure_theory.L1.simple_func.set_to_L1s_clm_add_left' MeasureTheory.L1.SimpleFunc.setToL1sClm_add_left'

theorem setToL1sClm_smul_left (c : ℝ) (hT : DominatedFinMeasAdditive μ T C) (f : α →₁ₛ[μ] E) :
    setToL1sClm α E μ (hT.smul c) f = c • setToL1sClm α E μ hT f :=
  setToL1s_smul_left T c f
#align measure_theory.L1.simple_func.set_to_L1s_clm_smul_left MeasureTheory.L1.SimpleFunc.setToL1sClm_smul_left

theorem setToL1sClm_smul_left' (c : ℝ) (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C')
    (h_smul : ∀ s, MeasurableSet s → μ s < ∞ → T' s = c • T s) (f : α →₁ₛ[μ] E) :
    setToL1sClm α E μ hT' f = c • setToL1sClm α E μ hT f :=
  setToL1s_smul_left' T T' c h_smul f
#align measure_theory.L1.simple_func.set_to_L1s_clm_smul_left' MeasureTheory.L1.SimpleFunc.setToL1sClm_smul_left'

theorem norm_setToL1sClm_le {T : Set α → E →L[ℝ] F} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (hC : 0 ≤ C) : ‖setToL1sClm α E μ hT‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _
#align measure_theory.L1.simple_func.norm_set_to_L1s_clm_le MeasureTheory.L1.SimpleFunc.norm_setToL1sClm_le

theorem norm_setToL1sClm_le' {T : Set α → E →L[ℝ] F} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C) :
    ‖setToL1sClm α E μ hT‖ ≤ max C 0 :=
  LinearMap.mkContinuous_norm_le' _ _
#align measure_theory.L1.simple_func.norm_set_to_L1s_clm_le' MeasureTheory.L1.SimpleFunc.norm_setToL1sClm_le'

theorem setToL1sClm_const [FiniteMeasure μ] {T : Set α → E →L[ℝ] F} {C : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (x : E) :
    setToL1sClm α E μ hT (simpleFunc.indicatorConst 1 MeasurableSet.univ (measure_ne_top μ _) x) =
      T univ x :=
  setToL1s_const (fun s => hT.eq_zero_of_measure_zero) hT.1 x
#align measure_theory.L1.simple_func.set_to_L1s_clm_const MeasureTheory.L1.SimpleFunc.setToL1sClm_const

section Order

variable {G' G'' : Type _} [NormedLatticeAddCommGroup G''] [NormedSpace ℝ G'']
  [NormedLatticeAddCommGroup G'] [NormedSpace ℝ G']

theorem setToL1sClm_mono_left {T T' : Set α → E →L[ℝ] G''} {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (hTT' : ∀ s x, T s x ≤ T' s x) (f : α →₁ₛ[μ] E) :
    setToL1sClm α E μ hT f ≤ setToL1sClm α E μ hT' f :=
  SimpleFunc.setToSimpleFunc_mono_left T T' hTT' _
#align measure_theory.L1.simple_func.set_to_L1s_clm_mono_left MeasureTheory.L1.SimpleFunc.setToL1sClm_mono_left

theorem setToL1sClm_mono_left' {T T' : Set α → E →L[ℝ] G''} {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (hTT' : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, T s x ≤ T' s x) (f : α →₁ₛ[μ] E) :
    setToL1sClm α E μ hT f ≤ setToL1sClm α E μ hT' f :=
  SimpleFunc.setToSimpleFunc_mono_left' T T' hTT' _ (SimpleFunc.integrable f)
#align measure_theory.L1.simple_func.set_to_L1s_clm_mono_left' MeasureTheory.L1.SimpleFunc.setToL1sClm_mono_left'

theorem setToL1sClm_nonneg {T : Set α → G' →L[ℝ] G''} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f : α →₁ₛ[μ] G'}
    (hf : 0 ≤ f) : 0 ≤ setToL1sClm α G' μ hT f :=
  setToL1s_nonneg (fun s => hT.eq_zero_of_measure_zero) hT.1 hT_nonneg hf
#align measure_theory.L1.simple_func.set_to_L1s_clm_nonneg MeasureTheory.L1.SimpleFunc.setToL1sClm_nonneg

theorem setToL1sClm_mono {T : Set α → G' →L[ℝ] G''} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f g : α →₁ₛ[μ] G'}
    (hfg : f ≤ g) : setToL1sClm α G' μ hT f ≤ setToL1sClm α G' μ hT g :=
  setToL1s_mono (fun s => hT.eq_zero_of_measure_zero) hT.1 hT_nonneg hfg
#align measure_theory.L1.simple_func.set_to_L1s_clm_mono MeasureTheory.L1.SimpleFunc.setToL1sClm_mono

end Order

end SetToL1s

end SimpleFunc

open SimpleFunc

section SetToL1

attribute [local instance] Lp.simple_func.module

attribute [local instance] Lp.simple_func.normed_space

variable (𝕜) [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [CompleteSpace F]
  {T T' T'' : Set α → E →L[ℝ] F} {C C' C'' : ℝ}

/-- Extend `set α → (E →L[ℝ] F)` to `(α →₁[μ] E) →L[𝕜] F`. -/
def setToL1' (hT : DominatedFinMeasAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) : (α →₁[μ] E) →L[𝕜] F :=
  (setToL1sClm' α E 𝕜 μ hT h_smul).extend (coeToLp α E 𝕜) (simpleFunc.denseRange one_ne_top)
    simpleFunc.uniformInducing
#align measure_theory.L1.set_to_L1' MeasureTheory.L1.setToL1'

variable {𝕜}

/-- Extend `set α → E →L[ℝ] F` to `(α →₁[μ] E) →L[ℝ] F`. -/
def setToL1 (hT : DominatedFinMeasAdditive μ T C) : (α →₁[μ] E) →L[ℝ] F :=
  (setToL1sClm α E μ hT).extend (coeToLp α E ℝ) (simpleFunc.denseRange one_ne_top)
    simpleFunc.uniformInducing
#align measure_theory.L1.set_to_L1 MeasureTheory.L1.setToL1

theorem setToL1_eq_setToL1sClm (hT : DominatedFinMeasAdditive μ T C) (f : α →₁ₛ[μ] E) :
    setToL1 hT f = setToL1sClm α E μ hT f :=
  uniformly_extend_of_ind simpleFunc.uniformInducing (simpleFunc.denseRange one_ne_top)
    (setToL1sClm α E μ hT).UniformContinuous _
#align measure_theory.L1.set_to_L1_eq_set_to_L1s_clm MeasureTheory.L1.setToL1_eq_setToL1sClm

theorem setToL1_eq_setToL1' (hT : DominatedFinMeasAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (f : α →₁[μ] E) :
    setToL1 hT f = setToL1' 𝕜 hT h_smul f :=
  rfl
#align measure_theory.L1.set_to_L1_eq_set_to_L1' MeasureTheory.L1.setToL1_eq_setToL1'

@[simp]
theorem setToL1_zero_left (hT : DominatedFinMeasAdditive μ (0 : Set α → E →L[ℝ] F) C)
    (f : α →₁[μ] E) : setToL1 hT f = 0 :=
  by
  suffices set_to_L1 hT = 0 by rw [this]; simp
  refine' ContinuousLinearMap.extend_unique (set_to_L1s_clm α E μ hT) _ _ _ _ _
  ext1 f
  rw [set_to_L1s_clm_zero_left hT f, ContinuousLinearMap.zero_comp, ContinuousLinearMap.zero_apply]
#align measure_theory.L1.set_to_L1_zero_left MeasureTheory.L1.setToL1_zero_left

theorem setToL1_zero_left' (hT : DominatedFinMeasAdditive μ T C)
    (h_zero : ∀ s, MeasurableSet s → μ s < ∞ → T s = 0) (f : α →₁[μ] E) : setToL1 hT f = 0 :=
  by
  suffices set_to_L1 hT = 0 by rw [this]; simp
  refine' ContinuousLinearMap.extend_unique (set_to_L1s_clm α E μ hT) _ _ _ _ _
  ext1 f
  rw [set_to_L1s_clm_zero_left' hT h_zero f, ContinuousLinearMap.zero_comp,
    ContinuousLinearMap.zero_apply]
#align measure_theory.L1.set_to_L1_zero_left' MeasureTheory.L1.setToL1_zero_left'

theorem setToL1_congr_left (T T' : Set α → E →L[ℝ] F) {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C') (h : T = T')
    (f : α →₁[μ] E) : setToL1 hT f = setToL1 hT' f :=
  by
  suffices set_to_L1 hT = set_to_L1 hT' by rw [this]
  refine' ContinuousLinearMap.extend_unique (set_to_L1s_clm α E μ hT) _ _ _ _ _
  ext1 f
  suffices set_to_L1 hT' f = set_to_L1s_clm α E μ hT f by rw [← this]; congr 1
  rw [set_to_L1_eq_set_to_L1s_clm]
  exact set_to_L1s_clm_congr_left hT' hT h.symm f
#align measure_theory.L1.set_to_L1_congr_left MeasureTheory.L1.setToL1_congr_left

theorem setToL1_congr_left' (T T' : Set α → E →L[ℝ] F) {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (h : ∀ s, MeasurableSet s → μ s < ∞ → T s = T' s) (f : α →₁[μ] E) :
    setToL1 hT f = setToL1 hT' f :=
  by
  suffices set_to_L1 hT = set_to_L1 hT' by rw [this]
  refine' ContinuousLinearMap.extend_unique (set_to_L1s_clm α E μ hT) _ _ _ _ _
  ext1 f
  suffices set_to_L1 hT' f = set_to_L1s_clm α E μ hT f by rw [← this]; congr 1
  rw [set_to_L1_eq_set_to_L1s_clm]
  exact (set_to_L1s_clm_congr_left' hT hT' h f).symm
#align measure_theory.L1.set_to_L1_congr_left' MeasureTheory.L1.setToL1_congr_left'

theorem setToL1_add_left (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (f : α →₁[μ] E) :
    setToL1 (hT.add hT') f = setToL1 hT f + setToL1 hT' f :=
  by
  suffices set_to_L1 (hT.add hT') = set_to_L1 hT + set_to_L1 hT' by
    rw [this, ContinuousLinearMap.add_apply]
  refine' ContinuousLinearMap.extend_unique (set_to_L1s_clm α E μ (hT.add hT')) _ _ _ _ _
  ext1 f
  simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.add_apply]
  suffices set_to_L1 hT f + set_to_L1 hT' f = set_to_L1s_clm α E μ (hT.add hT') f by rw [← this];
    congr
  rw [set_to_L1_eq_set_to_L1s_clm, set_to_L1_eq_set_to_L1s_clm, set_to_L1s_clm_add_left hT hT']
#align measure_theory.L1.set_to_L1_add_left MeasureTheory.L1.setToL1_add_left

theorem setToL1_add_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (hT'' : DominatedFinMeasAdditive μ T'' C'')
    (h_add : ∀ s, MeasurableSet s → μ s < ∞ → T'' s = T s + T' s) (f : α →₁[μ] E) :
    setToL1 hT'' f = setToL1 hT f + setToL1 hT' f :=
  by
  suffices set_to_L1 hT'' = set_to_L1 hT + set_to_L1 hT' by rw [this, ContinuousLinearMap.add_apply]
  refine' ContinuousLinearMap.extend_unique (set_to_L1s_clm α E μ hT'') _ _ _ _ _
  ext1 f
  simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.add_apply]
  suffices set_to_L1 hT f + set_to_L1 hT' f = set_to_L1s_clm α E μ hT'' f by rw [← this]; congr
  rw [set_to_L1_eq_set_to_L1s_clm, set_to_L1_eq_set_to_L1s_clm,
    set_to_L1s_clm_add_left' hT hT' hT'' h_add]
#align measure_theory.L1.set_to_L1_add_left' MeasureTheory.L1.setToL1_add_left'

theorem setToL1_smul_left (hT : DominatedFinMeasAdditive μ T C) (c : ℝ) (f : α →₁[μ] E) :
    setToL1 (hT.smul c) f = c • setToL1 hT f :=
  by
  suffices set_to_L1 (hT.smul c) = c • set_to_L1 hT by rw [this, ContinuousLinearMap.smul_apply]
  refine' ContinuousLinearMap.extend_unique (set_to_L1s_clm α E μ (hT.smul c)) _ _ _ _ _
  ext1 f
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.smul_comp,
    Pi.smul_apply, ContinuousLinearMap.coe_smul']
  suffices c • set_to_L1 hT f = set_to_L1s_clm α E μ (hT.smul c) f by rw [← this]; congr
  rw [set_to_L1_eq_set_to_L1s_clm, set_to_L1s_clm_smul_left c hT]
#align measure_theory.L1.set_to_L1_smul_left MeasureTheory.L1.setToL1_smul_left

theorem setToL1_smul_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (c : ℝ)
    (h_smul : ∀ s, MeasurableSet s → μ s < ∞ → T' s = c • T s) (f : α →₁[μ] E) :
    setToL1 hT' f = c • setToL1 hT f :=
  by
  suffices set_to_L1 hT' = c • set_to_L1 hT by rw [this, ContinuousLinearMap.smul_apply]
  refine' ContinuousLinearMap.extend_unique (set_to_L1s_clm α E μ hT') _ _ _ _ _
  ext1 f
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.smul_comp,
    Pi.smul_apply, ContinuousLinearMap.coe_smul']
  suffices c • set_to_L1 hT f = set_to_L1s_clm α E μ hT' f by rw [← this]; congr
  rw [set_to_L1_eq_set_to_L1s_clm, set_to_L1s_clm_smul_left' c hT hT' h_smul]
#align measure_theory.L1.set_to_L1_smul_left' MeasureTheory.L1.setToL1_smul_left'

theorem setToL1_smul (hT : DominatedFinMeasAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (c : 𝕜) (f : α →₁[μ] E) :
    setToL1 hT (c • f) = c • setToL1 hT f :=
  by
  rw [set_to_L1_eq_set_to_L1' hT h_smul, set_to_L1_eq_set_to_L1' hT h_smul]
  exact ContinuousLinearMap.map_smul _ _ _
#align measure_theory.L1.set_to_L1_smul MeasureTheory.L1.setToL1_smul

theorem setToL1_simpleFunc_indicatorConst (hT : DominatedFinMeasAdditive μ T C) {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s < ∞) (x : E) :
    setToL1 hT (simpleFunc.indicatorConst 1 hs hμs.Ne x) = T s x :=
  by
  rw [set_to_L1_eq_set_to_L1s_clm]
  exact set_to_L1s_indicator_const (fun s => hT.eq_zero_of_measure_zero) hT.1 hs hμs x
#align measure_theory.L1.set_to_L1_simple_func_indicator_const MeasureTheory.L1.setToL1_simpleFunc_indicatorConst

theorem setToL1_indicatorConstLp (hT : DominatedFinMeasAdditive μ T C) {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E) :
    setToL1 hT (indicatorConstLp 1 hs hμs x) = T s x :=
  by
  rw [← Lp.simple_func.coe_indicator_const hs hμs x]
  exact set_to_L1_simple_func_indicator_const hT hs hμs.lt_top x
#align measure_theory.L1.set_to_L1_indicator_const_Lp MeasureTheory.L1.setToL1_indicatorConstLp

theorem setToL1_const [FiniteMeasure μ] (hT : DominatedFinMeasAdditive μ T C) (x : E) :
    setToL1 hT (indicatorConstLp 1 MeasurableSet.univ (measure_ne_top _ _) x) = T univ x :=
  setToL1_indicatorConstLp hT MeasurableSet.univ (measure_ne_top _ _) x
#align measure_theory.L1.set_to_L1_const MeasureTheory.L1.setToL1_const

section Order

variable {G' G'' : Type _} [NormedLatticeAddCommGroup G''] [NormedSpace ℝ G''] [CompleteSpace G'']
  [NormedLatticeAddCommGroup G'] [NormedSpace ℝ G']

theorem setToL1_mono_left' {T T' : Set α → E →L[ℝ] G''} {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (hTT' : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, T s x ≤ T' s x) (f : α →₁[μ] E) :
    setToL1 hT f ≤ setToL1 hT' f :=
  by
  refine' Lp.induction one_ne_top _ _ _ _ f
  · intro c s hs hμs
    rw [set_to_L1_simple_func_indicator_const hT hs hμs,
      set_to_L1_simple_func_indicator_const hT' hs hμs]
    exact hTT' s hs hμs c
  · intro f g hf hg hfg_disj hf_le hg_le
    rw [(set_to_L1 hT).map_add, (set_to_L1 hT').map_add]
    exact add_le_add hf_le hg_le
  · exact isClosed_le (set_to_L1 hT).Continuous (set_to_L1 hT').Continuous
#align measure_theory.L1.set_to_L1_mono_left' MeasureTheory.L1.setToL1_mono_left'

theorem setToL1_mono_left {T T' : Set α → E →L[ℝ] G''} {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (hTT' : ∀ s x, T s x ≤ T' s x) (f : α →₁[μ] E) : setToL1 hT f ≤ setToL1 hT' f :=
  setToL1_mono_left' hT hT' (fun s _ _ x => hTT' s x) f
#align measure_theory.L1.set_to_L1_mono_left MeasureTheory.L1.setToL1_mono_left

theorem setToL1_nonneg {T : Set α → G' →L[ℝ] G''} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f : α →₁[μ] G'}
    (hf : 0 ≤ f) : 0 ≤ setToL1 hT f :=
  by
  suffices : ∀ f : { g : α →₁[μ] G' // 0 ≤ g }, 0 ≤ set_to_L1 hT f
  exact this (⟨f, hf⟩ : { g : α →₁[μ] G' // 0 ≤ g })
  refine' fun g =>
    @isClosed_property { g : α →₁ₛ[μ] G' // 0 ≤ g } { g : α →₁[μ] G' // 0 ≤ g } _ _ _
      (dense_range_coe_simple_func_nonneg_to_Lp_nonneg 1 μ G' one_ne_top) _ _ g
  · exact isClosed_le continuous_zero ((set_to_L1 hT).Continuous.comp continuous_induced_dom)
  · intro g
    have : (coe_simple_func_nonneg_to_Lp_nonneg 1 μ G' g : α →₁[μ] G') = (g : α →₁ₛ[μ] G') := rfl
    rw [this, set_to_L1_eq_set_to_L1s_clm]
    exact set_to_L1s_nonneg (fun s => hT.eq_zero_of_measure_zero) hT.1 hT_nonneg g.2
#align measure_theory.L1.set_to_L1_nonneg MeasureTheory.L1.setToL1_nonneg

theorem setToL1_mono {T : Set α → G' →L[ℝ] G''} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f g : α →₁[μ] G'}
    (hfg : f ≤ g) : setToL1 hT f ≤ setToL1 hT g :=
  by
  rw [← sub_nonneg] at hfg ⊢
  rw [← (set_to_L1 hT).map_sub]
  exact set_to_L1_nonneg hT hT_nonneg hfg
#align measure_theory.L1.set_to_L1_mono MeasureTheory.L1.setToL1_mono

end Order

theorem norm_setToL1_le_norm_setToL1sClm (hT : DominatedFinMeasAdditive μ T C) :
    ‖setToL1 hT‖ ≤ ‖setToL1sClm α E μ hT‖ :=
  calc
    ‖setToL1 hT‖ ≤ (1 : ℝ≥0) * ‖setToL1sClm α E μ hT‖ :=
      by
      refine'
        ContinuousLinearMap.op_norm_extend_le (set_to_L1s_clm α E μ hT) (coe_to_Lp α E ℝ)
          (simple_func.dense_range one_ne_top) fun x => le_of_eq _
      rw [NNReal.coe_one, one_mul]
      rfl
    _ = ‖setToL1sClm α E μ hT‖ := by rw [NNReal.coe_one, one_mul]
    
#align measure_theory.L1.norm_set_to_L1_le_norm_set_to_L1s_clm MeasureTheory.L1.norm_setToL1_le_norm_setToL1sClm

theorem norm_setToL1_le_mul_norm (hT : DominatedFinMeasAdditive μ T C) (hC : 0 ≤ C)
    (f : α →₁[μ] E) : ‖setToL1 hT f‖ ≤ C * ‖f‖ :=
  calc
    ‖setToL1 hT f‖ ≤ ‖setToL1sClm α E μ hT‖ * ‖f‖ :=
      ContinuousLinearMap.le_of_op_norm_le _ (norm_setToL1_le_norm_setToL1sClm hT) _
    _ ≤ C * ‖f‖ := mul_le_mul (norm_setToL1sClm_le hT hC) le_rfl (norm_nonneg _) hC
    
#align measure_theory.L1.norm_set_to_L1_le_mul_norm MeasureTheory.L1.norm_setToL1_le_mul_norm

theorem norm_setToL1_le_mul_norm' (hT : DominatedFinMeasAdditive μ T C) (f : α →₁[μ] E) :
    ‖setToL1 hT f‖ ≤ max C 0 * ‖f‖ :=
  calc
    ‖setToL1 hT f‖ ≤ ‖setToL1sClm α E μ hT‖ * ‖f‖ :=
      ContinuousLinearMap.le_of_op_norm_le _ (norm_setToL1_le_norm_setToL1sClm hT) _
    _ ≤ max C 0 * ‖f‖ :=
      mul_le_mul (norm_setToL1sClm_le' hT) le_rfl (norm_nonneg _) (le_max_right _ _)
    
#align measure_theory.L1.norm_set_to_L1_le_mul_norm' MeasureTheory.L1.norm_setToL1_le_mul_norm'

theorem norm_setToL1_le (hT : DominatedFinMeasAdditive μ T C) (hC : 0 ≤ C) : ‖setToL1 hT‖ ≤ C :=
  ContinuousLinearMap.op_norm_le_bound _ hC (norm_setToL1_le_mul_norm hT hC)
#align measure_theory.L1.norm_set_to_L1_le MeasureTheory.L1.norm_setToL1_le

theorem norm_setToL1_le' (hT : DominatedFinMeasAdditive μ T C) : ‖setToL1 hT‖ ≤ max C 0 :=
  ContinuousLinearMap.op_norm_le_bound _ (le_max_right _ _) (norm_setToL1_le_mul_norm' hT)
#align measure_theory.L1.norm_set_to_L1_le' MeasureTheory.L1.norm_setToL1_le'

theorem setToL1_lipschitz (hT : DominatedFinMeasAdditive μ T C) :
    LipschitzWith (Real.toNNReal C) (setToL1 hT) :=
  (setToL1 hT).lipschitz.weaken (norm_setToL1_le' hT)
#align measure_theory.L1.set_to_L1_lipschitz MeasureTheory.L1.setToL1_lipschitz

/-- If `fs i → f` in `L1`, then `set_to_L1 hT (fs i) → set_to_L1 hT f`. -/
theorem tendsto_setToL1 (hT : DominatedFinMeasAdditive μ T C) (f : α →₁[μ] E) {ι}
    (fs : ι → α →₁[μ] E) {l : Filter ι} (hfs : Tendsto fs l (𝓝 f)) :
    Tendsto (fun i => setToL1 hT (fs i)) l (𝓝 <| setToL1 hT f) :=
  ((setToL1 hT).Continuous.Tendsto _).comp hfs
#align measure_theory.L1.tendsto_set_to_L1 MeasureTheory.L1.tendsto_setToL1

end SetToL1

end L1

section Function

variable [CompleteSpace F] {T T' T'' : Set α → E →L[ℝ] F} {C C' C'' : ℝ} {f g : α → E}

variable (μ T)

/-- Extend `T : set α → E →L[ℝ] F` to `(α → E) → F` (for integrable functions `α → E`). We set it to
0 if the function is not integrable. -/
def setToFun (hT : DominatedFinMeasAdditive μ T C) (f : α → E) : F :=
  if hf : Integrable f μ then L1.setToL1 hT (hf.toL1 f) else 0
#align measure_theory.set_to_fun MeasureTheory.setToFun

variable {μ T}

theorem setToFun_eq (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ) :
    setToFun μ T hT f = L1.setToL1 hT (hf.toL1 f) :=
  dif_pos hf
#align measure_theory.set_to_fun_eq MeasureTheory.setToFun_eq

theorem L1.setToFun_eq_setToL1 (hT : DominatedFinMeasAdditive μ T C) (f : α →₁[μ] E) :
    setToFun μ T hT f = L1.setToL1 hT f := by
  rw [set_to_fun_eq hT (L1.integrable_coe_fn f), integrable.to_L1_coe_fn]
#align measure_theory.L1.set_to_fun_eq_set_to_L1 MeasureTheory.L1.setToFun_eq_setToL1

theorem setToFun_undef (hT : DominatedFinMeasAdditive μ T C) (hf : ¬Integrable f μ) :
    setToFun μ T hT f = 0 :=
  dif_neg hf
#align measure_theory.set_to_fun_undef MeasureTheory.setToFun_undef

theorem setToFun_non_aEStronglyMeasurable (hT : DominatedFinMeasAdditive μ T C)
    (hf : ¬AEStronglyMeasurable f μ) : setToFun μ T hT f = 0 :=
  setToFun_undef hT (not_and_of_not_left _ hf)
#align measure_theory.set_to_fun_non_ae_strongly_measurable MeasureTheory.setToFun_non_aEStronglyMeasurable

theorem setToFun_congr_left (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (h : T = T') (f : α → E) :
    setToFun μ T hT f = setToFun μ T' hT' f :=
  by
  by_cases hf : integrable f μ
  · simp_rw [set_to_fun_eq _ hf, L1.set_to_L1_congr_left T T' hT hT' h]
  · simp_rw [set_to_fun_undef _ hf]
#align measure_theory.set_to_fun_congr_left MeasureTheory.setToFun_congr_left

theorem setToFun_congr_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (h : ∀ s, MeasurableSet s → μ s < ∞ → T s = T' s)
    (f : α → E) : setToFun μ T hT f = setToFun μ T' hT' f :=
  by
  by_cases hf : integrable f μ
  · simp_rw [set_to_fun_eq _ hf, L1.set_to_L1_congr_left' T T' hT hT' h]
  · simp_rw [set_to_fun_undef _ hf]
#align measure_theory.set_to_fun_congr_left' MeasureTheory.setToFun_congr_left'

theorem setToFun_add_left (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (f : α → E) :
    setToFun μ (T + T') (hT.add hT') f = setToFun μ T hT f + setToFun μ T' hT' f :=
  by
  by_cases hf : integrable f μ
  · simp_rw [set_to_fun_eq _ hf, L1.set_to_L1_add_left hT hT']
  · simp_rw [set_to_fun_undef _ hf, add_zero]
#align measure_theory.set_to_fun_add_left MeasureTheory.setToFun_add_left

theorem setToFun_add_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (hT'' : DominatedFinMeasAdditive μ T'' C'')
    (h_add : ∀ s, MeasurableSet s → μ s < ∞ → T'' s = T s + T' s) (f : α → E) :
    setToFun μ T'' hT'' f = setToFun μ T hT f + setToFun μ T' hT' f :=
  by
  by_cases hf : integrable f μ
  · simp_rw [set_to_fun_eq _ hf, L1.set_to_L1_add_left' hT hT' hT'' h_add]
  · simp_rw [set_to_fun_undef _ hf, add_zero]
#align measure_theory.set_to_fun_add_left' MeasureTheory.setToFun_add_left'

theorem setToFun_smul_left (hT : DominatedFinMeasAdditive μ T C) (c : ℝ) (f : α → E) :
    setToFun μ (fun s => c • T s) (hT.smul c) f = c • setToFun μ T hT f :=
  by
  by_cases hf : integrable f μ
  · simp_rw [set_to_fun_eq _ hf, L1.set_to_L1_smul_left hT c]
  · simp_rw [set_to_fun_undef _ hf, smul_zero]
#align measure_theory.set_to_fun_smul_left MeasureTheory.setToFun_smul_left

theorem setToFun_smul_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (c : ℝ)
    (h_smul : ∀ s, MeasurableSet s → μ s < ∞ → T' s = c • T s) (f : α → E) :
    setToFun μ T' hT' f = c • setToFun μ T hT f :=
  by
  by_cases hf : integrable f μ
  · simp_rw [set_to_fun_eq _ hf, L1.set_to_L1_smul_left' hT hT' c h_smul]
  · simp_rw [set_to_fun_undef _ hf, smul_zero]
#align measure_theory.set_to_fun_smul_left' MeasureTheory.setToFun_smul_left'

@[simp]
theorem setToFun_zero (hT : DominatedFinMeasAdditive μ T C) : setToFun μ T hT (0 : α → E) = 0 :=
  by
  rw [set_to_fun_eq hT]
  · simp only [integrable.to_L1_zero, ContinuousLinearMap.map_zero]
  · exact integrable_zero _ _ _
#align measure_theory.set_to_fun_zero MeasureTheory.setToFun_zero

@[simp]
theorem setToFun_zero_left {hT : DominatedFinMeasAdditive μ (0 : Set α → E →L[ℝ] F) C} :
    setToFun μ 0 hT f = 0 := by
  by_cases hf : integrable f μ
  · rw [set_to_fun_eq hT hf]; exact L1.set_to_L1_zero_left hT _
  · exact set_to_fun_undef hT hf
#align measure_theory.set_to_fun_zero_left MeasureTheory.setToFun_zero_left

theorem setToFun_zero_left' (hT : DominatedFinMeasAdditive μ T C)
    (h_zero : ∀ s, MeasurableSet s → μ s < ∞ → T s = 0) : setToFun μ T hT f = 0 :=
  by
  by_cases hf : integrable f μ
  · rw [set_to_fun_eq hT hf]; exact L1.set_to_L1_zero_left' hT h_zero _
  · exact set_to_fun_undef hT hf
#align measure_theory.set_to_fun_zero_left' MeasureTheory.setToFun_zero_left'

theorem setToFun_add (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ)
    (hg : Integrable g μ) : setToFun μ T hT (f + g) = setToFun μ T hT f + setToFun μ T hT g := by
  rw [set_to_fun_eq hT (hf.add hg), set_to_fun_eq hT hf, set_to_fun_eq hT hg, integrable.to_L1_add,
    (L1.set_to_L1 hT).map_add]
#align measure_theory.set_to_fun_add MeasureTheory.setToFun_add

theorem setToFun_finset_sum' (hT : DominatedFinMeasAdditive μ T C) {ι} (s : Finset ι)
    {f : ι → α → E} (hf : ∀ i ∈ s, Integrable (f i) μ) :
    setToFun μ T hT (∑ i in s, f i) = ∑ i in s, setToFun μ T hT (f i) :=
  by
  revert hf
  refine' Finset.induction_on s _ _
  · intro h
    simp only [set_to_fun_zero, Finset.sum_empty]
  · intro i s his ih hf
    simp only [his, Finset.sum_insert, not_false_iff]
    rw [set_to_fun_add hT (hf i (Finset.mem_insert_self i s)) _]
    · rw [ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]
    · convert integrable_finset_sum s fun i hi => hf i (Finset.mem_insert_of_mem hi)
      ext1 x
      simp
#align measure_theory.set_to_fun_finset_sum' MeasureTheory.setToFun_finset_sum'

theorem setToFun_finset_sum (hT : DominatedFinMeasAdditive μ T C) {ι} (s : Finset ι) {f : ι → α → E}
    (hf : ∀ i ∈ s, Integrable (f i) μ) :
    (setToFun μ T hT fun a => ∑ i in s, f i a) = ∑ i in s, setToFun μ T hT (f i) := by
  convert set_to_fun_finset_sum' hT s hf; ext1 a; simp
#align measure_theory.set_to_fun_finset_sum MeasureTheory.setToFun_finset_sum

theorem setToFun_neg (hT : DominatedFinMeasAdditive μ T C) (f : α → E) :
    setToFun μ T hT (-f) = -setToFun μ T hT f :=
  by
  by_cases hf : integrable f μ
  ·
    rw [set_to_fun_eq hT hf, set_to_fun_eq hT hf.neg, integrable.to_L1_neg,
      (L1.set_to_L1 hT).map_neg]
  · rw [set_to_fun_undef hT hf, set_to_fun_undef hT, neg_zero]
    rwa [← integrable_neg_iff] at hf 
#align measure_theory.set_to_fun_neg MeasureTheory.setToFun_neg

theorem setToFun_sub (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ)
    (hg : Integrable g μ) : setToFun μ T hT (f - g) = setToFun μ T hT f - setToFun μ T hT g := by
  rw [sub_eq_add_neg, sub_eq_add_neg, set_to_fun_add hT hf hg.neg, set_to_fun_neg hT g]
#align measure_theory.set_to_fun_sub MeasureTheory.setToFun_sub

theorem setToFun_smul [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (hT : DominatedFinMeasAdditive μ T C) (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (c : 𝕜)
    (f : α → E) : setToFun μ T hT (c • f) = c • setToFun μ T hT f :=
  by
  by_cases hf : integrable f μ
  ·
    rw [set_to_fun_eq hT hf, set_to_fun_eq hT, integrable.to_L1_smul',
      L1.set_to_L1_smul hT h_smul c _]
  · by_cases hr : c = 0
    · rw [hr]; simp
    · have hf' : ¬integrable (c • f) μ := by rwa [integrable_smul_iff hr f]
      rw [set_to_fun_undef hT hf, set_to_fun_undef hT hf', smul_zero]
#align measure_theory.set_to_fun_smul MeasureTheory.setToFun_smul

theorem setToFun_congr_ae (hT : DominatedFinMeasAdditive μ T C) (h : f =ᵐ[μ] g) :
    setToFun μ T hT f = setToFun μ T hT g :=
  by
  by_cases hfi : integrable f μ
  · have hgi : integrable g μ := hfi.congr h
    rw [set_to_fun_eq hT hfi, set_to_fun_eq hT hgi, (integrable.to_L1_eq_to_L1_iff f g hfi hgi).2 h]
  · have hgi : ¬integrable g μ := by rw [integrable_congr h] at hfi ; exact hfi
    rw [set_to_fun_undef hT hfi, set_to_fun_undef hT hgi]
#align measure_theory.set_to_fun_congr_ae MeasureTheory.setToFun_congr_ae

theorem setToFun_measure_zero (hT : DominatedFinMeasAdditive μ T C) (h : μ = 0) :
    setToFun μ T hT f = 0 := by have : f =ᵐ[μ] 0 := by simp [h];
  rw [set_to_fun_congr_ae hT this, set_to_fun_zero]
#align measure_theory.set_to_fun_measure_zero MeasureTheory.setToFun_measure_zero

theorem setToFun_measure_zero' (hT : DominatedFinMeasAdditive μ T C)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → μ s = 0) : setToFun μ T hT f = 0 :=
  setToFun_zero_left' hT fun s hs hμs => hT.eq_zero_of_measure_zero hs (h s hs hμs)
#align measure_theory.set_to_fun_measure_zero' MeasureTheory.setToFun_measure_zero'

theorem setToFun_toL1 (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ) :
    setToFun μ T hT (hf.toL1 f) = setToFun μ T hT f :=
  setToFun_congr_ae hT hf.coeFn_toL1
#align measure_theory.set_to_fun_to_L1 MeasureTheory.setToFun_toL1

theorem setToFun_indicator_const (hT : DominatedFinMeasAdditive μ T C) {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E) :
    setToFun μ T hT (s.indicator fun _ => x) = T s x :=
  by
  rw [set_to_fun_congr_ae hT (@indicator_const_Lp_coe_fn _ _ _ 1 _ _ _ hs hμs x).symm]
  rw [L1.set_to_fun_eq_set_to_L1 hT]
  exact L1.set_to_L1_indicator_const_Lp hT hs hμs x
#align measure_theory.set_to_fun_indicator_const MeasureTheory.setToFun_indicator_const

theorem setToFun_const [FiniteMeasure μ] (hT : DominatedFinMeasAdditive μ T C) (x : E) :
    (setToFun μ T hT fun _ => x) = T univ x :=
  by
  have : (fun _ : α => x) = Set.indicator univ fun _ => x := (indicator_univ _).symm
  rw [this]
  exact set_to_fun_indicator_const hT MeasurableSet.univ (measure_ne_top _ _) x
#align measure_theory.set_to_fun_const MeasureTheory.setToFun_const

section Order

variable {G' G'' : Type _} [NormedLatticeAddCommGroup G''] [NormedSpace ℝ G''] [CompleteSpace G'']
  [NormedLatticeAddCommGroup G'] [NormedSpace ℝ G']

theorem setToFun_mono_left' {T T' : Set α → E →L[ℝ] G''} {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (hTT' : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, T s x ≤ T' s x) (f : α → E) :
    setToFun μ T hT f ≤ setToFun μ T' hT' f :=
  by
  by_cases hf : integrable f μ
  · simp_rw [set_to_fun_eq _ hf]; exact L1.set_to_L1_mono_left' hT hT' hTT' _
  · simp_rw [set_to_fun_undef _ hf]
#align measure_theory.set_to_fun_mono_left' MeasureTheory.setToFun_mono_left'

theorem setToFun_mono_left {T T' : Set α → E →L[ℝ] G''} {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (hTT' : ∀ s x, T s x ≤ T' s x) (f : α →₁[μ] E) : setToFun μ T hT f ≤ setToFun μ T' hT' f :=
  setToFun_mono_left' hT hT' (fun s _ _ x => hTT' s x) f
#align measure_theory.set_to_fun_mono_left MeasureTheory.setToFun_mono_left

theorem setToFun_nonneg {T : Set α → G' →L[ℝ] G''} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f : α → G'}
    (hf : 0 ≤ᵐ[μ] f) : 0 ≤ setToFun μ T hT f :=
  by
  by_cases hfi : integrable f μ
  · simp_rw [set_to_fun_eq _ hfi]
    refine' L1.set_to_L1_nonneg hT hT_nonneg _
    rw [← Lp.coe_fn_le]
    have h0 := Lp.coe_fn_zero G' 1 μ
    have h := integrable.coe_fn_to_L1 hfi
    filter_upwards [h0, h, hf]with _ h0a ha hfa
    rw [h0a, ha]
    exact hfa
  · simp_rw [set_to_fun_undef _ hfi]
#align measure_theory.set_to_fun_nonneg MeasureTheory.setToFun_nonneg

theorem setToFun_mono {T : Set α → G' →L[ℝ] G''} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f g : α → G'}
    (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g) :
    setToFun μ T hT f ≤ setToFun μ T hT g :=
  by
  rw [← sub_nonneg, ← set_to_fun_sub hT hg hf]
  refine' set_to_fun_nonneg hT hT_nonneg (hfg.mono fun a ha => _)
  rw [Pi.sub_apply, Pi.zero_apply, sub_nonneg]
  exact ha
#align measure_theory.set_to_fun_mono MeasureTheory.setToFun_mono

end Order

@[continuity]
theorem continuous_setToFun (hT : DominatedFinMeasAdditive μ T C) :
    Continuous fun f : α →₁[μ] E => setToFun μ T hT f := by simp_rw [L1.set_to_fun_eq_set_to_L1 hT];
  exact ContinuousLinearMap.continuous _
#align measure_theory.continuous_set_to_fun MeasureTheory.continuous_setToFun

/-- If `F i → f` in `L1`, then `set_to_fun μ T hT (F i) → set_to_fun μ T hT f`. -/
theorem tendsto_setToFun_of_L1 (hT : DominatedFinMeasAdditive μ T C) {ι} (f : α → E)
    (hfi : Integrable f μ) {fs : ι → α → E} {l : Filter ι} (hfsi : ∀ᶠ i in l, Integrable (fs i) μ)
    (hfs : Tendsto (fun i => ∫⁻ x, ‖fs i x - f x‖₊ ∂μ) l (𝓝 0)) :
    Tendsto (fun i => setToFun μ T hT (fs i)) l (𝓝 <| setToFun μ T hT f) := by
  classical
    let f_lp := hfi.to_L1 f
    let F_lp i := if hFi : integrable (fs i) μ then hFi.toL1 (fs i) else 0
    have tendsto_L1 : tendsto F_lp l (𝓝 f_lp) :=
      by
      rw [Lp.tendsto_Lp_iff_tendsto_ℒp']
      simp_rw [snorm_one_eq_lintegral_nnnorm, Pi.sub_apply]
      refine' (tendsto_congr' _).mp hfs
      filter_upwards [hfsi]with i hi
      refine' lintegral_congr_ae _
      filter_upwards [hi.coe_fn_to_L1, hfi.coe_fn_to_L1]with x hxi hxf
      simp_rw [F_lp, dif_pos hi, hxi, hxf]
    suffices tendsto (fun i => set_to_fun μ T hT (F_lp i)) l (𝓝 (set_to_fun μ T hT f))
      by
      refine' (tendsto_congr' _).mp this
      filter_upwards [hfsi]with i hi
      suffices h_ae_eq : F_lp i =ᵐ[μ] fs i; exact set_to_fun_congr_ae hT h_ae_eq
      simp_rw [F_lp, dif_pos hi]
      exact hi.coe_fn_to_L1
    rw [set_to_fun_congr_ae hT hfi.coe_fn_to_L1.symm]
    exact ((continuous_set_to_fun hT).Tendsto f_lp).comp tendsto_L1
#align measure_theory.tendsto_set_to_fun_of_L1 MeasureTheory.tendsto_setToFun_of_L1

theorem tendsto_setToFun_approxOn_of_measurable (hT : DominatedFinMeasAdditive μ T C)
    [MeasurableSpace E] [BorelSpace E] {f : α → E} {s : Set E} [SeparableSpace s]
    (hfi : Integrable f μ) (hfm : Measurable f) (hs : ∀ᵐ x ∂μ, f x ∈ closure s) {y₀ : E}
    (h₀ : y₀ ∈ s) (h₀i : Integrable (fun x => y₀) μ) :
    Tendsto (fun n => setToFun μ T hT (SimpleFunc.approxOn f hfm s y₀ h₀ n)) atTop
      (𝓝 <| setToFun μ T hT f) :=
  tendsto_setToFun_of_L1 hT _ hfi
    (eventually_of_forall (SimpleFunc.integrable_approxOn hfm hfi h₀ h₀i))
    (SimpleFunc.tendsto_approxOn_L1_nnnorm hfm _ hs (hfi.sub h₀i).2)
#align measure_theory.tendsto_set_to_fun_approx_on_of_measurable MeasureTheory.tendsto_setToFun_approxOn_of_measurable

theorem tendsto_setToFun_approxOn_of_measurable_of_range_subset
    (hT : DominatedFinMeasAdditive μ T C) [MeasurableSpace E] [BorelSpace E] {f : α → E}
    (fmeas : Measurable f) (hf : Integrable f μ) (s : Set E) [SeparableSpace s]
    (hs : range f ∪ {0} ⊆ s) :
    Tendsto (fun n => setToFun μ T hT (SimpleFunc.approxOn f fmeas s 0 (hs <| by simp) n)) atTop
      (𝓝 <| setToFun μ T hT f) :=
  by
  refine' tendsto_set_to_fun_approx_on_of_measurable hT hf fmeas _ _ (integrable_zero _ _ _)
  exact eventually_of_forall fun x => subset_closure (hs (Set.mem_union_left _ (mem_range_self _)))
#align measure_theory.tendsto_set_to_fun_approx_on_of_measurable_of_range_subset MeasureTheory.tendsto_setToFun_approxOn_of_measurable_of_range_subset

/-- Auxiliary lemma for `set_to_fun_congr_measure`: the function sending `f : α →₁[μ] G` to
`f : α →₁[μ'] G` is continuous when `μ' ≤ c' • μ` for `c' ≠ ∞`. -/
theorem continuous_L1_toL1 {μ' : Measure α} (c' : ℝ≥0∞) (hc' : c' ≠ ∞) (hμ'_le : μ' ≤ c' • μ) :
    Continuous fun f : α →₁[μ] G =>
      (Integrable.of_measure_le_smul c' hc' hμ'_le (L1.integrable_coeFn f)).toL1 f :=
  by
  by_cases hc'0 : c' = 0
  · have hμ'0 : μ' = 0 := by rw [← measure.nonpos_iff_eq_zero']; refine' hμ'_le.trans _; simp [hc'0]
    have h_im_zero :
      (fun f : α →₁[μ] G =>
          (integrable.of_measure_le_smul c' hc' hμ'_le (L1.integrable_coe_fn f)).toL1 f) =
        0 :=
      by ext1 f; ext1; simp_rw [hμ'0]; simp only [ae_zero]
    rw [h_im_zero]
    exact continuous_zero
  rw [Metric.continuous_iff]
  intro f ε hε_pos
  use ε / 2 / c'.to_real
  refine' ⟨div_pos (half_pos hε_pos) (to_real_pos hc'0 hc'), _⟩
  intro g hfg
  rw [Lp.dist_def] at hfg ⊢
  let h_int := fun f' : α →₁[μ] G => (L1.integrable_coe_fn f').of_measure_le_smul c' hc' hμ'_le
  have :
    snorm (integrable.to_L1 g (h_int g) - integrable.to_L1 f (h_int f)) 1 μ' = snorm (g - f) 1 μ' :=
    snorm_congr_ae ((integrable.coe_fn_to_L1 _).sub (integrable.coe_fn_to_L1 _))
  rw [this]
  have h_snorm_ne_top : snorm (g - f) 1 μ ≠ ∞ := by rw [← snorm_congr_ae (Lp.coe_fn_sub _ _)];
    exact Lp.snorm_ne_top _
  have h_snorm_ne_top' : snorm (g - f) 1 μ' ≠ ∞ :=
    by
    refine' ((snorm_mono_measure _ hμ'_le).trans_lt _).Ne
    rw [snorm_smul_measure_of_ne_zero hc'0, smul_eq_mul]
    refine' ENNReal.mul_lt_top _ h_snorm_ne_top
    simp [hc', hc'0]
  calc
    (snorm (g - f) 1 μ').toReal ≤ (c' * snorm (g - f) 1 μ).toReal :=
      by
      rw [to_real_le_to_real h_snorm_ne_top' (ENNReal.mul_ne_top hc' h_snorm_ne_top)]
      refine' (snorm_mono_measure (⇑g - ⇑f) hμ'_le).trans _
      rw [snorm_smul_measure_of_ne_zero hc'0, smul_eq_mul]
      simp
    _ = c'.to_real * (snorm (⇑g - ⇑f) 1 μ).toReal := to_real_mul
    _ ≤ c'.to_real * (ε / 2 / c'.to_real) :=
      (mul_le_mul le_rfl hfg.le to_real_nonneg to_real_nonneg)
    _ = ε / 2 := by refine' mul_div_cancel' (ε / 2) _; rw [Ne.def, to_real_eq_zero_iff];
      simp [hc', hc'0]
    _ < ε := half_lt_self hε_pos
    
#align measure_theory.continuous_L1_to_L1 MeasureTheory.continuous_L1_toL1

theorem setToFun_congr_measure_of_integrable {μ' : Measure α} (c' : ℝ≥0∞) (hc' : c' ≠ ∞)
    (hμ'_le : μ' ≤ c' • μ) (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ' T C') (f : α → E) (hfμ : Integrable f μ) :
    setToFun μ T hT f = setToFun μ' T hT' f :=
  by
  -- integrability for `μ` implies integrability for `μ'`.
  have h_int : ∀ g : α → E, integrable g μ → integrable g μ' := fun g hg =>
    integrable.of_measure_le_smul c' hc' hμ'_le hg
  -- We use `integrable.induction`
  refine' hfμ.induction _ _ _ _ _
  · intro c s hs hμs
    have hμ's : μ' s ≠ ∞ := by
      refine' ((hμ'_le s hs).trans_lt _).Ne
      rw [measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top hc' hμs.ne
    rw [set_to_fun_indicator_const hT hs hμs.ne, set_to_fun_indicator_const hT' hs hμ's]
  · intro f₂ g₂ h_dish hf₂ hg₂ h_eq_f h_eq_g
    rw [set_to_fun_add hT hf₂ hg₂, set_to_fun_add hT' (h_int f₂ hf₂) (h_int g₂ hg₂), h_eq_f, h_eq_g]
  · refine' isClosed_eq (continuous_set_to_fun hT) _
    have :
      (fun f : α →₁[μ] E => set_to_fun μ' T hT' f) = fun f : α →₁[μ] E =>
        set_to_fun μ' T hT' ((h_int f (L1.integrable_coe_fn f)).toL1 f) :=
      by ext1 f; exact set_to_fun_congr_ae hT' (integrable.coe_fn_to_L1 _).symm
    rw [this]
    exact (continuous_set_to_fun hT').comp (continuous_L1_to_L1 c' hc' hμ'_le)
  · intro f₂ g₂ hfg hf₂ hf_eq
    have hfg' : f₂ =ᵐ[μ'] g₂ := (measure.absolutely_continuous_of_le_smul hμ'_le).ae_eq hfg
    rw [← set_to_fun_congr_ae hT hfg, hf_eq, set_to_fun_congr_ae hT' hfg']
#align measure_theory.set_to_fun_congr_measure_of_integrable MeasureTheory.setToFun_congr_measure_of_integrable

theorem setToFun_congr_measure {μ' : Measure α} (c c' : ℝ≥0∞) (hc : c ≠ ∞) (hc' : c' ≠ ∞)
    (hμ_le : μ ≤ c • μ') (hμ'_le : μ' ≤ c' • μ) (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ' T C') (f : α → E) :
    setToFun μ T hT f = setToFun μ' T hT' f :=
  by
  by_cases hf : integrable f μ
  · exact set_to_fun_congr_measure_of_integrable c' hc' hμ'_le hT hT' f hf
  · -- if `f` is not integrable, both `set_to_fun` are 0.
    have h_int : ∀ g : α → E, ¬integrable g μ → ¬integrable g μ' := fun g =>
      mt fun h => h.of_measure_le_smul _ hc hμ_le
    simp_rw [set_to_fun_undef _ hf, set_to_fun_undef _ (h_int f hf)]
#align measure_theory.set_to_fun_congr_measure MeasureTheory.setToFun_congr_measure

theorem setToFun_congr_measure_of_add_right {μ' : Measure α}
    (hT_add : DominatedFinMeasAdditive (μ + μ') T C') (hT : DominatedFinMeasAdditive μ T C)
    (f : α → E) (hf : Integrable f (μ + μ')) : setToFun (μ + μ') T hT_add f = setToFun μ T hT f :=
  by
  refine' set_to_fun_congr_measure_of_integrable 1 one_ne_top _ hT_add hT f hf
  rw [one_smul]
  nth_rw 1 [← add_zero μ]
  exact add_le_add le_rfl bot_le
#align measure_theory.set_to_fun_congr_measure_of_add_right MeasureTheory.setToFun_congr_measure_of_add_right

theorem setToFun_congr_measure_of_add_left {μ' : Measure α}
    (hT_add : DominatedFinMeasAdditive (μ + μ') T C') (hT : DominatedFinMeasAdditive μ' T C)
    (f : α → E) (hf : Integrable f (μ + μ')) : setToFun (μ + μ') T hT_add f = setToFun μ' T hT f :=
  by
  refine' set_to_fun_congr_measure_of_integrable 1 one_ne_top _ hT_add hT f hf
  rw [one_smul]
  nth_rw 1 [← zero_add μ']
  exact add_le_add bot_le le_rfl
#align measure_theory.set_to_fun_congr_measure_of_add_left MeasureTheory.setToFun_congr_measure_of_add_left

theorem setToFun_top_smul_measure (hT : DominatedFinMeasAdditive (∞ • μ) T C) (f : α → E) :
    setToFun (∞ • μ) T hT f = 0 :=
  by
  refine' set_to_fun_measure_zero' hT fun s hs hμs => _
  rw [lt_top_iff_ne_top] at hμs 
  simp only [true_and_iff, measure.smul_apply, WithTop.mul_eq_top_iff, eq_self_iff_true,
    top_ne_zero, Ne.def, not_false_iff, not_or, Classical.not_not, smul_eq_mul] at hμs 
  simp only [hμs.right, measure.smul_apply, MulZeroClass.mul_zero, smul_eq_mul]
#align measure_theory.set_to_fun_top_smul_measure MeasureTheory.setToFun_top_smul_measure

theorem setToFun_congr_smul_measure (c : ℝ≥0∞) (hc_ne_top : c ≠ ∞)
    (hT : DominatedFinMeasAdditive μ T C) (hT_smul : DominatedFinMeasAdditive (c • μ) T C')
    (f : α → E) : setToFun μ T hT f = setToFun (c • μ) T hT_smul f :=
  by
  by_cases hc0 : c = 0
  · simp [hc0] at hT_smul 
    have h : ∀ s, MeasurableSet s → μ s < ∞ → T s = 0 := fun s hs hμs => hT_smul.eq_zero hs
    rw [set_to_fun_zero_left' _ h, set_to_fun_measure_zero]
    simp [hc0]
  refine' set_to_fun_congr_measure c⁻¹ c _ hc_ne_top (le_of_eq _) le_rfl hT hT_smul f
  · simp [hc0]
  · rw [smul_smul, ENNReal.inv_mul_cancel hc0 hc_ne_top, one_smul]
#align measure_theory.set_to_fun_congr_smul_measure MeasureTheory.setToFun_congr_smul_measure

theorem norm_setToFun_le_mul_norm (hT : DominatedFinMeasAdditive μ T C) (f : α →₁[μ] E)
    (hC : 0 ≤ C) : ‖setToFun μ T hT f‖ ≤ C * ‖f‖ := by rw [L1.set_to_fun_eq_set_to_L1];
  exact L1.norm_set_to_L1_le_mul_norm hT hC f
#align measure_theory.norm_set_to_fun_le_mul_norm MeasureTheory.norm_setToFun_le_mul_norm

theorem norm_setToFun_le_mul_norm' (hT : DominatedFinMeasAdditive μ T C) (f : α →₁[μ] E) :
    ‖setToFun μ T hT f‖ ≤ max C 0 * ‖f‖ := by rw [L1.set_to_fun_eq_set_to_L1];
  exact L1.norm_set_to_L1_le_mul_norm' hT f
#align measure_theory.norm_set_to_fun_le_mul_norm' MeasureTheory.norm_setToFun_le_mul_norm'

theorem norm_setToFun_le (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ) (hC : 0 ≤ C) :
    ‖setToFun μ T hT f‖ ≤ C * ‖hf.toL1 f‖ := by rw [set_to_fun_eq hT hf];
  exact L1.norm_set_to_L1_le_mul_norm hT hC _
#align measure_theory.norm_set_to_fun_le MeasureTheory.norm_setToFun_le

theorem norm_setToFun_le' (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ) :
    ‖setToFun μ T hT f‖ ≤ max C 0 * ‖hf.toL1 f‖ := by rw [set_to_fun_eq hT hf];
  exact L1.norm_set_to_L1_le_mul_norm' hT _
#align measure_theory.norm_set_to_fun_le' MeasureTheory.norm_setToFun_le'

/-- Lebesgue dominated convergence theorem provides sufficient conditions under which almost
  everywhere convergence of a sequence of functions implies the convergence of their image by
  `set_to_fun`.
  We could weaken the condition `bound_integrable` to require `has_finite_integral bound μ` instead
  (i.e. not requiring that `bound` is measurable), but in all applications proving integrability
  is easier. -/
theorem tendsto_setToFun_of_dominated_convergence (hT : DominatedFinMeasAdditive μ T C)
    {fs : ℕ → α → E} {f : α → E} (bound : α → ℝ)
    (fs_measurable : ∀ n, AEStronglyMeasurable (fs n) μ) (bound_integrable : Integrable bound μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖fs n a‖ ≤ bound a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => fs n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => setToFun μ T hT (fs n)) atTop (𝓝 <| setToFun μ T hT f) :=
  by
  -- `f` is a.e.-measurable, since it is the a.e.-pointwise limit of a.e.-measurable functions.
  have f_measurable : ae_strongly_measurable f μ :=
    aestronglyMeasurable_of_tendsto_ae _ fs_measurable h_lim
  -- all functions we consider are integrable
  have fs_int : ∀ n, integrable (fs n) μ := fun n =>
    bound_integrable.mono' (fs_measurable n) (h_bound _)
  have f_int : integrable f μ :=
    ⟨f_measurable,
      has_finite_integral_of_dominated_convergence bound_integrable.has_finite_integral h_bound
        h_lim⟩
  -- it suffices to prove the result for the corresponding L1 functions
  suffices
    tendsto (fun n => L1.set_to_L1 hT ((fs_int n).toL1 (fs n))) at_top
      (𝓝 (L1.set_to_L1 hT (f_int.to_L1 f)))
    by
    convert this
    · ext1 n; exact set_to_fun_eq hT (fs_int n)
    · exact set_to_fun_eq hT f_int
  -- the convergence of set_to_L1 follows from the convergence of the L1 functions
  refine' L1.tendsto_set_to_L1 hT _ _ _
  -- up to some rewriting, what we need to prove is `h_lim`
  rw [tendsto_iff_norm_tendsto_zero]
  have lintegral_norm_tendsto_zero :
    tendsto (fun n => ENNReal.toReal <| ∫⁻ a, ENNReal.ofReal ‖fs n a - f a‖ ∂μ) at_top (𝓝 0) :=
    (tendsto_to_real zero_ne_top).comp
      (tendsto_lintegral_norm_of_dominated_convergence fs_measurable
        bound_integrable.has_finite_integral h_bound h_lim)
  convert lintegral_norm_tendsto_zero
  ext1 n
  rw [L1.norm_def]
  congr 1
  refine' lintegral_congr_ae _
  rw [← integrable.to_L1_sub]
  refine' ((fs_int n).sub f_int).coeFn_toL1.mono fun x hx => _
  dsimp only
  rw [hx, ofReal_norm_eq_coe_nnnorm, Pi.sub_apply]
#align measure_theory.tendsto_set_to_fun_of_dominated_convergence MeasureTheory.tendsto_setToFun_of_dominated_convergence

/-- Lebesgue dominated convergence theorem for filters with a countable basis -/
theorem tendsto_setToFun_filter_of_dominated_convergence (hT : DominatedFinMeasAdditive μ T C) {ι}
    {l : Filter ι} [l.IsCountablyGenerated] {fs : ι → α → E} {f : α → E} (bound : α → ℝ)
    (hfs_meas : ∀ᶠ n in l, AEStronglyMeasurable (fs n) μ)
    (h_bound : ∀ᶠ n in l, ∀ᵐ a ∂μ, ‖fs n a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => fs n a) l (𝓝 (f a))) :
    Tendsto (fun n => setToFun μ T hT (fs n)) l (𝓝 <| setToFun μ T hT f) :=
  by
  rw [tendsto_iff_seq_tendsto]
  intro x xl
  have hxl : ∀ s ∈ l, ∃ a, ∀ b ≥ a, x b ∈ s := by rwa [tendsto_at_top'] at xl 
  have h :
    { x : ι | (fun n => ae_strongly_measurable (fs n) μ) x } ∩
        { x : ι | (fun n => ∀ᵐ a ∂μ, ‖fs n a‖ ≤ bound a) x } ∈
      l :=
    inter_mem hfs_meas h_bound
  obtain ⟨k, h⟩ := hxl _ h
  rw [← tendsto_add_at_top_iff_nat k]
  refine' tendsto_set_to_fun_of_dominated_convergence hT bound _ bound_integrable _ _
  · exact fun n => (h _ (self_le_add_left _ _)).1
  · exact fun n => (h _ (self_le_add_left _ _)).2
  · filter_upwards [h_lim]
    refine' fun a h_lin => @tendsto.comp _ _ _ (fun n => x (n + k)) (fun n => fs n a) _ _ _ h_lin _
    rw [tendsto_add_at_top_iff_nat]
    assumption
#align measure_theory.tendsto_set_to_fun_filter_of_dominated_convergence MeasureTheory.tendsto_setToFun_filter_of_dominated_convergence

variable {X : Type _} [TopologicalSpace X] [FirstCountableTopology X]

theorem continuousWithinAt_setToFun_of_dominated (hT : DominatedFinMeasAdditive μ T C)
    {fs : X → α → E} {x₀ : X} {bound : α → ℝ} {s : Set X}
    (hfs_meas : ∀ᶠ x in 𝓝[s] x₀, AEStronglyMeasurable (fs x) μ)
    (h_bound : ∀ᶠ x in 𝓝[s] x₀, ∀ᵐ a ∂μ, ‖fs x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_cont : ∀ᵐ a ∂μ, ContinuousWithinAt (fun x => fs x a) s x₀) :
    ContinuousWithinAt (fun x => setToFun μ T hT (fs x)) s x₀ :=
  tendsto_setToFun_filter_of_dominated_convergence hT bound ‹_› ‹_› ‹_› ‹_›
#align measure_theory.continuous_within_at_set_to_fun_of_dominated MeasureTheory.continuousWithinAt_setToFun_of_dominated

theorem continuousAt_setToFun_of_dominated (hT : DominatedFinMeasAdditive μ T C) {fs : X → α → E}
    {x₀ : X} {bound : α → ℝ} (hfs_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (fs x) μ)
    (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ a ∂μ, ‖fs x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_cont : ∀ᵐ a ∂μ, ContinuousAt (fun x => fs x a) x₀) :
    ContinuousAt (fun x => setToFun μ T hT (fs x)) x₀ :=
  tendsto_setToFun_filter_of_dominated_convergence hT bound ‹_› ‹_› ‹_› ‹_›
#align measure_theory.continuous_at_set_to_fun_of_dominated MeasureTheory.continuousAt_setToFun_of_dominated

theorem continuousOn_setToFun_of_dominated (hT : DominatedFinMeasAdditive μ T C) {fs : X → α → E}
    {bound : α → ℝ} {s : Set X} (hfs_meas : ∀ x ∈ s, AEStronglyMeasurable (fs x) μ)
    (h_bound : ∀ x ∈ s, ∀ᵐ a ∂μ, ‖fs x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_cont : ∀ᵐ a ∂μ, ContinuousOn (fun x => fs x a) s) :
    ContinuousOn (fun x => setToFun μ T hT (fs x)) s :=
  by
  intro x hx
  refine' continuous_within_at_set_to_fun_of_dominated hT _ _ bound_integrable _
  · filter_upwards [self_mem_nhdsWithin]with x hx using hfs_meas x hx
  · filter_upwards [self_mem_nhdsWithin]with x hx using h_bound x hx
  · filter_upwards [h_cont]with a ha using ha x hx
#align measure_theory.continuous_on_set_to_fun_of_dominated MeasureTheory.continuousOn_setToFun_of_dominated

theorem continuous_setToFun_of_dominated (hT : DominatedFinMeasAdditive μ T C) {fs : X → α → E}
    {bound : α → ℝ} (hfs_meas : ∀ x, AEStronglyMeasurable (fs x) μ)
    (h_bound : ∀ x, ∀ᵐ a ∂μ, ‖fs x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_cont : ∀ᵐ a ∂μ, Continuous fun x => fs x a) : Continuous fun x => setToFun μ T hT (fs x) :=
  continuous_iff_continuousAt.mpr fun x₀ =>
    continuousAt_setToFun_of_dominated hT (eventually_of_forall hfs_meas)
        (eventually_of_forall h_bound) ‹_› <|
      h_cont.mono fun _ => Continuous.continuousAt
#align measure_theory.continuous_set_to_fun_of_dominated MeasureTheory.continuous_setToFun_of_dominated

end Function

end MeasureTheory

