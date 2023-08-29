/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

#align_import measure_theory.integral.set_to_l1 from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Extension of a linear function from indicators to L1

Let `T : Set α → E →L[ℝ] F` be additive for measurable sets with finite measure, in the sense that
for `s, t` two such sets, `s ∩ t = ∅ → T (s ∪ t) = T s + T t`. `T` is akin to a bilinear map on
`Set α × E`, or a linear map on indicator functions.

This file constructs an extension of `T` to integrable simple functions, which are finite sums of
indicators of measurable sets with finite measure, then to integrable functions, which are limits of
integrable simple functions.

The main result is a continuous linear map `(α →₁[μ] E) →L[ℝ] F`. This extension process is used to
define the Bochner integral in the `MeasureTheory.Integral.Bochner` file and the conditional
expectation of an integrable function in `MeasureTheory.Function.ConditionalExpectation`.

## Main Definitions

- `FinMeasAdditive μ T`: the property that `T` is additive on measurable sets with finite measure.
  For two such sets, `s ∩ t = ∅ → T (s ∪ t) = T s + T t`.
- `DominatedFinMeasAdditive μ T C`: `FinMeasAdditive μ T ∧ ∀ s, ‖T s‖ ≤ C * (μ s).toReal`.
  This is the property needed to perform the extension from indicators to L1.
- `setToL1 (hT : DominatedFinMeasAdditive μ T C) : (α →₁[μ] E) →L[ℝ] F`: the extension of `T`
  from indicators to L1.
- `setToFun μ T (hT : DominatedFinMeasAdditive μ T C) (f : α → E) : F`: a version of the
  extension which applies to functions (with value 0 if the function is not integrable).

## Properties

For most properties of `setToFun`, we provide two lemmas. One version uses hypotheses valid on
all sets, like `T = T'`, and a second version which uses a primed name uses hypotheses on
measurable sets with finite measure, like `∀ s, MeasurableSet s → μ s < ∞ → T s = T' s`.

The lemmas listed here don't show all hypotheses. Refer to the actual lemmas for details.

Linearity:
- `setToFun_zero_left : setToFun μ 0 hT f = 0`
- `setToFun_add_left : setToFun μ (T + T') _ f = setToFun μ T hT f + setToFun μ T' hT' f`
- `setToFun_smul_left : setToFun μ (fun s ↦ c • (T s)) (hT.smul c) f = c • setToFun μ T hT f`
- `setToFun_zero : setToFun μ T hT (0 : α → E) = 0`
- `setToFun_neg : setToFun μ T hT (-f) = - setToFun μ T hT f`
If `f` and `g` are integrable:
- `setToFun_add : setToFun μ T hT (f + g) = setToFun μ T hT f + setToFun μ T hT g`
- `setToFun_sub : setToFun μ T hT (f - g) = setToFun μ T hT f - setToFun μ T hT g`
If `T` is verifies `∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x`:
- `setToFun_smul : setToFun μ T hT (c • f) = c • setToFun μ T hT f`

Other:
- `setToFun_congr_ae (h : f =ᵐ[μ] g) : setToFun μ T hT f = setToFun μ T hT g`
- `setToFun_measure_zero (h : μ = 0) : setToFun μ T hT f = 0`

If the space is a `NormedLatticeAddCommGroup` and `T` is such that `0 ≤ T s x` for `0 ≤ x`, we
also prove order-related properties:
- `setToFun_mono_left (h : ∀ s x, T s x ≤ T' s x) : setToFun μ T hT f ≤ setToFun μ T' hT' f`
- `setToFun_nonneg (hf : 0 ≤ᵐ[μ] f) : 0 ≤ setToFun μ T hT f`
- `setToFun_mono (hfg : f ≤ᵐ[μ] g) : setToFun μ T hT f ≤ setToFun μ T hT g`

## Implementation notes

The starting object `T : Set α → E →L[ℝ] F` matters only through its restriction on measurable sets
with finite measure. Its value on other sets is ignored.
-/


noncomputable section

open scoped Classical Topology BigOperators NNReal ENNReal MeasureTheory Pointwise

open Set Filter TopologicalSpace ENNReal EMetric

namespace MeasureTheory

variable {α E F F' G 𝕜 : Type*} {p : ℝ≥0∞} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [NormedAddCommGroup G] {m : MeasurableSpace α} {μ : Measure α}

-- mathport name: «expr →ₛ »
local infixr:25 " →ₛ " => SimpleFunc

open Finset

section FinMeasAdditive

/-- A set function is `FinMeasAdditive` if its value on the union of two disjoint measurable
sets with finite measure is the sum of its values on each set. -/
def FinMeasAdditive {β} [AddMonoid β] {_ : MeasurableSpace α} (μ : Measure α) (T : Set α → β) :
    Prop :=
  ∀ s t, MeasurableSet s → MeasurableSet t → μ s ≠ ∞ → μ t ≠ ∞ → s ∩ t = ∅ → T (s ∪ t) = T s + T t
#align measure_theory.fin_meas_additive MeasureTheory.FinMeasAdditive

namespace FinMeasAdditive

variable {β : Type*} [AddCommMonoid β] {T T' : Set α → β}

theorem zero : FinMeasAdditive μ (0 : Set α → β) := fun s t _ _ _ _ _ => by simp
                                                                            -- 🎉 no goals
#align measure_theory.fin_meas_additive.zero MeasureTheory.FinMeasAdditive.zero

theorem add (hT : FinMeasAdditive μ T) (hT' : FinMeasAdditive μ T') :
    FinMeasAdditive μ (T + T') := by
  intro s t hs ht hμs hμt hst
  -- ⊢ (T + T') (s ∪ t) = (T + T') s + (T + T') t
  simp only [hT s t hs ht hμs hμt hst, hT' s t hs ht hμs hμt hst, Pi.add_apply]
  -- ⊢ T s + T t + (T' s + T' t) = T s + T' s + (T t + T' t)
  abel
  -- 🎉 no goals
  -- 🎉 no goals
#align measure_theory.fin_meas_additive.add MeasureTheory.FinMeasAdditive.add

theorem smul [Monoid 𝕜] [DistribMulAction 𝕜 β] (hT : FinMeasAdditive μ T) (c : 𝕜) :
    FinMeasAdditive μ fun s => c • T s := fun s t hs ht hμs hμt hst => by
  simp [hT s t hs ht hμs hμt hst]
  -- 🎉 no goals
#align measure_theory.fin_meas_additive.smul MeasureTheory.FinMeasAdditive.smul

theorem of_eq_top_imp_eq_top {μ' : Measure α} (h : ∀ s, MeasurableSet s → μ s = ∞ → μ' s = ∞)
    (hT : FinMeasAdditive μ T) : FinMeasAdditive μ' T := fun s t hs ht hμ's hμ't hst =>
  hT s t hs ht (mt (h s hs) hμ's) (mt (h t ht) hμ't) hst
#align measure_theory.fin_meas_additive.of_eq_top_imp_eq_top MeasureTheory.FinMeasAdditive.of_eq_top_imp_eq_top

theorem of_smul_measure (c : ℝ≥0∞) (hc_ne_top : c ≠ ∞) (hT : FinMeasAdditive (c • μ) T) :
    FinMeasAdditive μ T := by
  refine' of_eq_top_imp_eq_top (fun s _ hμs => _) hT
  -- ⊢ ↑↑μ s = ⊤
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.mul_eq_top] at hμs
  -- ⊢ ↑↑μ s = ⊤
  simp only [hc_ne_top, or_false_iff, Ne.def, false_and_iff] at hμs
  -- ⊢ ↑↑μ s = ⊤
  exact hμs.2
  -- 🎉 no goals
#align measure_theory.fin_meas_additive.of_smul_measure MeasureTheory.FinMeasAdditive.of_smul_measure

theorem smul_measure (c : ℝ≥0∞) (hc_ne_zero : c ≠ 0) (hT : FinMeasAdditive μ T) :
    FinMeasAdditive (c • μ) T := by
  refine' of_eq_top_imp_eq_top (fun s _ hμs => _) hT
  -- ⊢ ↑↑(c • μ) s = ⊤
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.mul_eq_top]
  -- ⊢ c ≠ 0 ∧ ↑↑μ s = ⊤ ∨ c = ⊤ ∧ ↑↑μ s ≠ 0
  simp only [hc_ne_zero, true_and_iff, Ne.def, not_false_iff]
  -- ⊢ ↑↑μ s = ⊤ ∨ c = ⊤ ∧ ¬↑↑μ s = 0
  exact Or.inl hμs
  -- 🎉 no goals
#align measure_theory.fin_meas_additive.smul_measure MeasureTheory.FinMeasAdditive.smul_measure

theorem smul_measure_iff (c : ℝ≥0∞) (hc_ne_zero : c ≠ 0) (hc_ne_top : c ≠ ∞) :
    FinMeasAdditive (c • μ) T ↔ FinMeasAdditive μ T :=
  ⟨fun hT => of_smul_measure c hc_ne_top hT, fun hT => smul_measure c hc_ne_zero hT⟩
#align measure_theory.fin_meas_additive.smul_measure_iff MeasureTheory.FinMeasAdditive.smul_measure_iff

theorem map_empty_eq_zero {β} [AddCancelMonoid β] {T : Set α → β} (hT : FinMeasAdditive μ T) :
    T ∅ = 0 := by
  have h_empty : μ ∅ ≠ ∞ := (measure_empty.le.trans_lt ENNReal.coe_lt_top).ne
  -- ⊢ T ∅ = 0
  specialize hT ∅ ∅ MeasurableSet.empty MeasurableSet.empty h_empty h_empty (Set.inter_empty ∅)
  -- ⊢ T ∅ = 0
  rw [Set.union_empty] at hT
  -- ⊢ T ∅ = 0
  nth_rw 1 [← add_zero (T ∅)] at hT
  -- ⊢ T ∅ = 0
  exact (add_left_cancel hT).symm
  -- 🎉 no goals
#align measure_theory.fin_meas_additive.map_empty_eq_zero MeasureTheory.FinMeasAdditive.map_empty_eq_zero

theorem map_iUnion_fin_meas_set_eq_sum (T : Set α → β) (T_empty : T ∅ = 0)
    (h_add : FinMeasAdditive μ T) {ι} (S : ι → Set α) (sι : Finset ι)
    (hS_meas : ∀ i, MeasurableSet (S i)) (hSp : ∀ i ∈ sι, μ (S i) ≠ ∞)
    (h_disj : ∀ᵉ (i ∈ sι) (j ∈ sι), i ≠ j → Disjoint (S i) (S j)) :
    T (⋃ i ∈ sι, S i) = ∑ i in sι, T (S i) := by
  revert hSp h_disj
  -- ⊢ (∀ (i : ι), i ∈ sι → ↑↑μ (S i) ≠ ⊤) → (∀ (i : ι), i ∈ sι → ∀ (j : ι), j ∈ sι …
  refine' Finset.induction_on sι _ _
  -- ⊢ (∀ (i : ι), i ∈ ∅ → ↑↑μ (S i) ≠ ⊤) → (∀ (i : ι), i ∈ ∅ → ∀ (j : ι), j ∈ ∅ →  …
  · simp only [Finset.not_mem_empty, IsEmpty.forall_iff, iUnion_false, iUnion_empty, sum_empty,
      forall₂_true_iff, imp_true_iff, forall_true_left, not_false_iff, T_empty]
  intro a s has h hps h_disj
  -- ⊢ T (⋃ (i : ι) (_ : i ∈ insert a s), S i) = ∑ i in insert a s, T (S i)
  rw [Finset.sum_insert has, ← h]
  swap; · exact fun i hi => hps i (Finset.mem_insert_of_mem hi)
          -- 🎉 no goals
  swap;
  -- ⊢ ∀ (i : ι), i ∈ s → ∀ (j : ι), j ∈ s → i ≠ j → Disjoint (S i) (S j)
  · exact fun i hi j hj hij =>
      h_disj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
  rw [←
    h_add (S a) (⋃ i ∈ s, S i) (hS_meas a) (measurableSet_biUnion _ fun i _ => hS_meas i)
      (hps a (Finset.mem_insert_self a s))]
  · congr; convert Finset.iSup_insert a s S
    -- ⊢ ⋃ (i : ι) (_ : i ∈ insert a s), S i = S a ∪ ⋃ (i : ι) (_ : i ∈ s), S i
           -- 🎉 no goals
  · exact
      ((measure_biUnion_finset_le _ _).trans_lt <|
          ENNReal.sum_lt_top fun i hi => hps i <| Finset.mem_insert_of_mem hi).ne
  · simp_rw [Set.inter_iUnion]
    -- ⊢ ⋃ (i : ι) (_ : i ∈ s), S a ∩ S i = ∅
    refine' iUnion_eq_empty.mpr fun i => iUnion_eq_empty.mpr fun hi => _
    -- ⊢ S a ∩ S i = ∅
    rw [← Set.disjoint_iff_inter_eq_empty]
    -- ⊢ Disjoint (S a) (S i)
    refine' h_disj a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi) fun hai => _
    -- ⊢ False
    rw [← hai] at hi
    -- ⊢ False
    exact has hi
    -- 🎉 no goals
#align measure_theory.fin_meas_additive.map_Union_fin_meas_set_eq_sum MeasureTheory.FinMeasAdditive.map_iUnion_fin_meas_set_eq_sum

end FinMeasAdditive

/-- A `FinMeasAdditive` set function whose norm on every set is less than the measure of the
set (up to a multiplicative constant). -/
def DominatedFinMeasAdditive {β} [SeminormedAddCommGroup β] {_ : MeasurableSpace α} (μ : Measure α)
    (T : Set α → β) (C : ℝ) : Prop :=
  FinMeasAdditive μ T ∧ ∀ s, MeasurableSet s → μ s < ∞ → ‖T s‖ ≤ C * (μ s).toReal
#align measure_theory.dominated_fin_meas_additive MeasureTheory.DominatedFinMeasAdditive

namespace DominatedFinMeasAdditive

variable {β : Type*} [SeminormedAddCommGroup β] {T T' : Set α → β} {C C' : ℝ}

theorem zero {m : MeasurableSpace α} (μ : Measure α) (hC : 0 ≤ C) :
    DominatedFinMeasAdditive μ (0 : Set α → β) C := by
  refine' ⟨FinMeasAdditive.zero, fun s _ _ => _⟩
  -- ⊢ ‖OfNat.ofNat 0 s‖ ≤ C * ENNReal.toReal (↑↑μ s)
  rw [Pi.zero_apply, norm_zero]
  -- ⊢ 0 ≤ C * ENNReal.toReal (↑↑μ s)
  exact mul_nonneg hC toReal_nonneg
  -- 🎉 no goals
#align measure_theory.dominated_fin_meas_additive.zero MeasureTheory.DominatedFinMeasAdditive.zero

theorem eq_zero_of_measure_zero {β : Type*} [NormedAddCommGroup β] {T : Set α → β} {C : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) {s : Set α} (hs : MeasurableSet s) (hs_zero : μ s = 0) :
    T s = 0 := by
  refine' norm_eq_zero.mp _
  -- ⊢ ‖T s‖ = 0
  refine' ((hT.2 s hs (by simp [hs_zero])).trans (le_of_eq _)).antisymm (norm_nonneg _)
  -- ⊢ C * ENNReal.toReal (↑↑μ s) = 0
  rw [hs_zero, ENNReal.zero_toReal, mul_zero]
  -- 🎉 no goals
#align measure_theory.dominated_fin_meas_additive.eq_zero_of_measure_zero MeasureTheory.DominatedFinMeasAdditive.eq_zero_of_measure_zero

theorem eq_zero {β : Type*} [NormedAddCommGroup β] {T : Set α → β} {C : ℝ} {m : MeasurableSpace α}
    (hT : DominatedFinMeasAdditive (0 : Measure α) T C) {s : Set α} (hs : MeasurableSet s) :
    T s = 0 :=
  eq_zero_of_measure_zero hT hs (by simp only [Measure.coe_zero, Pi.zero_apply])
                                    -- 🎉 no goals
#align measure_theory.dominated_fin_meas_additive.eq_zero MeasureTheory.DominatedFinMeasAdditive.eq_zero

theorem add (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C') :
    DominatedFinMeasAdditive μ (T + T') (C + C') := by
  refine' ⟨hT.1.add hT'.1, fun s hs hμs => _⟩
  -- ⊢ ‖(T + T') s‖ ≤ (C + C') * ENNReal.toReal (↑↑μ s)
  rw [Pi.add_apply, add_mul]
  -- ⊢ ‖T s + T' s‖ ≤ C * ENNReal.toReal (↑↑μ s) + C' * ENNReal.toReal (↑↑μ s)
  exact (norm_add_le _ _).trans (add_le_add (hT.2 s hs hμs) (hT'.2 s hs hμs))
  -- 🎉 no goals
#align measure_theory.dominated_fin_meas_additive.add MeasureTheory.DominatedFinMeasAdditive.add

theorem smul [NormedField 𝕜] [NormedSpace 𝕜 β] (hT : DominatedFinMeasAdditive μ T C) (c : 𝕜) :
    DominatedFinMeasAdditive μ (fun s => c • T s) (‖c‖ * C) := by
  refine' ⟨hT.1.smul c, fun s hs hμs => _⟩
  -- ⊢ ‖(fun s => c • T s) s‖ ≤ ‖c‖ * C * ENNReal.toReal (↑↑μ s)
  dsimp only
  -- ⊢ ‖c • T s‖ ≤ ‖c‖ * C * ENNReal.toReal (↑↑μ s)
  rw [norm_smul, mul_assoc]
  -- ⊢ ‖c‖ * ‖T s‖ ≤ ‖c‖ * (C * ENNReal.toReal (↑↑μ s))
  exact mul_le_mul le_rfl (hT.2 s hs hμs) (norm_nonneg _) (norm_nonneg _)
  -- 🎉 no goals
#align measure_theory.dominated_fin_meas_additive.smul MeasureTheory.DominatedFinMeasAdditive.smul

theorem of_measure_le {μ' : Measure α} (h : μ ≤ μ') (hT : DominatedFinMeasAdditive μ T C)
    (hC : 0 ≤ C) : DominatedFinMeasAdditive μ' T C := by
  have h' : ∀ s, MeasurableSet s → μ s = ∞ → μ' s = ∞ := by
    intro s hs hμs; rw [eq_top_iff, ← hμs]; exact h s hs
  refine' ⟨hT.1.of_eq_top_imp_eq_top h', fun s hs hμ's => _⟩
  -- ⊢ ‖T s‖ ≤ C * ENNReal.toReal (↑↑μ' s)
  have hμs : μ s < ∞ := (h s hs).trans_lt hμ's
  -- ⊢ ‖T s‖ ≤ C * ENNReal.toReal (↑↑μ' s)
  refine' (hT.2 s hs hμs).trans (mul_le_mul le_rfl _ ENNReal.toReal_nonneg hC)
  -- ⊢ ENNReal.toReal (↑↑μ s) ≤ ENNReal.toReal (↑↑μ' s)
  rw [toReal_le_toReal hμs.ne hμ's.ne]
  -- ⊢ ↑↑μ s ≤ ↑↑μ' s
  exact h s hs
  -- 🎉 no goals
#align measure_theory.dominated_fin_meas_additive.of_measure_le MeasureTheory.DominatedFinMeasAdditive.of_measure_le

theorem add_measure_right {_ : MeasurableSpace α} (μ ν : Measure α)
    (hT : DominatedFinMeasAdditive μ T C) (hC : 0 ≤ C) : DominatedFinMeasAdditive (μ + ν) T C :=
  of_measure_le (Measure.le_add_right le_rfl) hT hC
#align measure_theory.dominated_fin_meas_additive.add_measure_right MeasureTheory.DominatedFinMeasAdditive.add_measure_right

theorem add_measure_left {_ : MeasurableSpace α} (μ ν : Measure α)
    (hT : DominatedFinMeasAdditive ν T C) (hC : 0 ≤ C) : DominatedFinMeasAdditive (μ + ν) T C :=
  of_measure_le (Measure.le_add_left le_rfl) hT hC
#align measure_theory.dominated_fin_meas_additive.add_measure_left MeasureTheory.DominatedFinMeasAdditive.add_measure_left

theorem of_smul_measure (c : ℝ≥0∞) (hc_ne_top : c ≠ ∞) (hT : DominatedFinMeasAdditive (c • μ) T C) :
    DominatedFinMeasAdditive μ T (c.toReal * C) := by
  have h : ∀ s, MeasurableSet s → c • μ s = ∞ → μ s = ∞ := by
    intro s _ hcμs
    simp only [hc_ne_top, Algebra.id.smul_eq_mul, ENNReal.mul_eq_top, or_false_iff, Ne.def,
      false_and_iff] at hcμs
    exact hcμs.2
  refine' ⟨hT.1.of_eq_top_imp_eq_top (μ := c • μ) h, fun s hs hμs => _⟩
  -- ⊢ ‖T s‖ ≤ ENNReal.toReal c * C * ENNReal.toReal (↑↑μ s)
  have hcμs : c • μ s ≠ ∞ := mt (h s hs) hμs.ne
  -- ⊢ ‖T s‖ ≤ ENNReal.toReal c * C * ENNReal.toReal (↑↑μ s)
  rw [smul_eq_mul] at hcμs
  -- ⊢ ‖T s‖ ≤ ENNReal.toReal c * C * ENNReal.toReal (↑↑μ s)
  simp_rw [DominatedFinMeasAdditive, Measure.smul_apply, smul_eq_mul, toReal_mul] at hT
  -- ⊢ ‖T s‖ ≤ ENNReal.toReal c * C * ENNReal.toReal (↑↑μ s)
  refine' (hT.2 s hs hcμs.lt_top).trans (le_of_eq _)
  -- ⊢ C * (ENNReal.toReal c * ENNReal.toReal (↑↑μ s)) = ENNReal.toReal c * C * ENN …
  ring
  -- 🎉 no goals
#align measure_theory.dominated_fin_meas_additive.of_smul_measure MeasureTheory.DominatedFinMeasAdditive.of_smul_measure

theorem of_measure_le_smul {μ' : Measure α} (c : ℝ≥0∞) (hc : c ≠ ∞) (h : μ ≤ c • μ')
    (hT : DominatedFinMeasAdditive μ T C) (hC : 0 ≤ C) :
    DominatedFinMeasAdditive μ' T (c.toReal * C) :=
  (hT.of_measure_le h hC).of_smul_measure c hc
#align measure_theory.dominated_fin_meas_additive.of_measure_le_smul MeasureTheory.DominatedFinMeasAdditive.of_measure_le_smul

end DominatedFinMeasAdditive

end FinMeasAdditive

namespace SimpleFunc

/-- Extend `Set α → (F →L[ℝ] F')` to `(α →ₛ F) → F'`. -/
def setToSimpleFunc {_ : MeasurableSpace α} (T : Set α → F →L[ℝ] F') (f : α →ₛ F) : F' :=
  ∑ x in f.range, T (f ⁻¹' {x}) x
#align measure_theory.simple_func.set_to_simple_func MeasureTheory.SimpleFunc.setToSimpleFunc

@[simp]
theorem setToSimpleFunc_zero {m : MeasurableSpace α} (f : α →ₛ F) :
    setToSimpleFunc (0 : Set α → F →L[ℝ] F') f = 0 := by simp [setToSimpleFunc]
                                                         -- 🎉 no goals
#align measure_theory.simple_func.set_to_simple_func_zero MeasureTheory.SimpleFunc.setToSimpleFunc_zero

theorem setToSimpleFunc_zero' {T : Set α → E →L[ℝ] F'}
    (h_zero : ∀ s, MeasurableSet s → μ s < ∞ → T s = 0) (f : α →ₛ E) (hf : Integrable f μ) :
    setToSimpleFunc T f = 0 := by
  simp_rw [setToSimpleFunc]
  -- ⊢ ∑ x in SimpleFunc.range f, ↑(T (↑f ⁻¹' {x})) x = 0
  refine' sum_eq_zero fun x _ => _
  -- ⊢ ↑(T (↑f ⁻¹' {x})) x = 0
  by_cases hx0 : x = 0
  -- ⊢ ↑(T (↑f ⁻¹' {x})) x = 0
  · simp [hx0]
    -- 🎉 no goals
  rw [h_zero (f ⁻¹' ({x} : Set E)) (measurableSet_fiber _ _)
      (measure_preimage_lt_top_of_integrable f hf hx0),
    ContinuousLinearMap.zero_apply]
#align measure_theory.simple_func.set_to_simple_func_zero' MeasureTheory.SimpleFunc.setToSimpleFunc_zero'

@[simp]
theorem setToSimpleFunc_zero_apply {m : MeasurableSpace α} (T : Set α → F →L[ℝ] F') :
    setToSimpleFunc T (0 : α →ₛ F) = 0 := by
  cases isEmpty_or_nonempty α <;> simp [setToSimpleFunc]
  -- ⊢ setToSimpleFunc T 0 = 0
                                  -- 🎉 no goals
                                  -- 🎉 no goals
#align measure_theory.simple_func.set_to_simple_func_zero_apply MeasureTheory.SimpleFunc.setToSimpleFunc_zero_apply

theorem setToSimpleFunc_eq_sum_filter {m : MeasurableSpace α} (T : Set α → F →L[ℝ] F')
    (f : α →ₛ F) :
    setToSimpleFunc T f = ∑ x in f.range.filter fun x => x ≠ 0, (T (f ⁻¹' {x})) x := by
  symm
  -- ⊢ ∑ x in filter (fun x => x ≠ 0) (SimpleFunc.range f), ↑(T (↑f ⁻¹' {x})) x = s …
  refine' sum_filter_of_ne fun x _ => mt fun hx0 => _
  -- ⊢ ↑(T (↑f ⁻¹' {x})) x = 0
  rw [hx0]
  -- ⊢ ↑(T (↑f ⁻¹' {0})) 0 = 0
  exact ContinuousLinearMap.map_zero _
  -- 🎉 no goals
#align measure_theory.simple_func.set_to_simple_func_eq_sum_filter MeasureTheory.SimpleFunc.setToSimpleFunc_eq_sum_filter

theorem map_setToSimpleFunc (T : Set α → F →L[ℝ] F') (h_add : FinMeasAdditive μ T) {f : α →ₛ G}
    (hf : Integrable f μ) {g : G → F} (hg : g 0 = 0) :
    (f.map g).setToSimpleFunc T = ∑ x in f.range, T (f ⁻¹' {x}) (g x) := by
  have T_empty : T ∅ = 0 := h_add.map_empty_eq_zero
  -- ⊢ setToSimpleFunc T (map g f) = ∑ x in SimpleFunc.range f, ↑(T (↑f ⁻¹' {x})) ( …
  have hfp : ∀ x ∈ f.range, x ≠ 0 → μ (f ⁻¹' {x}) ≠ ∞ := fun x _ hx0 =>
    (measure_preimage_lt_top_of_integrable f hf hx0).ne
  simp only [setToSimpleFunc, range_map]
  -- ⊢ ∑ x in Finset.image g (SimpleFunc.range f), ↑(T (↑(map g f) ⁻¹' {x})) x = ∑  …
  refine' Finset.sum_image' _ fun b hb => _
  -- ⊢ ↑(T (↑(map g f) ⁻¹' {g b})) (g b) = ∑ x in filter (fun c' => g c' = g b) (Si …
  rcases mem_range.1 hb with ⟨a, rfl⟩
  -- ⊢ ↑(T (↑(map g f) ⁻¹' {g (↑f a)})) (g (↑f a)) = ∑ x in filter (fun c' => g c'  …
  by_cases h0 : g (f a) = 0
  -- ⊢ ↑(T (↑(map g f) ⁻¹' {g (↑f a)})) (g (↑f a)) = ∑ x in filter (fun c' => g c'  …
  · simp_rw [h0]
    -- ⊢ ↑(T (↑(map g f) ⁻¹' {0})) 0 = ∑ x in filter (fun c' => g c' = 0) (SimpleFunc …
    rw [ContinuousLinearMap.map_zero, Finset.sum_eq_zero fun x hx => ?_]
    -- ⊢ ↑(T (↑f ⁻¹' {x})) (g x) = 0
    rw [mem_filter] at hx
    -- ⊢ ↑(T (↑f ⁻¹' {x})) (g x) = 0
    rw [hx.2, ContinuousLinearMap.map_zero]
    -- 🎉 no goals
  have h_left_eq :
    T (map g f ⁻¹' {g (f a)}) (g (f a)) =
      T (f ⁻¹' (f.range.filter fun b => g b = g (f a))) (g (f a)) :=
    by congr; rw [map_preimage_singleton]
  rw [h_left_eq]
  -- ⊢ ↑(T (↑f ⁻¹' ↑(filter (fun b => g b = g (↑f a)) (SimpleFunc.range f)))) (g (↑ …
  have h_left_eq' :
    T (f ⁻¹' (filter (fun b : G => g b = g (f a)) f.range)) (g (f a)) =
      T (⋃ y ∈ filter (fun b : G => g b = g (f a)) f.range, f ⁻¹' {y}) (g (f a)) :=
    by congr; rw [← Finset.set_biUnion_preimage_singleton]
  rw [h_left_eq']
  -- ⊢ ↑(T (⋃ (y : G) (_ : y ∈ filter (fun b => g b = g (↑f a)) (SimpleFunc.range f …
  rw [h_add.map_iUnion_fin_meas_set_eq_sum T T_empty]
  · simp only [sum_apply, ContinuousLinearMap.coe_sum']
    -- ⊢ ∑ c in filter (fun b => g b = g (↑f a)) (SimpleFunc.range f), ↑(T (↑f ⁻¹' {c …
    refine' Finset.sum_congr rfl fun x hx => _
    -- ⊢ ↑(T (↑f ⁻¹' {x})) (g (↑f a)) = ↑(T (↑f ⁻¹' {x})) (g x)
    rw [mem_filter] at hx
    -- ⊢ ↑(T (↑f ⁻¹' {x})) (g (↑f a)) = ↑(T (↑f ⁻¹' {x})) (g x)
    rw [hx.2]
    -- 🎉 no goals
  · exact fun i => measurableSet_fiber _ _
    -- 🎉 no goals
  · intro i hi
    -- ⊢ ↑↑μ (↑f ⁻¹' {i}) ≠ ⊤
    rw [mem_filter] at hi
    -- ⊢ ↑↑μ (↑f ⁻¹' {i}) ≠ ⊤
    refine' hfp i hi.1 fun hi0 => _
    -- ⊢ False
    rw [hi0, hg] at hi
    -- ⊢ False
    exact h0 hi.2.symm
    -- 🎉 no goals
  · intro i _j hi _ hij
    -- ⊢ Disjoint (↑f ⁻¹' {i}) (↑f ⁻¹' {hi})
    rw [Set.disjoint_iff]
    -- ⊢ ↑f ⁻¹' {i} ∩ ↑f ⁻¹' {hi} ⊆ ∅
    intro x hx
    -- ⊢ x ∈ ∅
    rw [Set.mem_inter_iff, Set.mem_preimage, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_singleton_iff] at hx
    rw [← hx.1, ← hx.2] at hij
    -- ⊢ x ∈ ∅
    exact absurd rfl hij
    -- 🎉 no goals
#align measure_theory.simple_func.map_set_to_simple_func MeasureTheory.SimpleFunc.map_setToSimpleFunc

theorem setToSimpleFunc_congr' (T : Set α → E →L[ℝ] F) (h_add : FinMeasAdditive μ T) {f g : α →ₛ E}
    (hf : Integrable f μ) (hg : Integrable g μ) (h : ∀ x y, x ≠ y → T (f ⁻¹' {x} ∩ g ⁻¹' {y}) = 0) :
    f.setToSimpleFunc T = g.setToSimpleFunc T :=
  show ((pair f g).map Prod.fst).setToSimpleFunc T = ((pair f g).map Prod.snd).setToSimpleFunc T by
    have h_pair : Integrable (f.pair g) μ := integrable_pair hf hg
    -- ⊢ setToSimpleFunc T (map Prod.fst (pair f g)) = setToSimpleFunc T (map Prod.sn …
    rw [map_setToSimpleFunc T h_add h_pair Prod.fst_zero]
    -- ⊢ ∑ x in SimpleFunc.range (pair f g), ↑(T (↑(pair f g) ⁻¹' {x})) x.fst = setTo …
    rw [map_setToSimpleFunc T h_add h_pair Prod.snd_zero]
    -- ⊢ ∑ x in SimpleFunc.range (pair f g), ↑(T (↑(pair f g) ⁻¹' {x})) x.fst = ∑ x i …
    refine' Finset.sum_congr rfl fun p hp => _
    -- ⊢ ↑(T (↑(pair f g) ⁻¹' {p})) p.fst = ↑(T (↑(pair f g) ⁻¹' {p})) p.snd
    rcases mem_range.1 hp with ⟨a, rfl⟩
    -- ⊢ ↑(T (↑(pair f g) ⁻¹' {↑(pair f g) a})) (↑(pair f g) a).fst = ↑(T (↑(pair f g …
    by_cases eq : f a = g a
    -- ⊢ ↑(T (↑(pair f g) ⁻¹' {↑(pair f g) a})) (↑(pair f g) a).fst = ↑(T (↑(pair f g …
    · dsimp only [pair_apply]; rw [eq]
      -- ⊢ ↑(T (↑(pair f g) ⁻¹' {(↑f a, ↑g a)})) (↑f a) = ↑(T (↑(pair f g) ⁻¹' {(↑f a,  …
                               -- 🎉 no goals
    · have : T (pair f g ⁻¹' {(f a, g a)}) = 0 := by
        have h_eq : T ((⇑(f.pair g)) ⁻¹' {(f a, g a)}) = T (f ⁻¹' {f a} ∩ g ⁻¹' {g a}) := by
          congr; rw [pair_preimage_singleton f g]
        rw [h_eq]
        exact h (f a) (g a) eq
      simp only [this, ContinuousLinearMap.zero_apply, pair_apply]
      -- 🎉 no goals
#align measure_theory.simple_func.set_to_simple_func_congr' MeasureTheory.SimpleFunc.setToSimpleFunc_congr'

theorem setToSimpleFunc_congr (T : Set α → E →L[ℝ] F)
    (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0) (h_add : FinMeasAdditive μ T) {f g : α →ₛ E}
    (hf : Integrable f μ) (h : f =ᵐ[μ] g) : f.setToSimpleFunc T = g.setToSimpleFunc T := by
  refine' setToSimpleFunc_congr' T h_add hf ((integrable_congr h).mp hf) _
  -- ⊢ ∀ (x y : E), x ≠ y → T (↑f ⁻¹' {x} ∩ ↑g ⁻¹' {y}) = 0
  refine' fun x y hxy => h_zero _ ((measurableSet_fiber f x).inter (measurableSet_fiber g y)) _
  -- ⊢ ↑↑μ (↑f ⁻¹' {x} ∩ ↑g ⁻¹' {y}) = 0
  rw [EventuallyEq, ae_iff] at h
  -- ⊢ ↑↑μ (↑f ⁻¹' {x} ∩ ↑g ⁻¹' {y}) = 0
  refine' measure_mono_null (fun z => _) h
  -- ⊢ z ∈ ↑f ⁻¹' {x} ∩ ↑g ⁻¹' {y} → z ∈ {a | ¬↑f a = ↑g a}
  simp_rw [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
  -- ⊢ ↑f z = x ∧ ↑g z = y → ¬↑f z = ↑g z
  intro h
  -- ⊢ ¬↑f z = ↑g z
  rwa [h.1, h.2]
  -- 🎉 no goals
#align measure_theory.simple_func.set_to_simple_func_congr MeasureTheory.SimpleFunc.setToSimpleFunc_congr

theorem setToSimpleFunc_congr_left (T T' : Set α → E →L[ℝ] F)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → T s = T' s) (f : α →ₛ E) (hf : Integrable f μ) :
    setToSimpleFunc T f = setToSimpleFunc T' f := by
  simp_rw [setToSimpleFunc]
  -- ⊢ ∑ x in SimpleFunc.range f, ↑(T (↑f ⁻¹' {x})) x = ∑ x in SimpleFunc.range f,  …
  refine' sum_congr rfl fun x _ => _
  -- ⊢ ↑(T (↑f ⁻¹' {x})) x = ↑(T' (↑f ⁻¹' {x})) x
  by_cases hx0 : x = 0
  -- ⊢ ↑(T (↑f ⁻¹' {x})) x = ↑(T' (↑f ⁻¹' {x})) x
  · simp [hx0]
    -- 🎉 no goals
  · rw [h (f ⁻¹' {x}) (SimpleFunc.measurableSet_fiber _ _)
        (SimpleFunc.measure_preimage_lt_top_of_integrable _ hf hx0)]
#align measure_theory.simple_func.set_to_simple_func_congr_left MeasureTheory.SimpleFunc.setToSimpleFunc_congr_left

theorem setToSimpleFunc_add_left {m : MeasurableSpace α} (T T' : Set α → F →L[ℝ] F') {f : α →ₛ F} :
    setToSimpleFunc (T + T') f = setToSimpleFunc T f + setToSimpleFunc T' f := by
  simp_rw [setToSimpleFunc, Pi.add_apply]
  -- ⊢ ∑ x in SimpleFunc.range f, ↑(T (↑f ⁻¹' {x}) + T' (↑f ⁻¹' {x})) x = ∑ x in Si …
  push_cast
  -- ⊢ ∑ x in SimpleFunc.range f, (↑(T (↑f ⁻¹' {x})) + ↑(T' (↑f ⁻¹' {x}))) x = ∑ x  …
  simp_rw [Pi.add_apply, sum_add_distrib]
  -- 🎉 no goals
#align measure_theory.simple_func.set_to_simple_func_add_left MeasureTheory.SimpleFunc.setToSimpleFunc_add_left

theorem setToSimpleFunc_add_left' (T T' T'' : Set α → E →L[ℝ] F)
    (h_add : ∀ s, MeasurableSet s → μ s < ∞ → T'' s = T s + T' s) {f : α →ₛ E}
    (hf : Integrable f μ) : setToSimpleFunc T'' f = setToSimpleFunc T f + setToSimpleFunc T' f := by
  simp_rw [setToSimpleFunc_eq_sum_filter]
  -- ⊢ ∑ x in filter (fun x => x ≠ 0) (SimpleFunc.range f), ↑(T'' (↑f ⁻¹' {x})) x = …
  suffices
    ∀ x ∈ filter (fun x : E => x ≠ 0) f.range, T'' (f ⁻¹' {x}) = T (f ⁻¹' {x}) + T' (f ⁻¹' {x}) by
    rw [← sum_add_distrib]
    refine' Finset.sum_congr rfl fun x hx => _
    rw [this x hx]
    push_cast
    rw [Pi.add_apply]
  intro x hx
  -- ⊢ T'' (↑f ⁻¹' {x}) = T (↑f ⁻¹' {x}) + T' (↑f ⁻¹' {x})
  refine'
    h_add (f ⁻¹' {x}) (measurableSet_preimage _ _) (measure_preimage_lt_top_of_integrable _ hf _)
  rw [mem_filter] at hx
  -- ⊢ x ≠ 0
  exact hx.2
  -- 🎉 no goals
#align measure_theory.simple_func.set_to_simple_func_add_left' MeasureTheory.SimpleFunc.setToSimpleFunc_add_left'

theorem setToSimpleFunc_smul_left {m : MeasurableSpace α} (T : Set α → F →L[ℝ] F') (c : ℝ)
    (f : α →ₛ F) : setToSimpleFunc (fun s => c • T s) f = c • setToSimpleFunc T f := by
  simp_rw [setToSimpleFunc, ContinuousLinearMap.smul_apply, smul_sum]
  -- 🎉 no goals
#align measure_theory.simple_func.set_to_simple_func_smul_left MeasureTheory.SimpleFunc.setToSimpleFunc_smul_left

theorem setToSimpleFunc_smul_left' (T T' : Set α → E →L[ℝ] F') (c : ℝ)
    (h_smul : ∀ s, MeasurableSet s → μ s < ∞ → T' s = c • T s) {f : α →ₛ E} (hf : Integrable f μ) :
    setToSimpleFunc T' f = c • setToSimpleFunc T f := by
  simp_rw [setToSimpleFunc_eq_sum_filter]
  -- ⊢ ∑ x in filter (fun x => x ≠ 0) (SimpleFunc.range f), ↑(T' (↑f ⁻¹' {x})) x =  …
  suffices ∀ x ∈ filter (fun x : E => x ≠ 0) f.range, T' (f ⁻¹' {x}) = c • T (f ⁻¹' {x}) by
    rw [smul_sum]
    refine' Finset.sum_congr rfl fun x hx => _
    rw [this x hx]
    rfl
  intro x hx
  -- ⊢ T' (↑f ⁻¹' {x}) = c • T (↑f ⁻¹' {x})
  refine'
    h_smul (f ⁻¹' {x}) (measurableSet_preimage _ _) (measure_preimage_lt_top_of_integrable _ hf _)
  rw [mem_filter] at hx
  -- ⊢ x ≠ 0
  exact hx.2
  -- 🎉 no goals
#align measure_theory.simple_func.set_to_simple_func_smul_left' MeasureTheory.SimpleFunc.setToSimpleFunc_smul_left'

theorem setToSimpleFunc_add (T : Set α → E →L[ℝ] F) (h_add : FinMeasAdditive μ T) {f g : α →ₛ E}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    setToSimpleFunc T (f + g) = setToSimpleFunc T f + setToSimpleFunc T g :=
  have hp_pair : Integrable (f.pair g) μ := integrable_pair hf hg
  calc
    setToSimpleFunc T (f + g) = ∑ x in (pair f g).range, T (pair f g ⁻¹' {x}) (x.fst + x.snd) := by
      rw [add_eq_map₂, map_setToSimpleFunc T h_add hp_pair]; simp
      -- ⊢ 0.fst + 0.snd = 0
                                                             -- 🎉 no goals
    _ = ∑ x in (pair f g).range, (T (pair f g ⁻¹' {x}) x.fst + T (pair f g ⁻¹' {x}) x.snd) :=
      (Finset.sum_congr rfl fun a _ => ContinuousLinearMap.map_add _ _ _)
    _ = (∑ x in (pair f g).range, T (pair f g ⁻¹' {x}) x.fst) +
          ∑ x in (pair f g).range, T (pair f g ⁻¹' {x}) x.snd := by
      rw [Finset.sum_add_distrib]
      -- 🎉 no goals
    _ = ((pair f g).map Prod.fst).setToSimpleFunc T +
          ((pair f g).map Prod.snd).setToSimpleFunc T := by
      rw [map_setToSimpleFunc T h_add hp_pair Prod.snd_zero,
        map_setToSimpleFunc T h_add hp_pair Prod.fst_zero]
#align measure_theory.simple_func.set_to_simple_func_add MeasureTheory.SimpleFunc.setToSimpleFunc_add

theorem setToSimpleFunc_neg (T : Set α → E →L[ℝ] F) (h_add : FinMeasAdditive μ T) {f : α →ₛ E}
    (hf : Integrable f μ) : setToSimpleFunc T (-f) = -setToSimpleFunc T f :=
  calc
    setToSimpleFunc T (-f) = setToSimpleFunc T (f.map Neg.neg) := rfl
    _ = -setToSimpleFunc T f := by
      rw [map_setToSimpleFunc T h_add hf neg_zero, setToSimpleFunc, ← sum_neg_distrib]
      -- ⊢ ∑ x in SimpleFunc.range f, ↑(T (↑f ⁻¹' {x})) (-x) = ∑ x in SimpleFunc.range  …
      exact Finset.sum_congr rfl fun x _ => ContinuousLinearMap.map_neg _ _
      -- 🎉 no goals
#align measure_theory.simple_func.set_to_simple_func_neg MeasureTheory.SimpleFunc.setToSimpleFunc_neg

theorem setToSimpleFunc_sub (T : Set α → E →L[ℝ] F) (h_add : FinMeasAdditive μ T) {f g : α →ₛ E}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    setToSimpleFunc T (f - g) = setToSimpleFunc T f - setToSimpleFunc T g := by
  rw [sub_eq_add_neg, setToSimpleFunc_add T h_add hf, setToSimpleFunc_neg T h_add hg,
    sub_eq_add_neg]
  rw [integrable_iff] at hg ⊢
  -- ⊢ ∀ (y : E), y ≠ 0 → ↑↑μ (↑(-g) ⁻¹' {y}) < ⊤
  intro x hx_ne
  -- ⊢ ↑↑μ (↑(-g) ⁻¹' {x}) < ⊤
  change μ (Neg.neg ∘ g ⁻¹' {x}) < ∞
  -- ⊢ ↑↑μ (Neg.neg ∘ ↑g ⁻¹' {x}) < ⊤
  rw [preimage_comp, neg_preimage, Set.neg_singleton]
  -- ⊢ ↑↑μ (↑g ⁻¹' {-x}) < ⊤
  refine' hg (-x) _
  -- ⊢ -x ≠ 0
  simp [hx_ne]
  -- 🎉 no goals
#align measure_theory.simple_func.set_to_simple_func_sub MeasureTheory.SimpleFunc.setToSimpleFunc_sub

theorem setToSimpleFunc_smul_real (T : Set α → E →L[ℝ] F) (h_add : FinMeasAdditive μ T) (c : ℝ)
    {f : α →ₛ E} (hf : Integrable f μ) : setToSimpleFunc T (c • f) = c • setToSimpleFunc T f :=
  calc
    setToSimpleFunc T (c • f) = ∑ x in f.range, T (f ⁻¹' {x}) (c • x) := by
      rw [smul_eq_map c f, map_setToSimpleFunc T h_add hf]; dsimp only; rw [smul_zero]
      -- ⊢ (fun x x_1 => x • x_1) c 0 = 0
                                                            -- ⊢ c • 0 = 0
                                                                        -- 🎉 no goals
    _ = ∑ x in f.range, c • T (f ⁻¹' {x}) x :=
      (Finset.sum_congr rfl fun b _ => by rw [ContinuousLinearMap.map_smul (T (f ⁻¹' {b})) c b])
                                          -- 🎉 no goals
    _ = c • setToSimpleFunc T f := by simp only [setToSimpleFunc, smul_sum, smul_smul, mul_comm]
                                      -- 🎉 no goals
#align measure_theory.simple_func.set_to_simple_func_smul_real MeasureTheory.SimpleFunc.setToSimpleFunc_smul_real

theorem setToSimpleFunc_smul {E} [NormedAddCommGroup E] [NormedField 𝕜] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [NormedSpace 𝕜 F] (T : Set α → E →L[ℝ] F) (h_add : FinMeasAdditive μ T)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (c : 𝕜) {f : α →ₛ E} (hf : Integrable f μ) :
    setToSimpleFunc T (c • f) = c • setToSimpleFunc T f :=
  calc
    setToSimpleFunc T (c • f) = ∑ x in f.range, T (f ⁻¹' {x}) (c • x) := by
      rw [smul_eq_map c f, map_setToSimpleFunc T h_add hf]; dsimp only; rw [smul_zero]
      -- ⊢ (fun x x_1 => x • x_1) c 0 = 0
                                                            -- ⊢ c • 0 = 0
                                                                        -- 🎉 no goals
    _ = ∑ x in f.range, c • T (f ⁻¹' {x}) x := (Finset.sum_congr rfl fun b _ => by rw [h_smul])
                                                                                   -- 🎉 no goals
    _ = c • setToSimpleFunc T f := by simp only [setToSimpleFunc, smul_sum, smul_smul, mul_comm]
                                      -- 🎉 no goals
#align measure_theory.simple_func.set_to_simple_func_smul MeasureTheory.SimpleFunc.setToSimpleFunc_smul

section Order

variable {G' G'' : Type*} [NormedLatticeAddCommGroup G''] [NormedSpace ℝ G'']
  [NormedLatticeAddCommGroup G'] [NormedSpace ℝ G']

theorem setToSimpleFunc_mono_left {m : MeasurableSpace α} (T T' : Set α → F →L[ℝ] G'')
    (hTT' : ∀ s x, T s x ≤ T' s x) (f : α →ₛ F) : setToSimpleFunc T f ≤ setToSimpleFunc T' f := by
  simp_rw [setToSimpleFunc]; exact sum_le_sum fun i _ => hTT' _ i
  -- ⊢ ∑ x in SimpleFunc.range f, ↑(T (↑f ⁻¹' {x})) x ≤ ∑ x in SimpleFunc.range f,  …
                             -- 🎉 no goals
#align measure_theory.simple_func.set_to_simple_func_mono_left MeasureTheory.SimpleFunc.setToSimpleFunc_mono_left

theorem setToSimpleFunc_mono_left' (T T' : Set α → E →L[ℝ] G'')
    (hTT' : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, T s x ≤ T' s x) (f : α →ₛ E)
    (hf : Integrable f μ) : setToSimpleFunc T f ≤ setToSimpleFunc T' f := by
  refine' sum_le_sum fun i _ => _
  -- ⊢ ↑(T (↑f ⁻¹' {i})) i ≤ ↑(T' (↑f ⁻¹' {i})) i
  by_cases h0 : i = 0
  -- ⊢ ↑(T (↑f ⁻¹' {i})) i ≤ ↑(T' (↑f ⁻¹' {i})) i
  · simp [h0]
    -- 🎉 no goals
  · exact hTT' _ (measurableSet_fiber _ _) (measure_preimage_lt_top_of_integrable _ hf h0) i
    -- 🎉 no goals
#align measure_theory.simple_func.set_to_simple_func_mono_left' MeasureTheory.SimpleFunc.setToSimpleFunc_mono_left'

theorem setToSimpleFunc_nonneg {m : MeasurableSpace α} (T : Set α → G' →L[ℝ] G'')
    (hT_nonneg : ∀ s x, 0 ≤ x → 0 ≤ T s x) (f : α →ₛ G') (hf : 0 ≤ f) :
    0 ≤ setToSimpleFunc T f := by
  refine' sum_nonneg fun i hi => hT_nonneg _ i _
  -- ⊢ 0 ≤ i
  rw [mem_range] at hi
  -- ⊢ 0 ≤ i
  obtain ⟨y, hy⟩ := Set.mem_range.mp hi
  -- ⊢ 0 ≤ i
  rw [← hy]
  -- ⊢ 0 ≤ ↑f y
  refine' le_trans _ (hf y)
  -- ⊢ 0 ≤ ↑0 y
  simp
  -- 🎉 no goals
#align measure_theory.simple_func.set_to_simple_func_nonneg MeasureTheory.SimpleFunc.setToSimpleFunc_nonneg

theorem setToSimpleFunc_nonneg' (T : Set α → G' →L[ℝ] G'')
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) (f : α →ₛ G') (hf : 0 ≤ f)
    (hfi : Integrable f μ) : 0 ≤ setToSimpleFunc T f := by
  refine' sum_nonneg fun i hi => _
  -- ⊢ 0 ≤ ↑(T (↑f ⁻¹' {i})) i
  by_cases h0 : i = 0
  -- ⊢ 0 ≤ ↑(T (↑f ⁻¹' {i})) i
  · simp [h0]
    -- 🎉 no goals
  refine'
    hT_nonneg _ (measurableSet_fiber _ _) (measure_preimage_lt_top_of_integrable _ hfi h0) i _
  rw [mem_range] at hi
  -- ⊢ 0 ≤ i
  obtain ⟨y, hy⟩ := Set.mem_range.mp hi
  -- ⊢ 0 ≤ i
  rw [← hy]
  -- ⊢ 0 ≤ ↑f y
  convert hf y
  -- 🎉 no goals
#align measure_theory.simple_func.set_to_simple_func_nonneg' MeasureTheory.SimpleFunc.setToSimpleFunc_nonneg'

theorem setToSimpleFunc_mono {T : Set α → G' →L[ℝ] G''} (h_add : FinMeasAdditive μ T)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f g : α →ₛ G'}
    (hfi : Integrable f μ) (hgi : Integrable g μ) (hfg : f ≤ g) :
    setToSimpleFunc T f ≤ setToSimpleFunc T g := by
  rw [← sub_nonneg, ← setToSimpleFunc_sub T h_add hgi hfi]
  -- ⊢ 0 ≤ setToSimpleFunc T (g - f)
  refine' setToSimpleFunc_nonneg' T hT_nonneg _ _ (hgi.sub hfi)
  -- ⊢ 0 ≤ g - f
  intro x
  -- ⊢ ↑0 x ≤ ↑(g - f) x
  simp only [coe_sub, sub_nonneg, coe_zero, Pi.zero_apply, Pi.sub_apply]
  -- ⊢ ↑f x ≤ ↑g x
  exact hfg x
  -- 🎉 no goals
#align measure_theory.simple_func.set_to_simple_func_mono MeasureTheory.SimpleFunc.setToSimpleFunc_mono

end Order

theorem norm_setToSimpleFunc_le_sum_op_norm {m : MeasurableSpace α} (T : Set α → F' →L[ℝ] F)
    (f : α →ₛ F') : ‖f.setToSimpleFunc T‖ ≤ ∑ x in f.range, ‖T (f ⁻¹' {x})‖ * ‖x‖ :=
  calc
    ‖∑ x in f.range, T (f ⁻¹' {x}) x‖ ≤ ∑ x in f.range, ‖T (f ⁻¹' {x}) x‖ := norm_sum_le _ _
    _ ≤ ∑ x in f.range, ‖T (f ⁻¹' {x})‖ * ‖x‖ := by
      refine' Finset.sum_le_sum fun b _ => _; simp_rw [ContinuousLinearMap.le_op_norm]
      -- ⊢ ‖↑(T (↑f ⁻¹' {b})) b‖ ≤ ‖T (↑f ⁻¹' {b})‖ * ‖b‖
                                              -- 🎉 no goals
#align measure_theory.simple_func.norm_set_to_simple_func_le_sum_op_norm MeasureTheory.SimpleFunc.norm_setToSimpleFunc_le_sum_op_norm

theorem norm_setToSimpleFunc_le_sum_mul_norm (T : Set α → F →L[ℝ] F') {C : ℝ}
    (hT_norm : ∀ s, MeasurableSet s → ‖T s‖ ≤ C * (μ s).toReal) (f : α →ₛ F) :
    ‖f.setToSimpleFunc T‖ ≤ C * ∑ x in f.range, (μ (f ⁻¹' {x})).toReal * ‖x‖ :=
  calc
    ‖f.setToSimpleFunc T‖ ≤ ∑ x in f.range, ‖T (f ⁻¹' {x})‖ * ‖x‖ :=
      norm_setToSimpleFunc_le_sum_op_norm T f
    _ ≤ ∑ x in f.range, C * (μ (f ⁻¹' {x})).toReal * ‖x‖ := by
      gcongr
      -- ⊢ ‖T (↑f ⁻¹' {i✝})‖ ≤ C * ENNReal.toReal (↑↑μ (↑f ⁻¹' {i✝}))
      exact hT_norm _ <| SimpleFunc.measurableSet_fiber _ _
      -- 🎉 no goals
    _ ≤ C * ∑ x in f.range, (μ (f ⁻¹' {x})).toReal * ‖x‖ := by simp_rw [mul_sum, ← mul_assoc]; rfl
                                                               -- ⊢ ∑ x in SimpleFunc.range f, C * ENNReal.toReal (↑↑μ (↑f ⁻¹' {x})) * ‖x‖ ≤ ∑ x …
                                                                                               -- 🎉 no goals
#align measure_theory.simple_func.norm_set_to_simple_func_le_sum_mul_norm MeasureTheory.SimpleFunc.norm_setToSimpleFunc_le_sum_mul_norm

theorem norm_setToSimpleFunc_le_sum_mul_norm_of_integrable (T : Set α → E →L[ℝ] F') {C : ℝ}
    (hT_norm : ∀ s, MeasurableSet s → μ s < ∞ → ‖T s‖ ≤ C * (μ s).toReal) (f : α →ₛ E)
    (hf : Integrable f μ) :
    ‖f.setToSimpleFunc T‖ ≤ C * ∑ x in f.range, (μ (f ⁻¹' {x})).toReal * ‖x‖ :=
  calc
    ‖f.setToSimpleFunc T‖ ≤ ∑ x in f.range, ‖T (f ⁻¹' {x})‖ * ‖x‖ :=
      norm_setToSimpleFunc_le_sum_op_norm T f
    _ ≤ ∑ x in f.range, C * (μ (f ⁻¹' {x})).toReal * ‖x‖ := by
      refine' Finset.sum_le_sum fun b hb => _
      -- ⊢ ‖T (↑f ⁻¹' {b})‖ * ‖b‖ ≤ C * ENNReal.toReal (↑↑μ (↑f ⁻¹' {b})) * ‖b‖
      obtain rfl | hb := eq_or_ne b 0
      -- ⊢ ‖T (↑f ⁻¹' {0})‖ * ‖0‖ ≤ C * ENNReal.toReal (↑↑μ (↑f ⁻¹' {0})) * ‖0‖
      · simp
        -- 🎉 no goals
      gcongr
      -- ⊢ ‖T (↑f ⁻¹' {b})‖ ≤ C * ENNReal.toReal (↑↑μ (↑f ⁻¹' {b}))
      exact hT_norm _ (SimpleFunc.measurableSet_fiber _ _) <|
        SimpleFunc.measure_preimage_lt_top_of_integrable _ hf hb
    _ ≤ C * ∑ x in f.range, (μ (f ⁻¹' {x})).toReal * ‖x‖ := by simp_rw [mul_sum, ← mul_assoc]; rfl
                                                               -- ⊢ ∑ x in SimpleFunc.range f, C * ENNReal.toReal (↑↑μ (↑f ⁻¹' {x})) * ‖x‖ ≤ ∑ x …
                                                                                               -- 🎉 no goals
#align measure_theory.simple_func.norm_set_to_simple_func_le_sum_mul_norm_of_integrable MeasureTheory.SimpleFunc.norm_setToSimpleFunc_le_sum_mul_norm_of_integrable

theorem setToSimpleFunc_indicator (T : Set α → F →L[ℝ] F') (hT_empty : T ∅ = 0)
    {m : MeasurableSpace α} {s : Set α} (hs : MeasurableSet s) (x : F) :
    SimpleFunc.setToSimpleFunc T
        (SimpleFunc.piecewise s hs (SimpleFunc.const α x) (SimpleFunc.const α 0)) =
      T s x := by
  obtain rfl | hs_empty := s.eq_empty_or_nonempty
  -- ⊢ setToSimpleFunc T (piecewise ∅ hs (const α x) (const α 0)) = ↑(T ∅) x
  · simp only [hT_empty, ContinuousLinearMap.zero_apply, piecewise_empty, const_zero,
      setToSimpleFunc_zero_apply]
  simp_rw [setToSimpleFunc]
  -- ⊢ ∑ x_1 in SimpleFunc.range (piecewise s hs (const α x) (const α 0)), ↑(T (↑(p …
  obtain rfl | hs_univ := eq_or_ne s univ
  -- ⊢ ∑ x_1 in SimpleFunc.range (piecewise Set.univ hs (const α x) (const α 0)), ↑ …
  · haveI hα := hs_empty.to_type
    -- ⊢ ∑ x_1 in SimpleFunc.range (piecewise Set.univ hs (const α x) (const α 0)), ↑ …
    simp [← Function.const_def]
    -- 🎉 no goals
  rw [range_indicator hs hs_empty hs_univ]
  -- ⊢ ∑ x_1 in {x, 0}, ↑(T (↑(piecewise s hs (const α x) (const α 0)) ⁻¹' {x_1}))  …
  by_cases hx0 : x = 0
  -- ⊢ ∑ x_1 in {x, 0}, ↑(T (↑(piecewise s hs (const α x) (const α 0)) ⁻¹' {x_1}))  …
  · simp_rw [hx0]; simp
    -- ⊢ ∑ x in {0, 0}, ↑(T (↑(piecewise s hs (const α 0) (const α 0)) ⁻¹' {x})) x =  …
                   -- 🎉 no goals
  rw [sum_insert]
  -- ⊢ ↑(T (↑(piecewise s hs (const α x) (const α 0)) ⁻¹' {x})) x + ∑ x_1 in {0}, ↑ …
  swap; · rw [Finset.mem_singleton]; exact hx0
  -- ⊢ ¬x ∈ {0}
          -- ⊢ ¬x = 0
                                     -- 🎉 no goals
  rw [sum_singleton, (T _).map_zero, add_zero]
  -- ⊢ ↑(T (↑(piecewise s hs (const α x) (const α 0)) ⁻¹' {x})) x = ↑(T s) x
  congr
  -- ⊢ ↑(piecewise s hs (const α x) (const α 0)) ⁻¹' {x} = s
  simp only [coe_piecewise, piecewise_eq_indicator, coe_const, Pi.const_zero,
    piecewise_eq_indicator]
  rw [indicator_preimage, ← Function.const_def, preimage_const_of_mem]
  -- ⊢ Set.ite s Set.univ (0 ⁻¹' {x}) = s
  swap; · exact Set.mem_singleton x
  -- ⊢ x ∈ {x}
          -- 🎉 no goals
  rw [← Pi.const_zero, ← Function.const_def, preimage_const_of_not_mem]
  -- ⊢ Set.ite s Set.univ ∅ = s
  swap; · rw [Set.mem_singleton_iff]; exact Ne.symm hx0
  -- ⊢ ¬0 ∈ {x}
          -- ⊢ ¬0 = x
                                      -- 🎉 no goals
  simp
  -- 🎉 no goals
#align measure_theory.simple_func.set_to_simple_func_indicator MeasureTheory.SimpleFunc.setToSimpleFunc_indicator

theorem setToSimpleFunc_const' [Nonempty α] (T : Set α → F →L[ℝ] F') (x : F)
    {m : MeasurableSpace α} : SimpleFunc.setToSimpleFunc T (SimpleFunc.const α x) = T univ x := by
  simp only [setToSimpleFunc, range_const, Set.mem_singleton, preimage_const_of_mem,
    sum_singleton, ← Function.const_def, coe_const]
#align measure_theory.simple_func.set_to_simple_func_const' MeasureTheory.SimpleFunc.setToSimpleFunc_const'

theorem setToSimpleFunc_const (T : Set α → F →L[ℝ] F') (hT_empty : T ∅ = 0) (x : F)
    {m : MeasurableSpace α} : SimpleFunc.setToSimpleFunc T (SimpleFunc.const α x) = T univ x := by
  cases hα : isEmpty_or_nonempty α
  -- ⊢ setToSimpleFunc T (const α x) = ↑(T Set.univ) x
  · have h_univ_empty : (univ : Set α) = ∅ := Subsingleton.elim _ _
    -- ⊢ setToSimpleFunc T (const α x) = ↑(T Set.univ) x
    rw [h_univ_empty, hT_empty]
    -- ⊢ setToSimpleFunc T (const α x) = ↑0 x
    simp only [setToSimpleFunc, ContinuousLinearMap.zero_apply, sum_empty,
      range_eq_empty_of_isEmpty]
  · exact setToSimpleFunc_const' T x
    -- 🎉 no goals
#align measure_theory.simple_func.set_to_simple_func_const MeasureTheory.SimpleFunc.setToSimpleFunc_const

end SimpleFunc

namespace L1

set_option linter.uppercaseLean3 false

open AEEqFun Lp.simpleFunc Lp

namespace SimpleFunc

theorem norm_eq_sum_mul (f : α →₁ₛ[μ] G) :
    ‖f‖ = ∑ x in (toSimpleFunc f).range, (μ (toSimpleFunc f ⁻¹' {x})).toReal * ‖x‖ := by
  rw [norm_toSimpleFunc, snorm_one_eq_lintegral_nnnorm]
  -- ⊢ ENNReal.toReal (∫⁻ (x : α), ↑‖↑(toSimpleFunc f) x‖₊ ∂μ) = ∑ x in SimpleFunc. …
  have h_eq := SimpleFunc.map_apply (fun x => (‖x‖₊ : ℝ≥0∞)) (toSimpleFunc f)
  -- ⊢ ENNReal.toReal (∫⁻ (x : α), ↑‖↑(toSimpleFunc f) x‖₊ ∂μ) = ∑ x in SimpleFunc. …
  simp_rw [← h_eq]
  -- ⊢ ENNReal.toReal (∫⁻ (x : α), ↑(SimpleFunc.map (fun x => ↑‖x‖₊) (toSimpleFunc  …
  rw [SimpleFunc.lintegral_eq_lintegral, SimpleFunc.map_lintegral, ENNReal.toReal_sum]
  -- ⊢ ∑ a in SimpleFunc.range (toSimpleFunc f), ENNReal.toReal (↑‖a‖₊ * ↑↑μ (↑(toS …
  · congr
    -- ⊢ (fun a => ENNReal.toReal (↑‖a‖₊ * ↑↑μ (↑(toSimpleFunc f) ⁻¹' {a}))) = fun x  …
    ext1 x
    -- ⊢ ENNReal.toReal (↑‖x‖₊ * ↑↑μ (↑(toSimpleFunc f) ⁻¹' {x})) = ENNReal.toReal (↑ …
    rw [ENNReal.toReal_mul, mul_comm, ← ofReal_norm_eq_coe_nnnorm,
      ENNReal.toReal_ofReal (norm_nonneg _)]
  · intro x _
    -- ⊢ ↑‖x‖₊ * ↑↑μ (↑(toSimpleFunc f) ⁻¹' {x}) ≠ ⊤
    by_cases hx0 : x = 0
    -- ⊢ ↑‖x‖₊ * ↑↑μ (↑(toSimpleFunc f) ⁻¹' {x}) ≠ ⊤
    · rw [hx0]; simp
      -- ⊢ ↑‖0‖₊ * ↑↑μ (↑(toSimpleFunc f) ⁻¹' {0}) ≠ ⊤
                -- 🎉 no goals
    · exact
        ENNReal.mul_ne_top ENNReal.coe_ne_top
          (SimpleFunc.measure_preimage_lt_top_of_integrable _ (SimpleFunc.integrable f) hx0).ne
#align measure_theory.L1.simple_func.norm_eq_sum_mul MeasureTheory.L1.SimpleFunc.norm_eq_sum_mul

section SetToL1S

variable [NormedField 𝕜] [NormedSpace 𝕜 E]

attribute [local instance] Lp.simpleFunc.module

attribute [local instance] Lp.simpleFunc.normedSpace

/-- Extend `Set α → (E →L[ℝ] F')` to `(α →₁ₛ[μ] E) → F'`. -/
def setToL1S (T : Set α → E →L[ℝ] F) (f : α →₁ₛ[μ] E) : F :=
  (toSimpleFunc f).setToSimpleFunc T
#align measure_theory.L1.simple_func.set_to_L1s MeasureTheory.L1.SimpleFunc.setToL1S

theorem setToL1S_eq_setToSimpleFunc (T : Set α → E →L[ℝ] F) (f : α →₁ₛ[μ] E) :
    setToL1S T f = (toSimpleFunc f).setToSimpleFunc T :=
  rfl
#align measure_theory.L1.simple_func.set_to_L1s_eq_set_to_simple_func MeasureTheory.L1.SimpleFunc.setToL1S_eq_setToSimpleFunc

@[simp]
theorem setToL1S_zero_left (f : α →₁ₛ[μ] E) : setToL1S (0 : Set α → E →L[ℝ] F) f = 0 :=
  SimpleFunc.setToSimpleFunc_zero _
#align measure_theory.L1.simple_func.set_to_L1s_zero_left MeasureTheory.L1.SimpleFunc.setToL1S_zero_left

theorem setToL1S_zero_left' {T : Set α → E →L[ℝ] F}
    (h_zero : ∀ s, MeasurableSet s → μ s < ∞ → T s = 0) (f : α →₁ₛ[μ] E) : setToL1S T f = 0 :=
  SimpleFunc.setToSimpleFunc_zero' h_zero _ (SimpleFunc.integrable f)
#align measure_theory.L1.simple_func.set_to_L1s_zero_left' MeasureTheory.L1.SimpleFunc.setToL1S_zero_left'

theorem setToL1S_congr (T : Set α → E →L[ℝ] F) (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0)
    (h_add : FinMeasAdditive μ T) {f g : α →₁ₛ[μ] E} (h : toSimpleFunc f =ᵐ[μ] toSimpleFunc g) :
    setToL1S T f = setToL1S T g :=
  SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable f) h
#align measure_theory.L1.simple_func.set_to_L1s_congr MeasureTheory.L1.SimpleFunc.setToL1S_congr

theorem setToL1S_congr_left (T T' : Set α → E →L[ℝ] F)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → T s = T' s) (f : α →₁ₛ[μ] E) :
    setToL1S T f = setToL1S T' f :=
  SimpleFunc.setToSimpleFunc_congr_left T T' h (simpleFunc.toSimpleFunc f) (SimpleFunc.integrable f)
#align measure_theory.L1.simple_func.set_to_L1s_congr_left MeasureTheory.L1.SimpleFunc.setToL1S_congr_left

/-- `setToL1S` does not change if we replace the measure `μ` by `μ'` with `μ ≪ μ'`. The statement
uses two functions `f` and `f'` because they have to belong to different types, but morally these
are the same function (we have `f =ᵐ[μ] f'`). -/
theorem setToL1S_congr_measure {μ' : Measure α} (T : Set α → E →L[ℝ] F)
    (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0) (h_add : FinMeasAdditive μ T) (hμ : μ ≪ μ')
    (f : α →₁ₛ[μ] E) (f' : α →₁ₛ[μ'] E) (h : (f : α → E) =ᵐ[μ] f') :
    setToL1S T f = setToL1S T f' := by
  refine' SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable f) _
  -- ⊢ ↑(toSimpleFunc f) =ᵐ[μ] ↑(toSimpleFunc f')
  refine' (toSimpleFunc_eq_toFun f).trans _
  -- ⊢ ↑↑↑f =ᵐ[μ] ↑(toSimpleFunc f')
  suffices : (f' : α → E) =ᵐ[μ] simpleFunc.toSimpleFunc f'; exact h.trans this
  -- ⊢ ↑↑↑f =ᵐ[μ] ↑(toSimpleFunc f')
                                                            -- ⊢ ↑↑↑f' =ᵐ[μ] ↑(toSimpleFunc f')
  have goal' : (f' : α → E) =ᵐ[μ'] simpleFunc.toSimpleFunc f' := (toSimpleFunc_eq_toFun f').symm
  -- ⊢ ↑↑↑f' =ᵐ[μ] ↑(toSimpleFunc f')
  exact hμ.ae_eq goal'
  -- 🎉 no goals
#align measure_theory.L1.simple_func.set_to_L1s_congr_measure MeasureTheory.L1.SimpleFunc.setToL1S_congr_measure

theorem setToL1S_add_left (T T' : Set α → E →L[ℝ] F) (f : α →₁ₛ[μ] E) :
    setToL1S (T + T') f = setToL1S T f + setToL1S T' f :=
  SimpleFunc.setToSimpleFunc_add_left T T'
#align measure_theory.L1.simple_func.set_to_L1s_add_left MeasureTheory.L1.SimpleFunc.setToL1S_add_left

theorem setToL1S_add_left' (T T' T'' : Set α → E →L[ℝ] F)
    (h_add : ∀ s, MeasurableSet s → μ s < ∞ → T'' s = T s + T' s) (f : α →₁ₛ[μ] E) :
    setToL1S T'' f = setToL1S T f + setToL1S T' f :=
  SimpleFunc.setToSimpleFunc_add_left' T T' T'' h_add (SimpleFunc.integrable f)
#align measure_theory.L1.simple_func.set_to_L1s_add_left' MeasureTheory.L1.SimpleFunc.setToL1S_add_left'

theorem setToL1S_smul_left (T : Set α → E →L[ℝ] F) (c : ℝ) (f : α →₁ₛ[μ] E) :
    setToL1S (fun s => c • T s) f = c • setToL1S T f :=
  SimpleFunc.setToSimpleFunc_smul_left T c _
#align measure_theory.L1.simple_func.set_to_L1s_smul_left MeasureTheory.L1.SimpleFunc.setToL1S_smul_left

theorem setToL1S_smul_left' (T T' : Set α → E →L[ℝ] F) (c : ℝ)
    (h_smul : ∀ s, MeasurableSet s → μ s < ∞ → T' s = c • T s) (f : α →₁ₛ[μ] E) :
    setToL1S T' f = c • setToL1S T f :=
  SimpleFunc.setToSimpleFunc_smul_left' T T' c h_smul (SimpleFunc.integrable f)
#align measure_theory.L1.simple_func.set_to_L1s_smul_left' MeasureTheory.L1.SimpleFunc.setToL1S_smul_left'

theorem setToL1S_add (T : Set α → E →L[ℝ] F) (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0)
    (h_add : FinMeasAdditive μ T) (f g : α →₁ₛ[μ] E) :
    setToL1S T (f + g) = setToL1S T f + setToL1S T g := by
  simp_rw [setToL1S]
  -- ⊢ SimpleFunc.setToSimpleFunc T (toSimpleFunc (f + g)) = SimpleFunc.setToSimple …
  rw [← SimpleFunc.setToSimpleFunc_add T h_add (SimpleFunc.integrable f)
      (SimpleFunc.integrable g)]
  exact
    SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable _)
      (add_toSimpleFunc f g)
#align measure_theory.L1.simple_func.set_to_L1s_add MeasureTheory.L1.SimpleFunc.setToL1S_add

theorem setToL1S_neg {T : Set α → E →L[ℝ] F} (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0)
    (h_add : FinMeasAdditive μ T) (f : α →₁ₛ[μ] E) : setToL1S T (-f) = -setToL1S T f := by
  simp_rw [setToL1S]
  -- ⊢ SimpleFunc.setToSimpleFunc T (toSimpleFunc (-f)) = -SimpleFunc.setToSimpleFu …
  have : simpleFunc.toSimpleFunc (-f) =ᵐ[μ] ⇑(-simpleFunc.toSimpleFunc f) :=
    neg_toSimpleFunc f
  rw [SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable _) this]
  -- ⊢ SimpleFunc.setToSimpleFunc T (-toSimpleFunc f) = -SimpleFunc.setToSimpleFunc …
  exact SimpleFunc.setToSimpleFunc_neg T h_add (SimpleFunc.integrable f)
  -- 🎉 no goals
#align measure_theory.L1.simple_func.set_to_L1s_neg MeasureTheory.L1.SimpleFunc.setToL1S_neg

theorem setToL1S_sub {T : Set α → E →L[ℝ] F} (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0)
    (h_add : FinMeasAdditive μ T) (f g : α →₁ₛ[μ] E) :
    setToL1S T (f - g) = setToL1S T f - setToL1S T g := by
  rw [sub_eq_add_neg, setToL1S_add T h_zero h_add, setToL1S_neg h_zero h_add, sub_eq_add_neg]
  -- 🎉 no goals
#align measure_theory.L1.simple_func.set_to_L1s_sub MeasureTheory.L1.SimpleFunc.setToL1S_sub

set_option synthInstance.maxHeartbeats 30000 in
theorem setToL1S_smul_real (T : Set α → E →L[ℝ] F)
    (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0) (h_add : FinMeasAdditive μ T) (c : ℝ)
    (f : α →₁ₛ[μ] E) : setToL1S T (c • f) = c • setToL1S T f := by
  simp_rw [setToL1S]
  -- ⊢ SimpleFunc.setToSimpleFunc T (toSimpleFunc (c • f)) = c • SimpleFunc.setToSi …
  rw [← SimpleFunc.setToSimpleFunc_smul_real T h_add c (SimpleFunc.integrable f)]
  -- ⊢ SimpleFunc.setToSimpleFunc T (toSimpleFunc (c • f)) = SimpleFunc.setToSimple …
  refine' SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable _) _
  -- ⊢ ↑(toSimpleFunc (c • f)) =ᵐ[μ] ↑(c • toSimpleFunc f)
  exact smul_toSimpleFunc c f
  -- 🎉 no goals
#align measure_theory.L1.simple_func.set_to_L1s_smul_real MeasureTheory.L1.SimpleFunc.setToL1S_smul_real

set_option synthInstance.maxHeartbeats 30000 in
theorem setToL1S_smul {E} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
    [NormedSpace 𝕜 F] (T : Set α → E →L[ℝ] F) (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0)
    (h_add : FinMeasAdditive μ T) (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (c : 𝕜)
    (f : α →₁ₛ[μ] E) : setToL1S T (c • f) = c • setToL1S T f := by
  simp_rw [setToL1S]
  -- ⊢ SimpleFunc.setToSimpleFunc T (toSimpleFunc (c • f)) = c • SimpleFunc.setToSi …
  rw [← SimpleFunc.setToSimpleFunc_smul T h_add h_smul c (SimpleFunc.integrable f)]
  -- ⊢ SimpleFunc.setToSimpleFunc T (toSimpleFunc (c • f)) = SimpleFunc.setToSimple …
  refine' SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable _) _
  -- ⊢ ↑(toSimpleFunc (c • f)) =ᵐ[μ] ↑(c • toSimpleFunc f)
  exact smul_toSimpleFunc c f
  -- 🎉 no goals
#align measure_theory.L1.simple_func.set_to_L1s_smul MeasureTheory.L1.SimpleFunc.setToL1S_smul

theorem norm_setToL1S_le (T : Set α → E →L[ℝ] F) {C : ℝ}
    (hT_norm : ∀ s, MeasurableSet s → μ s < ∞ → ‖T s‖ ≤ C * (μ s).toReal) (f : α →₁ₛ[μ] E) :
    ‖setToL1S T f‖ ≤ C * ‖f‖ := by
  rw [setToL1S, norm_eq_sum_mul f]
  -- ⊢ ‖SimpleFunc.setToSimpleFunc T (toSimpleFunc f)‖ ≤ C * ∑ x in SimpleFunc.rang …
  exact
    SimpleFunc.norm_setToSimpleFunc_le_sum_mul_norm_of_integrable T hT_norm _
      (SimpleFunc.integrable f)
#align measure_theory.L1.simple_func.norm_set_to_L1s_le MeasureTheory.L1.SimpleFunc.norm_setToL1S_le

theorem setToL1S_indicatorConst {T : Set α → E →L[ℝ] F} {s : Set α}
    (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0) (h_add : FinMeasAdditive μ T)
    (hs : MeasurableSet s) (hμs : μ s < ∞) (x : E) :
    setToL1S T (simpleFunc.indicatorConst 1 hs hμs.ne x) = T s x := by
  have h_empty : T ∅ = 0 := h_zero _ MeasurableSet.empty measure_empty
  -- ⊢ setToL1S T (indicatorConst 1 hs (_ : ↑↑μ s ≠ ⊤) x) = ↑(T s) x
  rw [setToL1S_eq_setToSimpleFunc]
  -- ⊢ SimpleFunc.setToSimpleFunc T (toSimpleFunc (indicatorConst 1 hs (_ : ↑↑μ s ≠ …
  refine' Eq.trans _ (SimpleFunc.setToSimpleFunc_indicator T h_empty hs x)
  -- ⊢ SimpleFunc.setToSimpleFunc T (toSimpleFunc (indicatorConst 1 hs (_ : ↑↑μ s ≠ …
  refine' SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable _) _
  -- ⊢ ↑(toSimpleFunc (indicatorConst 1 hs (_ : ↑↑μ s ≠ ⊤) x)) =ᵐ[μ] ↑(SimpleFunc.p …
  exact toSimpleFunc_indicatorConst hs hμs.ne x
  -- 🎉 no goals
#align measure_theory.L1.simple_func.set_to_L1s_indicator_const MeasureTheory.L1.SimpleFunc.setToL1S_indicatorConst

theorem setToL1S_const [IsFiniteMeasure μ] {T : Set α → E →L[ℝ] F}
    (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0) (h_add : FinMeasAdditive μ T) (x : E) :
    setToL1S T (simpleFunc.indicatorConst 1 MeasurableSet.univ (measure_ne_top μ _) x) = T univ x :=
  setToL1S_indicatorConst h_zero h_add MeasurableSet.univ (measure_lt_top _ _) x
#align measure_theory.L1.simple_func.set_to_L1s_const MeasureTheory.L1.SimpleFunc.setToL1S_const

section Order

variable {G'' G' : Type*} [NormedLatticeAddCommGroup G'] [NormedSpace ℝ G']
  [NormedLatticeAddCommGroup G''] [NormedSpace ℝ G''] {T : Set α → G'' →L[ℝ] G'}

theorem setToL1S_mono_left {T T' : Set α → E →L[ℝ] G''} (hTT' : ∀ s x, T s x ≤ T' s x)
    (f : α →₁ₛ[μ] E) : setToL1S T f ≤ setToL1S T' f :=
  SimpleFunc.setToSimpleFunc_mono_left T T' hTT' _
#align measure_theory.L1.simple_func.set_to_L1s_mono_left MeasureTheory.L1.SimpleFunc.setToL1S_mono_left

theorem setToL1S_mono_left' {T T' : Set α → E →L[ℝ] G''}
    (hTT' : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, T s x ≤ T' s x) (f : α →₁ₛ[μ] E) :
    setToL1S T f ≤ setToL1S T' f :=
  SimpleFunc.setToSimpleFunc_mono_left' T T' hTT' _ (SimpleFunc.integrable f)
#align measure_theory.L1.simple_func.set_to_L1s_mono_left' MeasureTheory.L1.SimpleFunc.setToL1S_mono_left'

theorem setToL1S_nonneg (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0)
    (h_add : FinMeasAdditive μ T)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f : α →₁ₛ[μ] G''}
    (hf : 0 ≤ f) : 0 ≤ setToL1S T f := by
  simp_rw [setToL1S]
  -- ⊢ 0 ≤ SimpleFunc.setToSimpleFunc T (toSimpleFunc f)
  obtain ⟨f', hf', hff'⟩ : ∃ f' : α →ₛ G'', 0 ≤ f' ∧ simpleFunc.toSimpleFunc f =ᵐ[μ] f' := by
    obtain ⟨f'', hf'', hff''⟩ := exists_simpleFunc_nonneg_ae_eq hf
    exact ⟨f'', hf'', (Lp.simpleFunc.toSimpleFunc_eq_toFun f).trans hff''⟩
  rw [SimpleFunc.setToSimpleFunc_congr _ h_zero h_add (SimpleFunc.integrable _) hff']
  -- ⊢ 0 ≤ SimpleFunc.setToSimpleFunc (fun s => T s) f'
  exact
    SimpleFunc.setToSimpleFunc_nonneg' T hT_nonneg _ hf' ((SimpleFunc.integrable f).congr hff')
#align measure_theory.L1.simple_func.set_to_L1s_nonneg MeasureTheory.L1.SimpleFunc.setToL1S_nonneg

theorem setToL1S_mono (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0)
    (h_add : FinMeasAdditive μ T)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f g : α →₁ₛ[μ] G''}
    (hfg : f ≤ g) : setToL1S T f ≤ setToL1S T g := by
  rw [← sub_nonneg] at hfg ⊢
  -- ⊢ 0 ≤ setToL1S T g - setToL1S T f
  rw [← setToL1S_sub h_zero h_add]
  -- ⊢ 0 ≤ setToL1S (fun s => T s) (g - f)
  exact setToL1S_nonneg h_zero h_add hT_nonneg hfg
  -- 🎉 no goals
#align measure_theory.L1.simple_func.set_to_L1s_mono MeasureTheory.L1.SimpleFunc.setToL1S_mono

end Order

variable [NormedSpace 𝕜 F]

variable (α E μ 𝕜)

/-- Extend `Set α → E →L[ℝ] F` to `(α →₁ₛ[μ] E) →L[𝕜] F`. -/
def setToL1SCLM' {T : Set α → E →L[ℝ] F} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) : (α →₁ₛ[μ] E) →L[𝕜] F :=
  LinearMap.mkContinuous
    ⟨⟨setToL1S T, setToL1S_add T (fun _ => hT.eq_zero_of_measure_zero) hT.1⟩,
      setToL1S_smul T (fun _ => hT.eq_zero_of_measure_zero) hT.1 h_smul⟩
    C fun f => norm_setToL1S_le T hT.2 f
#align measure_theory.L1.simple_func.set_to_L1s_clm' MeasureTheory.L1.SimpleFunc.setToL1SCLM'

/-- Extend `Set α → E →L[ℝ] F` to `(α →₁ₛ[μ] E) →L[ℝ] F`. -/
def setToL1SCLM {T : Set α → E →L[ℝ] F} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C) :
    (α →₁ₛ[μ] E) →L[ℝ] F :=
  LinearMap.mkContinuous
    ⟨⟨setToL1S T, setToL1S_add T (fun _ => hT.eq_zero_of_measure_zero) hT.1⟩,
      setToL1S_smul_real T (fun _ => hT.eq_zero_of_measure_zero) hT.1⟩
    C fun f => norm_setToL1S_le T hT.2 f
#align measure_theory.L1.simple_func.set_to_L1s_clm MeasureTheory.L1.SimpleFunc.setToL1SCLM

variable {α E μ 𝕜}

variable {T T' T'' : Set α → E →L[ℝ] F} {C C' C'' : ℝ}

@[simp]
theorem setToL1SCLM_zero_left (hT : DominatedFinMeasAdditive μ (0 : Set α → E →L[ℝ] F) C)
    (f : α →₁ₛ[μ] E) : setToL1SCLM α E μ hT f = 0 :=
  setToL1S_zero_left _
#align measure_theory.L1.simple_func.set_to_L1s_clm_zero_left MeasureTheory.L1.SimpleFunc.setToL1SCLM_zero_left

theorem setToL1SCLM_zero_left' (hT : DominatedFinMeasAdditive μ T C)
    (h_zero : ∀ s, MeasurableSet s → μ s < ∞ → T s = 0) (f : α →₁ₛ[μ] E) :
    setToL1SCLM α E μ hT f = 0 :=
  setToL1S_zero_left' h_zero f
#align measure_theory.L1.simple_func.set_to_L1s_clm_zero_left' MeasureTheory.L1.SimpleFunc.setToL1SCLM_zero_left'

theorem setToL1SCLM_congr_left (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (h : T = T') (f : α →₁ₛ[μ] E) :
    setToL1SCLM α E μ hT f = setToL1SCLM α E μ hT' f :=
  setToL1S_congr_left T T' (fun _ _ _ => by rw [h]) f
                                            -- 🎉 no goals
#align measure_theory.L1.simple_func.set_to_L1s_clm_congr_left MeasureTheory.L1.SimpleFunc.setToL1SCLM_congr_left

theorem setToL1SCLM_congr_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (h : ∀ s, MeasurableSet s → μ s < ∞ → T s = T' s)
    (f : α →₁ₛ[μ] E) : setToL1SCLM α E μ hT f = setToL1SCLM α E μ hT' f :=
  setToL1S_congr_left T T' h f
#align measure_theory.L1.simple_func.set_to_L1s_clm_congr_left' MeasureTheory.L1.SimpleFunc.setToL1SCLM_congr_left'

theorem setToL1SCLM_congr_measure {μ' : Measure α} (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ' T C') (hμ : μ ≪ μ') (f : α →₁ₛ[μ] E) (f' : α →₁ₛ[μ'] E)
    (h : (f : α → E) =ᵐ[μ] f') : setToL1SCLM α E μ hT f = setToL1SCLM α E μ' hT' f' :=
  setToL1S_congr_measure T (fun _ => hT.eq_zero_of_measure_zero) hT.1 hμ _ _ h
#align measure_theory.L1.simple_func.set_to_L1s_clm_congr_measure MeasureTheory.L1.SimpleFunc.setToL1SCLM_congr_measure

theorem setToL1SCLM_add_left (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (f : α →₁ₛ[μ] E) :
    setToL1SCLM α E μ (hT.add hT') f = setToL1SCLM α E μ hT f + setToL1SCLM α E μ hT' f :=
  setToL1S_add_left T T' f
#align measure_theory.L1.simple_func.set_to_L1s_clm_add_left MeasureTheory.L1.SimpleFunc.setToL1SCLM_add_left

theorem setToL1SCLM_add_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (hT'' : DominatedFinMeasAdditive μ T'' C'')
    (h_add : ∀ s, MeasurableSet s → μ s < ∞ → T'' s = T s + T' s) (f : α →₁ₛ[μ] E) :
    setToL1SCLM α E μ hT'' f = setToL1SCLM α E μ hT f + setToL1SCLM α E μ hT' f :=
  setToL1S_add_left' T T' T'' h_add f
#align measure_theory.L1.simple_func.set_to_L1s_clm_add_left' MeasureTheory.L1.SimpleFunc.setToL1SCLM_add_left'

theorem setToL1SCLM_smul_left (c : ℝ) (hT : DominatedFinMeasAdditive μ T C) (f : α →₁ₛ[μ] E) :
    setToL1SCLM α E μ (hT.smul c) f = c • setToL1SCLM α E μ hT f :=
  setToL1S_smul_left T c f
#align measure_theory.L1.simple_func.set_to_L1s_clm_smul_left MeasureTheory.L1.SimpleFunc.setToL1SCLM_smul_left

theorem setToL1SCLM_smul_left' (c : ℝ) (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C')
    (h_smul : ∀ s, MeasurableSet s → μ s < ∞ → T' s = c • T s) (f : α →₁ₛ[μ] E) :
    setToL1SCLM α E μ hT' f = c • setToL1SCLM α E μ hT f :=
  setToL1S_smul_left' T T' c h_smul f
#align measure_theory.L1.simple_func.set_to_L1s_clm_smul_left' MeasureTheory.L1.SimpleFunc.setToL1SCLM_smul_left'

theorem norm_setToL1SCLM_le {T : Set α → E →L[ℝ] F} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (hC : 0 ≤ C) : ‖setToL1SCLM α E μ hT‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _
#align measure_theory.L1.simple_func.norm_set_to_L1s_clm_le MeasureTheory.L1.SimpleFunc.norm_setToL1SCLM_le

theorem norm_setToL1SCLM_le' {T : Set α → E →L[ℝ] F} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C) :
    ‖setToL1SCLM α E μ hT‖ ≤ max C 0 :=
  LinearMap.mkContinuous_norm_le' _ _
#align measure_theory.L1.simple_func.norm_set_to_L1s_clm_le' MeasureTheory.L1.SimpleFunc.norm_setToL1SCLM_le'

theorem setToL1SCLM_const [IsFiniteMeasure μ] {T : Set α → E →L[ℝ] F} {C : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (x : E) :
    setToL1SCLM α E μ hT (simpleFunc.indicatorConst 1 MeasurableSet.univ (measure_ne_top μ _) x) =
      T univ x :=
  setToL1S_const (fun _ => hT.eq_zero_of_measure_zero) hT.1 x
#align measure_theory.L1.simple_func.set_to_L1s_clm_const MeasureTheory.L1.SimpleFunc.setToL1SCLM_const

section Order

variable {G' G'' : Type*} [NormedLatticeAddCommGroup G''] [NormedSpace ℝ G'']
  [NormedLatticeAddCommGroup G'] [NormedSpace ℝ G']

theorem setToL1SCLM_mono_left {T T' : Set α → E →L[ℝ] G''} {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (hTT' : ∀ s x, T s x ≤ T' s x) (f : α →₁ₛ[μ] E) :
    setToL1SCLM α E μ hT f ≤ setToL1SCLM α E μ hT' f :=
  SimpleFunc.setToSimpleFunc_mono_left T T' hTT' _
#align measure_theory.L1.simple_func.set_to_L1s_clm_mono_left MeasureTheory.L1.SimpleFunc.setToL1SCLM_mono_left

theorem setToL1SCLM_mono_left' {T T' : Set α → E →L[ℝ] G''} {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (hTT' : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, T s x ≤ T' s x) (f : α →₁ₛ[μ] E) :
    setToL1SCLM α E μ hT f ≤ setToL1SCLM α E μ hT' f :=
  SimpleFunc.setToSimpleFunc_mono_left' T T' hTT' _ (SimpleFunc.integrable f)
#align measure_theory.L1.simple_func.set_to_L1s_clm_mono_left' MeasureTheory.L1.SimpleFunc.setToL1SCLM_mono_left'

theorem setToL1SCLM_nonneg {T : Set α → G' →L[ℝ] G''} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f : α →₁ₛ[μ] G'}
    (hf : 0 ≤ f) : 0 ≤ setToL1SCLM α G' μ hT f :=
  setToL1S_nonneg (fun _ => hT.eq_zero_of_measure_zero) hT.1 hT_nonneg hf
#align measure_theory.L1.simple_func.set_to_L1s_clm_nonneg MeasureTheory.L1.SimpleFunc.setToL1SCLM_nonneg

theorem setToL1SCLM_mono {T : Set α → G' →L[ℝ] G''} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f g : α →₁ₛ[μ] G'}
    (hfg : f ≤ g) : setToL1SCLM α G' μ hT f ≤ setToL1SCLM α G' μ hT g :=
  setToL1S_mono (fun _ => hT.eq_zero_of_measure_zero) hT.1 hT_nonneg hfg
#align measure_theory.L1.simple_func.set_to_L1s_clm_mono MeasureTheory.L1.SimpleFunc.setToL1SCLM_mono

end Order

end SetToL1S

end SimpleFunc

open SimpleFunc

section SetToL1

attribute [local instance] Lp.simpleFunc.module

attribute [local instance] Lp.simpleFunc.normedSpace

variable (𝕜) [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [CompleteSpace F]
  {T T' T'' : Set α → E →L[ℝ] F} {C C' C'' : ℝ}

/-- Extend `set α → (E →L[ℝ] F)` to `(α →₁[μ] E) →L[𝕜] F`. -/
def setToL1' (hT : DominatedFinMeasAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) : (α →₁[μ] E) →L[𝕜] F :=
  (setToL1SCLM' α E 𝕜 μ hT h_smul).extend (coeToLp α E 𝕜) (simpleFunc.denseRange one_ne_top)
    simpleFunc.uniformInducing
#align measure_theory.L1.set_to_L1' MeasureTheory.L1.setToL1'

variable {𝕜}

/-- Extend `Set α → E →L[ℝ] F` to `(α →₁[μ] E) →L[ℝ] F`. -/
def setToL1 (hT : DominatedFinMeasAdditive μ T C) : (α →₁[μ] E) →L[ℝ] F :=
  (setToL1SCLM α E μ hT).extend (coeToLp α E ℝ) (simpleFunc.denseRange one_ne_top)
    simpleFunc.uniformInducing
#align measure_theory.L1.set_to_L1 MeasureTheory.L1.setToL1

theorem setToL1_eq_setToL1SCLM (hT : DominatedFinMeasAdditive μ T C) (f : α →₁ₛ[μ] E) :
    setToL1 hT f = setToL1SCLM α E μ hT f :=
  uniformly_extend_of_ind simpleFunc.uniformInducing (simpleFunc.denseRange one_ne_top)
    (setToL1SCLM α E μ hT).uniformContinuous _
#align measure_theory.L1.set_to_L1_eq_set_to_L1s_clm MeasureTheory.L1.setToL1_eq_setToL1SCLM

theorem setToL1_eq_setToL1' (hT : DominatedFinMeasAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (f : α →₁[μ] E) :
    setToL1 hT f = setToL1' 𝕜 hT h_smul f :=
  rfl
#align measure_theory.L1.set_to_L1_eq_set_to_L1' MeasureTheory.L1.setToL1_eq_setToL1'

@[simp]
theorem setToL1_zero_left (hT : DominatedFinMeasAdditive μ (0 : Set α → E →L[ℝ] F) C)
    (f : α →₁[μ] E) : setToL1 hT f = 0 := by
  suffices setToL1 hT = 0 by rw [this]; simp
  -- ⊢ setToL1 hT = 0
  refine' ContinuousLinearMap.extend_unique (setToL1SCLM α E μ hT) _ _ _ _ _
  -- ⊢ ContinuousLinearMap.comp 0 (coeToLp α E ℝ) = setToL1SCLM α E μ hT
  ext1 f
  -- ⊢ ↑(ContinuousLinearMap.comp 0 (coeToLp α E ℝ)) f = ↑(setToL1SCLM α E μ hT) f
  rw [setToL1SCLM_zero_left hT f, ContinuousLinearMap.zero_comp, ContinuousLinearMap.zero_apply]
  -- 🎉 no goals
#align measure_theory.L1.set_to_L1_zero_left MeasureTheory.L1.setToL1_zero_left

theorem setToL1_zero_left' (hT : DominatedFinMeasAdditive μ T C)
    (h_zero : ∀ s, MeasurableSet s → μ s < ∞ → T s = 0) (f : α →₁[μ] E) : setToL1 hT f = 0 := by
  suffices setToL1 hT = 0 by rw [this]; simp
  -- ⊢ setToL1 hT = 0
  refine' ContinuousLinearMap.extend_unique (setToL1SCLM α E μ hT) _ _ _ _ _
  -- ⊢ ContinuousLinearMap.comp 0 (coeToLp α E ℝ) = setToL1SCLM α E μ hT
  ext1 f
  -- ⊢ ↑(ContinuousLinearMap.comp 0 (coeToLp α E ℝ)) f = ↑(setToL1SCLM α E μ hT) f
  rw [setToL1SCLM_zero_left' hT h_zero f, ContinuousLinearMap.zero_comp,
    ContinuousLinearMap.zero_apply]
#align measure_theory.L1.set_to_L1_zero_left' MeasureTheory.L1.setToL1_zero_left'

theorem setToL1_congr_left (T T' : Set α → E →L[ℝ] F) {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C') (h : T = T')
    (f : α →₁[μ] E) : setToL1 hT f = setToL1 hT' f := by
  suffices setToL1 hT = setToL1 hT' by rw [this]
  -- ⊢ setToL1 hT = setToL1 hT'
  refine' ContinuousLinearMap.extend_unique (setToL1SCLM α E μ hT) _ _ _ _ _
  -- ⊢ ContinuousLinearMap.comp (setToL1 hT') (coeToLp α E ℝ) = setToL1SCLM α E μ hT
  ext1 f
  -- ⊢ ↑(ContinuousLinearMap.comp (setToL1 hT') (coeToLp α E ℝ)) f = ↑(setToL1SCLM  …
  suffices setToL1 hT' f = setToL1SCLM α E μ hT f by rw [← this]; rfl
  -- ⊢ ↑(setToL1 hT') ↑f = ↑(setToL1SCLM α E μ hT) f
  rw [setToL1_eq_setToL1SCLM]
  -- ⊢ ↑(setToL1SCLM α E μ hT') f = ↑(setToL1SCLM α E μ hT) f
  exact setToL1SCLM_congr_left hT' hT h.symm f
  -- 🎉 no goals
#align measure_theory.L1.set_to_L1_congr_left MeasureTheory.L1.setToL1_congr_left

theorem setToL1_congr_left' (T T' : Set α → E →L[ℝ] F) {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (h : ∀ s, MeasurableSet s → μ s < ∞ → T s = T' s) (f : α →₁[μ] E) :
    setToL1 hT f = setToL1 hT' f := by
  suffices setToL1 hT = setToL1 hT' by rw [this]
  -- ⊢ setToL1 hT = setToL1 hT'
  refine' ContinuousLinearMap.extend_unique (setToL1SCLM α E μ hT) _ _ _ _ _
  -- ⊢ ContinuousLinearMap.comp (setToL1 hT') (coeToLp α E ℝ) = setToL1SCLM α E μ hT
  ext1 f
  -- ⊢ ↑(ContinuousLinearMap.comp (setToL1 hT') (coeToLp α E ℝ)) f = ↑(setToL1SCLM  …
  suffices setToL1 hT' f = setToL1SCLM α E μ hT f by rw [← this]; rfl
  -- ⊢ ↑(setToL1 hT') ↑f = ↑(setToL1SCLM α E μ hT) f
  rw [setToL1_eq_setToL1SCLM]
  -- ⊢ ↑(setToL1SCLM α E μ hT') f = ↑(setToL1SCLM α E μ hT) f
  exact (setToL1SCLM_congr_left' hT hT' h f).symm
  -- 🎉 no goals
#align measure_theory.L1.set_to_L1_congr_left' MeasureTheory.L1.setToL1_congr_left'

theorem setToL1_add_left (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (f : α →₁[μ] E) :
    setToL1 (hT.add hT') f = setToL1 hT f + setToL1 hT' f := by
  suffices setToL1 (hT.add hT') = setToL1 hT + setToL1 hT' by
    rw [this, ContinuousLinearMap.add_apply]
  refine' ContinuousLinearMap.extend_unique (setToL1SCLM α E μ (hT.add hT')) _ _ _ _ _
  -- ⊢ ContinuousLinearMap.comp (setToL1 hT + setToL1 hT') (coeToLp α E ℝ) = setToL …
  ext1 f
  -- ⊢ ↑(ContinuousLinearMap.comp (setToL1 hT + setToL1 hT') (coeToLp α E ℝ)) f = ↑ …
  simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.add_apply]
  suffices setToL1 hT f + setToL1 hT' f = setToL1SCLM α E μ (hT.add hT') f by
    rw [← this]; rfl
  rw [setToL1_eq_setToL1SCLM, setToL1_eq_setToL1SCLM, setToL1SCLM_add_left hT hT']
  -- 🎉 no goals
#align measure_theory.L1.set_to_L1_add_left MeasureTheory.L1.setToL1_add_left

theorem setToL1_add_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (hT'' : DominatedFinMeasAdditive μ T'' C'')
    (h_add : ∀ s, MeasurableSet s → μ s < ∞ → T'' s = T s + T' s) (f : α →₁[μ] E) :
    setToL1 hT'' f = setToL1 hT f + setToL1 hT' f := by
  suffices setToL1 hT'' = setToL1 hT + setToL1 hT' by rw [this, ContinuousLinearMap.add_apply]
  -- ⊢ setToL1 hT'' = setToL1 hT + setToL1 hT'
  refine' ContinuousLinearMap.extend_unique (setToL1SCLM α E μ hT'') _ _ _ _ _
  -- ⊢ ContinuousLinearMap.comp (setToL1 hT + setToL1 hT') (coeToLp α E ℝ) = setToL …
  ext1 f
  -- ⊢ ↑(ContinuousLinearMap.comp (setToL1 hT + setToL1 hT') (coeToLp α E ℝ)) f = ↑ …
  simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.add_apply]
  suffices setToL1 hT f + setToL1 hT' f = setToL1SCLM α E μ hT'' f by rw [← this]; congr
  -- ⊢ ↑(setToL1 hT) ↑f + ↑(setToL1 hT') ↑f = ↑(setToL1SCLM α E μ hT'') f
  rw [setToL1_eq_setToL1SCLM, setToL1_eq_setToL1SCLM,
    setToL1SCLM_add_left' hT hT' hT'' h_add]
#align measure_theory.L1.set_to_L1_add_left' MeasureTheory.L1.setToL1_add_left'

theorem setToL1_smul_left (hT : DominatedFinMeasAdditive μ T C) (c : ℝ) (f : α →₁[μ] E) :
    setToL1 (hT.smul c) f = c • setToL1 hT f := by
  suffices setToL1 (hT.smul c) = c • setToL1 hT by rw [this, ContinuousLinearMap.smul_apply]
  -- ⊢ setToL1 (_ : DominatedFinMeasAdditive μ (fun s => c • T s) (‖c‖ * C)) = c •  …
  refine' ContinuousLinearMap.extend_unique (setToL1SCLM α E μ (hT.smul c)) _ _ _ _ _
  -- ⊢ ContinuousLinearMap.comp (c • setToL1 hT) (coeToLp α E ℝ) = setToL1SCLM α E  …
  ext1 f
  -- ⊢ ↑(ContinuousLinearMap.comp (c • setToL1 hT) (coeToLp α E ℝ)) f = ↑(setToL1SC …
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.smul_comp,
    Pi.smul_apply, ContinuousLinearMap.coe_smul']
  suffices c • setToL1 hT f = setToL1SCLM α E μ (hT.smul c) f by rw [← this]; congr
  -- ⊢ c • ↑(setToL1 hT) ↑f = ↑(setToL1SCLM α E μ (_ : DominatedFinMeasAdditive μ ( …
  rw [setToL1_eq_setToL1SCLM, setToL1SCLM_smul_left c hT]
  -- 🎉 no goals
#align measure_theory.L1.set_to_L1_smul_left MeasureTheory.L1.setToL1_smul_left

theorem setToL1_smul_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (c : ℝ)
    (h_smul : ∀ s, MeasurableSet s → μ s < ∞ → T' s = c • T s) (f : α →₁[μ] E) :
    setToL1 hT' f = c • setToL1 hT f := by
  suffices setToL1 hT' = c • setToL1 hT by rw [this, ContinuousLinearMap.smul_apply]
  -- ⊢ setToL1 hT' = c • setToL1 hT
  refine' ContinuousLinearMap.extend_unique (setToL1SCLM α E μ hT') _ _ _ _ _
  -- ⊢ ContinuousLinearMap.comp (c • setToL1 hT) (coeToLp α E ℝ) = setToL1SCLM α E  …
  ext1 f
  -- ⊢ ↑(ContinuousLinearMap.comp (c • setToL1 hT) (coeToLp α E ℝ)) f = ↑(setToL1SC …
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.smul_comp,
    Pi.smul_apply, ContinuousLinearMap.coe_smul']
  suffices c • setToL1 hT f = setToL1SCLM α E μ hT' f by rw [← this]; congr
  -- ⊢ c • ↑(setToL1 hT) ↑f = ↑(setToL1SCLM α E μ hT') f
  rw [setToL1_eq_setToL1SCLM, setToL1SCLM_smul_left' c hT hT' h_smul]
  -- 🎉 no goals
#align measure_theory.L1.set_to_L1_smul_left' MeasureTheory.L1.setToL1_smul_left'

theorem setToL1_smul (hT : DominatedFinMeasAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (c : 𝕜) (f : α →₁[μ] E) :
    setToL1 hT (c • f) = c • setToL1 hT f := by
  rw [setToL1_eq_setToL1' hT h_smul, setToL1_eq_setToL1' hT h_smul]
  -- ⊢ ↑(setToL1' 𝕜 hT h_smul) (c • f) = c • ↑(setToL1' 𝕜 hT h_smul) f
  exact ContinuousLinearMap.map_smul _ _ _
  -- 🎉 no goals
#align measure_theory.L1.set_to_L1_smul MeasureTheory.L1.setToL1_smul

theorem setToL1_simpleFunc_indicatorConst (hT : DominatedFinMeasAdditive μ T C) {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s < ∞) (x : E) :
    setToL1 hT (simpleFunc.indicatorConst 1 hs hμs.ne x) = T s x := by
  rw [setToL1_eq_setToL1SCLM]
  -- ⊢ ↑(setToL1SCLM α E μ hT) (indicatorConst 1 hs (_ : ↑↑μ s ≠ ⊤) x) = ↑(T s) x
  exact setToL1S_indicatorConst (fun s => hT.eq_zero_of_measure_zero) hT.1 hs hμs x
  -- 🎉 no goals
#align measure_theory.L1.set_to_L1_simple_func_indicator_const MeasureTheory.L1.setToL1_simpleFunc_indicatorConst

theorem setToL1_indicatorConstLp (hT : DominatedFinMeasAdditive μ T C) {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E) :
    setToL1 hT (indicatorConstLp 1 hs hμs x) = T s x := by
  rw [← Lp.simpleFunc.coe_indicatorConst hs hμs x]
  -- ⊢ ↑(setToL1 hT) ↑(indicatorConst 1 hs hμs x) = ↑(T s) x
  exact setToL1_simpleFunc_indicatorConst hT hs hμs.lt_top x
  -- 🎉 no goals
#align measure_theory.L1.set_to_L1_indicator_const_Lp MeasureTheory.L1.setToL1_indicatorConstLp

theorem setToL1_const [IsFiniteMeasure μ] (hT : DominatedFinMeasAdditive μ T C) (x : E) :
    setToL1 hT (indicatorConstLp 1 MeasurableSet.univ (measure_ne_top _ _) x) = T univ x :=
  setToL1_indicatorConstLp hT MeasurableSet.univ (measure_ne_top _ _) x
#align measure_theory.L1.set_to_L1_const MeasureTheory.L1.setToL1_const

section Order

variable {G' G'' : Type*} [NormedLatticeAddCommGroup G''] [NormedSpace ℝ G''] [CompleteSpace G'']
  [NormedLatticeAddCommGroup G'] [NormedSpace ℝ G']

theorem setToL1_mono_left' {T T' : Set α → E →L[ℝ] G''} {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (hTT' : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, T s x ≤ T' s x) (f : α →₁[μ] E) :
    setToL1 hT f ≤ setToL1 hT' f := by
  induction f using Lp.induction with
  | hp_ne_top h => exact one_ne_top h
  | @h_ind c s hs hμs =>
    rw [setToL1_simpleFunc_indicatorConst hT hs hμs, setToL1_simpleFunc_indicatorConst hT' hs hμs]
    exact hTT' s hs hμs c
  | @h_add f g hf hg _ hf_le hg_le =>
    rw [(setToL1 hT).map_add, (setToL1 hT').map_add]
    exact add_le_add hf_le hg_le
  | h_closed => exact isClosed_le (setToL1 hT).continuous (setToL1 hT').continuous
#align measure_theory.L1.set_to_L1_mono_left' MeasureTheory.L1.setToL1_mono_left'

theorem setToL1_mono_left {T T' : Set α → E →L[ℝ] G''} {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (hTT' : ∀ s x, T s x ≤ T' s x) (f : α →₁[μ] E) : setToL1 hT f ≤ setToL1 hT' f :=
  setToL1_mono_left' hT hT' (fun s _ _ x => hTT' s x) f
#align measure_theory.L1.set_to_L1_mono_left MeasureTheory.L1.setToL1_mono_left

theorem setToL1_nonneg {T : Set α → G' →L[ℝ] G''} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f : α →₁[μ] G'}
    (hf : 0 ≤ f) : 0 ≤ setToL1 hT f := by
  suffices : ∀ f : { g : α →₁[μ] G' // 0 ≤ g }, 0 ≤ setToL1 hT f
  -- ⊢ 0 ≤ ↑(setToL1 hT) f
  exact this (⟨f, hf⟩ : { g : α →₁[μ] G' // 0 ≤ g })
  -- ⊢ ∀ (f : { g // 0 ≤ g }), 0 ≤ ↑(setToL1 hT) ↑f
  refine' fun g =>
    @isClosed_property { g : α →₁ₛ[μ] G' // 0 ≤ g } { g : α →₁[μ] G' // 0 ≤ g } _ _
      (fun g => 0 ≤ setToL1 hT g)
      (denseRange_coeSimpleFuncNonnegToLpNonneg 1 μ G' one_ne_top) _ _ g
  · exact isClosed_le continuous_zero ((setToL1 hT).continuous.comp continuous_induced_dom)
    -- 🎉 no goals
  · intro g
    -- ⊢ 0 ≤ ↑(setToL1 hT) ↑(coeSimpleFuncNonnegToLpNonneg 1 μ G' g)
    have : (coeSimpleFuncNonnegToLpNonneg 1 μ G' g : α →₁[μ] G') = (g : α →₁ₛ[μ] G') := rfl
    -- ⊢ 0 ≤ ↑(setToL1 hT) ↑(coeSimpleFuncNonnegToLpNonneg 1 μ G' g)
    rw [this, setToL1_eq_setToL1SCLM]
    -- ⊢ 0 ≤ ↑(setToL1SCLM α G' μ hT) ↑g
    exact setToL1S_nonneg (fun s => hT.eq_zero_of_measure_zero) hT.1 hT_nonneg g.2
    -- 🎉 no goals
#align measure_theory.L1.set_to_L1_nonneg MeasureTheory.L1.setToL1_nonneg

theorem setToL1_mono {T : Set α → G' →L[ℝ] G''} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f g : α →₁[μ] G'}
    (hfg : f ≤ g) : setToL1 hT f ≤ setToL1 hT g := by
  rw [← sub_nonneg] at hfg ⊢
  -- ⊢ 0 ≤ ↑(setToL1 hT) g - ↑(setToL1 hT) f
  rw [← (setToL1 hT).map_sub]
  -- ⊢ 0 ≤ ↑(setToL1 hT) (g - f)
  exact setToL1_nonneg hT hT_nonneg hfg
  -- 🎉 no goals
#align measure_theory.L1.set_to_L1_mono MeasureTheory.L1.setToL1_mono

end Order

theorem norm_setToL1_le_norm_setToL1SCLM (hT : DominatedFinMeasAdditive μ T C) :
    ‖setToL1 hT‖ ≤ ‖setToL1SCLM α E μ hT‖ :=
  calc
    ‖setToL1 hT‖ ≤ (1 : ℝ≥0) * ‖setToL1SCLM α E μ hT‖ := by
      refine'
        ContinuousLinearMap.op_norm_extend_le (setToL1SCLM α E μ hT) (coeToLp α E ℝ)
          (simpleFunc.denseRange one_ne_top) fun x => le_of_eq _
      rw [NNReal.coe_one, one_mul]
      -- ⊢ ‖x‖ = ‖↑(coeToLp α E ℝ) x‖
      rfl
      -- 🎉 no goals
    _ = ‖setToL1SCLM α E μ hT‖ := by rw [NNReal.coe_one, one_mul]
                                     -- 🎉 no goals
#align measure_theory.L1.norm_set_to_L1_le_norm_set_to_L1s_clm MeasureTheory.L1.norm_setToL1_le_norm_setToL1SCLM

theorem norm_setToL1_le_mul_norm (hT : DominatedFinMeasAdditive μ T C) (hC : 0 ≤ C)
    (f : α →₁[μ] E) : ‖setToL1 hT f‖ ≤ C * ‖f‖ :=
  calc
    ‖setToL1 hT f‖ ≤ ‖setToL1SCLM α E μ hT‖ * ‖f‖ :=
      ContinuousLinearMap.le_of_op_norm_le _ (norm_setToL1_le_norm_setToL1SCLM hT) _
    _ ≤ C * ‖f‖ := mul_le_mul (norm_setToL1SCLM_le hT hC) le_rfl (norm_nonneg _) hC
#align measure_theory.L1.norm_set_to_L1_le_mul_norm MeasureTheory.L1.norm_setToL1_le_mul_norm

theorem norm_setToL1_le_mul_norm' (hT : DominatedFinMeasAdditive μ T C) (f : α →₁[μ] E) :
    ‖setToL1 hT f‖ ≤ max C 0 * ‖f‖ :=
  calc
    ‖setToL1 hT f‖ ≤ ‖setToL1SCLM α E μ hT‖ * ‖f‖ :=
      ContinuousLinearMap.le_of_op_norm_le _ (norm_setToL1_le_norm_setToL1SCLM hT) _
    _ ≤ max C 0 * ‖f‖ :=
      mul_le_mul (norm_setToL1SCLM_le' hT) le_rfl (norm_nonneg _) (le_max_right _ _)
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

/-- If `fs i → f` in `L1`, then `setToL1 hT (fs i) → setToL1 hT f`. -/
theorem tendsto_setToL1 (hT : DominatedFinMeasAdditive μ T C) (f : α →₁[μ] E) {ι}
    (fs : ι → α →₁[μ] E) {l : Filter ι} (hfs : Tendsto fs l (𝓝 f)) :
    Tendsto (fun i => setToL1 hT (fs i)) l (𝓝 <| setToL1 hT f) :=
  ((setToL1 hT).continuous.tendsto _).comp hfs
#align measure_theory.L1.tendsto_set_to_L1 MeasureTheory.L1.tendsto_setToL1

end SetToL1

end L1

section Function

set_option linter.uppercaseLean3 false

variable [CompleteSpace F] {T T' T'' : Set α → E →L[ℝ] F} {C C' C'' : ℝ} {f g : α → E}

variable (μ T)

/-- Extend `T : Set α → E →L[ℝ] F` to `(α → E) → F` (for integrable functions `α → E`). We set it to
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
  rw [setToFun_eq hT (L1.integrable_coeFn f), Integrable.toL1_coeFn]
  -- 🎉 no goals
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
    setToFun μ T hT f = setToFun μ T' hT' f := by
  by_cases hf : Integrable f μ
  -- ⊢ setToFun μ T hT f = setToFun μ T' hT' f
  · simp_rw [setToFun_eq _ hf, L1.setToL1_congr_left T T' hT hT' h]
    -- 🎉 no goals
  · simp_rw [setToFun_undef _ hf]
    -- 🎉 no goals
#align measure_theory.set_to_fun_congr_left MeasureTheory.setToFun_congr_left

theorem setToFun_congr_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (h : ∀ s, MeasurableSet s → μ s < ∞ → T s = T' s)
    (f : α → E) : setToFun μ T hT f = setToFun μ T' hT' f := by
  by_cases hf : Integrable f μ
  -- ⊢ setToFun μ T hT f = setToFun μ T' hT' f
  · simp_rw [setToFun_eq _ hf, L1.setToL1_congr_left' T T' hT hT' h]
    -- 🎉 no goals
  · simp_rw [setToFun_undef _ hf]
    -- 🎉 no goals
#align measure_theory.set_to_fun_congr_left' MeasureTheory.setToFun_congr_left'

theorem setToFun_add_left (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (f : α → E) :
    setToFun μ (T + T') (hT.add hT') f = setToFun μ T hT f + setToFun μ T' hT' f := by
  by_cases hf : Integrable f μ
  -- ⊢ setToFun μ (T + T') (_ : DominatedFinMeasAdditive μ (T + T') (C + C')) f = s …
  · simp_rw [setToFun_eq _ hf, L1.setToL1_add_left hT hT']
    -- 🎉 no goals
  · simp_rw [setToFun_undef _ hf, add_zero]
    -- 🎉 no goals
#align measure_theory.set_to_fun_add_left MeasureTheory.setToFun_add_left

theorem setToFun_add_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (hT'' : DominatedFinMeasAdditive μ T'' C'')
    (h_add : ∀ s, MeasurableSet s → μ s < ∞ → T'' s = T s + T' s) (f : α → E) :
    setToFun μ T'' hT'' f = setToFun μ T hT f + setToFun μ T' hT' f := by
  by_cases hf : Integrable f μ
  -- ⊢ setToFun μ T'' hT'' f = setToFun μ T hT f + setToFun μ T' hT' f
  · simp_rw [setToFun_eq _ hf, L1.setToL1_add_left' hT hT' hT'' h_add]
    -- 🎉 no goals
  · simp_rw [setToFun_undef _ hf, add_zero]
    -- 🎉 no goals
#align measure_theory.set_to_fun_add_left' MeasureTheory.setToFun_add_left'

theorem setToFun_smul_left (hT : DominatedFinMeasAdditive μ T C) (c : ℝ) (f : α → E) :
    setToFun μ (fun s => c • T s) (hT.smul c) f = c • setToFun μ T hT f := by
  by_cases hf : Integrable f μ
  -- ⊢ setToFun μ (fun s => c • T s) (_ : DominatedFinMeasAdditive μ (fun s => c •  …
  · simp_rw [setToFun_eq _ hf, L1.setToL1_smul_left hT c]
    -- 🎉 no goals
  · simp_rw [setToFun_undef _ hf, smul_zero]
    -- 🎉 no goals
#align measure_theory.set_to_fun_smul_left MeasureTheory.setToFun_smul_left

theorem setToFun_smul_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (c : ℝ)
    (h_smul : ∀ s, MeasurableSet s → μ s < ∞ → T' s = c • T s) (f : α → E) :
    setToFun μ T' hT' f = c • setToFun μ T hT f := by
  by_cases hf : Integrable f μ
  -- ⊢ setToFun μ T' hT' f = c • setToFun μ T hT f
  · simp_rw [setToFun_eq _ hf, L1.setToL1_smul_left' hT hT' c h_smul]
    -- 🎉 no goals
  · simp_rw [setToFun_undef _ hf, smul_zero]
    -- 🎉 no goals
#align measure_theory.set_to_fun_smul_left' MeasureTheory.setToFun_smul_left'

@[simp]
theorem setToFun_zero (hT : DominatedFinMeasAdditive μ T C) : setToFun μ T hT (0 : α → E) = 0 := by
  erw [setToFun_eq hT (integrable_zero _ _ _), Integrable.toL1_zero, ContinuousLinearMap.map_zero]
  -- 🎉 no goals
#align measure_theory.set_to_fun_zero MeasureTheory.setToFun_zero

@[simp]
theorem setToFun_zero_left {hT : DominatedFinMeasAdditive μ (0 : Set α → E →L[ℝ] F) C} :
    setToFun μ 0 hT f = 0 := by
  by_cases hf : Integrable f μ
  -- ⊢ setToFun μ 0 hT f = 0
  · rw [setToFun_eq hT hf]; exact L1.setToL1_zero_left hT _
    -- ⊢ ↑(L1.setToL1 hT) (Integrable.toL1 f hf) = 0
                            -- 🎉 no goals
  · exact setToFun_undef hT hf
    -- 🎉 no goals
#align measure_theory.set_to_fun_zero_left MeasureTheory.setToFun_zero_left

theorem setToFun_zero_left' (hT : DominatedFinMeasAdditive μ T C)
    (h_zero : ∀ s, MeasurableSet s → μ s < ∞ → T s = 0) : setToFun μ T hT f = 0 := by
  by_cases hf : Integrable f μ
  -- ⊢ setToFun μ T hT f = 0
  · rw [setToFun_eq hT hf]; exact L1.setToL1_zero_left' hT h_zero _
    -- ⊢ ↑(L1.setToL1 hT) (Integrable.toL1 f hf) = 0
                            -- 🎉 no goals
  · exact setToFun_undef hT hf
    -- 🎉 no goals
#align measure_theory.set_to_fun_zero_left' MeasureTheory.setToFun_zero_left'

theorem setToFun_add (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ)
    (hg : Integrable g μ) : setToFun μ T hT (f + g) = setToFun μ T hT f + setToFun μ T hT g := by
  rw [setToFun_eq hT (hf.add hg), setToFun_eq hT hf, setToFun_eq hT hg, Integrable.toL1_add,
    (L1.setToL1 hT).map_add]
#align measure_theory.set_to_fun_add MeasureTheory.setToFun_add

theorem setToFun_finset_sum' (hT : DominatedFinMeasAdditive μ T C) {ι} (s : Finset ι)
    {f : ι → α → E} (hf : ∀ i ∈ s, Integrable (f i) μ) :
    setToFun μ T hT (∑ i in s, f i) = ∑ i in s, setToFun μ T hT (f i) := by
  revert hf
  -- ⊢ (∀ (i : ι), i ∈ s → Integrable (f i)) → setToFun μ T hT (∑ i in s, f i) = ∑  …
  refine' Finset.induction_on s _ _
  -- ⊢ (∀ (i : ι), i ∈ ∅ → Integrable (f i)) → setToFun μ T hT (∑ i in ∅, f i) = ∑  …
  · intro _
    -- ⊢ setToFun μ T hT (∑ i in ∅, f i) = ∑ i in ∅, setToFun μ T hT (f i)
    simp only [setToFun_zero, Finset.sum_empty]
    -- 🎉 no goals
  · intro i s his ih hf
    -- ⊢ setToFun μ T hT (∑ i in insert i s, f i) = ∑ i in insert i s, setToFun μ T h …
    simp only [his, Finset.sum_insert, not_false_iff]
    -- ⊢ setToFun μ T hT (f i + ∑ i in s, f i) = setToFun μ T hT (f i) + ∑ i in s, se …
    rw [setToFun_add hT (hf i (Finset.mem_insert_self i s)) _]
    -- ⊢ setToFun μ T hT (f i) + setToFun μ T hT (∑ i in s, f i) = setToFun μ T hT (f …
    · rw [ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]
      -- 🎉 no goals
    · convert integrable_finset_sum s fun i hi => hf i (Finset.mem_insert_of_mem hi) with x
      -- ⊢ Finset.sum s (fun i => f i) x = ∑ i in s, f i x
      simp
      -- 🎉 no goals
#align measure_theory.set_to_fun_finset_sum' MeasureTheory.setToFun_finset_sum'

theorem setToFun_finset_sum (hT : DominatedFinMeasAdditive μ T C) {ι} (s : Finset ι) {f : ι → α → E}
    (hf : ∀ i ∈ s, Integrable (f i) μ) :
    (setToFun μ T hT fun a => ∑ i in s, f i a) = ∑ i in s, setToFun μ T hT (f i) := by
  convert setToFun_finset_sum' hT s hf with a; simp
  -- ⊢ ∑ i in s, f i a = Finset.sum s (fun i => f i) a
                                               -- 🎉 no goals
#align measure_theory.set_to_fun_finset_sum MeasureTheory.setToFun_finset_sum

theorem setToFun_neg (hT : DominatedFinMeasAdditive μ T C) (f : α → E) :
    setToFun μ T hT (-f) = -setToFun μ T hT f := by
  by_cases hf : Integrable f μ
  -- ⊢ setToFun μ T hT (-f) = -setToFun μ T hT f
  · rw [setToFun_eq hT hf, setToFun_eq hT hf.neg, Integrable.toL1_neg,
      (L1.setToL1 hT).map_neg]
  · rw [setToFun_undef hT hf, setToFun_undef hT, neg_zero]
    -- ⊢ ¬Integrable (-f)
    rwa [← integrable_neg_iff] at hf
    -- 🎉 no goals
#align measure_theory.set_to_fun_neg MeasureTheory.setToFun_neg

theorem setToFun_sub (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ)
    (hg : Integrable g μ) : setToFun μ T hT (f - g) = setToFun μ T hT f - setToFun μ T hT g := by
  rw [sub_eq_add_neg, sub_eq_add_neg, setToFun_add hT hf hg.neg, setToFun_neg hT g]
  -- 🎉 no goals
#align measure_theory.set_to_fun_sub MeasureTheory.setToFun_sub

theorem setToFun_smul [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (hT : DominatedFinMeasAdditive μ T C) (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (c : 𝕜)
    (f : α → E) : setToFun μ T hT (c • f) = c • setToFun μ T hT f := by
  by_cases hf : Integrable f μ
  -- ⊢ setToFun μ T hT (c • f) = c • setToFun μ T hT f
  · rw [setToFun_eq hT hf, setToFun_eq hT, Integrable.toL1_smul',
      L1.setToL1_smul hT h_smul c _]
  · by_cases hr : c = 0
    -- ⊢ setToFun μ T hT (c • f) = c • setToFun μ T hT f
    · rw [hr]; simp
      -- ⊢ setToFun μ T hT (0 • f) = 0 • setToFun μ T hT f
               -- 🎉 no goals
    · have hf' : ¬Integrable (c • f) μ := by rwa [integrable_smul_iff hr f]
      -- ⊢ setToFun μ T hT (c • f) = c • setToFun μ T hT f
      rw [setToFun_undef hT hf, setToFun_undef hT hf', smul_zero]
      -- 🎉 no goals
#align measure_theory.set_to_fun_smul MeasureTheory.setToFun_smul

theorem setToFun_congr_ae (hT : DominatedFinMeasAdditive μ T C) (h : f =ᵐ[μ] g) :
    setToFun μ T hT f = setToFun μ T hT g := by
  by_cases hfi : Integrable f μ
  -- ⊢ setToFun μ T hT f = setToFun μ T hT g
  · have hgi : Integrable g μ := hfi.congr h
    -- ⊢ setToFun μ T hT f = setToFun μ T hT g
    rw [setToFun_eq hT hfi, setToFun_eq hT hgi, (Integrable.toL1_eq_toL1_iff f g hfi hgi).2 h]
    -- 🎉 no goals
  · have hgi : ¬Integrable g μ := by rw [integrable_congr h] at hfi; exact hfi
    -- ⊢ setToFun μ T hT f = setToFun μ T hT g
    rw [setToFun_undef hT hfi, setToFun_undef hT hgi]
    -- 🎉 no goals
#align measure_theory.set_to_fun_congr_ae MeasureTheory.setToFun_congr_ae

theorem setToFun_measure_zero (hT : DominatedFinMeasAdditive μ T C) (h : μ = 0) :
    setToFun μ T hT f = 0 := by
  have : f =ᵐ[μ] 0 := by simp [h, EventuallyEq]
  -- ⊢ setToFun μ T hT f = 0
  rw [setToFun_congr_ae hT this, setToFun_zero]
  -- 🎉 no goals
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
    setToFun μ T hT (s.indicator fun _ => x) = T s x := by
  rw [setToFun_congr_ae hT (@indicatorConstLp_coeFn _ _ _ 1 _ _ _ hs hμs x).symm]
  -- ⊢ setToFun μ T hT ↑↑(indicatorConstLp 1 hs hμs x) = ↑(T s) x
  rw [L1.setToFun_eq_setToL1 hT]
  -- ⊢ ↑(L1.setToL1 hT) (indicatorConstLp 1 hs hμs x) = ↑(T s) x
  exact L1.setToL1_indicatorConstLp hT hs hμs x
  -- 🎉 no goals
#align measure_theory.set_to_fun_indicator_const MeasureTheory.setToFun_indicator_const

theorem setToFun_const [IsFiniteMeasure μ] (hT : DominatedFinMeasAdditive μ T C) (x : E) :
    (setToFun μ T hT fun _ => x) = T univ x := by
  have : (fun _ : α => x) = Set.indicator univ fun _ => x := (indicator_univ _).symm
  -- ⊢ (setToFun μ T hT fun x_1 => x) = ↑(T Set.univ) x
  rw [this]
  -- ⊢ setToFun μ T hT (indicator Set.univ fun x_1 => x) = ↑(T Set.univ) x
  exact setToFun_indicator_const hT MeasurableSet.univ (measure_ne_top _ _) x
  -- 🎉 no goals
#align measure_theory.set_to_fun_const MeasureTheory.setToFun_const

section Order

variable {G' G'' : Type*} [NormedLatticeAddCommGroup G''] [NormedSpace ℝ G''] [CompleteSpace G'']
  [NormedLatticeAddCommGroup G'] [NormedSpace ℝ G']

theorem setToFun_mono_left' {T T' : Set α → E →L[ℝ] G''} {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (hTT' : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, T s x ≤ T' s x) (f : α → E) :
    setToFun μ T hT f ≤ setToFun μ T' hT' f := by
  by_cases hf : Integrable f μ
  -- ⊢ setToFun μ T hT f ≤ setToFun μ T' hT' f
  · simp_rw [setToFun_eq _ hf]; exact L1.setToL1_mono_left' hT hT' hTT' _
    -- ⊢ ↑(L1.setToL1 hT) (Integrable.toL1 f hf) ≤ ↑(L1.setToL1 hT') (Integrable.toL1 …
                                -- 🎉 no goals
  · simp_rw [setToFun_undef _ hf]; rfl
    -- ⊢ 0 ≤ 0
                                   -- 🎉 no goals
#align measure_theory.set_to_fun_mono_left' MeasureTheory.setToFun_mono_left'

theorem setToFun_mono_left {T T' : Set α → E →L[ℝ] G''} {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (hTT' : ∀ s x, T s x ≤ T' s x) (f : α →₁[μ] E) : setToFun μ T hT f ≤ setToFun μ T' hT' f :=
  setToFun_mono_left' hT hT' (fun s _ _ x => hTT' s x) f
#align measure_theory.set_to_fun_mono_left MeasureTheory.setToFun_mono_left

theorem setToFun_nonneg {T : Set α → G' →L[ℝ] G''} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f : α → G'}
    (hf : 0 ≤ᵐ[μ] f) : 0 ≤ setToFun μ T hT f := by
  by_cases hfi : Integrable f μ
  -- ⊢ 0 ≤ setToFun μ T hT f
  · simp_rw [setToFun_eq _ hfi]
    -- ⊢ 0 ≤ ↑(L1.setToL1 hT) (Integrable.toL1 f hfi)
    refine' L1.setToL1_nonneg hT hT_nonneg _
    -- ⊢ 0 ≤ Integrable.toL1 f hfi
    rw [← Lp.coeFn_le]
    -- ⊢ ↑↑0 ≤ᵐ[μ] ↑↑(Integrable.toL1 f hfi)
    have h0 := Lp.coeFn_zero G' 1 μ
    -- ⊢ ↑↑0 ≤ᵐ[μ] ↑↑(Integrable.toL1 f hfi)
    have h := Integrable.coeFn_toL1 hfi
    -- ⊢ ↑↑0 ≤ᵐ[μ] ↑↑(Integrable.toL1 f hfi)
    filter_upwards [h0, h, hf] with _ h0a ha hfa
    -- ⊢ ↑↑0 a✝ ≤ ↑↑(Integrable.toL1 f hfi) a✝
    rw [h0a, ha]
    -- ⊢ OfNat.ofNat 0 a✝ ≤ f a✝
    exact hfa
    -- 🎉 no goals
  · simp_rw [setToFun_undef _ hfi]; rfl
    -- ⊢ 0 ≤ 0
                                    -- 🎉 no goals
#align measure_theory.set_to_fun_nonneg MeasureTheory.setToFun_nonneg

theorem setToFun_mono {T : Set α → G' →L[ℝ] G''} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f g : α → G'}
    (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g) :
    setToFun μ T hT f ≤ setToFun μ T hT g := by
  rw [← sub_nonneg, ← setToFun_sub hT hg hf]
  -- ⊢ 0 ≤ setToFun μ T hT (g - f)
  refine' setToFun_nonneg hT hT_nonneg (hfg.mono fun a ha => _)
  -- ⊢ OfNat.ofNat 0 a ≤ (g - f) a
  rw [Pi.sub_apply, Pi.zero_apply, sub_nonneg]
  -- ⊢ f a ≤ g a
  exact ha
  -- 🎉 no goals
#align measure_theory.set_to_fun_mono MeasureTheory.setToFun_mono

end Order

@[continuity]
theorem continuous_setToFun (hT : DominatedFinMeasAdditive μ T C) :
    Continuous fun f : α →₁[μ] E => setToFun μ T hT f := by
  simp_rw [L1.setToFun_eq_setToL1 hT]; exact ContinuousLinearMap.continuous _
  -- ⊢ Continuous fun f => ↑(L1.setToL1 hT) f
                                       -- 🎉 no goals
#align measure_theory.continuous_set_to_fun MeasureTheory.continuous_setToFun

/-- If `F i → f` in `L1`, then `setToFun μ T hT (F i) → setToFun μ T hT f`. -/
theorem tendsto_setToFun_of_L1 (hT : DominatedFinMeasAdditive μ T C) {ι} (f : α → E)
    (hfi : Integrable f μ) {fs : ι → α → E} {l : Filter ι} (hfsi : ∀ᶠ i in l, Integrable (fs i) μ)
    (hfs : Tendsto (fun i => ∫⁻ x, ‖fs i x - f x‖₊ ∂μ) l (𝓝 0)) :
    Tendsto (fun i => setToFun μ T hT (fs i)) l (𝓝 <| setToFun μ T hT f) := by
  classical
    let f_lp := hfi.toL1 f
    let F_lp i := if hFi : Integrable (fs i) μ then hFi.toL1 (fs i) else 0
    have tendsto_L1 : Tendsto F_lp l (𝓝 f_lp) := by
      rw [Lp.tendsto_Lp_iff_tendsto_ℒp']
      simp_rw [snorm_one_eq_lintegral_nnnorm, Pi.sub_apply]
      refine' (tendsto_congr' _).mp hfs
      filter_upwards [hfsi]with i hi
      refine' lintegral_congr_ae _
      filter_upwards [hi.coeFn_toL1, hfi.coeFn_toL1] with x hxi hxf
      simp_rw [dif_pos hi, hxi, hxf]
    suffices Tendsto (fun i => setToFun μ T hT (F_lp i)) l (𝓝 (setToFun μ T hT f)) by
      refine' (tendsto_congr' _).mp this
      filter_upwards [hfsi] with i hi
      suffices h_ae_eq : F_lp i =ᵐ[μ] fs i; exact setToFun_congr_ae hT h_ae_eq
      simp_rw [dif_pos hi]
      exact hi.coeFn_toL1
    rw [setToFun_congr_ae hT hfi.coeFn_toL1.symm]
    exact ((continuous_setToFun hT).tendsto f_lp).comp tendsto_L1
#align measure_theory.tendsto_set_to_fun_of_L1 MeasureTheory.tendsto_setToFun_of_L1

theorem tendsto_setToFun_approxOn_of_measurable (hT : DominatedFinMeasAdditive μ T C)
    [MeasurableSpace E] [BorelSpace E] {f : α → E} {s : Set E} [SeparableSpace s]
    (hfi : Integrable f μ) (hfm : Measurable f) (hs : ∀ᵐ x ∂μ, f x ∈ closure s) {y₀ : E}
    (h₀ : y₀ ∈ s) (h₀i : Integrable (fun _ => y₀) μ) :
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
                                                                                 -- 🎉 no goals
      (𝓝 <| setToFun μ T hT f) := by
  refine tendsto_setToFun_approxOn_of_measurable hT hf fmeas ?_ _ (integrable_zero _ _ _)
  -- ⊢ ∀ᵐ (x : α) ∂μ, f x ∈ closure s
  exact eventually_of_forall fun x => subset_closure (hs (Set.mem_union_left _ (mem_range_self _)))
  -- 🎉 no goals
#align measure_theory.tendsto_set_to_fun_approx_on_of_measurable_of_range_subset MeasureTheory.tendsto_setToFun_approxOn_of_measurable_of_range_subset

/-- Auxiliary lemma for `setToFun_congr_measure`: the function sending `f : α →₁[μ] G` to
`f : α →₁[μ'] G` is continuous when `μ' ≤ c' • μ` for `c' ≠ ∞`. -/
theorem continuous_L1_toL1 {μ' : Measure α} (c' : ℝ≥0∞) (hc' : c' ≠ ∞) (hμ'_le : μ' ≤ c' • μ) :
    Continuous fun f : α →₁[μ] G =>
      (Integrable.of_measure_le_smul c' hc' hμ'_le (L1.integrable_coeFn f)).toL1 f := by
  by_cases hc'0 : c' = 0
  -- ⊢ Continuous fun f => Integrable.toL1 ↑↑f (_ : Integrable ↑↑f)
  · have hμ'0 : μ' = 0 := by rw [← Measure.nonpos_iff_eq_zero']; refine' hμ'_le.trans _; simp [hc'0]
    -- ⊢ Continuous fun f => Integrable.toL1 ↑↑f (_ : Integrable ↑↑f)
    have h_im_zero :
      (fun f : α →₁[μ] G =>
          (Integrable.of_measure_le_smul c' hc' hμ'_le (L1.integrable_coeFn f)).toL1 f) =
        0 := by
      ext1 f; ext1; simp_rw [hμ'0]; simp only [ae_zero, EventuallyEq, eventually_bot]
    rw [h_im_zero]
    -- ⊢ Continuous 0
    exact continuous_zero
    -- 🎉 no goals
  rw [Metric.continuous_iff]
  -- ⊢ ∀ (b : { x // x ∈ Lp G 1 }) (ε : ℝ), ε > 0 → ∃ δ, δ > 0 ∧ ∀ (a : { x // x ∈  …
  intro f ε hε_pos
  -- ⊢ ∃ δ, δ > 0 ∧ ∀ (a : { x // x ∈ Lp G 1 }), dist a f < δ → dist (Integrable.to …
  use ε / 2 / c'.toReal
  -- ⊢ ε / 2 / ENNReal.toReal c' > 0 ∧ ∀ (a : { x // x ∈ Lp G 1 }), dist a f < ε /  …
  refine' ⟨div_pos (half_pos hε_pos) (toReal_pos hc'0 hc'), _⟩
  -- ⊢ ∀ (a : { x // x ∈ Lp G 1 }), dist a f < ε / 2 / ENNReal.toReal c' → dist (In …
  intro g hfg
  -- ⊢ dist (Integrable.toL1 ↑↑g (_ : Integrable ↑↑g)) (Integrable.toL1 ↑↑f (_ : In …
  rw [Lp.dist_def] at hfg ⊢
  -- ⊢ ENNReal.toReal (snorm (↑↑(Integrable.toL1 ↑↑g (_ : Integrable ↑↑g)) - ↑↑(Int …
  let h_int := fun f' : α →₁[μ] G => (L1.integrable_coeFn f').of_measure_le_smul c' hc' hμ'_le
  -- ⊢ ENNReal.toReal (snorm (↑↑(Integrable.toL1 ↑↑g (_ : Integrable ↑↑g)) - ↑↑(Int …
  have :
    snorm (⇑(Integrable.toL1 g (h_int g)) - ⇑(Integrable.toL1 f (h_int f))) 1 μ' =
      snorm (⇑g - ⇑f) 1 μ' :=
    snorm_congr_ae ((Integrable.coeFn_toL1 _).sub (Integrable.coeFn_toL1 _))
  rw [this]
  -- ⊢ ENNReal.toReal (snorm (↑↑g - ↑↑f) 1 μ') < ε
  have h_snorm_ne_top : snorm (⇑g - ⇑f) 1 μ ≠ ∞ := by
    rw [← snorm_congr_ae (Lp.coeFn_sub _ _)]; exact Lp.snorm_ne_top _
  have h_snorm_ne_top' : snorm (⇑g - ⇑f) 1 μ' ≠ ∞ := by
    refine' ((snorm_mono_measure _ hμ'_le).trans_lt _).ne
    rw [snorm_smul_measure_of_ne_zero hc'0, smul_eq_mul]
    refine' ENNReal.mul_lt_top _ h_snorm_ne_top
    simp [hc', hc'0]
  calc
    (snorm (⇑g - ⇑f) 1 μ').toReal ≤ (c' * snorm (⇑g - ⇑f) 1 μ).toReal := by
      rw [toReal_le_toReal h_snorm_ne_top' (ENNReal.mul_ne_top hc' h_snorm_ne_top)]
      refine' (snorm_mono_measure (⇑g - ⇑f) hμ'_le).trans _
      rw [snorm_smul_measure_of_ne_zero hc'0, smul_eq_mul]
      simp
    _ = c'.toReal * (snorm (⇑g - ⇑f) 1 μ).toReal := toReal_mul
    _ ≤ c'.toReal * (ε / 2 / c'.toReal) :=
      (mul_le_mul le_rfl hfg.le toReal_nonneg toReal_nonneg)
    _ = ε / 2 := by
      refine' mul_div_cancel' (ε / 2) _; rw [Ne.def, toReal_eq_zero_iff]; simp [hc', hc'0]
    _ < ε := half_lt_self hε_pos
#align measure_theory.continuous_L1_to_L1 MeasureTheory.continuous_L1_toL1

theorem setToFun_congr_measure_of_integrable {μ' : Measure α} (c' : ℝ≥0∞) (hc' : c' ≠ ∞)
    (hμ'_le : μ' ≤ c' • μ) (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ' T C') (f : α → E) (hfμ : Integrable f μ) :
    setToFun μ T hT f = setToFun μ' T hT' f := by
  -- integrability for `μ` implies integrability for `μ'`.
  have h_int : ∀ g : α → E, Integrable g μ → Integrable g μ' := fun g hg =>
    Integrable.of_measure_le_smul c' hc' hμ'_le hg
  -- We use `Integrable.induction`
  apply hfμ.induction (P := fun f => setToFun μ T hT f = setToFun μ' T hT' f)
  · intro c s hs hμs
    -- ⊢ setToFun μ T hT (indicator s fun x => c) = setToFun μ' T hT' (indicator s fu …
    have hμ's : μ' s ≠ ∞ := by
      refine' ((hμ'_le s hs).trans_lt _).ne
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top hc' hμs.ne
    rw [setToFun_indicator_const hT hs hμs.ne, setToFun_indicator_const hT' hs hμ's]
    -- 🎉 no goals
  · intro f₂ g₂ _ hf₂ hg₂ h_eq_f h_eq_g
    -- ⊢ setToFun μ T hT (f₂ + g₂) = setToFun μ' T hT' (f₂ + g₂)
    rw [setToFun_add hT hf₂ hg₂, setToFun_add hT' (h_int f₂ hf₂) (h_int g₂ hg₂), h_eq_f, h_eq_g]
    -- 🎉 no goals
  · refine' isClosed_eq (continuous_setToFun hT) _
    -- ⊢ Continuous fun f => setToFun μ' T hT' ↑↑f
    have :
      (fun f : α →₁[μ] E => setToFun μ' T hT' f) = fun f : α →₁[μ] E =>
        setToFun μ' T hT' ((h_int f (L1.integrable_coeFn f)).toL1 f) := by
      ext1 f; exact setToFun_congr_ae hT' (Integrable.coeFn_toL1 _).symm
    rw [this]
    -- ⊢ Continuous fun f => setToFun μ' T hT' ↑↑(Integrable.toL1 ↑↑f (_ : Integrable …
    exact (continuous_setToFun hT').comp (continuous_L1_toL1 c' hc' hμ'_le)
    -- 🎉 no goals
  · intro f₂ g₂ hfg _ hf_eq
    -- ⊢ setToFun μ T hT g₂ = setToFun μ' T hT' g₂
    have hfg' : f₂ =ᵐ[μ'] g₂ := (Measure.absolutelyContinuous_of_le_smul hμ'_le).ae_eq hfg
    -- ⊢ setToFun μ T hT g₂ = setToFun μ' T hT' g₂
    rw [← setToFun_congr_ae hT hfg, hf_eq, setToFun_congr_ae hT' hfg']
    -- 🎉 no goals
#align measure_theory.set_to_fun_congr_measure_of_integrable MeasureTheory.setToFun_congr_measure_of_integrable

theorem setToFun_congr_measure {μ' : Measure α} (c c' : ℝ≥0∞) (hc : c ≠ ∞) (hc' : c' ≠ ∞)
    (hμ_le : μ ≤ c • μ') (hμ'_le : μ' ≤ c' • μ) (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ' T C') (f : α → E) :
    setToFun μ T hT f = setToFun μ' T hT' f := by
  by_cases hf : Integrable f μ
  -- ⊢ setToFun μ T hT f = setToFun μ' T hT' f
  · exact setToFun_congr_measure_of_integrable c' hc' hμ'_le hT hT' f hf
    -- 🎉 no goals
  · -- if `f` is not integrable, both `setToFun` are 0.
    have h_int : ∀ g : α → E, ¬Integrable g μ → ¬Integrable g μ' := fun g =>
      mt fun h => h.of_measure_le_smul _ hc hμ_le
    simp_rw [setToFun_undef _ hf, setToFun_undef _ (h_int f hf)]
    -- 🎉 no goals
#align measure_theory.set_to_fun_congr_measure MeasureTheory.setToFun_congr_measure

theorem setToFun_congr_measure_of_add_right {μ' : Measure α}
    (hT_add : DominatedFinMeasAdditive (μ + μ') T C') (hT : DominatedFinMeasAdditive μ T C)
    (f : α → E) (hf : Integrable f (μ + μ')) :
    setToFun (μ + μ') T hT_add f = setToFun μ T hT f := by
  refine' setToFun_congr_measure_of_integrable 1 one_ne_top _ hT_add hT f hf
  -- ⊢ μ ≤ 1 • (μ + μ')
  rw [one_smul]
  -- ⊢ μ ≤ μ + μ'
  nth_rw 1 [← add_zero μ]
  -- ⊢ μ + 0 ≤ μ + μ'
  exact add_le_add le_rfl bot_le
  -- 🎉 no goals
#align measure_theory.set_to_fun_congr_measure_of_add_right MeasureTheory.setToFun_congr_measure_of_add_right

theorem setToFun_congr_measure_of_add_left {μ' : Measure α}
    (hT_add : DominatedFinMeasAdditive (μ + μ') T C') (hT : DominatedFinMeasAdditive μ' T C)
    (f : α → E) (hf : Integrable f (μ + μ')) :
    setToFun (μ + μ') T hT_add f = setToFun μ' T hT f := by
  refine' setToFun_congr_measure_of_integrable 1 one_ne_top _ hT_add hT f hf
  -- ⊢ μ' ≤ 1 • (μ + μ')
  rw [one_smul]
  -- ⊢ μ' ≤ μ + μ'
  nth_rw 1 [← zero_add μ']
  -- ⊢ 0 + μ' ≤ μ + μ'
  exact add_le_add bot_le le_rfl
  -- 🎉 no goals
#align measure_theory.set_to_fun_congr_measure_of_add_left MeasureTheory.setToFun_congr_measure_of_add_left

theorem setToFun_top_smul_measure (hT : DominatedFinMeasAdditive (∞ • μ) T C) (f : α → E) :
    setToFun (∞ • μ) T hT f = 0 := by
  refine' setToFun_measure_zero' hT fun s _ hμs => _
  -- ⊢ ↑↑(⊤ • μ) s = 0
  rw [lt_top_iff_ne_top] at hμs
  -- ⊢ ↑↑(⊤ • μ) s = 0
  simp only [true_and_iff, Measure.smul_apply, ENNReal.mul_eq_top, eq_self_iff_true,
    top_ne_zero, Ne.def, not_false_iff, not_or, Classical.not_not, smul_eq_mul] at hμs
  simp only [hμs.right, Measure.smul_apply, mul_zero, smul_eq_mul]
  -- 🎉 no goals
#align measure_theory.set_to_fun_top_smul_measure MeasureTheory.setToFun_top_smul_measure

theorem setToFun_congr_smul_measure (c : ℝ≥0∞) (hc_ne_top : c ≠ ∞)
    (hT : DominatedFinMeasAdditive μ T C) (hT_smul : DominatedFinMeasAdditive (c • μ) T C')
    (f : α → E) : setToFun μ T hT f = setToFun (c • μ) T hT_smul f := by
  by_cases hc0 : c = 0
  -- ⊢ setToFun μ T hT f = setToFun (c • μ) T hT_smul f
  · simp [hc0] at hT_smul
    -- ⊢ setToFun μ T hT f = setToFun (c • μ) T hT_smul✝ f
    have h : ∀ s, MeasurableSet s → μ s < ∞ → T s = 0 := fun s hs _ => hT_smul.eq_zero hs
    -- ⊢ setToFun μ T hT f = setToFun (c • μ) T hT_smul✝ f
    rw [setToFun_zero_left' _ h, setToFun_measure_zero]
    -- ⊢ c • μ = 0
    simp [hc0]
    -- 🎉 no goals
  refine' setToFun_congr_measure c⁻¹ c _ hc_ne_top (le_of_eq _) le_rfl hT hT_smul f
  -- ⊢ c⁻¹ ≠ ⊤
  · simp [hc0]
    -- 🎉 no goals
  · rw [smul_smul, ENNReal.inv_mul_cancel hc0 hc_ne_top, one_smul]
    -- 🎉 no goals
#align measure_theory.set_to_fun_congr_smul_measure MeasureTheory.setToFun_congr_smul_measure

theorem norm_setToFun_le_mul_norm (hT : DominatedFinMeasAdditive μ T C) (f : α →₁[μ] E)
    (hC : 0 ≤ C) : ‖setToFun μ T hT f‖ ≤ C * ‖f‖ := by
  rw [L1.setToFun_eq_setToL1]; exact L1.norm_setToL1_le_mul_norm hT hC f
  -- ⊢ ‖↑(L1.setToL1 hT) f‖ ≤ C * ‖f‖
                               -- 🎉 no goals
#align measure_theory.norm_set_to_fun_le_mul_norm MeasureTheory.norm_setToFun_le_mul_norm

theorem norm_setToFun_le_mul_norm' (hT : DominatedFinMeasAdditive μ T C) (f : α →₁[μ] E) :
    ‖setToFun μ T hT f‖ ≤ max C 0 * ‖f‖ := by
  rw [L1.setToFun_eq_setToL1]; exact L1.norm_setToL1_le_mul_norm' hT f
  -- ⊢ ‖↑(L1.setToL1 hT) f‖ ≤ max C 0 * ‖f‖
                               -- 🎉 no goals
#align measure_theory.norm_set_to_fun_le_mul_norm' MeasureTheory.norm_setToFun_le_mul_norm'

theorem norm_setToFun_le (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ) (hC : 0 ≤ C) :
    ‖setToFun μ T hT f‖ ≤ C * ‖hf.toL1 f‖ := by
  rw [setToFun_eq hT hf]; exact L1.norm_setToL1_le_mul_norm hT hC _
  -- ⊢ ‖↑(L1.setToL1 hT) (Integrable.toL1 f hf)‖ ≤ C * ‖Integrable.toL1 f hf‖
                          -- 🎉 no goals
#align measure_theory.norm_set_to_fun_le MeasureTheory.norm_setToFun_le

theorem norm_setToFun_le' (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ) :
    ‖setToFun μ T hT f‖ ≤ max C 0 * ‖hf.toL1 f‖ := by
  rw [setToFun_eq hT hf]; exact L1.norm_setToL1_le_mul_norm' hT _
  -- ⊢ ‖↑(L1.setToL1 hT) (Integrable.toL1 f hf)‖ ≤ max C 0 * ‖Integrable.toL1 f hf‖
                          -- 🎉 no goals
#align measure_theory.norm_set_to_fun_le' MeasureTheory.norm_setToFun_le'

/-- Lebesgue dominated convergence theorem provides sufficient conditions under which almost
  everywhere convergence of a sequence of functions implies the convergence of their image by
  `setToFun`.
  We could weaken the condition `bound_integrable` to require `HasFiniteIntegral bound μ` instead
  (i.e. not requiring that `bound` is measurable), but in all applications proving integrability
  is easier. -/
theorem tendsto_setToFun_of_dominated_convergence (hT : DominatedFinMeasAdditive μ T C)
    {fs : ℕ → α → E} {f : α → E} (bound : α → ℝ)
    (fs_measurable : ∀ n, AEStronglyMeasurable (fs n) μ) (bound_integrable : Integrable bound μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖fs n a‖ ≤ bound a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => fs n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => setToFun μ T hT (fs n)) atTop (𝓝 <| setToFun μ T hT f) := by
  -- `f` is a.e.-measurable, since it is the a.e.-pointwise limit of a.e.-measurable functions.
  have f_measurable : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae _ fs_measurable h_lim
  -- all functions we consider are integrable
  have fs_int : ∀ n, Integrable (fs n) μ := fun n =>
    bound_integrable.mono' (fs_measurable n) (h_bound _)
  have f_int : Integrable f μ :=
    ⟨f_measurable,
      hasFiniteIntegral_of_dominated_convergence bound_integrable.hasFiniteIntegral h_bound
        h_lim⟩
  -- it suffices to prove the result for the corresponding L1 functions
  suffices
    Tendsto (fun n => L1.setToL1 hT ((fs_int n).toL1 (fs n))) atTop
      (𝓝 (L1.setToL1 hT (f_int.toL1 f))) by
    convert this with n
    · exact setToFun_eq hT (fs_int n)
    · exact setToFun_eq hT f_int
  -- the convergence of setToL1 follows from the convergence of the L1 functions
  refine' L1.tendsto_setToL1 hT _ _ _
  -- ⊢ Tendsto (fun n => Integrable.toL1 (fs n) (_ : Integrable (fs n))) atTop (𝓝 ( …
  -- up to some rewriting, what we need to prove is `h_lim`
  rw [tendsto_iff_norm_tendsto_zero]
  -- ⊢ Tendsto (fun e => ‖Integrable.toL1 (fs e) (_ : Integrable (fs e)) - Integrab …
  have lintegral_norm_tendsto_zero :
    Tendsto (fun n => ENNReal.toReal <| ∫⁻ a, ENNReal.ofReal ‖fs n a - f a‖ ∂μ) atTop (𝓝 0) :=
    (tendsto_toReal zero_ne_top).comp
      (tendsto_lintegral_norm_of_dominated_convergence fs_measurable
        bound_integrable.hasFiniteIntegral h_bound h_lim)
  convert lintegral_norm_tendsto_zero with n
  -- ⊢ ‖Integrable.toL1 (fs n) (_ : Integrable (fs n)) - Integrable.toL1 f f_int‖ = …
  rw [L1.norm_def]
  -- ⊢ ENNReal.toReal (∫⁻ (a : α), ↑‖↑↑(Integrable.toL1 (fs n) (_ : Integrable (fs  …
  congr 1
  -- ⊢ ∫⁻ (a : α), ↑‖↑↑(Integrable.toL1 (fs n) (_ : Integrable (fs n)) - Integrable …
  refine' lintegral_congr_ae _
  -- ⊢ (fun a => ↑‖↑↑(Integrable.toL1 (fs n) (_ : Integrable (fs n)) - Integrable.t …
  rw [← Integrable.toL1_sub]
  -- ⊢ (fun a => ↑‖↑↑(Integrable.toL1 (fs n - f) (_ : Integrable (fs n - f))) a‖₊)  …
  refine' ((fs_int n).sub f_int).coeFn_toL1.mono fun x hx => _
  -- ⊢ (fun a => ↑‖↑↑(Integrable.toL1 (fs n - f) (_ : Integrable (fs n - f))) a‖₊)  …
  dsimp only
  -- ⊢ ↑‖↑↑(Integrable.toL1 (fs n - f) (_ : Integrable (fs n - f))) x‖₊ = ENNReal.o …
  rw [hx, ofReal_norm_eq_coe_nnnorm, Pi.sub_apply]
  -- 🎉 no goals
#align measure_theory.tendsto_set_to_fun_of_dominated_convergence MeasureTheory.tendsto_setToFun_of_dominated_convergence

/-- Lebesgue dominated convergence theorem for filters with a countable basis -/
theorem tendsto_setToFun_filter_of_dominated_convergence (hT : DominatedFinMeasAdditive μ T C) {ι}
    {l : Filter ι} [l.IsCountablyGenerated] {fs : ι → α → E} {f : α → E} (bound : α → ℝ)
    (hfs_meas : ∀ᶠ n in l, AEStronglyMeasurable (fs n) μ)
    (h_bound : ∀ᶠ n in l, ∀ᵐ a ∂μ, ‖fs n a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => fs n a) l (𝓝 (f a))) :
    Tendsto (fun n => setToFun μ T hT (fs n)) l (𝓝 <| setToFun μ T hT f) := by
  rw [tendsto_iff_seq_tendsto]
  -- ⊢ ∀ (x : ℕ → ι), Tendsto x atTop l → Tendsto ((fun n => setToFun μ T hT (fs n) …
  intro x xl
  -- ⊢ Tendsto ((fun n => setToFun μ T hT (fs n)) ∘ x) atTop (𝓝 (setToFun μ T hT f))
  have hxl : ∀ s ∈ l, ∃ a, ∀ b ≥ a, x b ∈ s := by rwa [tendsto_atTop'] at xl
  -- ⊢ Tendsto ((fun n => setToFun μ T hT (fs n)) ∘ x) atTop (𝓝 (setToFun μ T hT f))
  have h :
    { x : ι | (fun n => AEStronglyMeasurable (fs n) μ) x } ∩
        { x : ι | (fun n => ∀ᵐ a ∂μ, ‖fs n a‖ ≤ bound a) x } ∈ l :=
    inter_mem hfs_meas h_bound
  obtain ⟨k, h⟩ := hxl _ h
  -- ⊢ Tendsto ((fun n => setToFun μ T hT (fs n)) ∘ x) atTop (𝓝 (setToFun μ T hT f))
  rw [← tendsto_add_atTop_iff_nat k]
  -- ⊢ Tendsto (fun n => ((fun n => setToFun μ T hT (fs n)) ∘ x) (n + k)) atTop (𝓝  …
  refine' tendsto_setToFun_of_dominated_convergence hT bound _ bound_integrable _ _
  · exact fun n => (h _ (self_le_add_left _ _)).1
    -- 🎉 no goals
  · exact fun n => (h _ (self_le_add_left _ _)).2
    -- 🎉 no goals
  · filter_upwards [h_lim]
    -- ⊢ ∀ (a : α), Tendsto (fun n => fs n a) l (𝓝 (f a)) → Tendsto (fun n => fs (x ( …
    refine' fun a h_lin => @Tendsto.comp _ _ _ (fun n => x (n + k)) (fun n => fs n a) _ _ _ h_lin _
    -- ⊢ Tendsto (fun n => x (n + k)) atTop l
    rw [tendsto_add_atTop_iff_nat]
    -- ⊢ Tendsto x atTop l
    assumption
    -- 🎉 no goals
#align measure_theory.tendsto_set_to_fun_filter_of_dominated_convergence MeasureTheory.tendsto_setToFun_filter_of_dominated_convergence

variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]

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
    ContinuousOn (fun x => setToFun μ T hT (fs x)) s := by
  intro x hx
  -- ⊢ ContinuousWithinAt (fun x => setToFun μ T hT (fs x)) s x
  refine' continuousWithinAt_setToFun_of_dominated hT _ _ bound_integrable _
  · filter_upwards [self_mem_nhdsWithin] with x hx using hfs_meas x hx
    -- 🎉 no goals
  · filter_upwards [self_mem_nhdsWithin] with x hx using h_bound x hx
    -- 🎉 no goals
  · filter_upwards [h_cont] with a ha using ha x hx
    -- 🎉 no goals
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
