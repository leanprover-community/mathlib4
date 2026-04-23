/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Set.Disjoint
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SetLike

/-!
# Additivity on measurable sets with finite measure

Let `T : Set α → E →L[ℝ] F` be additive for measurable sets with finite measure, in the sense that
for `s, t` two such sets, `Disjoint s t → T (s ∪ t) = T s + T t`. `T` is akin to a bilinear map on
`Set α × E`, or a linear map on indicator functions.

This property is named `FinMeasAdditive` in this file. We also define `DominatedFinMeasAdditive`,
which requires in addition that the norm on every set is less than the measure of the set
(up to a multiplicative constant); in `Mathlib/MeasureTheory/Integral/SetToL1.lean` we extend
set functions with this stronger property to integrable (L1) functions.

## Main definitions

- `FinMeasAdditive μ T`: the property that `T` is additive on measurable sets with finite measure.
  For two such sets, `Disjoint s t → T (s ∪ t) = T s + T t`.
- `DominatedFinMeasAdditive μ T C`: `FinMeasAdditive μ T ∧ ∀ s, ‖T s‖ ≤ C * μ.real s`.
  This is the property needed to perform the extension from indicators to L1.

## Implementation notes

The starting object `T : Set α → E →L[ℝ] F` matters only through its restriction on measurable sets
with finite measure. Its value on other sets is ignored.
-/

@[expose] public section


noncomputable section

open Set Filter ENNReal Finset

namespace MeasureTheory

variable {α E F F' G 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [NormedAddCommGroup G] {m : MeasurableSpace α} {μ : Measure α}

local infixr:25 " →ₛ " => SimpleFunc

section FinMeasAdditive

/-- A set function is `FinMeasAdditive` if its value on the union of two disjoint measurable
sets with finite measure is the sum of its values on each set. -/
def FinMeasAdditive {β} [AddMonoid β] {_ : MeasurableSpace α} (μ : Measure α) (T : Set α → β) :
    Prop :=
  ∀ s t, MeasurableSet s → MeasurableSet t → μ s ≠ ∞ → μ t ≠ ∞ → Disjoint s t →
    T (s ∪ t) = T s + T t

namespace FinMeasAdditive

variable {β : Type*} [AddCommMonoid β] {T T' : Set α → β}

theorem zero : FinMeasAdditive μ (0 : Set α → β) := fun _ _ _ _ _ _ _ => by simp

theorem add (hT : FinMeasAdditive μ T) (hT' : FinMeasAdditive μ T') :
    FinMeasAdditive μ (T + T') := by
  intro s t hs ht hμs hμt hst
  simp only [hT s t hs ht hμs hμt hst, hT' s t hs ht hμs hμt hst, Pi.add_apply]
  abel

theorem smul [DistribSMul 𝕜 β] (hT : FinMeasAdditive μ T) (c : 𝕜) :
    FinMeasAdditive μ fun s => c • T s := fun s t hs ht hμs hμt hst => by
  simp [hT s t hs ht hμs hμt hst]

theorem of_eq_top_imp_eq_top {μ' : Measure α} (h : ∀ s, MeasurableSet s → μ s = ∞ → μ' s = ∞)
    (hT : FinMeasAdditive μ T) : FinMeasAdditive μ' T := fun s t hs ht hμ's hμ't hst =>
  hT s t hs ht (mt (h s hs) hμ's) (mt (h t ht) hμ't) hst

theorem of_smul_measure {c : ℝ≥0∞} (hc_ne_top : c ≠ ∞) (hT : FinMeasAdditive (c • μ) T) :
    FinMeasAdditive μ T := by
  refine of_eq_top_imp_eq_top (fun s _ hμs => ?_) hT
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.mul_eq_top] at hμs
  simp only [hc_ne_top, or_false, Ne, false_and] at hμs
  exact hμs.2

theorem smul_measure (c : ℝ≥0∞) (hc_ne_zero : c ≠ 0) (hT : FinMeasAdditive μ T) :
    FinMeasAdditive (c • μ) T := by
  refine of_eq_top_imp_eq_top (fun s _ hμs => ?_) hT
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.mul_eq_top]
  simp only [hc_ne_zero, true_and, Ne, not_false_iff]
  exact Or.inl hμs

theorem smul_measure_iff (c : ℝ≥0∞) (hc_ne_zero : c ≠ 0) (hc_ne_top : c ≠ ∞) :
    FinMeasAdditive (c • μ) T ↔ FinMeasAdditive μ T :=
  ⟨fun hT => of_smul_measure hc_ne_top hT, fun hT => smul_measure c hc_ne_zero hT⟩

theorem map_empty_eq_zero {β} [AddCancelMonoid β] {T : Set α → β} (hT : FinMeasAdditive μ T) :
    T ∅ = 0 := by
  have h_empty : μ ∅ ≠ ∞ := (measure_empty.le.trans_lt ENNReal.coe_lt_top).ne
  specialize hT ∅ ∅ MeasurableSet.empty MeasurableSet.empty h_empty h_empty (disjoint_empty _)
  rw [Set.union_empty] at hT
  nth_rw 1 [← add_zero (T ∅)] at hT
  exact (add_left_cancel hT).symm

theorem map_iUnion_fin_meas_set_eq_sum (T : Set α → β) (T_empty : T ∅ = 0)
    (h_add : FinMeasAdditive μ T) {ι} (S : ι → Set α) (sι : Finset ι)
    (hS_meas : ∀ i, MeasurableSet (S i)) (hSp : ∀ i ∈ sι, μ (S i) ≠ ∞)
    (h_disj : ∀ᵉ (i ∈ sι) (j ∈ sι), i ≠ j → Disjoint (S i) (S j)) :
    T (⋃ i ∈ sι, S i) = ∑ i ∈ sι, T (S i) := by
  classical
  revert hSp h_disj
  refine Finset.induction_on sι ?_ ?_
  · simp only [Finset.notMem_empty, IsEmpty.forall_iff, iUnion_false, iUnion_empty, sum_empty,
      imp_true_iff, T_empty]
  intro a s has h hps h_disj
  rw [Finset.sum_insert has, ← h]
  swap; · exact fun i hi => hps i (Finset.mem_insert_of_mem hi)
  swap
  · exact fun i hi j hj hij =>
      h_disj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
  rw [←
    h_add (S a) (⋃ i ∈ s, S i) (hS_meas a) (measurableSet_biUnion _ fun i _ => hS_meas i)
      (hps a (Finset.mem_insert_self a s))]
  · congr; convert Finset.iSup_insert a s S
  · exact (measure_biUnion_lt_top s.finite_toSet fun i hi ↦
      (hps i <| Finset.mem_insert_of_mem hi).lt_top).ne
  · simp_rw [Set.disjoint_iUnion_right]
    intro i hi
    refine h_disj a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi) fun hai ↦ ?_
    rw [← hai] at hi
    exact has hi

end FinMeasAdditive

/-- A `FinMeasAdditive` set function whose norm on every set is less than the measure of the
set (up to a multiplicative constant). -/
def DominatedFinMeasAdditive {β} [SeminormedAddCommGroup β] {_ : MeasurableSpace α} (μ : Measure α)
    (T : Set α → β) (C : ℝ) : Prop :=
  FinMeasAdditive μ T ∧ ∀ s, MeasurableSet s → μ s < ∞ → ‖T s‖ ≤ C * μ.real s

namespace DominatedFinMeasAdditive

variable {β : Type*} [SeminormedAddCommGroup β] {T T' : Set α → β} {C C' : ℝ}

theorem zero {m : MeasurableSpace α} (μ : Measure α) (hC : 0 ≤ C) :
    DominatedFinMeasAdditive μ (0 : Set α → β) C := by
  refine ⟨FinMeasAdditive.zero, fun s _ _ => ?_⟩
  rw [Pi.zero_apply, norm_zero]
  exact mul_nonneg hC toReal_nonneg

theorem eq_zero_of_measure_zero {β : Type*} [NormedAddCommGroup β] {T : Set α → β} {C : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) {s : Set α} (hs : MeasurableSet s) (hs_zero : μ s = 0) :
    T s = 0 := by
  refine norm_eq_zero.mp ?_
  refine ((hT.2 s hs (by simp [hs_zero])).trans (le_of_eq ?_)).antisymm (norm_nonneg _)
  rw [measureReal_def, hs_zero, ENNReal.toReal_zero, mul_zero]

theorem eq_zero {β : Type*} [NormedAddCommGroup β] {T : Set α → β} {C : ℝ} {_ : MeasurableSpace α}
    (hT : DominatedFinMeasAdditive (0 : Measure α) T C) {s : Set α} (hs : MeasurableSet s) :
    T s = 0 :=
  eq_zero_of_measure_zero hT hs (by simp only [Measure.coe_zero, Pi.zero_apply])

theorem add (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C') :
    DominatedFinMeasAdditive μ (T + T') (C + C') := by
  refine ⟨hT.1.add hT'.1, fun s hs hμs => ?_⟩
  rw [Pi.add_apply, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hT.2 s hs hμs) (hT'.2 s hs hμs))

theorem smul [SeminormedAddGroup 𝕜] [DistribSMul 𝕜 β] [IsBoundedSMul 𝕜 β]
    (hT : DominatedFinMeasAdditive μ T C) (c : 𝕜) :
    DominatedFinMeasAdditive μ (fun s => c • T s) (‖c‖ * C) := by
  refine ⟨hT.1.smul c, fun s hs hμs => (norm_smul_le _ _).trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul le_rfl (hT.2 s hs hμs) (norm_nonneg _) (norm_nonneg _)

theorem of_measure_le {μ' : Measure α} (h : μ ≤ μ') (hT : DominatedFinMeasAdditive μ T C)
    (hC : 0 ≤ C) : DominatedFinMeasAdditive μ' T C := by
  have h' : ∀ s, μ s = ∞ → μ' s = ∞ := fun s hs ↦ top_unique <| hs.symm.trans_le (h _)
  refine ⟨hT.1.of_eq_top_imp_eq_top fun s _ ↦ h' s, fun s hs hμ's ↦ ?_⟩
  have hμs : μ s < ∞ := (h s).trans_lt hμ's
  calc
    ‖T s‖ ≤ C * μ.real s := hT.2 s hs hμs
    _ ≤ C * μ'.real s := by
      simp only [measureReal_def]
      gcongr
      exact hμ's.ne

theorem add_measure_right {_ : MeasurableSpace α} (μ ν : Measure α)
    (hT : DominatedFinMeasAdditive μ T C) (hC : 0 ≤ C) : DominatedFinMeasAdditive (μ + ν) T C :=
  of_measure_le (Measure.le_add_right le_rfl) hT hC

theorem add_measure_left {_ : MeasurableSpace α} (μ ν : Measure α)
    (hT : DominatedFinMeasAdditive ν T C) (hC : 0 ≤ C) : DominatedFinMeasAdditive (μ + ν) T C :=
  of_measure_le (Measure.le_add_left le_rfl) hT hC

theorem of_smul_measure {c : ℝ≥0∞} (hc_ne_top : c ≠ ∞) (hT : DominatedFinMeasAdditive (c • μ) T C) :
    DominatedFinMeasAdditive μ T (c.toReal * C) := by
  have h : ∀ s, MeasurableSet s → c • μ s = ∞ → μ s = ∞ := by
    intro s _ hcμs
    simp only [hc_ne_top, smul_eq_mul, ENNReal.mul_eq_top, or_false, Ne,
      false_and] at hcμs
    exact hcμs.2
  refine ⟨hT.1.of_eq_top_imp_eq_top (μ := c • μ) h, fun s hs hμs => ?_⟩
  have hcμs : c • μ s ≠ ∞ := mt (h s hs) hμs.ne
  rw [smul_eq_mul] at hcμs
  refine (hT.2 s hs hcμs.lt_top).trans (le_of_eq ?_)
  simp only [measureReal_ennreal_smul_apply]
  ring

theorem of_measure_le_smul {μ' : Measure α} {c : ℝ≥0∞} (hc : c ≠ ∞) (h : μ ≤ c • μ')
    (hT : DominatedFinMeasAdditive μ T C) (hC : 0 ≤ C) :
    DominatedFinMeasAdditive μ' T (c.toReal * C) :=
  (hT.of_measure_le h hC).of_smul_measure hc

end DominatedFinMeasAdditive

end FinMeasAdditive

namespace SimpleFunc

/-- Extend `Set α → (F →L[ℝ] F')` to `(α →ₛ F) → F'`. -/
def setToSimpleFunc {_ : MeasurableSpace α} (T : Set α → F →L[ℝ] F') (f : α →ₛ F) : F' :=
  ∑ x ∈ f.range, T (f ⁻¹' {x}) x

@[simp]
theorem setToSimpleFunc_zero {m : MeasurableSpace α} (f : α →ₛ F) :
    setToSimpleFunc (0 : Set α → F →L[ℝ] F') f = 0 := by simp [setToSimpleFunc]

theorem setToSimpleFunc_zero' {T : Set α → E →L[ℝ] F'}
    (h_zero : ∀ s, MeasurableSet s → μ s < ∞ → T s = 0) (f : α →ₛ E) (hf : Integrable f μ) :
    setToSimpleFunc T f = 0 := by
  simp_rw [setToSimpleFunc]
  refine sum_eq_zero fun x _ => ?_
  by_cases hx0 : x = 0
  · simp [hx0]
  rw [h_zero (f ⁻¹' ({x} : Set E)) (measurableSet_fiber _ _)
      (measure_preimage_lt_top_of_integrable f hf hx0),
    ContinuousLinearMap.zero_apply]

@[simp]
theorem setToSimpleFunc_zero_apply {m : MeasurableSpace α} (T : Set α → F →L[ℝ] F') :
    setToSimpleFunc T (0 : α →ₛ F) = 0 := by
  cases isEmpty_or_nonempty α <;> simp [setToSimpleFunc]

theorem setToSimpleFunc_eq_sum_filter [DecidablePred fun x ↦ x ≠ (0 : F)]
    {m : MeasurableSpace α} (T : Set α → F →L[ℝ] F') (f : α →ₛ F) :
    setToSimpleFunc T f = ∑ x ∈ f.range with x ≠ 0, T (f ⁻¹' {x}) x := by
  symm
  refine sum_filter_of_ne fun x _ => mt fun hx0 => ?_
  rw [hx0]
  exact map_zero _

theorem map_setToSimpleFunc (T : Set α → F →L[ℝ] F') (h_add : FinMeasAdditive μ T) {f : α →ₛ G}
    (hf : Integrable f μ) {g : G → F} (hg : g 0 = 0) :
    (f.map g).setToSimpleFunc T = ∑ x ∈ f.range, T (f ⁻¹' {x}) (g x) := by
  classical
  have T_empty : T ∅ = 0 := h_add.map_empty_eq_zero
  have hfp : ∀ x ∈ f.range, x ≠ 0 → μ (f ⁻¹' {x}) ≠ ∞ := fun x _ hx0 =>
    (measure_preimage_lt_top_of_integrable f hf hx0).ne
  simp only [setToSimpleFunc, range_map]
  refine Finset.sum_image' _ fun b hb => ?_
  rcases mem_range.1 hb with ⟨a, rfl⟩
  by_cases h0 : g (f a) = 0
  · simp_rw [h0]
    rw [map_zero, Finset.sum_eq_zero fun x hx => ?_]
    rw [mem_filter] at hx
    rw [hx.2, map_zero]
  have h_left_eq :
    T (map g f ⁻¹' {g (f a)}) (g (f a))
      = T (f ⁻¹' ({b ∈ f.range | g b = g (f a)} : Finset _)) (g (f a)) := by
    rw [map_preimage_singleton]
  rw [h_left_eq]
  have h_left_eq' :
    T (f ⁻¹' ({b ∈ f.range | g b = g (f a)} : Finset _)) (g (f a))
      = T (⋃ y ∈ {b ∈ f.range | g b = g (f a)}, f ⁻¹' {y}) (g (f a)) := by
    rw [← Finset.set_biUnion_preimage_singleton]
  rw [h_left_eq']
  rw [h_add.map_iUnion_fin_meas_set_eq_sum T T_empty]
  · simp only [sum_apply, ContinuousLinearMap.coe_sum']
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [mem_filter] at hx
    rw [hx.2]
  · exact fun i => measurableSet_fiber _ _
  · grind
  · grind [Set.disjoint_iff]

theorem setToSimpleFunc_congr' (T : Set α → E →L[ℝ] F) (h_add : FinMeasAdditive μ T) {f g : α →ₛ E}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (h : Pairwise fun x y => T (f ⁻¹' {x} ∩ g ⁻¹' {y}) = 0) :
    f.setToSimpleFunc T = g.setToSimpleFunc T :=
  show ((pair f g).map Prod.fst).setToSimpleFunc T = ((pair f g).map Prod.snd).setToSimpleFunc T by
    have h_pair : Integrable (f.pair g) μ := integrable_pair hf hg
    rw [map_setToSimpleFunc T h_add h_pair Prod.fst_zero]
    rw [map_setToSimpleFunc T h_add h_pair Prod.snd_zero]
    refine Finset.sum_congr rfl fun p hp => ?_
    rcases mem_range.1 hp with ⟨a, rfl⟩
    by_cases eq : f a = g a
    · dsimp only [pair_apply]; rw [eq]
    · have : T (pair f g ⁻¹' {(f a, g a)}) = 0 := by
        have h_eq : T ((⇑(f.pair g)) ⁻¹' {(f a, g a)}) = T (f ⁻¹' {f a} ∩ g ⁻¹' {g a}) := by
          congr; rw [pair_preimage_singleton f g]
        rw [h_eq]
        exact h eq
      simp only [this, ContinuousLinearMap.zero_apply, pair_apply]

theorem setToSimpleFunc_congr (T : Set α → E →L[ℝ] F)
    (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0) (h_add : FinMeasAdditive μ T) {f g : α →ₛ E}
    (hf : Integrable f μ) (h : f =ᵐ[μ] g) : f.setToSimpleFunc T = g.setToSimpleFunc T := by
  refine setToSimpleFunc_congr' T h_add hf ((integrable_congr h).mp hf) ?_
  refine fun x y hxy => h_zero _ ((measurableSet_fiber f x).inter (measurableSet_fiber g y)) ?_
  rw [EventuallyEq, ae_iff] at h
  refine measure_mono_null (fun z => ?_) h
  simp_rw [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
  intro h
  rwa [h.1, h.2]

theorem setToSimpleFunc_congr_left (T T' : Set α → E →L[ℝ] F)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → T s = T' s) (f : α →ₛ E) (hf : Integrable f μ) :
    setToSimpleFunc T f = setToSimpleFunc T' f := by
  simp_rw [setToSimpleFunc]
  refine sum_congr rfl fun x _ => ?_
  by_cases hx0 : x = 0
  · simp [hx0]
  · rw [h (f ⁻¹' {x}) (SimpleFunc.measurableSet_fiber _ _)
        (SimpleFunc.measure_preimage_lt_top_of_integrable _ hf hx0)]

theorem setToSimpleFunc_add_left {m : MeasurableSpace α} (T T' : Set α → F →L[ℝ] F') {f : α →ₛ F} :
    setToSimpleFunc (T + T') f = setToSimpleFunc T f + setToSimpleFunc T' f := by
  simp_rw [setToSimpleFunc, Pi.add_apply]
  push_cast
  simp_rw [Pi.add_apply, sum_add_distrib]

theorem setToSimpleFunc_add_left' (T T' T'' : Set α → E →L[ℝ] F)
    (h_add : ∀ s, MeasurableSet s → μ s < ∞ → T'' s = T s + T' s) {f : α →ₛ E}
    (hf : Integrable f μ) : setToSimpleFunc T'' f = setToSimpleFunc T f + setToSimpleFunc T' f := by
  classical
  simp_rw [setToSimpleFunc_eq_sum_filter]
  suffices ∀ x ∈ {x ∈ f.range | x ≠ 0}, T'' (f ⁻¹' {x}) = T (f ⁻¹' {x}) + T' (f ⁻¹' {x}) by
    rw [← sum_add_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [this x hx]
    push_cast
    rw [Pi.add_apply]
  intro x hx
  refine
    h_add (f ⁻¹' {x}) (measurableSet_preimage _ _) (measure_preimage_lt_top_of_integrable _ hf ?_)
  rw [mem_filter] at hx
  exact hx.2

theorem setToSimpleFunc_smul_left {m : MeasurableSpace α} (T : Set α → F →L[ℝ] F') (c : ℝ)
    (f : α →ₛ F) : setToSimpleFunc (fun s => c • T s) f = c • setToSimpleFunc T f := by
  simp_rw [setToSimpleFunc, ContinuousLinearMap.smul_apply, smul_sum]

theorem setToSimpleFunc_smul_left' (T T' : Set α → E →L[ℝ] F') (c : ℝ)
    (h_smul : ∀ s, MeasurableSet s → μ s < ∞ → T' s = c • T s) {f : α →ₛ E} (hf : Integrable f μ) :
    setToSimpleFunc T' f = c • setToSimpleFunc T f := by
  classical
  simp_rw [setToSimpleFunc_eq_sum_filter]
  suffices ∀ x ∈ {x ∈ f.range | x ≠ 0}, T' (f ⁻¹' {x}) = c • T (f ⁻¹' {x}) by
    rw [smul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [this x hx, ContinuousLinearMap.smul_apply]
  intro x hx
  refine
    h_smul (f ⁻¹' {x}) (measurableSet_preimage _ _) (measure_preimage_lt_top_of_integrable _ hf ?_)
  rw [mem_filter] at hx
  exact hx.2

theorem setToSimpleFunc_add (T : Set α → E →L[ℝ] F) (h_add : FinMeasAdditive μ T) {f g : α →ₛ E}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    setToSimpleFunc T (f + g) = setToSimpleFunc T f + setToSimpleFunc T g :=
  have hp_pair : Integrable (f.pair g) μ := integrable_pair hf hg
  calc
    setToSimpleFunc T (f + g) = ∑ x ∈ (pair f g).range, T (pair f g ⁻¹' {x}) (x.fst + x.snd) := by
      rw [add_eq_map₂, map_setToSimpleFunc T h_add hp_pair]; simp
    _ = ∑ x ∈ (pair f g).range, (T (pair f g ⁻¹' {x}) x.fst + T (pair f g ⁻¹' {x}) x.snd) :=
      (Finset.sum_congr rfl fun _ _ => ContinuousLinearMap.map_add _ _ _)
    _ = (∑ x ∈ (pair f g).range, T (pair f g ⁻¹' {x}) x.fst) +
          ∑ x ∈ (pair f g).range, T (pair f g ⁻¹' {x}) x.snd := by
      rw [Finset.sum_add_distrib]
    _ = ((pair f g).map Prod.fst).setToSimpleFunc T +
          ((pair f g).map Prod.snd).setToSimpleFunc T := by
      rw [map_setToSimpleFunc T h_add hp_pair Prod.snd_zero,
        map_setToSimpleFunc T h_add hp_pair Prod.fst_zero]

theorem setToSimpleFunc_neg (T : Set α → E →L[ℝ] F) (h_add : FinMeasAdditive μ T) {f : α →ₛ E}
    (hf : Integrable f μ) : setToSimpleFunc T (-f) = -setToSimpleFunc T f :=
  calc
    setToSimpleFunc T (-f) = setToSimpleFunc T (f.map Neg.neg) := rfl
    _ = -setToSimpleFunc T f := by
      rw [map_setToSimpleFunc T h_add hf neg_zero, setToSimpleFunc, ← sum_neg_distrib]
      exact Finset.sum_congr rfl fun x _ => map_neg _ _

theorem setToSimpleFunc_sub (T : Set α → E →L[ℝ] F) (h_add : FinMeasAdditive μ T) {f g : α →ₛ E}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    setToSimpleFunc T (f - g) = setToSimpleFunc T f - setToSimpleFunc T g := by
  rw [sub_eq_add_neg, setToSimpleFunc_add T h_add hf, setToSimpleFunc_neg T h_add hg,
    sub_eq_add_neg]
  rw [integrable_iff] at hg ⊢
  intro x hx_ne
  rw [SimpleFunc.coe_neg, Pi.neg_def, ← Function.comp_def, preimage_comp, neg_preimage,
    Set.neg_singleton]
  refine hg (-x) ?_
  simp [hx_ne]

theorem setToSimpleFunc_smul_real (T : Set α → E →L[ℝ] F) (h_add : FinMeasAdditive μ T) (c : ℝ)
    {f : α →ₛ E} (hf : Integrable f μ) : setToSimpleFunc T (c • f) = c • setToSimpleFunc T f :=
  calc
    setToSimpleFunc T (c • f) = ∑ x ∈ f.range, T (f ⁻¹' {x}) (c • x) := by
      rw [smul_eq_map c f, map_setToSimpleFunc T h_add hf]; dsimp only; rw [smul_zero]
    _ = ∑ x ∈ f.range, c • T (f ⁻¹' {x}) x :=
      (Finset.sum_congr rfl fun b _ => by rw [map_smul (T (f ⁻¹' {b})) c b])
    _ = c • setToSimpleFunc T f := by simp only [setToSimpleFunc, smul_sum]

theorem setToSimpleFunc_smul {E} [NormedAddCommGroup E] [SMulZeroClass 𝕜 E]
    [NormedSpace ℝ E] [DistribSMul 𝕜 F] (T : Set α → E →L[ℝ] F) (h_add : FinMeasAdditive μ T)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (c : 𝕜) {f : α →ₛ E} (hf : Integrable f μ) :
    setToSimpleFunc T (c • f) = c • setToSimpleFunc T f :=
  calc
    setToSimpleFunc T (c • f) = ∑ x ∈ f.range, T (f ⁻¹' {x}) (c • x) := by
      rw [smul_eq_map c f, map_setToSimpleFunc T h_add hf]; dsimp only; rw [smul_zero]
    _ = ∑ x ∈ f.range, c • T (f ⁻¹' {x}) x := Finset.sum_congr rfl fun b _ => by rw [h_smul]
    _ = c • setToSimpleFunc T f := by simp only [setToSimpleFunc, smul_sum]

section Order

variable {G' G'' : Type*}
  [NormedAddCommGroup G''] [PartialOrder G''] [IsOrderedAddMonoid G''] [NormedSpace ℝ G'']
  [NormedAddCommGroup G'] [PartialOrder G'] [NormedSpace ℝ G']

theorem setToSimpleFunc_mono_left {m : MeasurableSpace α} (T T' : Set α → F →L[ℝ] G'')
    (hTT' : ∀ s x, T s x ≤ T' s x) (f : α →ₛ F) : setToSimpleFunc T f ≤ setToSimpleFunc T' f := by
  simp_rw [setToSimpleFunc]; gcongr; apply hTT'

theorem setToSimpleFunc_mono_left' (T T' : Set α → E →L[ℝ] G'')
    (hTT' : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, T s x ≤ T' s x) (f : α →ₛ E)
    (hf : Integrable f μ) : setToSimpleFunc T f ≤ setToSimpleFunc T' f := by
  unfold setToSimpleFunc
  gcongr with i _
  by_cases h0 : i = 0
  · simp [h0]
  · exact hTT' _ (measurableSet_fiber _ _) (measure_preimage_lt_top_of_integrable _ hf h0) i

theorem setToSimpleFunc_nonneg {m : MeasurableSpace α} (T : Set α → G' →L[ℝ] G'')
    (hT_nonneg : ∀ s x, 0 ≤ x → 0 ≤ T s x) (f : α →ₛ G') (hf : 0 ≤ f) :
    0 ≤ setToSimpleFunc T f := by
  refine sum_nonneg fun i hi => hT_nonneg _ i ?_
  rw [mem_range] at hi
  obtain ⟨y, hy⟩ := Set.mem_range.mp hi
  rw [← hy]
  refine le_trans ?_ (hf y)
  simp

theorem setToSimpleFunc_nonneg' (T : Set α → G' →L[ℝ] G'')
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) (f : α →ₛ G') (hf : 0 ≤ f)
    (hfi : Integrable f μ) : 0 ≤ setToSimpleFunc T f := by
  refine sum_nonneg fun i hi => ?_
  by_cases h0 : i = 0
  · simp [h0]
  refine
    hT_nonneg _ (measurableSet_fiber _ _) (measure_preimage_lt_top_of_integrable _ hfi h0) i ?_
  rw [mem_range] at hi
  obtain ⟨y, hy⟩ := Set.mem_range.mp hi
  rw [← hy]
  convert hf y

theorem setToSimpleFunc_mono [IsOrderedAddMonoid G']
    {T : Set α → G' →L[ℝ] G''} (h_add : FinMeasAdditive μ T)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f g : α →ₛ G'}
    (hfi : Integrable f μ) (hgi : Integrable g μ) (hfg : f ≤ g) :
    setToSimpleFunc T f ≤ setToSimpleFunc T g := by
  rw [← sub_nonneg, ← setToSimpleFunc_sub T h_add hgi hfi]
  refine setToSimpleFunc_nonneg' T hT_nonneg _ ?_ (hgi.sub hfi)
  intro x
  simp only [coe_sub, sub_nonneg, coe_zero, Pi.zero_apply, Pi.sub_apply]
  exact hfg x

end Order

theorem norm_setToSimpleFunc_le_sum_opNorm {m : MeasurableSpace α} (T : Set α → F' →L[ℝ] F)
    (f : α →ₛ F') : ‖f.setToSimpleFunc T‖ ≤ ∑ x ∈ f.range, ‖T (f ⁻¹' {x})‖ * ‖x‖ :=
  calc
    ‖∑ x ∈ f.range, T (f ⁻¹' {x}) x‖ ≤ ∑ x ∈ f.range, ‖T (f ⁻¹' {x}) x‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ f.range, ‖T (f ⁻¹' {x})‖ * ‖x‖ := by
      gcongr with b; apply ContinuousLinearMap.le_opNorm

theorem norm_setToSimpleFunc_le_sum_mul_norm (T : Set α → F →L[ℝ] F') {C : ℝ}
    (hT_norm : ∀ s, MeasurableSet s → ‖T s‖ ≤ C * μ.real s) (f : α →ₛ F) :
    ‖f.setToSimpleFunc T‖ ≤ C * ∑ x ∈ f.range, μ.real (f ⁻¹' {x}) * ‖x‖ :=
  calc
    ‖f.setToSimpleFunc T‖ ≤ ∑ x ∈ f.range, ‖T (f ⁻¹' {x})‖ * ‖x‖ :=
      norm_setToSimpleFunc_le_sum_opNorm T f
    _ ≤ ∑ x ∈ f.range, C * μ.real (f ⁻¹' {x}) * ‖x‖ := by
      gcongr
      exact hT_norm _ <| SimpleFunc.measurableSet_fiber _ _
    _ ≤ C * ∑ x ∈ f.range, μ.real (f ⁻¹' {x}) * ‖x‖ := by simp_rw [mul_sum, ← mul_assoc]; rfl

theorem norm_setToSimpleFunc_le_sum_mul_norm_of_integrable (T : Set α → E →L[ℝ] F') {C : ℝ}
    (hT_norm : ∀ s, MeasurableSet s → μ s < ∞ → ‖T s‖ ≤ C * μ.real s) (f : α →ₛ E)
    (hf : Integrable f μ) :
    ‖f.setToSimpleFunc T‖ ≤ C * ∑ x ∈ f.range, μ.real (f ⁻¹' {x}) * ‖x‖ :=
  calc
    ‖f.setToSimpleFunc T‖ ≤ ∑ x ∈ f.range, ‖T (f ⁻¹' {x})‖ * ‖x‖ :=
      norm_setToSimpleFunc_le_sum_opNorm T f
    _ ≤ ∑ x ∈ f.range, C * μ.real (f ⁻¹' {x}) * ‖x‖ := by
      refine Finset.sum_le_sum fun b hb => ?_
      obtain rfl | hb := eq_or_ne b 0
      · simp
      gcongr
      exact hT_norm _ (SimpleFunc.measurableSet_fiber _ _) <|
        SimpleFunc.measure_preimage_lt_top_of_integrable _ hf hb
    _ ≤ C * ∑ x ∈ f.range, μ.real (f ⁻¹' {x}) * ‖x‖ := by simp_rw [mul_sum, ← mul_assoc]; rfl

theorem setToSimpleFunc_indicator (T : Set α → F →L[ℝ] F') (hT_empty : T ∅ = 0)
    {m : MeasurableSpace α} {s : Set α} (hs : MeasurableSet s) (x : F) :
    SimpleFunc.setToSimpleFunc T
        (SimpleFunc.piecewise s hs (SimpleFunc.const α x) (SimpleFunc.const α 0)) =
      T s x := by
  classical
  obtain rfl | hs_empty := s.eq_empty_or_nonempty
  · simp only [hT_empty, ContinuousLinearMap.zero_apply, piecewise_empty, const_zero,
      setToSimpleFunc_zero_apply]
  simp_rw [setToSimpleFunc]
  obtain rfl | hs_univ := eq_or_ne s univ
  · haveI hα := hs_empty.to_type
    simp [← Function.const_def]
  rw [range_indicator hs hs_empty hs_univ]
  by_cases hx0 : x = 0
  · simp_rw [hx0]; simp
  rw [sum_insert]
  swap; · rw [Finset.mem_singleton]; exact hx0
  rw [sum_singleton, (T _).map_zero, add_zero]
  congr
  simp only [coe_piecewise, piecewise_eq_indicator, coe_const, Function.const_zero,
    piecewise_eq_indicator]
  rw [indicator_preimage, ← Function.const_def, preimage_const_of_mem]
  swap; · exact Set.mem_singleton x
  rw [← Function.const_zero, ← Function.const_def, preimage_const_of_notMem]
  swap; · rw [Set.mem_singleton_iff]; exact Ne.symm hx0
  simp

theorem setToSimpleFunc_const' [Nonempty α] (T : Set α → F →L[ℝ] F') (x : F)
    {m : MeasurableSpace α} : SimpleFunc.setToSimpleFunc T (SimpleFunc.const α x) = T univ x := by
  simp only [setToSimpleFunc, range_const, Set.mem_singleton, preimage_const_of_mem,
    sum_singleton, ← Function.const_def, coe_const]

theorem setToSimpleFunc_const (T : Set α → F →L[ℝ] F') (hT_empty : T ∅ = 0) (x : F)
    {m : MeasurableSpace α} : SimpleFunc.setToSimpleFunc T (SimpleFunc.const α x) = T univ x := by
  cases isEmpty_or_nonempty α
  · have h_univ_empty : (univ : Set α) = ∅ := Subsingleton.elim _ _
    rw [h_univ_empty, hT_empty]
    simp only [setToSimpleFunc, ContinuousLinearMap.zero_apply, sum_empty,
      range_eq_empty_of_isEmpty]
  · exact setToSimpleFunc_const' T x

end SimpleFunc

end MeasureTheory
