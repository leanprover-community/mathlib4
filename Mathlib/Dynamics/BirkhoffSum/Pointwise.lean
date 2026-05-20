/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/
module

import Mathlib.Analysis.Oscillation
import Mathlib.Dynamics.BirkhoffSum.Maximal
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Order.Partition.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Topology.Continuous
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!

-/

noncomputable section

open MeasureTheory Measure MeasurableSpace Filter Topology Module
open scoped NNReal ENNReal Function

variable {α R E : Type*} {f : α → α} {g : α → ℝ} {n : ℕ} [RCLike R]
  [MeasurableSpace α] (μ : Measure α) (hf : MeasurePreserving f μ μ)
  (hg : Integrable g μ)

variable {μ} (R) in
abbrev koopman : Lp R 2 μ →ₗᵢ[R] Lp R 2 μ := Lp.compMeasurePreservingₗᵢ R f hf

local infixr:25 " →ₛ " => SimpleFunc

-- note: if it's only an addsubgroup, we would get dreaded instance diamonds later
variable (R) in
def Lp2S : Submodule R (Lp R 2 μ) :=
  { Lp.simpleFunc R 2 μ with
    smul_mem' a x hx := Lp.simpleFunc.smul.smul a ⟨x, hx⟩ |>.prop}

variable {μ} (R) in
def simpleCoboundaries : Submodule R (Lp R 2 μ) :=
  (Lp2S R μ).map ((koopman R hf).toLinearMap - 1)

example (g) : g ∈ simpleCoboundaries R hf →
    ∃ s : α →ₛ R, g =ᵐ[μ] s ∘ f - s := by
  simp only [simpleCoboundaries, Lp2S, Lp.simpleFunc, Submodule.mem_map, Submodule.mem_mk,
    AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq, LinearMap.sub_apply,
    LinearIsometry.coe_toLinearMap, End.one_apply, Subtype.exists, exists_and_left,
    exists_exists_eq_and, forall_exists_index]
  intro s _ rfl
  use s
  simp only [AddSubgroupClass.coe_sub, Lp.compMeasurePreservingₗᵢ_apply_coe,
    AEEqFun.compMeasurePreserving_mk]
  rw [← AEEqFun.mk_sub]
  exact AEEqFun.coeFn_mk _ _

@[fun_prop]
lemma LinearMap.continuous_id {E : Type*} [AddCommMonoid E] [Module R E] [TopologicalSpace E] :
    Continuous (1 : E →ₗ[R] E) := _root_.continuous_id

lemma simpleCoboundaries_dense :
    (koopman R hf).coboundaries ≤ (simpleCoboundaries R hf).topologicalClosure := by
  apply Continuous.range_subset_closure_image_dense
  · fun_prop
  · exact Lp.simpleFunc.dense (by decide)

lemma simpleCoboundaries_closure_eq :
    (koopman R hf).coboundaries.topologicalClosure =
    (simpleCoboundaries R hf).topologicalClosure := by
  apply le_antisymm
  · nth_rw 2 [← Submodule.topologicalClosure.idempotent _]
    exact Submodule.topologicalClosure.mono (simpleCoboundaries_dense ..)
  · apply Submodule.topologicalClosure.mono
    exact Set.image_subset_range ..

lemma topologicalClosure_fixedPoints_sup_simpleCoboundaries_eq_top :
    ((koopman R hf).fixedPoints ⊔ simpleCoboundaries R hf).topologicalClosure = ⊤ := by
  have : (koopman R hf).fixedPoints ⊔ (koopman R hf).coboundaries.topologicalClosure = ⊤ :=
    (koopman R hf).toContinuousLinearMap.fixedPoints_sup_topologicalClosure_coboundary_eq_top
    (koopman R hf).norm_toContinuousLinearMap_le
  rw [simpleCoboundaries_closure_eq] at this
  rw [eq_top_iff]
  apply this.ge.trans
  exact ClosureOperator.sup_closure_le ..

variable (R f) in
def convergenceSet := {g : Lp R 1 μ | ∀ᵐ x ∂μ, oscillation (birkhoffAverage R f g · x) atTop = 0}

variable [IsFiniteMeasure μ]

open Set

#exit

lemma mem_convergenceSet_of_mem_coboundary {g : Lp E 1 μ}
    (hg : g ∈ (koopman R E hf 1).coboundaries) : g ∈ convergenceSet R E f μ := by
  rcases hg with ⟨h, hh⟩
  simp at hh

  sorry

lemma ENNReal.forall_pos_of_forall_mul {motive : ℝ≥0∞ → Prop} (k : ℝ≥0∞)
    (h : ∀ ε > 0, motive (k * ε)) (hk₀ : k ≠ 0 := by positivity) (hk : k ≠ ∞ := by finiteness) :
    ∀ ε > 0, motive ε := fun ε hε ↦
  ENNReal.mul_div_cancel (a := k) (b := ε) hk₀ hk ▸ h (ε / k) (ENNReal.div_pos hε.ne_zero hk)

omit [IsFiniteMeasure μ] in
lemma foo {f : α → ℝ≥0∞} (h : ∀ ε > 0, ∀ᵐ x ∂μ, f x ≤ ε) : ∀ᵐ x ∂μ, f x ≤ 0 := by
  have H : ∀ᵐ x ∂μ, ∀ n : ℕ, f x ≤ (n : ℝ≥0∞)⁻¹ :=
    ae_all_iff.mpr fun n ↦ h _ (ENNReal.inv_pos.mpr (by finiteness))
  filter_upwards [H] with x hx
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hε.ne_zero
  exact (hx n).trans (by simp [hn.le])

include hf in
theorem closed_convergenceSet : IsClosed (convergenceSet R E f μ) := by
  refine isClosed_of_closure_subset (fun g hg ↦ ?_)
  rw [EMetric.mem_closure_iff] at hg
  simp only [convergenceSet, ← nonpos_iff_eq_zero, Set.mem_setOf_eq]
  apply foo
  refine ENNReal.forall_pos_of_forall_mul 2 fun δ hδ ↦ ?_
  by_cases! hδ' : δ = ∞; · bound
  apply ae_iff.mpr <| nonpos_iff_eq_zero.mp _
  push Not
  have (h : Lp E 1 μ) (hh : h ∈ convergenceSet R E f μ) :
      ∀ᵐ x ∂μ, 2 * δ < oscillation (birkhoffAverage R f g · x) atTop →
      δ < birkhoffAverageSup f (‖(⇑g - ⇑h) ·‖) x := by
    filter_upwards [hh] with x hosc hx
    have := hx.trans_le <| oscillation_le_add_sub (f₂ := (birkhoffAverage R f h · x)) ..
    rw [hosc] at this
    grw [oscillation_le_two_mul_iSup_enorm] at this
    simp only [Pi.sub_apply, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      ENNReal.ofNat_ne_top, ENNReal.mul_lt_mul_iff_right] at this
    change _ < ⨆ n, ‖(birkhoffAverage R f g - _) n x‖ₑ at this
    rw [← birkhoffAverage_sub] at this
    simp_rw [← EReal.coe_ennreal_lt_coe_ennreal_iff, EReal.coe_ennreal_iSup] at this
    exact this.trans_le (iSup_mono fun _ ↦ EReal.coe_le_coe norm_birkhoffAverage_le)
  refine le_of_forall_gt fun c hc ↦ ?_
  rcases hg (δ * c) (by positivity) with ⟨h, hh, hh'⟩
  apply measure_mono_ae (this h hh) |>.trans_lt

  apply iSup_distribution_birkhoffAverageSup_le_norm' μ hf (by fun_prop) δ |>.trans_lt
  rw [Integrable.toL1_sub g h (by fun_prop) (by fun_prop), ← edist_eq_enorm_sub,
    Integrable.toL1_coeFn, Integrable.toL1_coeFn]
  apply ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.mpr hδ') (by finiteness) hh' |>.trans_le
  rw [ENNReal.inv_mul_cancel_left (by positivity) hδ']
