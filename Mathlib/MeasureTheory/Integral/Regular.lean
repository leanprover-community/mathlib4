/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
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
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
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
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.UrysohnsLemma

/-!
# Integrals of continuous functions with respect to regular measures

When a measure is regular, one may express the measure of compact sets and of open sets
in terms of the integral of continuous functions equal to 1 on the compact set, or to 0 outside
of the open set respectively.
-/

public section

open Filter Set MeasureTheory Measure

/-- In a locally compact regular space with an inner regular measure, the measure of a compact
set `k` is the infimum of the integrals of compactly supported functions equal to `1` on `k`. -/
lemma IsCompact.measure_eq_biInf_integral_hasCompactSupport
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {k : Set X} (hk : IsCompact k)
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [InnerRegularCompactLTTop μ]
    [LocallyCompactSpace X] [RegularSpace X] :
    μ k = ⨅ (f : X → ℝ) (_ : Continuous f) (_ : HasCompactSupport f) (_ : EqOn f 1 k)
      (_ : 0 ≤ f), ENNReal.ofReal (∫ x, f x ∂μ) := by
  apply le_antisymm
  · simp only [le_iInf_iff]
    intro f f_cont f_comp fk f_nonneg
    apply (f_cont.integrable_of_hasCompactSupport f_comp).measure_le_integral
    · exact Eventually.of_forall f_nonneg
    · exact fun x hx ↦ by simp [fk hx]
  · apply le_of_forall_gt (fun r hr ↦ ?_)
    simp only [iInf_lt_iff, exists_prop]
    obtain ⟨U, kU, U_open, mu_U⟩ : ∃ U, k ⊆ U ∧ IsOpen U ∧ μ U < r :=
      hk.exists_isOpen_lt_of_lt r hr
    obtain ⟨⟨f, f_cont⟩, fk, fU, f_comp, f_range⟩ : ∃ (f : C(X, ℝ)), EqOn f 1 k ∧ EqOn f 0 Uᶜ
        ∧ HasCompactSupport f ∧ ∀ (x : X), f x ∈ Icc 0 1 := exists_continuous_one_zero_of_isCompact
      hk U_open.isClosed_compl (disjoint_compl_right_iff_subset.mpr kU)
    refine ⟨f, f_cont, f_comp, fk, fun x ↦ (f_range x).1, ?_⟩
    exact (integral_le_measure (fun x _hx ↦ (f_range x).2) (fun x hx ↦ (fU hx).le)).trans_lt mu_U

/-- Given an inner regular finite measure, the measure of an open set is the supremum of the
integrals of nonnegative continuous functions supported in this set and bounded by `1`. -/
lemma IsOpen.measure_eq_biSup_integral_continuous
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]
    {U : Set X} (hU : IsOpen U)
    (μ : Measure X) [IsFiniteMeasure μ] [InnerRegularCompactLTTop μ] [NormalSpace X] :
    μ U = ⨆ (f : X → ℝ) (_ : Continuous f) (_ : EqOn f 0 Uᶜ) (_ : 0 ≤ f) (_ : f ≤ 1),
      ENNReal.ofReal (∫ x, f x ∂μ) := by
  apply le_antisymm
  · apply le_of_forall_lt (fun r hr ↦ ?_)
    simp only [lt_iSup_iff, exists_prop]
    obtain ⟨K, KU, K_comp, hK⟩ : ∃ K ⊆ U, IsCompact K ∧ r < μ K :=
      MeasurableSet.exists_lt_isCompact_of_ne_top hU.measurableSet (by simp) hr
    obtain ⟨⟨f, f_cont⟩, fU, fK, f_range⟩ : ∃ (f : C(X, ℝ)), EqOn f 0 Uᶜ ∧ EqOn f 1 K
        ∧ ∀ (x : X), f x ∈ Icc 0 1 := exists_continuous_zero_one_of_isClosed
      hU.isClosed_compl K_comp.isClosed (disjoint_compl_left_iff_subset.mpr KU)
    refine ⟨f, f_cont, fU, fun x ↦ (f_range x).1, fun x ↦ (f_range x).2, ?_⟩
    apply hK.trans_le
    apply Integrable.measure_le_integral
    · apply Integrable.of_mem_Icc 0 1 f_cont.aemeasurable
      filter_upwards [] with x using f_range x
    · filter_upwards [] with x using (f_range x).1
    · intro x hx
      apply Eq.ge
      exact fK hx
  · simp only [iSup_le_iff]
    intro f f_cont fU f_nonneg f_le
    exact integral_le_measure (fun x hx ↦ f_le x) (fun x hx ↦ le_of_eq (fU hx))
