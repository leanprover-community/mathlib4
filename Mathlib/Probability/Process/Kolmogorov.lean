/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Floor
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.Metrizable.Real

/-!
# Stochastic processes satisfying the Kolmogorov condition

A stochastic process `X : T → Ω → E` on an index space `T` and a measurable space `Ω`
with measure `P` is said to satisfy the Kolmogorov condition with exponents `p, q` and constant `M`
if for all `s, t : T`, the pair `(X s, X t)` is measurable for the Borel sigma-algebra on `E × E`
and the following condition holds:
`∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P ≤ M * edist s t ^ q`.

This condition is the main assumption of the Kolmogorov-Chentsov theorem, which gives the existence
of a continuous modification of the process.

The measurability condition on pairs ensures that the distance `edist (X s ω) (X t ω)` is
measurable in `ω` for fixed `s, t`. In a space with second-countable topology, the measurability
of pairs can be obtained from measurability of each `X t`.

## Main definitions

* `IsKolmogorovProcess`: property of being a stochastic process that satisfies
  the Kolmogorov condition.
* `IsAEKolmogorovProcess`: a stochastic process satisfies `IsAEKolmogorovProcess` if it is
  a modification of a process satisfying the Kolmogorov condition.

## Main statements

* `IsKolmogorovProcess.mk_of_secondCountableTopology`: in a space with second-countable topology,
  a process is a Kolmogorov process if each `X t` is measurable and the Kolmogorov condition holds.

-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {T Ω E : Type*} [PseudoEMetricSpace T] {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]
  {p q : ℝ} {M : ℝ≥0} {P : Measure Ω} {X : T → Ω → E}

/-- A stochastic process `X : T → Ω → E` on an index space `T` and a measurable space `Ω`
with measure `P` is said to satisfy the Kolmogorov condition with exponents `p, q` and constant `M`
if for all `s, t : T`, the pair `(X s, X t)` is measurable for the Borel sigma-algebra on `E × E`
and the following condition holds: `∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P ≤ M * edist s t ^ q`. -/
structure IsKolmogorovProcess (X : T → Ω → E) (P : Measure Ω) (p q : ℝ) (M : ℝ≥0) : Prop where
  measurablePair : ∀ s t : T, Measurable[_, borel (E × E)] fun ω ↦ (X s ω, X t ω)
  kolmogorovCondition : ∀ s t : T, ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P ≤ M * edist s t ^ q
  p_pos : 0 < p
  q_pos : 0 < q

/-- Property of being a modification of a stochastic process that satisfies the Kolmogorov
condition (`IsKolmogorovProcess`). -/
def IsAEKolmogorovProcess (X : T → Ω → E) (P : Measure Ω) (p q : ℝ) (M : ℝ≥0) : Prop :=
  ∃ Y, IsKolmogorovProcess Y P p q M ∧ ∀ t, X t =ᵐ[P] Y t

lemma IsKolmogorovProcess.IsAEKolmogorovProcess (hX : IsKolmogorovProcess X P p q M) :
    IsAEKolmogorovProcess X P p q M := ⟨X, hX, by simp⟩

namespace IsAEKolmogorovProcess

/-- A process with the property `IsKolmogorovProcess` such that `∀ t, X t =ᵐ[P] h.mk X t`. -/
protected noncomputable
def mk (X : T → Ω → E) (h : IsAEKolmogorovProcess X P p q M) : T → Ω → E :=
  Classical.choose h

lemma IsKolmogorovProcess_mk (h : IsAEKolmogorovProcess X P p q M) :
    IsKolmogorovProcess (h.mk X) P p q M := (Classical.choose_spec h).1

lemma ae_eq_mk (h : IsAEKolmogorovProcess X P p q M) : ∀ t, X t =ᵐ[P] h.mk X t :=
  (Classical.choose_spec h).2

lemma kolmogorovCondition (hX : IsAEKolmogorovProcess X P p q M) (s t : T) :
    ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P ≤ M * edist s t ^ q := by
  convert hX.IsKolmogorovProcess_mk.kolmogorovCondition s t using 1
  refine lintegral_congr_ae ?_
  filter_upwards [hX.ae_eq_mk s, hX.ae_eq_mk t] with ω hω₁ hω₂
  simp_rw [hω₁, hω₂]

lemma p_pos (hX : IsAEKolmogorovProcess X P p q M) : 0 < p := hX.IsKolmogorovProcess_mk.p_pos

lemma q_pos (hX : IsAEKolmogorovProcess X P p q M) : 0 < q := hX.IsKolmogorovProcess_mk.q_pos

lemma congr {Y : T → Ω → E} (hX : IsAEKolmogorovProcess X P p q M)
    (h : ∀ t, X t =ᵐ[P] Y t) :
    IsAEKolmogorovProcess Y P p q M := by
  refine ⟨hX.mk X, hX.IsKolmogorovProcess_mk, fun t ↦ ?_⟩
  filter_upwards [hX.ae_eq_mk t, h t] with ω hX hY using hY.symm.trans hX

end IsAEKolmogorovProcess

section Measurability

lemma IsKolmogorovProcess.stronglyMeasurable_edist
    (hX : IsKolmogorovProcess X P p q M) {s t : T} :
    StronglyMeasurable (fun ω ↦ edist (X s ω) (X t ω)) := by
  borelize (E × E)
  exact continuous_edist.stronglyMeasurable.comp_measurable (hX.measurablePair s t)

lemma IsAEKolmogorovProcess.aestronglyMeasurable_edist
    (hX : IsAEKolmogorovProcess X P p q M) {s t : T} :
    AEStronglyMeasurable (fun ω ↦ edist (X s ω) (X t ω)) P := by
  refine ⟨(fun ω ↦ edist (hX.mk X s ω) (hX.mk X t ω)),
    hX.IsKolmogorovProcess_mk.stronglyMeasurable_edist, ?_⟩
  filter_upwards [hX.ae_eq_mk s, hX.ae_eq_mk t] with ω hω₁ hω₂ using by simp [hω₁, hω₂]

lemma IsKolmogorovProcess.measurable_edist (hX : IsKolmogorovProcess X P p q M) {s t : T} :
    Measurable (fun ω ↦ edist (X s ω) (X t ω)) := hX.stronglyMeasurable_edist.measurable

lemma IsAEKolmogorovProcess.aemeasurable_edist (hX : IsAEKolmogorovProcess X P p q M) {s t : T} :
    AEMeasurable (fun ω ↦ edist (X s ω) (X t ω)) P := hX.aestronglyMeasurable_edist.aemeasurable

variable [MeasurableSpace E] [BorelSpace E]

lemma IsKolmogorovProcess.measurable (hX : IsKolmogorovProcess X P p q M) (s : T) :
    Measurable (X s) :=
  (measurable_fst.mono prod_le_borel_prod le_rfl).comp (hX.measurablePair s s)

lemma IsAEKolmogorovProcess.aemeasurable (hX : IsAEKolmogorovProcess X P p q M) (s : T) :
    AEMeasurable (X s) P := by
  refine ⟨hX.mk X s, hX.IsKolmogorovProcess_mk.measurable s, ?_⟩
  filter_upwards [hX.ae_eq_mk s] with ω hω using hω

lemma IsKolmogorovProcess.mk_of_secondCountableTopology [SecondCountableTopology E]
    (h_meas : ∀ s, Measurable (X s))
    (h_kol : ∀ s t : T, ∫⁻ ω, (edist (X s ω) (X t ω)) ^ p ∂P ≤ M * edist s t ^ q)
    (hp : 0 < p) (hq : 0 < q) :
    IsKolmogorovProcess X P p q M where
  measurablePair s t := by
    suffices Measurable (fun ω ↦ (X s ω, X t ω)) by
      rwa [Prod.borelSpace.measurable_eq] at this
    fun_prop
  kolmogorovCondition := h_kol
  p_pos := hp
  q_pos := hq

end Measurability

section ZeroDist

lemma IsAEKolmogorovProcess.edist_eq_zero (hX : IsAEKolmogorovProcess X P p q M)
    {s t : T} (h : edist s t = 0) :
    ∀ᵐ ω ∂P, edist (X s ω) (X t ω) = 0 := by
  suffices (fun ω ↦ edist (X s ω) (X t ω) ^ p) =ᵐ[P] 0 by
    filter_upwards [this] with ω hω
    simpa [hX.p_pos, not_lt_of_gt hX.p_pos] using hω
  rw [← lintegral_eq_zero_iff' (hX.aemeasurable_edist.pow_const p), ← nonpos_iff_eq_zero]
  calc ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P
  _ ≤ M * edist s t ^ q := hX.kolmogorovCondition s t
  _ = 0 := by simp [h, hX.q_pos]

lemma IsKolmogorovProcess.edist_eq_zero (hX : IsKolmogorovProcess X P p q M)
    {s t : T} (h : edist s t = 0) :
    ∀ᵐ ω ∂P, edist (X s ω) (X t ω) = 0 :=
  hX.IsAEKolmogorovProcess.edist_eq_zero h

lemma IsAEKolmogorovProcess.edist_eq_zero_of_const_eq_zero (hX : IsAEKolmogorovProcess X P p q 0)
    (s t : T) :
    ∀ᵐ ω ∂P, edist (X s ω) (X t ω) = 0 := by
  suffices (fun ω ↦ edist (X s ω) (X t ω) ^ p) =ᵐ[P] 0 by
    filter_upwards [this] with ω hω
    simpa [hX.p_pos, not_lt_of_gt hX.p_pos] using hω
  rw [← lintegral_eq_zero_iff' (hX.aemeasurable_edist.pow_const p), ← nonpos_iff_eq_zero]
  calc ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P
  _ ≤ 0 * edist s t ^ q := hX.kolmogorovCondition s t
  _ = 0 := by simp

lemma IsKolmogorovProcess.edist_eq_zero_of_const_eq_zero (hX : IsKolmogorovProcess X P p q 0)
    (s t : T) :
    ∀ᵐ ω ∂P, edist (X s ω) (X t ω) = 0 :=
  hX.IsAEKolmogorovProcess.edist_eq_zero_of_const_eq_zero s t

end ZeroDist

end ProbabilityTheory
