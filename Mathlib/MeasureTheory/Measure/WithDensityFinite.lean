/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Exhaustion
public import Mathlib.Probability.ConditionalProbability
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# s-finite measures can be written as `withDensity` of a finite measure

If `μ` is an s-finite measure, then there exists a finite measure `μ.toFinite`
such that a set is `μ`-null iff it is `μ.toFinite`-null.
In particular, `MeasureTheory.ae μ.toFinite = MeasureTheory.ae μ` and `μ.toFinite = 0` iff `μ = 0`.
As a corollary, `μ` can be represented as `μ.toFinite.withDensity (μ.rnDeriv μ.toFinite)`.

Our definition of `MeasureTheory.Measure.toFinite` ensures some extra properties:

- if `μ` is a finite measure, then `μ.toFinite = μ[|univ] = (μ univ)⁻¹ • μ`;
- in particular, `μ.toFinite = μ` for a probability measure;
- if `μ ≠ 0`, then `μ.toFinite` is a probability measure.

## Main definitions

In this definition and the results below, `μ` is an s-finite measure (`SFinite μ`).

* `MeasureTheory.Measure.toFinite`: a finite measure with `μ ≪ μ.toFinite` and `μ.toFinite ≪ μ`.
  If `μ ≠ 0`, this is a probability measure.

## Main statements

* `absolutelyContinuous_toFinite`: `μ ≪ μ.toFinite`.
* `toFinite_absolutelyContinuous`: `μ.toFinite ≪ μ`.
* `ae_toFinite`: `ae μ.toFinite = ae μ`.

-/

@[expose] public section

open Set
open scoped ENNReal ProbabilityTheory

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- Auxiliary definition for `MeasureTheory.Measure.toFinite`. -/
noncomputable def Measure.toFiniteAux (μ : Measure α) [SFinite μ] : Measure α :=
  letI := Classical.dec
  if IsFiniteMeasure μ then μ else (exists_isFiniteMeasure_absolutelyContinuous μ).choose

/-- A finite measure obtained from an s-finite measure `μ`, such that
`μ = μ.toFinite.withDensity (μ.rnDeriv μ.toFinite)`
(see `MeasureTheory.Measure.withDensity_rnDeriv_eq` along with
`MeasureTheory.absolutelyContinuous_toFinite`). If `μ` is non-zero, then `μ.toFinite` is a
probability measure. -/
noncomputable def Measure.toFinite (μ : Measure α) [SFinite μ] : Measure α :=
  μ.toFiniteAux[|univ]

@[local simp]
lemma ae_toFiniteAux [SFinite μ] : ae μ.toFiniteAux = ae μ := by
  rw [Measure.toFiniteAux]
  split_ifs
  · simp
  · obtain ⟨_, h₁, h₂⟩ := (exists_isFiniteMeasure_absolutelyContinuous μ).choose_spec
    exact h₂.ae_le.antisymm h₁.ae_le

@[local instance]
theorem isFiniteMeasure_toFiniteAux [SFinite μ] : IsFiniteMeasure μ.toFiniteAux := by
  rw [Measure.toFiniteAux]
  split_ifs
  · assumption
  · exact (exists_isFiniteMeasure_absolutelyContinuous μ).choose_spec.1

@[simp]
lemma ae_toFinite [SFinite μ] : ae μ.toFinite = ae μ := by
  simp [Measure.toFinite, ProbabilityTheory.cond]

@[simp]
lemma toFinite_apply_eq_zero_iff [SFinite μ] {s : Set α} : μ.toFinite s = 0 ↔ μ s = 0 := by
  simp only [← compl_mem_ae_iff, ae_toFinite]

@[simp]
lemma toFinite_eq_zero_iff [SFinite μ] : μ.toFinite = 0 ↔ μ = 0 := by
  simp_rw [← Measure.measure_univ_eq_zero, toFinite_apply_eq_zero_iff]

@[simp]
lemma toFinite_zero : Measure.toFinite (0 : Measure α) = 0 := by simp

lemma toFinite_eq_self [IsProbabilityMeasure μ] : μ.toFinite = μ := by
  rw [Measure.toFinite, Measure.toFiniteAux, if_pos, ProbabilityTheory.cond_univ]
  infer_instance

instance [SFinite μ] : IsFiniteMeasure μ.toFinite := by
  rw [Measure.toFinite]
  infer_instance

instance [SFinite μ] [NeZero μ] : IsProbabilityMeasure μ.toFinite := by
  apply ProbabilityTheory.cond_isProbabilityMeasure
  simp [ne_eq, ← compl_mem_ae_iff, ae_toFiniteAux]

lemma absolutelyContinuous_toFinite (μ : Measure α) [SFinite μ] : μ ≪ μ.toFinite :=
  Measure.ae_le_iff_absolutelyContinuous.mp ae_toFinite.ge

lemma sfiniteSeq_absolutelyContinuous_toFinite (μ : Measure α) [SFinite μ] (n : ℕ) :
    sfiniteSeq μ n ≪ μ.toFinite :=
  (sfiniteSeq_le μ n).absolutelyContinuous.trans (absolutelyContinuous_toFinite μ)

lemma toFinite_absolutelyContinuous (μ : Measure α) [SFinite μ] : μ.toFinite ≪ μ :=
  Measure.ae_le_iff_absolutelyContinuous.mp ae_toFinite.le

lemma restrict_compl_sigmaFiniteSet [SFinite μ] :
    μ.restrict μ.sigmaFiniteSetᶜ = ∞ • μ.toFinite.restrict μ.sigmaFiniteSetᶜ := by
  rw [Measure.sigmaFiniteSet,
    restrict_compl_sigmaFiniteSetWRT (Measure.AbsolutelyContinuous.refl μ)]
  ext t ht
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
  by_cases hμt : μ (t ∩ (μ.sigmaFiniteSetWRT μ)ᶜ) = 0
  · rw [hμt, toFinite_absolutelyContinuous μ hμt]
  · rw [ENNReal.top_mul hμt, ENNReal.top_mul]
    exact fun h ↦ hμt (absolutelyContinuous_toFinite μ h)

end MeasureTheory
