/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Probability.Decision.Risk.Defs
public import Mathlib.Probability.Kernel.Composition.CompNotation
public import Mathlib.Probability.Kernel.Composition.CompProd
import Batteries.Tactic.Congr
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.Probability.Kernel.Composition.MeasureComp
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

/-!
# Basic properties of the risk of an estimator

## Main statements

* `iSup_bayesRisk_le_minimaxRisk`: the maximal Bayes risk is less than or equal to the minimax risk.
* `bayesRisk_le_bayesRisk_comp`: data-processing inequality for the Bayes risk with respect to a
  prior: if we compose the data generating kernel `P` with a Markov kernel, then the Bayes risk
  increases.
* `bayesRisk_le_iInf`: for `P` a Markov kernel, the Bayes risk is less than `⨅ y, ∫⁻ θ, ℓ θ y ∂π`.

In several cases, there is no information in the data about the parameter and the Bayes risk takes
its maximal value.
* `bayesRisk_const`: if the data generating kernel is constant, then the Bayes risk is equal to
  `⨅ y, ∫⁻ θ, ℓ θ y ∂π`.
* `bayesRisk_of_subsingleton`: if the observation space is a subsingleton, then the Bayes risk is
  equal to `⨅ y, ∫⁻ θ, ℓ θ y ∂π`.

## TODO

In many cases, the maximal Bayes risk and the minimax risk are equal
(by a so-called minimax theorem).

-/

public section

open MeasureTheory Function
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Θ 𝓧 𝓧' 𝓨 : Type*} {mΘ : MeasurableSpace Θ}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓧' : MeasurableSpace 𝓧'} {m𝓨 : MeasurableSpace 𝓨}
  {ℓ : Θ → 𝓨 → ℝ≥0∞} {P : Kernel Θ 𝓧} {κ : Kernel 𝓧 𝓨} {π : Measure Θ}

section BayesRiskLeMinimaxRisk

lemma avgRisk_le_iSup_risk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨)
    (π : Measure Θ) [IsProbabilityMeasure π] :
    avgRisk ℓ P κ π ≤ ⨆ θ, ∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ) := lintegral_le_iSup _

lemma bayesRisk_le_avgRisk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨)
    (π : Measure Θ) [hκ : IsMarkovKernel κ] :
    bayesRisk ℓ P π ≤ avgRisk ℓ P κ π := iInf₂_le κ hκ

lemma bayesRisk_le_minimaxRisk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    (π : Measure Θ) [IsProbabilityMeasure π] :
    bayesRisk ℓ P π ≤ minimaxRisk ℓ P := iInf₂_mono fun _ _ ↦ avgRisk_le_iSup_risk _ _ _ _

/-- The maximal Bayes risk is less than or equal to the minimax risk. -/
lemma iSup_bayesRisk_le_minimaxRisk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) :
    ⨆ (π : Measure Θ) (_ : IsProbabilityMeasure π), bayesRisk ℓ P π
      ≤ minimaxRisk ℓ P := iSup₂_le fun _ _ ↦ bayesRisk_le_minimaxRisk _ _ _

end BayesRiskLeMinimaxRisk

section Const

/-- See `avgRisk_const_left'` for a similar result with integrals swapped. -/
lemma avgRisk_const_left (ℓ : Θ → 𝓨 → ℝ≥0∞) (μ : Measure 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ) :
    avgRisk ℓ (Kernel.const Θ μ) κ π = ∫⁻ θ, ∫⁻ y, ℓ θ y ∂(κ ∘ₘ μ) ∂π := by
  simp [avgRisk]

/-- See `avgRisk_const_left` for a similar result with integrals swapped. -/
lemma avgRisk_const_left' (hl : Measurable (uncurry ℓ)) (μ : Measure 𝓧) [SFinite μ]
    (κ : Kernel 𝓧 𝓨) [IsSFiniteKernel κ] (π : Measure Θ) [SFinite π] :
    avgRisk ℓ (Kernel.const Θ μ) κ π = ∫⁻ y, ∫⁻ θ, ℓ θ y ∂π ∂(κ ∘ₘ μ) := by
  rw [avgRisk_const_left, lintegral_lintegral_swap (by fun_prop)]

/-- See `avgRisk_const_right` for a simpler result when `P` is a Markov kernel. -/
lemma avgRisk_const_right' (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (ν : Measure 𝓨) (π : Measure Θ) :
    avgRisk ℓ P (Kernel.const 𝓧 ν) π = ∫⁻ θ, P θ .univ * ∫⁻ y, ℓ θ y ∂ν ∂π := by
  simp [avgRisk, Kernel.const_comp]

/-- See `avgRisk_const_right'` for a similar result when `P` is not a Markov kernel. -/
lemma avgRisk_const_right (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (ν : Measure 𝓨) (π : Measure Θ) :
    avgRisk ℓ P (Kernel.const 𝓧 ν) π = ∫⁻ θ, ∫⁻ y, ℓ θ y ∂ν ∂π := by
  simp [avgRisk_const_right']

/-- See `bayesRisk_le_iInf` for a simpler result when `P` is a Markov kernel. -/
lemma bayesRisk_le_iInf' (hl : Measurable (uncurry ℓ)) (P : Kernel Θ 𝓧) (π : Measure Θ) :
    bayesRisk ℓ P π ≤ ⨅ y, ∫⁻ θ, ℓ θ y * P θ .univ ∂π := by
  simp_rw [le_iInf_iff, bayesRisk]
  refine fun y ↦ iInf_le_of_le (Kernel.const _ (Measure.dirac y)) ?_
  simp only [iInf_pos, avgRisk_const_right', mul_comm]
  gcongr with θ
  rw [lintegral_dirac' _ (by fun_prop)]

/-- See `bayesRisk_le_iInf'` for a similar result when `P` is not a Markov kernel. -/
lemma bayesRisk_le_iInf (hl : Measurable (uncurry ℓ)) (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (π : Measure Θ) :
    bayesRisk ℓ P π ≤ ⨅ y, ∫⁻ θ, ℓ θ y ∂π :=
  (bayesRisk_le_iInf' hl P π).trans_eq (by simp)

lemma bayesRisk_const' (hl : Measurable (uncurry ℓ))
    (μ : Measure 𝓧) [SFinite μ] (π : Measure Θ) [SFinite π]
    (hl_pos : μ .univ = ∞ → ⨅ y, ∫⁻ θ, ℓ θ y ∂π = 0 → ∃ y, ∫⁻ θ, ℓ θ y ∂π = 0)
    (h_zero : μ = 0 → Nonempty 𝓨) :
    bayesRisk ℓ (Kernel.const Θ μ) π = ⨅ y, ∫⁻ θ, ℓ θ y * μ .univ ∂π := by
  refine le_antisymm ((bayesRisk_le_iInf' hl _ _).trans_eq (by simp)) ?_
  simp_rw [bayesRisk, le_iInf_iff]
  intro κ hκ
  rw [avgRisk_const_left' hl]
  refine le_trans ?_ (iInf_mul_le_lintegral (fun y ↦ ∫⁻ θ, ℓ θ y ∂π))
  rw [Measure.comp_apply_univ, ENNReal.iInf_mul' hl_pos (fun hμ ↦ h_zero (by simpa using hμ))]
  gcongr with y
  rw [lintegral_mul_const]
  fun_prop

lemma bayesRisk_const_of_neZero (hl : Measurable (uncurry ℓ))
    (μ : Measure 𝓧) [NeZero μ] [IsFiniteMeasure μ] (π : Measure Θ) [SFinite π] :
    bayesRisk ℓ (Kernel.const Θ μ) π = ⨅ y, ∫⁻ θ, ℓ θ y * μ .univ ∂π :=
  bayesRisk_const' hl μ π (by simp) (by simp [NeZero.out])

lemma bayesRisk_const_of_nonempty [Nonempty 𝓨] (hl : Measurable (uncurry ℓ))
    (μ : Measure 𝓧) [IsFiniteMeasure μ] (π : Measure Θ) [SFinite π] :
    bayesRisk ℓ (Kernel.const Θ μ) π = ⨅ y, ∫⁻ θ, ℓ θ y * μ .univ ∂π :=
  bayesRisk_const' hl μ π (by simp) (fun _ ↦ inferInstance)

lemma bayesRisk_const (hl : Measurable (uncurry ℓ))
    (μ : Measure 𝓧) [IsProbabilityMeasure μ] (π : Measure Θ) [SFinite π] :
    bayesRisk ℓ (Kernel.const Θ μ) π = ⨅ y, ∫⁻ θ, ℓ θ y ∂π := by
  simp [bayesRisk_const_of_neZero hl μ π]

end Const

section Bounds

/-- See `avgRisk_le_mul` for the usual case in which `π` is a probability measure and the kernels
are Markov. -/
lemma avgRisk_le_mul' (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ)
    {C : ℝ≥0} (hℓC : ∀ θ y, ℓ θ y ≤ C) :
    avgRisk ℓ P κ π ≤ C * κ.bound * P.bound * π Set.univ :=
  calc ∫⁻ θ, ∫⁻ y, ℓ θ y ∂(κ ∘ₖ P) θ ∂π
  _ ≤ ∫⁻ θ, ∫⁻ y, C ∂(κ ∘ₖ P) θ ∂π := by gcongr with θ y; exact hℓC θ y
  _ = ∫⁻ θ, C * ∫⁻ x, κ x .univ ∂P θ ∂π := by simp [Kernel.comp_apply' _ _ _ .univ]
  _ ≤ ∫⁻ θ, C * ∫⁻ x, κ.bound ∂P θ ∂π := by
    gcongr with θ x
    exact Kernel.measure_le_bound κ x Set.univ
  _ ≤ ∫⁻ θ, C * κ.bound * P.bound ∂π := by
    conv_lhs => simp only [lintegral_const, ← mul_assoc]
    gcongr with θ
    exact Kernel.measure_le_bound P θ Set.univ
  _ = C * κ.bound * P.bound * π Set.univ := by simp

lemma avgRisk_le_mul (P : Kernel Θ 𝓧) [IsMarkovKernel P] (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ]
    (π : Measure Θ) [IsProbabilityMeasure π] {C : ℝ≥0} (hℓC : ∀ θ y, ℓ θ y ≤ C) :
    avgRisk ℓ P κ π ≤ C := by
  refine (avgRisk_le_mul' P κ π hℓC).trans ?_
  rcases isEmpty_or_nonempty Θ
  · simp
  · rcases isEmpty_or_nonempty 𝓧 <;> simp

/-- For a bounded loss, the Bayes risk with respect to a prior is bounded by a constant.
See `bayesRisk_le_mul` for the usual cases where all measures are probability measures. -/
lemma bayesRisk_le_mul' [h𝓨 : Nonempty 𝓨] (P : Kernel Θ 𝓧) (π : Measure Θ)
    {C : ℝ≥0} (hℓC : ∀ θ y, ℓ θ y ≤ C) :
    bayesRisk ℓ P π ≤ C * P.bound * π Set.univ := by
  refine (bayesRisk_le_avgRisk ℓ P (Kernel.const 𝓧 (Measure.dirac h𝓨.some)) π).trans ?_
  refine (avgRisk_le_mul' P (Kernel.const 𝓧 (Measure.dirac h𝓨.some)) π hℓC).trans ?_
  rcases isEmpty_or_nonempty 𝓧 <;> simp

/-- For a bounded loss, the Bayes risk with respect to a prior is bounded by a constant. -/
lemma bayesRisk_le_mul [Nonempty 𝓨] (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (π : Measure Θ) [IsProbabilityMeasure π] {C : ℝ≥0} (hℓC : ∀ θ y, ℓ θ y ≤ C) :
    bayesRisk ℓ P π ≤ C := by
  refine (bayesRisk_le_mul' P π hℓC).trans ?_
  rcases isEmpty_or_nonempty Θ <;> simp

/-- For a bounded loss, the Bayes risk with respect to a prior is finite. -/
lemma bayesRisk_lt_top [Nonempty 𝓨] (P : Kernel Θ 𝓧)
    [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π] {C : ℝ≥0} (hℓC : ∀ θ y, ℓ θ y ≤ C) :
    bayesRisk ℓ P π < ∞ := by
  refine (bayesRisk_le_mul' P π hℓC).trans_lt ?_
  simp [ENNReal.mul_lt_top_iff, P.bound_lt_top]

end Bounds

lemma bayesRisk_discard (hl : Measurable (uncurry ℓ)) (π : Measure Θ) [SFinite π] :
    bayesRisk ℓ (Kernel.discard Θ) π = ⨅ y, ∫⁻ θ, ℓ θ y ∂π := by
  rw [Kernel.discard_eq_const, bayesRisk_const hl]

section Subsingleton

variable [Subsingleton 𝓧] [Nonempty 𝓨]

lemma bayesRisk_eq_iInf_measure_of_subsingleton :
    bayesRisk ℓ P π
      = ⨅ (μ : Measure 𝓨) (_ : IsProbabilityMeasure μ), avgRisk ℓ P (Kernel.const 𝓧 μ) π := by
  rcases isEmpty_or_nonempty 𝓧 with hX | hX
  · simp [iInf_subtype']
  obtain x := hX.some
  rw [bayesRisk, iInf_subtype', iInf_subtype']
  let e : {κ : Kernel 𝓧 𝓨 // IsMarkovKernel κ} ≃ {μ : Measure 𝓨 // IsProbabilityMeasure μ} :=
    { toFun κ := ⟨κ.1 x, κ.2.isProbabilityMeasure x⟩
      invFun μ := ⟨Kernel.const 𝓧 μ, ⟨fun _ ↦ μ.2⟩⟩
      left_inv κ := by ext y; simp only [Kernel.const_apply, Subsingleton.elim x y]
      right_inv μ := by simp }
  rw [← Equiv.iInf_comp e.symm]
  rfl

lemma bayesRisk_of_subsingleton' [SFinite π] (hl : Measurable (uncurry ℓ)) :
    bayesRisk ℓ P π = ⨅ y, ∫⁻ θ, ℓ θ y * P θ .univ ∂π := by
  refine le_antisymm (bayesRisk_le_iInf' hl _ _) ?_
  rw [bayesRisk_eq_iInf_measure_of_subsingleton]
  simp only [avgRisk_const_right', le_iInf_iff]
  refine fun μ hμ ↦ (iInf_le_lintegral (μ := μ) _).trans_eq ?_
  rw [lintegral_lintegral_swap]
  · congr with θ
    rw [lintegral_mul_const _ (by fun_prop), mul_comm]
  · have := P.measurable_coe .univ
    fun_prop

lemma bayesRisk_of_subsingleton [IsMarkovKernel P] [SFinite π] (hl : Measurable (uncurry ℓ)) :
    bayesRisk ℓ P π = ⨅ y, ∫⁻ θ, ℓ θ y ∂π := by
  simp [bayesRisk_of_subsingleton' hl]

end Subsingleton

section Compositions

/-- **Data processing inequality** for the Bayes risk with respect to a prior: composition of the
data generating kernel by a Markov kernel increases the risk. -/
lemma bayesRisk_le_bayesRisk_comp (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    (π : Measure Θ) (η : Kernel 𝓧 𝓧') [IsMarkovKernel η] :
    bayesRisk ℓ P π ≤ bayesRisk ℓ (η ∘ₖ P) π := by
  simp only [bayesRisk, avgRisk, le_iInf_iff]
  intro κ hκ
  rw [← κ.comp_assoc η]
  exact iInf_le_of_le (κ ∘ₖ η) (iInf_le_of_le inferInstance le_rfl)

/-- **Data processing inequality** for the Bayes risk with respect to a prior: taking the map of
the data generating kernel by a function increases the risk. -/
lemma bayesRisk_le_bayesRisk_map (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    (π : Measure Θ) {f : 𝓧 → 𝓧'} (hf : Measurable f) :
    bayesRisk ℓ P π ≤ bayesRisk ℓ (P.map f) π := by
  rw [← Kernel.deterministic_comp_eq_map hf]
  exact bayesRisk_le_bayesRisk_comp _ _ _ _

lemma bayesRisk_compProd_le_bayesRisk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    [IsSFiniteKernel P] (π : Measure Θ) (η : Kernel (Θ × 𝓧) 𝓧') [IsMarkovKernel η] :
    bayesRisk ℓ (P ⊗ₖ η) π ≤ bayesRisk ℓ P π := by
  have : P = (Kernel.deterministic Prod.fst (by fun_prop)) ∘ₖ (P ⊗ₖ η) := by
    rw [Kernel.deterministic_comp_eq_map, ← Kernel.fst_eq, Kernel.fst_compProd]
  nth_rw 2 [this]
  exact bayesRisk_le_bayesRisk_comp _ _ _ _

end Compositions

end ProbabilityTheory
