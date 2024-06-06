/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Integral.Average

#align_import measure_theory.measure.probability_measure from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-!
# Probability measures

This file defines the type of probability measures on a given measurable space. When the underlying
space has a topology and the measurable space structure (sigma algebra) is finer than the Borel
sigma algebra, then the type of probability measures is equipped with the topology of convergence
in distribution (weak convergence of measures). The topology of convergence in distribution is the
coarsest topology w.r.t. which for every bounded continuous `ℝ≥0`-valued random variable `X`, the
expected value of `X` depends continuously on the choice of probability measure. This is a special
case of the topology of weak convergence of finite measures.

## Main definitions

The main definitions are
 * the type `MeasureTheory.ProbabilityMeasure Ω` with the topology of convergence in
   distribution (a.k.a. convergence in law, weak convergence of measures);
 * `MeasureTheory.ProbabilityMeasure.toFiniteMeasure`: Interpret a probability measure as
   a finite measure;
 * `MeasureTheory.FiniteMeasure.normalize`: Normalize a finite measure to a probability measure
   (returns junk for the zero measure).
 * `MeasureTheory.ProbabilityMeasure.map`: The push-forward `f* μ` of a probability measure
   `μ` on `Ω` along a measurable function `f : Ω → Ω'`.

## Main results

 * `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`: Convergence of
   probability measures is characterized by the convergence of expected values of all bounded
   continuous random variables. This shows that the chosen definition of topology coincides with
   the common textbook definition of convergence in distribution, i.e., weak convergence of
   measures. A similar characterization by the convergence of expected values (in the
   `MeasureTheory.lintegral` sense) of all bounded continuous nonnegative random variables is
   `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto`.
 * `MeasureTheory.FiniteMeasure.tendsto_normalize_iff_tendsto`: The convergence of finite
   measures to a nonzero limit is characterized by the convergence of the probability-normalized
   versions and of the total masses.
 * `MeasureTheory.ProbabilityMeasure.continuous_map`: For a continuous function `f : Ω → Ω'`, the
   push-forward of probability measures `f* : ProbabilityMeasure Ω → ProbabilityMeasure Ω'` is
   continuous.
 * `MeasureTheory.ProbabilityMeasure.t2Space`: The topology of convergence in distribution is
   Hausdorff on Borel spaces where indicators of closed sets have continuous decreasing
   approximating sequences (in particular on any pseudo-metrizable spaces).

TODO:
 * Probability measures form a convex space.

## Implementation notes

The topology of convergence in distribution on `MeasureTheory.ProbabilityMeasure Ω` is inherited
weak convergence of finite measures via the mapping
`MeasureTheory.ProbabilityMeasure.toFiniteMeasure`.

Like `MeasureTheory.FiniteMeasure Ω`, the implementation of `MeasureTheory.ProbabilityMeasure Ω`
is directly as a subtype of `MeasureTheory.Measure Ω`, and the coercion to a function is the
composition `ENNReal.toNNReal` and the coercion to function of `MeasureTheory.Measure Ω`.

## References

* [Billingsley, *Convergence of probability measures*][billingsley1999]

## Tags

convergence in distribution, convergence in law, weak convergence of measures, probability measure

-/


noncomputable section

open MeasureTheory

open Set

open Filter

open BoundedContinuousFunction

open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace MeasureTheory

section ProbabilityMeasure

/-! ### Probability measures

In this section we define the type of probability measures on a measurable space `Ω`, denoted by
`MeasureTheory.ProbabilityMeasure Ω`.

If `Ω` is moreover a topological space and the sigma algebra on `Ω` is finer than the Borel sigma
algebra (i.e. `[OpensMeasurableSpace Ω]`), then `MeasureTheory.ProbabilityMeasure Ω` is
equipped with the topology of weak convergence of measures. Since every probability measure is a
finite measure, this is implemented as the induced topology from the mapping
`MeasureTheory.ProbabilityMeasure.toFiniteMeasure`.
-/


/-- Probability measures are defined as the subtype of measures that have the property of being
probability measures (i.e., their total mass is one). -/
def ProbabilityMeasure (Ω : Type*) [MeasurableSpace Ω] : Type _ :=
  { μ : Measure Ω // IsProbabilityMeasure μ }
#align measure_theory.probability_measure MeasureTheory.ProbabilityMeasure

namespace ProbabilityMeasure

variable {Ω : Type*} [MeasurableSpace Ω]

instance [Inhabited Ω] : Inhabited (ProbabilityMeasure Ω) :=
  ⟨⟨Measure.dirac default, Measure.dirac.isProbabilityMeasure⟩⟩

-- Porting note: as with other subtype synonyms (e.g., `ℝ≥0`), we need a new function for the
-- coercion instead of relying on `Subtype.val`.
/-- Coercion from `MeasureTheory.ProbabilityMeasure Ω` to `MeasureTheory.Measure Ω`. -/
@[coe]
def toMeasure : ProbabilityMeasure Ω → Measure Ω := Subtype.val

/-- A probability measure can be interpreted as a measure. -/
instance : Coe (ProbabilityMeasure Ω) (MeasureTheory.Measure Ω) where
  coe := toMeasure

instance (μ : ProbabilityMeasure Ω) : IsProbabilityMeasure (μ : Measure Ω) :=
  μ.prop

@[simp, norm_cast] lemma coe_mk (μ : Measure Ω) (hμ) : toMeasure ⟨μ, hμ⟩ = μ := rfl

@[simp]
theorem val_eq_to_measure (ν : ProbabilityMeasure Ω) : ν.val = (ν : Measure Ω) :=
  rfl
#align measure_theory.probability_measure.val_eq_to_measure MeasureTheory.ProbabilityMeasure.val_eq_to_measure

theorem toMeasure_injective : Function.Injective ((↑) : ProbabilityMeasure Ω → Measure Ω) :=
  Subtype.coe_injective
#align measure_theory.probability_measure.coe_injective MeasureTheory.ProbabilityMeasure.toMeasure_injective

instance instFunLike : FunLike (ProbabilityMeasure Ω) (Set Ω) ℝ≥0 where
  coe μ s := ((μ : Measure Ω) s).toNNReal
  coe_injective' μ ν h := toMeasure_injective $ Measure.ext fun s _ ↦ by
    simpa [ENNReal.toNNReal_eq_toNNReal_iff, measure_ne_top] using congr_fun h s

lemma coeFn_def (μ : ProbabilityMeasure Ω) : μ = fun s ↦ ((μ : Measure Ω) s).toNNReal := rfl
#align measure_theory.probability_measure.coe_fn_eq_to_nnreal_coe_fn_to_measure MeasureTheory.ProbabilityMeasure.coeFn_def

lemma coeFn_mk (μ : Measure Ω) (hμ) :
    DFunLike.coe (F := ProbabilityMeasure Ω) ⟨μ, hμ⟩ = fun s ↦ (μ s).toNNReal := rfl

@[simp, norm_cast]
lemma mk_apply (μ : Measure Ω) (hμ) (s : Set Ω) :
    DFunLike.coe (F := ProbabilityMeasure Ω) ⟨μ, hμ⟩ s = (μ s).toNNReal := rfl

@[simp, norm_cast]
theorem coeFn_univ (ν : ProbabilityMeasure Ω) : ν univ = 1 :=
  congr_arg ENNReal.toNNReal ν.prop.measure_univ
#align measure_theory.probability_measure.coe_fn_univ MeasureTheory.ProbabilityMeasure.coeFn_univ

theorem coeFn_univ_ne_zero (ν : ProbabilityMeasure Ω) : ν univ ≠ 0 := by
  simp only [coeFn_univ, Ne, one_ne_zero, not_false_iff]
#align measure_theory.probability_measure.coe_fn_univ_ne_zero MeasureTheory.ProbabilityMeasure.coeFn_univ_ne_zero

/-- A probability measure can be interpreted as a finite measure. -/
def toFiniteMeasure (μ : ProbabilityMeasure Ω) : FiniteMeasure Ω :=
  ⟨μ, inferInstance⟩
#align measure_theory.probability_measure.to_finite_measure MeasureTheory.ProbabilityMeasure.toFiniteMeasure

@[simp] lemma coeFn_toFiniteMeasure (μ : ProbabilityMeasure Ω) : ⇑μ.toFiniteMeasure = μ := rfl
lemma toFiniteMeasure_apply (μ : ProbabilityMeasure Ω) (s : Set Ω) :
    μ.toFiniteMeasure s = μ s := rfl

@[simp]
theorem toMeasure_comp_toFiniteMeasure_eq_toMeasure (ν : ProbabilityMeasure Ω) :
    (ν.toFiniteMeasure : Measure Ω) = (ν : Measure Ω) :=
  rfl
#align measure_theory.probability_measure.coe_comp_to_finite_measure_eq_coe MeasureTheory.ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure

@[simp]
theorem coeFn_comp_toFiniteMeasure_eq_coeFn (ν : ProbabilityMeasure Ω) :
    (ν.toFiniteMeasure : Set Ω → ℝ≥0) = (ν : Set Ω → ℝ≥0) :=
  rfl
#align measure_theory.probability_measure.coe_fn_comp_to_finite_measure_eq_coe_fn MeasureTheory.ProbabilityMeasure.coeFn_comp_toFiniteMeasure_eq_coeFn

@[simp]
theorem toFiniteMeasure_apply_eq_apply (ν : ProbabilityMeasure Ω) (s : Set Ω) :
    ν.toFiniteMeasure s = ν s := rfl

@[simp]
theorem ennreal_coeFn_eq_coeFn_toMeasure (ν : ProbabilityMeasure Ω) (s : Set Ω) :
    (ν s : ℝ≥0∞) = (ν : Measure Ω) s := by
  rw [← coeFn_comp_toFiniteMeasure_eq_coeFn, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    toMeasure_comp_toFiniteMeasure_eq_toMeasure]
#align measure_theory.probability_measure.ennreal_coe_fn_eq_coe_fn_to_measure MeasureTheory.ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure

theorem apply_mono (μ : ProbabilityMeasure Ω) {s₁ s₂ : Set Ω} (h : s₁ ⊆ s₂) : μ s₁ ≤ μ s₂ := by
  rw [← coeFn_comp_toFiniteMeasure_eq_coeFn]
  exact MeasureTheory.FiniteMeasure.apply_mono _ h
#align measure_theory.probability_measure.apply_mono MeasureTheory.ProbabilityMeasure.apply_mono

@[simp] theorem apply_le_one (μ : ProbabilityMeasure Ω) (s : Set Ω) : μ s ≤ 1 := by
  simpa using apply_mono μ (subset_univ s)

theorem nonempty (μ : ProbabilityMeasure Ω) : Nonempty Ω := by
  by_contra maybe_empty
  have zero : (μ : Measure Ω) univ = 0 := by
    rw [univ_eq_empty_iff.mpr (not_nonempty_iff.mp maybe_empty), measure_empty]
  rw [measure_univ] at zero
  exact zero_ne_one zero.symm
#align measure_theory.probability_measure.nonempty_of_probability_measure MeasureTheory.ProbabilityMeasure.nonempty

@[ext]
theorem eq_of_forall_toMeasure_apply_eq (μ ν : ProbabilityMeasure Ω)
    (h : ∀ s : Set Ω, MeasurableSet s → (μ : Measure Ω) s = (ν : Measure Ω) s) : μ = ν := by
  apply toMeasure_injective
  ext1 s s_mble
  exact h s s_mble
#align measure_theory.probability_measure.eq_of_forall_measure_apply_eq MeasureTheory.ProbabilityMeasure.eq_of_forall_toMeasure_apply_eq

theorem eq_of_forall_apply_eq (μ ν : ProbabilityMeasure Ω)
    (h : ∀ s : Set Ω, MeasurableSet s → μ s = ν s) : μ = ν := by
  ext1 s s_mble
  simpa [ennreal_coeFn_eq_coeFn_toMeasure] using congr_arg ((↑) : ℝ≥0 → ℝ≥0∞) (h s s_mble)
#align measure_theory.probability_measure.eq_of_forall_apply_eq MeasureTheory.ProbabilityMeasure.eq_of_forall_apply_eq

@[simp]
theorem mass_toFiniteMeasure (μ : ProbabilityMeasure Ω) : μ.toFiniteMeasure.mass = 1 :=
  μ.coeFn_univ
#align measure_theory.probability_measure.mass_to_finite_measure MeasureTheory.ProbabilityMeasure.mass_toFiniteMeasure

theorem toFiniteMeasure_nonzero (μ : ProbabilityMeasure Ω) : μ.toFiniteMeasure ≠ 0 := by
  rw [← FiniteMeasure.mass_nonzero_iff, μ.mass_toFiniteMeasure]
  exact one_ne_zero
#align measure_theory.probability_measure.to_finite_measure_nonzero MeasureTheory.ProbabilityMeasure.toFiniteMeasure_nonzero

section convergence_in_distribution

variable [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

theorem testAgainstNN_lipschitz (μ : ProbabilityMeasure Ω) :
    LipschitzWith 1 fun f : Ω →ᵇ ℝ≥0 => μ.toFiniteMeasure.testAgainstNN f :=
  μ.mass_toFiniteMeasure ▸ μ.toFiniteMeasure.testAgainstNN_lipschitz
#align measure_theory.probability_measure.test_against_nn_lipschitz MeasureTheory.ProbabilityMeasure.testAgainstNN_lipschitz

/-- The topology of weak convergence on `MeasureTheory.ProbabilityMeasure Ω`. This is inherited
(induced) from the topology of weak convergence of finite measures via the inclusion
`MeasureTheory.ProbabilityMeasure.toFiniteMeasure`. -/
instance : TopologicalSpace (ProbabilityMeasure Ω) :=
  TopologicalSpace.induced toFiniteMeasure inferInstance

theorem toFiniteMeasure_continuous :
    Continuous (toFiniteMeasure : ProbabilityMeasure Ω → FiniteMeasure Ω) :=
  continuous_induced_dom
#align measure_theory.probability_measure.to_finite_measure_continuous MeasureTheory.ProbabilityMeasure.toFiniteMeasure_continuous

/-- Probability measures yield elements of the `WeakDual` of bounded continuous nonnegative
functions via `MeasureTheory.FiniteMeasure.testAgainstNN`, i.e., integration. -/
def toWeakDualBCNN : ProbabilityMeasure Ω → WeakDual ℝ≥0 (Ω →ᵇ ℝ≥0) :=
  FiniteMeasure.toWeakDualBCNN ∘ toFiniteMeasure
#align measure_theory.probability_measure.to_weak_dual_bcnn MeasureTheory.ProbabilityMeasure.toWeakDualBCNN

@[simp]
theorem coe_toWeakDualBCNN (μ : ProbabilityMeasure Ω) :
    ⇑μ.toWeakDualBCNN = μ.toFiniteMeasure.testAgainstNN :=
  rfl
#align measure_theory.probability_measure.coe_to_weak_dual_bcnn MeasureTheory.ProbabilityMeasure.coe_toWeakDualBCNN

@[simp]
theorem toWeakDualBCNN_apply (μ : ProbabilityMeasure Ω) (f : Ω →ᵇ ℝ≥0) :
    μ.toWeakDualBCNN f = (∫⁻ ω, f ω ∂(μ : Measure Ω)).toNNReal :=
  rfl
#align measure_theory.probability_measure.to_weak_dual_bcnn_apply MeasureTheory.ProbabilityMeasure.toWeakDualBCNN_apply

theorem toWeakDualBCNN_continuous : Continuous fun μ : ProbabilityMeasure Ω => μ.toWeakDualBCNN :=
  FiniteMeasure.toWeakDualBCNN_continuous.comp toFiniteMeasure_continuous
#align measure_theory.probability_measure.to_weak_dual_bcnn_continuous MeasureTheory.ProbabilityMeasure.toWeakDualBCNN_continuous

/- Integration of (nonnegative bounded continuous) test functions against Borel probability
measures depends continuously on the measure. -/
theorem continuous_testAgainstNN_eval (f : Ω →ᵇ ℝ≥0) :
    Continuous fun μ : ProbabilityMeasure Ω => μ.toFiniteMeasure.testAgainstNN f :=
  (FiniteMeasure.continuous_testAgainstNN_eval f).comp toFiniteMeasure_continuous
#align measure_theory.probability_measure.continuous_test_against_nn_eval MeasureTheory.ProbabilityMeasure.continuous_testAgainstNN_eval

-- The canonical mapping from probability measures to finite measures is an embedding.
theorem toFiniteMeasure_embedding (Ω : Type*) [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] :
    Embedding (toFiniteMeasure : ProbabilityMeasure Ω → FiniteMeasure Ω) :=
  { induced := rfl
    inj := fun _μ _ν h => Subtype.eq <| congr_arg FiniteMeasure.toMeasure h }
#align measure_theory.probability_measure.to_finite_measure_embedding MeasureTheory.ProbabilityMeasure.toFiniteMeasure_embedding

theorem tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds {δ : Type*} (F : Filter δ)
    {μs : δ → ProbabilityMeasure Ω} {μ₀ : ProbabilityMeasure Ω} :
    Tendsto μs F (𝓝 μ₀) ↔ Tendsto (toFiniteMeasure ∘ μs) F (𝓝 μ₀.toFiniteMeasure) :=
  Embedding.tendsto_nhds_iff (toFiniteMeasure_embedding Ω)
#align measure_theory.probability_measure.tendsto_nhds_iff_to_finite_measures_tendsto_nhds MeasureTheory.ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds

/-- A characterization of weak convergence of probability measures by the condition that the
integrals of every continuous bounded nonnegative function converge to the integral of the function
against the limit measure. -/
theorem tendsto_iff_forall_lintegral_tendsto {γ : Type*} {F : Filter γ}
    {μs : γ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : Ω →ᵇ ℝ≥0,
        Tendsto (fun i => ∫⁻ ω, f ω ∂(μs i : Measure Ω)) F (𝓝 (∫⁻ ω, f ω ∂(μ : Measure Ω))) := by
  rw [tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds]
  exact FiniteMeasure.tendsto_iff_forall_lintegral_tendsto
#align measure_theory.probability_measure.tendsto_iff_forall_lintegral_tendsto MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto

/-- The characterization of weak convergence of probability measures by the usual (defining)
condition that the integrals of every continuous bounded function converge to the integral of the
function against the limit measure. -/
theorem tendsto_iff_forall_integral_tendsto {γ : Type*} {F : Filter γ}
    {μs : γ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : Ω →ᵇ ℝ,
        Tendsto (fun i => ∫ ω, f ω ∂(μs i : Measure Ω)) F (𝓝 (∫ ω, f ω ∂(μ : Measure Ω))) := by
  rw [tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds]
  rw [FiniteMeasure.tendsto_iff_forall_integral_tendsto]
  rfl
#align measure_theory.probability_measure.tendsto_iff_forall_integral_tendsto MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto

end convergence_in_distribution -- section

section Hausdorff

variable [TopologicalSpace Ω] [HasOuterApproxClosed Ω] [BorelSpace Ω]
variable (Ω)

/-- On topological spaces where indicators of closed sets have decreasing approximating sequences of
continuous functions (`HasOuterApproxClosed`), the topology of convergence in distribution of Borel
probability measures is Hausdorff (`T2Space`). -/
instance t2Space : T2Space (ProbabilityMeasure Ω) :=
  Embedding.t2Space (toFiniteMeasure_embedding Ω)

end Hausdorff -- section

end ProbabilityMeasure

-- namespace
end ProbabilityMeasure

-- section
section NormalizeFiniteMeasure

/-! ### Normalization of finite measures to probability measures

This section is about normalizing finite measures to probability measures.

The weak convergence of finite measures to nonzero limit measures is characterized by
the convergence of the total mass and the convergence of the normalized probability
measures.
-/

namespace FiniteMeasure

variable {Ω : Type*} [Nonempty Ω] {m0 : MeasurableSpace Ω} (μ : FiniteMeasure Ω)

/-- Normalize a finite measure so that it becomes a probability measure, i.e., divide by the
total mass. -/
def normalize : ProbabilityMeasure Ω :=
  if zero : μ.mass = 0 then ⟨Measure.dirac ‹Nonempty Ω›.some, Measure.dirac.isProbabilityMeasure⟩
  else
    { val := μ.mass⁻¹ • (μ : Measure Ω)
      property := by
        refine ⟨?_⟩
        simp only [mass, Measure.coe_nnreal_smul_apply,
                    ← ennreal_coeFn_eq_coeFn_toMeasure μ univ]
        norm_cast
        exact inv_mul_cancel zero }
#align measure_theory.finite_measure.normalize MeasureTheory.FiniteMeasure.normalize

@[simp]
theorem self_eq_mass_mul_normalize (s : Set Ω) : μ s = μ.mass * μ.normalize s := by
  obtain rfl | h := eq_or_ne μ 0
  · simp
  have mass_nonzero : μ.mass ≠ 0 := by rwa [μ.mass_nonzero_iff]
  simp only [normalize, dif_neg mass_nonzero]
  simp [ProbabilityMeasure.coe_mk, toMeasure_smul, mul_inv_cancel_left₀ mass_nonzero, coeFn_def]
#align measure_theory.finite_measure.self_eq_mass_mul_normalize MeasureTheory.FiniteMeasure.self_eq_mass_mul_normalize

theorem self_eq_mass_smul_normalize : μ = μ.mass • μ.normalize.toFiniteMeasure := by
  apply eq_of_forall_apply_eq
  intro s _s_mble
  rw [μ.self_eq_mass_mul_normalize s, smul_apply, smul_eq_mul,
    ProbabilityMeasure.coeFn_comp_toFiniteMeasure_eq_coeFn]
#align measure_theory.finite_measure.self_eq_mass_smul_normalize MeasureTheory.FiniteMeasure.self_eq_mass_smul_normalize

theorem normalize_eq_of_nonzero (nonzero : μ ≠ 0) (s : Set Ω) : μ.normalize s = μ.mass⁻¹ * μ s := by
  simp only [μ.self_eq_mass_mul_normalize, μ.mass_nonzero_iff.mpr nonzero, inv_mul_cancel_left₀,
    Ne, not_false_iff]
#align measure_theory.finite_measure.normalize_eq_of_nonzero MeasureTheory.FiniteMeasure.normalize_eq_of_nonzero

theorem normalize_eq_inv_mass_smul_of_nonzero (nonzero : μ ≠ 0) :
    μ.normalize.toFiniteMeasure = μ.mass⁻¹ • μ := by
  nth_rw 3 [μ.self_eq_mass_smul_normalize]
  rw [← smul_assoc]
  simp only [μ.mass_nonzero_iff.mpr nonzero, Algebra.id.smul_eq_mul, inv_mul_cancel, Ne,
    not_false_iff, one_smul]
#align measure_theory.finite_measure.normalize_eq_inv_mass_smul_of_nonzero MeasureTheory.FiniteMeasure.normalize_eq_inv_mass_smul_of_nonzero

theorem toMeasure_normalize_eq_of_nonzero (nonzero : μ ≠ 0) :
    (μ.normalize : Measure Ω) = μ.mass⁻¹ • μ := by
  ext1 s _s_mble
  rw [← μ.normalize.ennreal_coeFn_eq_coeFn_toMeasure s, μ.normalize_eq_of_nonzero nonzero s,
    ENNReal.coe_mul, ennreal_coeFn_eq_coeFn_toMeasure]
  exact Measure.coe_nnreal_smul_apply _ _ _
#align measure_theory.finite_measure.coe_normalize_eq_of_nonzero MeasureTheory.FiniteMeasure.toMeasure_normalize_eq_of_nonzero

@[simp]
theorem _root_.ProbabilityMeasure.toFiniteMeasure_normalize_eq_self {m0 : MeasurableSpace Ω}
    (μ : ProbabilityMeasure Ω) : μ.toFiniteMeasure.normalize = μ := by
  apply ProbabilityMeasure.eq_of_forall_apply_eq
  intro s _s_mble
  rw [μ.toFiniteMeasure.normalize_eq_of_nonzero μ.toFiniteMeasure_nonzero s]
  simp only [ProbabilityMeasure.mass_toFiniteMeasure, inv_one, one_mul, μ.coeFn_toFiniteMeasure]
#align probability_measure.to_finite_measure_normalize_eq_self ProbabilityMeasure.toFiniteMeasure_normalize_eq_self

/-- Averaging with respect to a finite measure is the same as integrating against
`MeasureTheory.FiniteMeasure.normalize`. -/
theorem average_eq_integral_normalize {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (nonzero : μ ≠ 0) (f : Ω → E) :
    average (μ : Measure Ω) f = ∫ ω, f ω ∂(μ.normalize : Measure Ω) := by
  rw [μ.toMeasure_normalize_eq_of_nonzero nonzero, average]
  congr
  simp [ENNReal.coe_inv (μ.mass_nonzero_iff.mpr nonzero), ennreal_mass]
#align measure_theory.finite_measure.average_eq_integral_normalize MeasureTheory.FiniteMeasure.average_eq_integral_normalize

variable [TopologicalSpace Ω]

theorem testAgainstNN_eq_mass_mul (f : Ω →ᵇ ℝ≥0) :
    μ.testAgainstNN f = μ.mass * μ.normalize.toFiniteMeasure.testAgainstNN f := by
  nth_rw 1 [μ.self_eq_mass_smul_normalize]
  rw [μ.normalize.toFiniteMeasure.smul_testAgainstNN_apply μ.mass f, smul_eq_mul]
#align measure_theory.finite_measure.test_against_nn_eq_mass_mul MeasureTheory.FiniteMeasure.testAgainstNN_eq_mass_mul

theorem normalize_testAgainstNN (nonzero : μ ≠ 0) (f : Ω →ᵇ ℝ≥0) :
    μ.normalize.toFiniteMeasure.testAgainstNN f = μ.mass⁻¹ * μ.testAgainstNN f := by
  simp [μ.testAgainstNN_eq_mass_mul, inv_mul_cancel_left₀ <| μ.mass_nonzero_iff.mpr nonzero]
#align measure_theory.finite_measure.normalize_test_against_nn MeasureTheory.FiniteMeasure.normalize_testAgainstNN

variable [OpensMeasurableSpace Ω]
variable {μ}

theorem tendsto_testAgainstNN_of_tendsto_normalize_testAgainstNN_of_tendsto_mass {γ : Type*}
    {F : Filter γ} {μs : γ → FiniteMeasure Ω}
    (μs_lim : Tendsto (fun i => (μs i).normalize) F (𝓝 μ.normalize))
    (mass_lim : Tendsto (fun i => (μs i).mass) F (𝓝 μ.mass)) (f : Ω →ᵇ ℝ≥0) :
    Tendsto (fun i => (μs i).testAgainstNN f) F (𝓝 (μ.testAgainstNN f)) := by
  by_cases h_mass : μ.mass = 0
  · simp only [μ.mass_zero_iff.mp h_mass, zero_testAgainstNN_apply, zero_mass,
      eq_self_iff_true] at *
    exact tendsto_zero_testAgainstNN_of_tendsto_zero_mass mass_lim f
  simp_rw [fun i => (μs i).testAgainstNN_eq_mass_mul f, μ.testAgainstNN_eq_mass_mul f]
  rw [ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds] at μs_lim
  rw [tendsto_iff_forall_testAgainstNN_tendsto] at μs_lim
  have lim_pair :
    Tendsto (fun i => (⟨(μs i).mass, (μs i).normalize.toFiniteMeasure.testAgainstNN f⟩ : ℝ≥0 × ℝ≥0))
      F (𝓝 ⟨μ.mass, μ.normalize.toFiniteMeasure.testAgainstNN f⟩) :=
    (Prod.tendsto_iff _ _).mpr ⟨mass_lim, μs_lim f⟩
  exact tendsto_mul.comp lim_pair
#align measure_theory.finite_measure.tendsto_test_against_nn_of_tendsto_normalize_test_against_nn_of_tendsto_mass MeasureTheory.FiniteMeasure.tendsto_testAgainstNN_of_tendsto_normalize_testAgainstNN_of_tendsto_mass

theorem tendsto_normalize_testAgainstNN_of_tendsto {γ : Type*} {F : Filter γ}
    {μs : γ → FiniteMeasure Ω} (μs_lim : Tendsto μs F (𝓝 μ)) (nonzero : μ ≠ 0) (f : Ω →ᵇ ℝ≥0) :
    Tendsto (fun i => (μs i).normalize.toFiniteMeasure.testAgainstNN f) F
      (𝓝 (μ.normalize.toFiniteMeasure.testAgainstNN f)) := by
  have lim_mass := μs_lim.mass
  have aux : {(0 : ℝ≥0)}ᶜ ∈ 𝓝 μ.mass :=
    isOpen_compl_singleton.mem_nhds (μ.mass_nonzero_iff.mpr nonzero)
  have eventually_nonzero : ∀ᶠ i in F, μs i ≠ 0 := by
    simp_rw [← mass_nonzero_iff]
    exact lim_mass aux
  have eve : ∀ᶠ i in F,
      (μs i).normalize.toFiniteMeasure.testAgainstNN f =
        (μs i).mass⁻¹ * (μs i).testAgainstNN f := by
    filter_upwards [eventually_iff.mp eventually_nonzero]
    intro i hi
    apply normalize_testAgainstNN _ hi
  simp_rw [tendsto_congr' eve, μ.normalize_testAgainstNN nonzero]
  have lim_pair :
    Tendsto (fun i => (⟨(μs i).mass⁻¹, (μs i).testAgainstNN f⟩ : ℝ≥0 × ℝ≥0)) F
      (𝓝 ⟨μ.mass⁻¹, μ.testAgainstNN f⟩) := by
    refine (Prod.tendsto_iff _ _).mpr ⟨?_, ?_⟩
    · exact (continuousOn_inv₀.continuousAt aux).tendsto.comp lim_mass
    · exact tendsto_iff_forall_testAgainstNN_tendsto.mp μs_lim f
  exact tendsto_mul.comp lim_pair
#align measure_theory.finite_measure.tendsto_normalize_test_against_nn_of_tendsto MeasureTheory.FiniteMeasure.tendsto_normalize_testAgainstNN_of_tendsto

/-- If the normalized versions of finite measures converge weakly and their total masses
also converge, then the finite measures themselves converge weakly. -/
theorem tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass {γ : Type*} {F : Filter γ}
    {μs : γ → FiniteMeasure Ω} (μs_lim : Tendsto (fun i => (μs i).normalize) F (𝓝 μ.normalize))
    (mass_lim : Tendsto (fun i => (μs i).mass) F (𝓝 μ.mass)) : Tendsto μs F (𝓝 μ) := by
  rw [tendsto_iff_forall_testAgainstNN_tendsto]
  exact fun f =>
    tendsto_testAgainstNN_of_tendsto_normalize_testAgainstNN_of_tendsto_mass μs_lim mass_lim f
#align measure_theory.finite_measure.tendsto_of_tendsto_normalize_test_against_nn_of_tendsto_mass MeasureTheory.FiniteMeasure.tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass

/-- If finite measures themselves converge weakly to a nonzero limit measure, then their
normalized versions also converge weakly. -/
theorem tendsto_normalize_of_tendsto {γ : Type*} {F : Filter γ} {μs : γ → FiniteMeasure Ω}
    (μs_lim : Tendsto μs F (𝓝 μ)) (nonzero : μ ≠ 0) :
    Tendsto (fun i => (μs i).normalize) F (𝓝 μ.normalize) := by
  rw [ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds,
    tendsto_iff_forall_testAgainstNN_tendsto]
  exact fun f => tendsto_normalize_testAgainstNN_of_tendsto μs_lim nonzero f
#align measure_theory.finite_measure.tendsto_normalize_of_tendsto MeasureTheory.FiniteMeasure.tendsto_normalize_of_tendsto

/-- The weak convergence of finite measures to a nonzero limit can be characterized by the weak
convergence of both their normalized versions (probability measures) and their total masses. -/
theorem tendsto_normalize_iff_tendsto {γ : Type*} {F : Filter γ} {μs : γ → FiniteMeasure Ω}
    (nonzero : μ ≠ 0) :
    Tendsto (fun i => (μs i).normalize) F (𝓝 μ.normalize) ∧
        Tendsto (fun i => (μs i).mass) F (𝓝 μ.mass) ↔
      Tendsto μs F (𝓝 μ) := by
  constructor
  · rintro ⟨normalized_lim, mass_lim⟩
    exact tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass normalized_lim mass_lim
  · intro μs_lim
    exact ⟨tendsto_normalize_of_tendsto μs_lim nonzero, μs_lim.mass⟩
#align measure_theory.finite_measure.tendsto_normalize_iff_tendsto MeasureTheory.FiniteMeasure.tendsto_normalize_iff_tendsto

end FiniteMeasure --namespace

end NormalizeFiniteMeasure -- section

section map

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

namespace ProbabilityMeasure

/-- The push-forward of a probability measure by a measurable function. -/
noncomputable def map (ν : ProbabilityMeasure Ω) {f : Ω → Ω'} (f_aemble : AEMeasurable f ν) :
    ProbabilityMeasure Ω' :=
  ⟨(ν : Measure Ω).map f,
   ⟨by simp only [Measure.map_apply_of_aemeasurable f_aemble MeasurableSet.univ,
                  preimage_univ, measure_univ]⟩⟩

@[simp] lemma toMeasure_map (ν : ProbabilityMeasure Ω) {f : Ω → Ω'} (hf : AEMeasurable f ν) :
    (ν.map hf).toMeasure = ν.toMeasure.map f := rfl

/-- Note that this is an equality of elements of `ℝ≥0∞`. See also
`MeasureTheory.ProbabilityMeasure.map_apply` for the corresponding equality as elements of `ℝ≥0`. -/
lemma map_apply' (ν : ProbabilityMeasure Ω) {f : Ω → Ω'} (f_aemble : AEMeasurable f ν)
    {A : Set Ω'} (A_mble : MeasurableSet A) :
    (ν.map f_aemble : Measure Ω') A = (ν : Measure Ω) (f ⁻¹' A) :=
  Measure.map_apply_of_aemeasurable f_aemble A_mble

lemma map_apply_of_aemeasurable (ν : ProbabilityMeasure Ω) {f : Ω → Ω'}
    (f_aemble : AEMeasurable f ν) {A : Set Ω'} (A_mble : MeasurableSet A) :
    (ν.map f_aemble) A = ν (f ⁻¹' A) := by
  have := ν.map_apply' f_aemble A_mble
  exact (ENNReal.toNNReal_eq_toNNReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mpr this

lemma map_apply (ν : ProbabilityMeasure Ω) {f : Ω → Ω'} (f_aemble : AEMeasurable f ν)
    {A : Set Ω'} (A_mble : MeasurableSet A) :
    (ν.map f_aemble) A = ν (f ⁻¹' A) :=
  map_apply_of_aemeasurable ν f_aemble A_mble

variable [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
variable [TopologicalSpace Ω'] [BorelSpace Ω']

/-- If `f : X → Y` is continuous and `Y` is equipped with the Borel sigma algebra, then
convergence (in distribution) of `ProbabilityMeasure`s on `X` implies convergence (in
distribution) of the push-forwards of these measures by `f`. -/
lemma tendsto_map_of_tendsto_of_continuous {ι : Type*} {L : Filter ι}
    (νs : ι → ProbabilityMeasure Ω) (ν : ProbabilityMeasure Ω) (lim : Tendsto νs L (𝓝 ν))
    {f : Ω → Ω'} (f_cont : Continuous f) :
    Tendsto (fun i ↦ (νs i).map f_cont.measurable.aemeasurable) L
      (𝓝 (ν.map f_cont.measurable.aemeasurable)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto] at lim ⊢
  intro g
  convert lim (g.compContinuous ⟨f, f_cont⟩) <;>
  · simp only [map, compContinuous_apply, ContinuousMap.coe_mk]
    refine lintegral_map ?_ f_cont.measurable
    exact (ENNReal.continuous_coe.comp g.continuous).measurable

/-- If `f : X → Y` is continuous and `Y` is equipped with the Borel sigma algebra, then
the push-forward of probability measures `f* : ProbabilityMeasure X → ProbabilityMeasure Y`
is continuous (in the topologies of convergence in distribution). -/
lemma continuous_map {f : Ω → Ω'} (f_cont : Continuous f) :
    Continuous (fun ν ↦ ProbabilityMeasure.map ν f_cont.measurable.aemeasurable) := by
  rw [continuous_iff_continuousAt]
  exact fun _ ↦ tendsto_map_of_tendsto_of_continuous _ _ continuous_id.continuousAt f_cont

end ProbabilityMeasure -- namespace

end map -- section

end MeasureTheory -- namespace
