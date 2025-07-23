/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Probability.Decision.BoolMeasure
import Mathlib.Probability.Decision.Risk

/-!
# Kernel with two values

-/

open MeasureTheory

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Θ 𝓧 𝓧' 𝓨 𝓩 : Type*} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧}
  {m𝓧' : MeasurableSpace 𝓧'} {m𝓨 : MeasurableSpace 𝓨} {m𝓩 : MeasurableSpace 𝓩}
  {μ ν : Measure 𝓧} {p : ℝ≥0∞}

/-- The kernel that sends `false` to `μ` and `true` to `ν`. -/
def boolKernel (μ ν : Measure 𝓧) : Kernel Bool 𝓧 where
  toFun := fun b ↦ if b then ν else μ
  measurable' := .of_discrete

@[simp] lemma boolKernel_true : boolKernel μ ν true = ν := rfl

@[simp] lemma boolKernel_false : boolKernel μ ν false = μ := rfl

@[simp] lemma boolKernel_apply (b : Bool) : boolKernel μ ν b = if b then ν else μ := rfl

instance [IsFiniteMeasure μ] [IsFiniteMeasure ν] : IsFiniteKernel (boolKernel μ ν) :=
  ⟨max (μ .univ) (ν .univ), max_lt (measure_lt_top _ _) (measure_lt_top _ _),
    fun b ↦ by cases b <;> simp⟩

instance [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsMarkovKernel (boolKernel μ ν) := by
  refine ⟨fun b ↦ ?_⟩
  simp only [boolKernel_apply]
  split <;> infer_instance

lemma Kernel_bool_eq_boolKernel (κ : Kernel Bool 𝓧) :
    κ = boolKernel (κ false) (κ true) := by
  ext (_ | _) <;> simp

@[simp]
lemma comp_boolKernel (κ : Kernel 𝓧 𝓨) :
    κ ∘ₖ (boolKernel μ ν) = boolKernel (κ ∘ₘ μ) (κ ∘ₘ ν) := by
  ext b : 1
  rw [Kernel.comp_apply]
  cases b with
  | false => simp
  | true => simp

lemma measure_comp_boolKernel (μ ν : Measure 𝓧) (π : Measure Bool) :
    boolKernel μ ν ∘ₘ π = π {true} • ν + π {false} • μ := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp only [boolKernel_apply, lintegral_fintype, Fintype.univ_bool, Finset.mem_singleton,
    Bool.true_eq_false, not_false_eq_true, Finset.sum_insert, ↓reduceIte, Finset.sum_singleton,
    Bool.false_eq_true, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  congr 1 <;> rw [mul_comm]

lemma absolutelyContinuous_measure_comp_boolKernel_left (μ ν : Measure 𝓧)
    {π : Measure Bool} (hπ : π {false} ≠ 0) :
    μ ≪ boolKernel μ ν ∘ₘ π :=
  measure_comp_boolKernel _ _ _ ▸ add_comm _ (π {true} • ν) ▸
    (Measure.absolutelyContinuous_smul hπ).add_right _

lemma absolutelyContinuous_measure_comp_boolKernel_right (μ ν : Measure 𝓧)
    {π : Measure Bool} (hπ : π {true} ≠ 0) :
    ν ≪ boolKernel μ ν ∘ₘ π :=
  measure_comp_boolKernel _ _ _ ▸ (Measure.absolutelyContinuous_smul hπ).add_right _

lemma sum_smul_rnDeriv_boolKernel (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    (π {true} • ν.rnDeriv (boolKernel μ ν ∘ₘ π) + π {false} • (μ.rnDeriv (boolKernel μ ν ∘ₘ π)))
      =ᵐ[boolKernel μ ν ∘ₘ π] 1 := by
  have h1 := ν.rnDeriv_smul_left_of_ne_top (boolKernel μ ν ∘ₘ π)
    (measure_ne_top π {true})
  have h2 := μ.rnDeriv_smul_left_of_ne_top (boolKernel μ ν ∘ₘ π)
    (measure_ne_top π {false})
  have : IsFiniteMeasure (π {true} • ν) := ν.smul_finite (measure_ne_top _ _)
  have : IsFiniteMeasure (π {false} • μ) := μ.smul_finite (measure_ne_top _ _)
  have h3 := (π {true} • ν).rnDeriv_add  (π {false} • μ) (boolKernel μ ν ∘ₘ π)
  have h4 := (boolKernel μ ν ∘ₘ π).rnDeriv_self
  filter_upwards [h1, h2, h3, h4] with a h1 h2 h3 h4
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply] at h1 h2 h3 h4 ⊢
  rw [← h1, ← h2, ← h3, ← measure_comp_boolKernel, h4]

lemma sum_smul_rnDeriv_boolKernel' (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    ∀ᵐ x ∂(boolKernel μ ν ∘ₘ π), π {true} * ν.rnDeriv (boolKernel μ ν ∘ₘ π) x
      + π {false} * μ.rnDeriv (boolKernel μ ν ∘ₘ π) x = 1 := by
  filter_upwards [sum_smul_rnDeriv_boolKernel μ ν π] with x hx
  simpa using hx

/-- The kernel from `𝓧` to `Bool` defined by
`x ↦ (π₀ * ∂μ/∂(boolKernel μ ν ∘ₘ π) x + π₁ * ∂ν/∂(boolKernel μ ν ∘ₘ π) x)`.
It is the Bayesian inverse of `boolKernel μ ν` with respect to `π`
(see `bayesInv_boolKernel`). -/
noncomputable
def boolKernelInv (μ ν : Measure 𝓧) (π : Measure Bool) : Kernel 𝓧 Bool where
  toFun x :=
    if π {true} * ν.rnDeriv (boolKernel μ ν ∘ₘ π) x
      + π {false} * μ.rnDeriv (boolKernel μ ν ∘ₘ π) x = 1
    then (π {true} * ν.rnDeriv (boolKernel μ ν ∘ₘ π) x) • Measure.dirac true
      + (π {false} * μ.rnDeriv (boolKernel μ ν ∘ₘ π) x) • Measure.dirac false
    else Measure.dirac true
  measurable' := by
    refine Measurable.ite ?_ ?_ measurable_const
    · refine measurableSet_preimage ?_ (measurableSet_singleton _)
      exact ((ν.measurable_rnDeriv _).const_mul _).add ((μ.measurable_rnDeriv _).const_mul _)
    refine Measure.measurable_of_measurable_coe _ (fun s _ ↦ ?_)
    simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      MeasurableSpace.measurableSet_top, Measure.dirac_apply', smul_eq_mul]
    exact ((measurable_const.mul (ν.measurable_rnDeriv _)).mul measurable_const).add
      ((measurable_const.mul (μ.measurable_rnDeriv _)).mul measurable_const)

lemma boolKernelInv_apply (μ ν : Measure 𝓧) (π : Measure Bool) (x : 𝓧) :
    boolKernelInv μ ν π x
      = if π {true} * ν.rnDeriv (boolKernel μ ν ∘ₘ π) x
          + π {false} * μ.rnDeriv (boolKernel μ ν ∘ₘ π) x = 1
        then (π {true} * ν.rnDeriv (boolKernel μ ν ∘ₘ π) x) • Measure.dirac true
          + (π {false} * μ.rnDeriv (boolKernel μ ν ∘ₘ π) x) • Measure.dirac false
        else Measure.dirac true := rfl

lemma boolKernelInv_apply_ae (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    ∀ᵐ x ∂(boolKernel μ ν ∘ₘ π), boolKernelInv μ ν π x
      = (π {true} * ν.rnDeriv (boolKernel μ ν ∘ₘ π) x) • Measure.dirac true
        + (π {false} * μ.rnDeriv (boolKernel μ ν ∘ₘ π) x) • Measure.dirac false := by
  filter_upwards [sum_smul_rnDeriv_boolKernel' μ ν π] with x hx
  rw [boolKernelInv_apply, if_pos hx]

lemma boolKernelInv_apply' (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] (s : Set Bool) :
    ∀ᵐ x ∂(boolKernel μ ν ∘ₘ π), boolKernelInv μ ν π x s
      = π {true} * ν.rnDeriv (boolKernel μ ν ∘ₘ π) x * s.indicator 1 true
        + π {false} * μ.rnDeriv (boolKernel μ ν ∘ₘ π) x * s.indicator 1 false := by
  filter_upwards [boolKernelInv_apply_ae μ ν π] with x hx
  rw [hx]
  simp

lemma boolKernelInv_apply_false (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    ∀ᵐ x ∂(boolKernel μ ν ∘ₘ π),
      boolKernelInv μ ν π x {false} = π {false} * μ.rnDeriv (boolKernel μ ν ∘ₘ π) x := by
  filter_upwards [boolKernelInv_apply_ae μ ν π] with x hx
  simp [hx]

lemma boolKernelInv_apply_true (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    ∀ᵐ x ∂(boolKernel μ ν ∘ₘ π),
      boolKernelInv μ ν π x {true} = π {true} * ν.rnDeriv (boolKernel μ ν ∘ₘ π) x := by
  filter_upwards [boolKernelInv_apply_ae μ ν π] with x hx
  simp [hx]

instance (π : Measure Bool) : IsMarkovKernel (boolKernelInv μ ν π) := by
  constructor
  intro x
  rw [boolKernelInv_apply]
  split_ifs with h
  · constructor
    simp [h]
  · infer_instance

lemma posterior_boolKernel (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    ((boolKernel μ ν)†π) =ᵐ[boolKernel μ ν ∘ₘ π] boolKernelInv μ ν π := by
  have h_eq := posterior_eq_withDensity Measure.absolutelyContinuous_comp_of_countable
    (κ := boolKernel μ ν) (μ := π)
  have h_rnDeriv_false := Kernel.rnDeriv_eq_rnDeriv_measure (κ := boolKernel μ ν)
    (η := Kernel.const Bool (boolKernel μ ν ∘ₘ π)) (a := false)
  have h_rnDeriv_true := Kernel.rnDeriv_eq_rnDeriv_measure (κ := boolKernel μ ν)
    (η := Kernel.const Bool (boolKernel μ ν ∘ₘ π)) (a := true)
  simp only [Kernel.const_apply, boolKernel_apply, Bool.false_eq_true, ↓reduceIte]
    at h_rnDeriv_false
  simp only [Kernel.const_apply, boolKernel_apply, ↓reduceIte] at h_rnDeriv_true
  filter_upwards [h_eq, boolKernelInv_apply_false μ ν π, boolKernelInv_apply_true μ ν π,
    h_rnDeriv_false, h_rnDeriv_true] with x hx hx_false hx_true h_rnDeriv_false h_rnDeriv_true
  rw [hx]
  ext
  · simp only [MeasurableSpace.measurableSet_top, withDensity_apply, Measure.restrict_singleton,
      lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    rw [hx_false]
    congr!
  · simp only [MeasurableSpace.measurableSet_top, withDensity_apply, Measure.restrict_singleton,
      lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    rw [hx_true]
    congr!

lemma bayesRiskPrior_eq_of_hasGenBayesEstimator_binary {𝓨 : Type*}
    [MeasurableSpace 𝓨] {ℓ : Bool → 𝓨 → ℝ≥0∞}
    (hl : Measurable (Function.uncurry ℓ))
    (P : Kernel Bool 𝓧) [IsFiniteKernel P] (π : Measure Bool) [IsFiniteMeasure π]
    [h : HasGenBayesEstimator ℓ P π] :
    bayesRiskPrior ℓ P π
      = ∫⁻ x, ⨅ z, π {true} * (P true).rnDeriv (P ∘ₘ π) x * ℓ true z
        + π {false} * (P false).rnDeriv (P ∘ₘ π) x * ℓ false z ∂(P ∘ₘ π) := by
  rw [bayesRiskPrior_eq_of_hasGenBayesEstimator hl]
  have h1 := posterior_boolKernel (P false) (P true) π
  have h2 : P = boolKernel (P false) (P true) := Kernel_bool_eq_boolKernel P
  have h3 : (P†π) = (boolKernel (P false) (P true))†π := by congr
  nth_rw 1 3 [h2]
  simp_rw [h3]
  apply lintegral_congr_ae
  filter_upwards [h1, boolKernelInv_apply_false (P false) (P true) π,
    boolKernelInv_apply_true (P false) (P true) π] with x hx h_false h_true
  congr with z
  rw [Bool.lintegral_bool, hx, h_false, h_true, ← h2]
  ring_nf

end ProbabilityTheory
