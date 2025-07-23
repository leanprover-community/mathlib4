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

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨} {μ ν : Measure 𝓧}

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

lemma boolKernel_comp_measure (μ ν : Measure 𝓧) (π : Measure Bool) :
    boolKernel μ ν ∘ₘ π = π {true} • ν + π {false} • μ := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp only [boolKernel_apply, lintegral_fintype, Fintype.univ_bool, Finset.mem_singleton,
    Bool.true_eq_false, not_false_eq_true, Finset.sum_insert, ↓reduceIte, Finset.sum_singleton,
    Bool.false_eq_true, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  congr 1 <;> rw [mul_comm]

lemma absolutelyContinuous_boolKernel_comp_measure_left (μ ν : Measure 𝓧)
    {π : Measure Bool} (hπ : π {false} ≠ 0) :
    μ ≪ boolKernel μ ν ∘ₘ π :=
  boolKernel_comp_measure _ _ _ ▸ add_comm _ (π {true} • ν) ▸
    (Measure.absolutelyContinuous_smul hπ).add_right _

lemma absolutelyContinuous_boolKernel_comp_measure_right (μ ν : Measure 𝓧)
    {π : Measure Bool} (hπ : π {true} ≠ 0) :
    ν ≪ boolKernel μ ν ∘ₘ π :=
  boolKernel_comp_measure _ _ _ ▸ (Measure.absolutelyContinuous_smul hπ).add_right _

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
  rw [← h1, ← h2, ← h3, ← boolKernel_comp_measure, h4]

lemma sum_smul_rnDeriv_boolKernel' (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    ∀ᵐ x ∂(boolKernel μ ν ∘ₘ π), π {true} * ν.rnDeriv (boolKernel μ ν ∘ₘ π) x
      + π {false} * μ.rnDeriv (boolKernel μ ν ∘ₘ π) x = 1 := by
  filter_upwards [sum_smul_rnDeriv_boolKernel μ ν π] with x hx using by simpa using hx

lemma posterior_boolKernel_apply_false (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    ∀ᵐ x ∂boolKernel μ ν ∘ₘ π, ((boolKernel μ ν)†π) x {false}
      = π {false} * μ.rnDeriv (boolKernel μ ν ∘ₘ π) x := by
  filter_upwards [posterior_eq_withDensity_of_countable (boolKernel μ ν) π] with x hx
  rw [hx]
  simp

lemma posterior_boolKernel_apply_true (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    ∀ᵐ x ∂boolKernel μ ν ∘ₘ π, ((boolKernel μ ν)†π) x {true}
      = π {true} * ν.rnDeriv (boolKernel μ ν ∘ₘ π) x := by
  filter_upwards [posterior_eq_withDensity_of_countable (boolKernel μ ν) π] with x hx
  rw [hx]
  simp

end ProbabilityTheory
