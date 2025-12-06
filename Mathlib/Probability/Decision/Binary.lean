/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Probability.Decision.BayesEstimator
public import Mathlib.Probability.Decision.BoolMeasure
public import Mathlib.Probability.Decision.Risk.Countable

/-!
# Simple Bayesian binary hypothesis testing

## Main definitions

* `binaryLoss`

## Main statements

* `fooBar_unique`

-/

@[expose] public section

open MeasureTheory

open scoped ENNReal NNReal

section

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

lemma max_eq_add_add_abs_sub (a b : α) : max a b = 2⁻¹ * (a + b + |a - b|) := by
  rw [← max_add_min a, ← max_sub_min_eq_abs', add_sub_left_comm, add_sub_cancel_right]
  ring

lemma min_eq_add_sub_abs_sub (a b : α) : min a b = 2⁻¹ * (a + b - |a - b|) := by
  rw [← min_add_max a, ← max_sub_min_eq_abs', add_sub_assoc, sub_sub_cancel]
  ring

end

namespace ProbabilityTheory

variable {Θ 𝓧 𝓧' 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧}
  {m𝓧' : MeasurableSpace 𝓧'} {m𝓨 : MeasurableSpace 𝓨}
  {μ ν : Measure 𝓧} {p : ℝ≥0∞} {π : Measure Bool}

section BinaryLoss

/-- The binary loss function, which is 0 if the two arguments are equal and 1 otherwise. -/
def binaryLoss [DecidableEq Θ] : Θ → Θ → ℝ≥0∞ := fun θ y ↦ if θ = y then 0 else 1

@[simp]
lemma integral_binaryLoss_true (ν : Measure Bool) : ∫⁻ y, binaryLoss true y ∂ν = ν {false} := by
  simp [binaryLoss, lintegral_bool]

@[simp]
lemma integral_binaryLoss_false (ν : Measure Bool) : ∫⁻ y, binaryLoss false y ∂ν = ν {true} := by
  simp [binaryLoss, lintegral_bool]

instance (P : Kernel Bool 𝓧) [IsFiniteKernel P] (π : Measure Bool) [IsFiniteMeasure π] :
    HasGenBayesEstimator binaryLoss P π :=
  hasGenBayesEstimator_of_finite (by fun_prop)

end BinaryLoss

section BinaryBayesEstimator

/-! ### Explicit form for the Bayes estimator. -/

/-- The function `x ↦ 𝕀{π₀ * ∂μ/∂(boolKernel μ ν ∘ₘ π) x ≤ π₁ * ∂ν/∂(boolKernel μ ν ∘ₘ π) x}`.
It is a generalized Bayes estimator for the simple binary hypothesis testing problem. -/
noncomputable
def binaryBayesEstimator (μ ν : Measure 𝓧) (π : Measure Bool) : 𝓧 → Bool :=
  fun x ↦ (π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x
    ≤ π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x)

lemma binaryBayesEstimator_eq :
    binaryBayesEstimator μ ν π =
      let E : Set 𝓧 := {x | π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x
        ≤ π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x}
      fun x ↦ Bool.ofNat (E.indicator 1 x) := by
  unfold binaryBayesEstimator
  ext x
  simp [Bool.ofNat]

@[fun_prop]
lemma measurable_binaryBayesEstimator : Measurable (binaryBayesEstimator μ ν π) :=
  Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) (by fun_prop) (by fun_prop)

lemma isGenBayesEstimator_binaryBayesEstimator (μ ν : Measure 𝓧) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    IsGenBayesEstimator binaryLoss (Kernel.boolKernel μ ν) (binaryBayesEstimator μ ν π) π := by
  refine ⟨by fun_prop, ?_⟩
  simp only [binaryLoss, lintegral_bool, Bool.false_eq, ite_mul, zero_mul, one_mul,
    Bool.true_eq]
  filter_upwards [posterior_boolKernel_apply_true μ ν π,
    posterior_boolKernel_apply_false μ ν π] with x h_true h_false
  refine le_antisymm (le_iInf fun b ↦ ?_) (iInf_le _ _)
  simp only [binaryBayesEstimator, decide_eq_false_iff_not, not_le, h_false, decide_eq_true_eq,
    h_true]
  by_cases hπ : π {false} * (∂μ/∂Kernel.boolKernel μ ν ∘ₘ π) x
      ≤ π {true} * (∂ν/∂Kernel.boolKernel μ ν ∘ₘ π) x
    <;> cases b
  · simp [hπ, not_lt.mpr hπ]
  · simp [hπ, not_lt.mpr hπ]
  · simp [hπ, not_le.mp hπ]
  · simpa [hπ, not_le.mp hπ] using (not_le.mp hπ).le

end BinaryBayesEstimator

/-- The Bayes risk of simple binary hypothesis testing with respect to a prior. -/
noncomputable
def bayesBinaryRisk (μ ν : Measure 𝓧) (π : Measure Bool) : ℝ≥0∞ :=
  bayesRisk binaryLoss (Kernel.boolKernel μ ν) π

lemma bayesBinaryRisk_eq (μ ν : Measure 𝓧) (π : Measure Bool) :
    bayesBinaryRisk μ ν π
      = ⨅ (κ : Kernel 𝓧 Bool) (_ : IsMarkovKernel κ),
        π {true} * (κ ∘ₘ ν) {false} + π {false} * (κ ∘ₘ μ) {true} := by
  simp [bayesBinaryRisk, bayesRisk_fintype, mul_comm]

variable {π : Measure Bool}

/-- `B (a•μ, b•ν; π) = B (μ, ν; (a*π₀, b*π₁)).` -/
lemma bayesBinaryRisk_smul_smul (μ ν : Measure 𝓧) (π : Measure Bool) (a b : ℝ≥0∞) :
    bayesBinaryRisk (a • μ) (b • ν) π
      = bayesBinaryRisk μ ν (π.withDensity (fun x ↦ if x then b else a)) := by
  simp [bayesBinaryRisk_eq, Measure.comp_smul, lintegral_dirac, mul_assoc]

/-- **Data processing inequality** for the Bayes binary risk. -/
lemma bayesBinaryRisk_le_bayesBinaryRisk_comp (μ ν : Measure 𝓧) (π : Measure Bool)
    (η : Kernel 𝓧 𝓧') [IsMarkovKernel η] :
    bayesBinaryRisk μ ν π ≤ bayesBinaryRisk (η ∘ₘ μ) (η ∘ₘ ν) π :=
  (bayesRisk_le_bayesRisk_comp _ _ _ η).trans_eq (by simp [bayesBinaryRisk])

@[simp]
lemma bayesBinaryRisk_self (μ : Measure 𝓧) (π : Measure Bool) :
    bayesBinaryRisk μ μ π = min (π {false}) (π {true}) * μ .univ := by
  have : Kernel.boolKernel μ μ = Kernel.const Bool μ := by ext; simp
  rw [bayesBinaryRisk, mul_comm, mul_min, this,
    bayesRisk_const_of_fintype (by fun_prop)]
  simp [lintegral_bool, binaryLoss, iInf_bool_eq]

lemma bayesBinaryRisk_dirac (a b : ℝ≥0∞) (x : 𝓧) (π : Measure Bool) :
    bayesBinaryRisk (a • Measure.dirac x) (b • Measure.dirac x) π
      = min (π {false} * a) (π {true} * b) := by
  simp [bayesBinaryRisk_smul_smul]

lemma bayesBinaryRisk_le_min (μ ν : Measure 𝓧) (π : Measure Bool) :
    bayesBinaryRisk μ ν π ≤ min (π {false} * μ .univ) (π {true} * ν .univ) := by
  refine (bayesBinaryRisk_le_bayesBinaryRisk_comp μ ν π (Kernel.discard 𝓧)).trans_eq ?_
  simp_rw [Measure.discard_comp, bayesBinaryRisk_dirac]

@[simp] lemma bayesBinaryRisk_zero_left : bayesBinaryRisk 0 ν π = 0 :=
  le_antisymm ((bayesBinaryRisk_le_min _ _ _).trans (by simp)) zero_le'

@[simp] lemma bayesBinaryRisk_zero_right : bayesBinaryRisk μ 0 π = 0 :=
  le_antisymm ((bayesBinaryRisk_le_min _ _ _).trans (by simp)) zero_le'

@[simp] lemma bayesBinaryRisk_zero_prior : bayesBinaryRisk μ ν 0 = 0 := by
  simp [bayesBinaryRisk]

lemma bayesBinaryRisk_ne_top (μ ν : Measure 𝓧) [IsFiniteMeasure μ]
    (π : Measure Bool) [IsFiniteMeasure π] :
    bayesBinaryRisk μ ν π ≠ ∞ := by
  refine lt_top_iff_ne_top.mp ((bayesBinaryRisk_le_min μ ν π).trans_lt ?_)
  exact min_lt_iff.mpr <| Or.inl <| ENNReal.mul_lt_top (measure_lt_top π _) (measure_lt_top μ _)

lemma bayesBinaryRisk_of_measure_true_eq_zero (μ ν : Measure 𝓧) (hπ : π {true} = 0) :
    bayesBinaryRisk μ ν π = 0 :=
  le_antisymm ((bayesBinaryRisk_le_min μ ν π).trans (by simp [hπ])) zero_le'

lemma bayesBinaryRisk_of_measure_false_eq_zero (μ ν : Measure 𝓧) (hπ : π {false} = 0) :
    bayesBinaryRisk μ ν π = 0 :=
  le_antisymm ((bayesBinaryRisk_le_min μ ν π).trans (by simp [hπ])) zero_le'

lemma bayesBinaryRisk_comm (μ ν : Measure 𝓧) (π : Measure Bool) :
    bayesBinaryRisk μ ν π = bayesBinaryRisk ν μ (π.map Bool.not) := by
  simp only [bayesBinaryRisk_eq, Measure.map_not_apply_true, Measure.map_not_apply_false]
  simp_rw [add_comm, iInf_subtype']
  -- from this point on the proof is basically a change of variable inside the iInf,
  -- to do this I define an equivalence between `Subtype IsMarkovKernel` and itself through
  -- the `Bool.not` operation, maybe it can be shortened or something can be separated as
  -- a different lemma, but I'm not sure how useful this would be
  have : Bool.not ∘ Bool.not = id := by ext; simp [Bool.not_not]
  let e : (Kernel 𝓧 Bool) ≃ (Kernel 𝓧 Bool) := by
    refine ⟨fun κ ↦ κ.map Bool.not, fun κ ↦ κ.map Bool.not, fun κ ↦ ?_, fun κ ↦ ?_⟩ <;>
    · simp only
      rw [← Kernel.map_comp_right _ (by fun_prop) (by fun_prop), this, Kernel.map_id]
  let e' : (Subtype (@IsMarkovKernel 𝓧 Bool _ _)) ≃ (Subtype (@IsMarkovKernel 𝓧 Bool _ _)) := by
    refine ⟨fun ⟨κ, _⟩ ↦ ⟨e κ, ?_⟩, fun ⟨κ, _⟩ ↦ ⟨e.symm κ, ?_⟩, fun κ ↦ by simp, fun κ ↦ by simp⟩
      <;> simp only [Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, e]
      <;> exact Kernel.IsMarkovKernel.map κ (by fun_prop)
  rw [← Equiv.iInf_comp e']
  congr with κ
  simp only [Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, e', e]
  congr 2 <;>
  · rw [Measure.bind_apply (by trivial) (Kernel.aemeasurable _),
      Measure.bind_apply (by trivial) (Kernel.aemeasurable _)]
    congr with x
    rw [Kernel.map_apply' _ (by fun_prop)]
    · simp
    · exact measurableSet_singleton _

lemma bayesBinaryRisk_eq_bayesBinaryRisk_one_one (μ ν : Measure 𝓧) (π : Measure Bool) :
    bayesBinaryRisk μ ν π
      = bayesBinaryRisk (π {false} • μ) (π {true} • ν) (boolMeasure 1 1) := by
  rw [bayesBinaryRisk_smul_smul, measure_eq_boolMeasure π, withDensity_eq_boolMeasure]
  simp

lemma avgRisk_binary_of_deterministic_indicator (μ ν : Measure 𝓧) (π : Measure Bool)
    {E : Set 𝓧} (hE : MeasurableSet E) :
    avgRisk binaryLoss (Kernel.boolKernel μ ν)
      (Kernel.deterministic (fun x ↦ Bool.ofNat (E.indicator 1 x))
        (Measurable.of_discrete.comp' (measurable_one.indicator hE))) π
      = π {false} * μ E + π {true} * ν Eᶜ := by
  have h_meas : Measurable fun x ↦ Bool.ofNat (E.indicator 1 x) :=
    Measurable.of_discrete.comp' (measurable_one.indicator hE)
  have h1 : (fun x ↦ Bool.ofNat (E.indicator 1 x)) ⁻¹' {false} = Eᶜ := by ext; simp [Bool.ofNat]
  have h2 : (fun x ↦ Bool.ofNat (E.indicator 1 x)) ⁻¹' {true} = E := by ext; simp [Bool.ofNat]
  rw [avgRisk, lintegral_bool, mul_comm (π {false}), mul_comm (π {true})]
  simp only [Kernel.comp_boolKernel, Kernel.boolKernel_apply, Bool.false_eq_true, ↓reduceIte,
    integral_binaryLoss_false, integral_binaryLoss_true]
  simp_rw [Measure.deterministic_comp_eq_map, Measure.map_apply h_meas trivial, h1, h2]

lemma bayesBinaryRisk_eq_iInf_measurableSet (μ ν : Measure 𝓧) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    bayesBinaryRisk μ ν π = ⨅ (E) (_ : MeasurableSet E), π {false} * μ E + π {true} * ν Eᶜ := by
  apply le_antisymm
  · simp_rw [le_iInf_iff, bayesBinaryRisk, bayesRisk]
    intro E hE
    rw [← avgRisk_binary_of_deterministic_indicator _ _ _ hE]
    exact iInf_le_of_le _ (iInf_le _ (Kernel.isMarkovKernel_deterministic _))
  · let E := {x | π {false} * (∂μ/∂Kernel.boolKernel μ ν ∘ₘ π) x
      ≤ π {true} * (∂ν/∂Kernel.boolKernel μ ν ∘ₘ π) x}
    have hE : MeasurableSet E := measurableSet_le (by fun_prop) (by fun_prop)
    rw [bayesBinaryRisk, ← IsGenBayesEstimator.isBayesEstimator
      (isGenBayesEstimator_binaryBayesEstimator μ ν π) .of_discrete, IsGenBayesEstimator.kernel]
    simp_rw [binaryBayesEstimator_eq]
    rw [avgRisk_binary_of_deterministic_indicator _ _ _ hE]
    exact iInf_le_of_le E (iInf_le _ hE)

lemma bayesRisk_eq_of_hasGenBayesEstimator_binary {𝓨 : Type*} [MeasurableSpace 𝓨]
    {ℓ : Bool → 𝓨 → ℝ≥0∞} (hl : Measurable (Function.uncurry ℓ))
    (P : Kernel Bool 𝓧) [IsFiniteKernel P] (π : Measure Bool) [IsFiniteMeasure π]
    [h : HasGenBayesEstimator ℓ P π] :
    bayesRisk ℓ P π
      = ∫⁻ x, ⨅ z, π {true} * (P true).rnDeriv (P ∘ₘ π) x * ℓ true z
        + π {false} * (P false).rnDeriv (P ∘ₘ π) x * ℓ false z ∂(P ∘ₘ π) := by
  rw [bayesRisk_eq_of_hasGenBayesEstimator hl]
  have h2 : P = Kernel.boolKernel (P false) (P true) := Kernel.eq_boolKernel P
  have h3 : (P†π) = (Kernel.boolKernel (P false) (P true))†π := by congr
  nth_rw 1 3 [h2]
  simp_rw [h3]
  apply lintegral_congr_ae
  filter_upwards [posterior_boolKernel_apply_false (P false) (P true) π,
    posterior_boolKernel_apply_true (P false) (P true) π] with x h_false h_true
  congr with z
  rw [lintegral_bool, h_false, h_true, ← h2]
  ring_nf

lemma bayesBinaryRisk_eq_lintegral_min (μ ν : Measure 𝓧) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    bayesBinaryRisk μ ν π = ∫⁻ x, min (π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x)
      (π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x) ∂(Kernel.boolKernel μ ν ∘ₘ π) := by
  simp [bayesBinaryRisk, bayesRisk_eq_of_hasGenBayesEstimator_binary .of_discrete,
    iInf_bool_eq, binaryLoss]

lemma ENNReal.ofReal_min {a b : ℝ} : ENNReal.ofReal (min a b) = min (.ofReal a) (.ofReal b) := by
  wlog hab : a ≤ b
  · rw [min_comm a, min_comm (ENNReal.ofReal a)]
    exact this (by linarith)
  rw [min_eq_left hab, min_eq_left]
  exact ENNReal.ofReal_le_ofReal hab

lemma toReal_bayesBinaryRisk_eq_integral_min (μ ν : Measure 𝓧) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    (bayesBinaryRisk μ ν π).toReal
      = ∫ x, min (π.real {false} * (μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x).toReal)
        (π.real {true} * (ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x).toReal)
        ∂(Kernel.boolKernel μ ν ∘ₘ π) := by
  rw [bayesBinaryRisk_eq_lintegral_min, integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · filter_upwards with x; positivity
  · fun_prop
  congr 1
  apply lintegral_congr_ae
  filter_upwards [μ.rnDeriv_ne_top _, ν.rnDeriv_ne_top _] with x hxμ hxν
  rw [ENNReal.ofReal_min, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ofReal_measureReal, ofReal_measureReal, ENNReal.ofReal_toReal (by finiteness),
    ENNReal.ofReal_toReal (by finiteness)]

@[fun_prop]
lemma integrable_toReal_rnDeriv [IsFiniteMeasure μ] :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal) ν :=
  integrable_toReal_of_lintegral_ne_top (by fun_prop)
    (Measure.lintegral_rnDeriv_le.trans_lt (by simp)).ne

lemma toReal_bayesBinaryRisk_eq_integral_abs (μ ν : Measure 𝓧) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    (bayesBinaryRisk μ ν π).toReal
      = 2⁻¹ * (π.real {false} * μ.real .univ + π.real {true} * ν.real .univ
        - ∫ x, |π.real {false} * (μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x).toReal
          - π.real {true} * (ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x).toReal|
          ∂(Kernel.boolKernel μ ν ∘ₘ π)) := by
  simp_rw [toReal_bayesBinaryRisk_eq_integral_min, min_eq_add_sub_abs_sub, integral_const_mul]
  congr
  rw [integral_sub (by fun_prop) (by fun_prop), integral_add (by fun_prop) (by fun_prop)]
  simp only [Measure.real, sub_left_inj, integral_const_mul]
  calc
    _ = (π {false}).toReal * (μ .univ).toReal + (π {true}).toReal
        * ∫ (a : 𝓧), ((∂ν/∂Kernel.boolKernel μ ν ∘ₘ π) a).toReal ∂(Kernel.boolKernel μ ν ∘ₘ π) := by
      by_cases hπ_false : π {false} = 0
      · simp [hπ_false]
      rw [Measure.integral_toReal_rnDeriv (absolutelyContinuous_boolKernel_comp_left μ ν hπ_false)]
      rfl
    _ = (π {false}).toReal * (μ .univ).toReal + (π {true}).toReal * (ν .univ).toReal := by
      by_cases hπ_true : π {true} = 0
      · simp [hπ_true]
      rw [Measure.integral_toReal_rnDeriv (absolutelyContinuous_boolKernel_comp_right μ ν hπ_true)]
      rfl

end ProbabilityTheory
