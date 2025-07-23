/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Probability.Decision.BoolKernel

/-!
# Simple Bayesian binary hypothesis testing

## Main definitions

* `binaryLoss`

## Main statements

* `fooBar_unique`

## Notation

## Implementation details

-/

open MeasureTheory

open scoped ENNReal NNReal

namespace ProbabilityTheory

@[simp]
lemma _root_.MeasureTheory.Measure.discard_comp {α : Type*} {_ : MeasurableSpace α}
    (μ : Measure α) :
    (Kernel.discard α) ∘ₘ μ = μ .univ • (Measure.dirac ()) := by
  ext s hs; simp [Measure.bind_apply hs (Kernel.aemeasurable _), mul_comm]

variable {Θ 𝓧 𝓧' 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧}
  {m𝓧' : MeasurableSpace 𝓧'} {m𝓨 : MeasurableSpace 𝓨}
  {μ ν : Measure 𝓧} {p : ℝ≥0∞}

section binaryLoss

def binaryLoss [DecidableEq Θ] : Θ → Θ → ℝ≥0∞ := fun θ y ↦ if θ = y then 0 else 1

@[simp]
lemma risk_binaryLoss_true (μ ν : Measure 𝓧) (κ : Kernel 𝓧 Bool) :
    risk binaryLoss (boolKernel μ ν) κ true = (κ ∘ₘ ν) {false} := by
  simp only [risk, comp_boolKernel, boolKernel_apply, ↓reduceIte, binaryLoss, Bool.true_eq]
  calc ∫⁻ z, if z = true then 0 else 1 ∂(κ ∘ₘ ν)
  _ = ∫⁻ z, Set.indicator {false} (fun _ ↦ 1) z ∂(κ ∘ₘ ν) := by
    congr with z
    rw [Set.indicator_apply]
    simp only [Set.mem_singleton_iff]
    split_ifs with h1 h2 h2
    · exact absurd (h2.symm.trans h1) Bool.false_ne_true
    · rfl
    · rfl
    · simp only [Bool.not_eq_true, Bool.not_eq_false] at h1 h2
      exact absurd (h1.symm.trans h2) Bool.false_ne_true
  _ = (κ ∘ₘ ν) {false} := lintegral_indicator_one (measurableSet_singleton _)

@[simp]
lemma risk_binaryLoss_false (μ ν : Measure 𝓧) (κ : Kernel 𝓧 Bool) :
    risk binaryLoss (boolKernel μ ν) κ false = (κ ∘ₘ μ) {true} := by
  simp only [risk, comp_boolKernel, boolKernel_apply, Bool.false_eq, Bool.true_eq_false, ↓reduceIte,
    binaryLoss]
  calc ∫⁻ z, if z = false then 0 else 1 ∂(κ ∘ₘ μ)
  _ = ∫⁻ z, Set.indicator {true} (fun _ ↦ 1) z ∂(κ ∘ₘ μ) := by
    congr with z
    rw [Set.indicator_apply]
    classical
    simp only [Set.mem_singleton_iff]
    split_ifs with h1 h2 h2
    · exact absurd (h1.symm.trans h2) Bool.false_ne_true
    · rfl
    · rfl
    · simp at h1 h2
      exact absurd (h2.symm.trans h1) Bool.false_ne_true
  _ = (κ ∘ₘ μ) {true} := lintegral_indicator_one (measurableSet_singleton _)

/-- The function `x ↦ 𝕀{π₀ * ∂μ/∂(boolKernel μ ν ∘ₘ π) x ≤ π₁ * ∂ν/∂(boolKernel μ ν ∘ₘ π) x}`.
It is a Generalized Bayes estimator for the simple binary hypothesis testing problem. -/
noncomputable
def binaryGenBayesEstimator (μ ν : Measure 𝓧) (π : Measure Bool) : 𝓧 → Bool :=
  let E : Set 𝓧 := {x | π {false} * μ.rnDeriv (boolKernel μ ν ∘ₘ π) x
    ≤ π {true} * ν.rnDeriv (boolKernel μ ν ∘ₘ π) x}
  fun x ↦ Bool.ofNat (E.indicator 1 x)

lemma binaryGenBayesEstimator_isGenBayesEstimator (μ ν : Measure 𝓧) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    IsGenBayesEstimator binaryLoss (boolKernel μ ν)
      (binaryGenBayesEstimator μ ν π) π := by
  refine ⟨?_, ?_⟩
  · simp_rw [binaryGenBayesEstimator]
    refine Measurable.of_discrete.comp' (measurable_one.indicator (measurableSet_le ?_ ?_))
      <;> fun_prop
  · filter_upwards [posterior_boolKernel μ ν π, boolKernelInv_apply' μ ν π {true},
      boolKernelInv_apply' μ ν π {false}] with x hx h_true h_false
    refine le_antisymm (le_iInf fun b ↦ ?_) (iInf_le _ _)
    simp only [binaryLoss, binaryGenBayesEstimator, Bool.ofNat, ne_eq,
      Set.indicator_apply_eq_zero, Set.mem_setOf_eq, Pi.ofNat_apply, one_ne_zero, imp_false,
      Bool.lintegral_bool, Bool.false_eq, decide_eq_false_iff_not, ite_mul, zero_mul,
      one_mul, Bool.true_eq, decide_eq_true_eq]
    by_cases hπ : π {false} * (∂μ/∂boolKernel μ ν ∘ₘ π) x ≤ π {true} * (∂ν/∂boolKernel μ ν ∘ₘ π) x
    · simp only [hπ, not_true_eq_false, not_false_eq_true, ↓reduceIte, add_zero]
      cases b <;> simp_all
    · cases b
      · simp_all
      · simp_all only [Set.mem_singleton_iff, Set.indicator_of_mem, Pi.one_apply, mul_one,
          Bool.false_eq_true, not_false_eq_true, Set.indicator_of_notMem, mul_zero, add_zero,
          Bool.true_eq_false, zero_add, not_le, not_true_eq_false, ↓reduceIte]
        gcongr

noncomputable instance (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    HasGenBayesEstimator binaryLoss (boolKernel μ ν) π :=
  ⟨binaryGenBayesEstimator μ ν π, binaryGenBayesEstimator_isGenBayesEstimator μ ν π⟩

end binaryLoss

/-- The Bayes risk of simple binary hypothesis testing with respect to a prior. -/
noncomputable
def bayesBinaryRisk (μ ν : Measure 𝓧) (π : Measure Bool) : ℝ≥0∞ :=
  bayesRiskPrior binaryLoss (boolKernel μ ν) π

lemma bayesBinaryRisk_eq (μ ν : Measure 𝓧) (π : Measure Bool) :
    bayesBinaryRisk μ ν π
      = ⨅ (κ : Kernel 𝓧 Bool) (_ : IsMarkovKernel κ),
        π {true} * (κ ∘ₘ ν) {false} + π {false} * (κ ∘ₘ μ) {true} := by
  rw [bayesBinaryRisk, bayesRiskPrior]
  congr with κ
  congr with _
  rw [bayesianRisk, lintegral_fintype, mul_comm (π {false}), mul_comm (π {true})]
  simp

variable {π : Measure Bool}

/-- `B (a•μ, b•ν; π) = B (μ, ν; (a*π₀, b*π₁)).` -/
lemma bayesBinaryRisk_smul_smul (μ ν : Measure 𝓧) (π : Measure Bool) (a b : ℝ≥0∞) :
    bayesBinaryRisk (a • μ) (b • ν) π
      = bayesBinaryRisk μ ν (π.withDensity (fun x ↦ bif x then b else a)) := by
  simp [bayesBinaryRisk_eq, Measure.comp_smul, lintegral_dirac, mul_assoc]

lemma bayesBinaryRisk_eq_bayesBinaryRisk_one_one (μ ν : Measure 𝓧) (π : Measure Bool) :
    bayesBinaryRisk μ ν π
      = bayesBinaryRisk (π {false} • μ) (π {true} • ν) (Bool.boolMeasure 1 1) := by
  rw [bayesBinaryRisk_smul_smul, Bool.measure_eq_boolMeasure π, Bool.boolMeasure_withDensity]
  simp

/-- **Data processing inequality** for the Bayes binary risk. -/
lemma bayesBinaryRisk_le_bayesBinaryRisk_comp (μ ν : Measure 𝓧) (π : Measure Bool)
    (η : Kernel 𝓧 𝓧') [IsMarkovKernel η] :
    bayesBinaryRisk μ ν π ≤ bayesBinaryRisk (η ∘ₘ μ) (η ∘ₘ ν) π :=
  (bayesRiskPrior_le_bayesRiskPrior_comp _ _ _ η).trans_eq (by simp [bayesBinaryRisk])

lemma nonempty_subtype_isMarkovKernel_of_nonempty {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}
    {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨} [Nonempty 𝓨] :
    Nonempty (Subtype (@IsMarkovKernel 𝓧 𝓨 m𝓧 m𝓨)) := by
  simp only [nonempty_subtype]
  let y : 𝓨 := Classical.ofNonempty
  exact ⟨Kernel.const _ (Measure.dirac y), inferInstance⟩

@[simp]
lemma bayesBinaryRisk_self (μ : Measure 𝓧) (π : Measure Bool) :
    bayesBinaryRisk μ μ π = min (π {false}) (π {true}) * μ .univ := by
  rw [bayesBinaryRisk_eq]
  refine le_antisymm ?_ ?_
  · let η : Kernel 𝓧 Bool :=
      if π {true} ≤ π {false} then (Kernel.const 𝓧 (Measure.dirac false))
        else (Kernel.const 𝓧 (Measure.dirac true))
    refine iInf_le_of_le η ?_
    simp_rw [η]
    convert iInf_le _ ?_ using 1
    · split_ifs with h <;> simp [le_of_not_ge, h]
    · split_ifs <;> infer_instance
  · calc
      _ ≥ ⨅ κ, ⨅ (_ : IsMarkovKernel κ), min (π {false}) (π {true}) * (κ ∘ₘ μ) {false}
          + min (π {false}) (π {true}) * (κ ∘ₘ μ) {true} := by
        gcongr <;> simp
      _ = ⨅ κ, ⨅ (_ : IsMarkovKernel κ), min (π {false}) (π {true}) * μ .univ := by
        simp_rw [← mul_add, ← measure_union (show Disjoint {false} {true} from by simp)
          (by trivial), (set_fintype_card_eq_univ_iff ({false} ∪ {true})).mp rfl,
          Measure.comp_apply_univ]
        rfl
      _ = _ := by
        rw [iInf_subtype']
        convert iInf_const
        exact nonempty_subtype_isMarkovKernel_of_nonempty

lemma bayesBinaryRisk_dirac (a b : ℝ≥0∞) (x : 𝓧) (π : Measure Bool) :
    bayesBinaryRisk (a • Measure.dirac x) (b • Measure.dirac x) π
      = min (π {false} * a) (π {true} * b) := by
  rw [bayesBinaryRisk_smul_smul, bayesBinaryRisk_self]
  simp [lintegral_dirac]

lemma bayesBinaryRisk_le_min (μ ν : Measure 𝓧) (π : Measure Bool) :
    bayesBinaryRisk μ ν π ≤ min (π {false} * μ .univ) (π {true} * ν .univ) := by
  convert bayesBinaryRisk_le_bayesBinaryRisk_comp μ ν π (Kernel.discard 𝓧)
  simp_rw [Measure.discard_comp, bayesBinaryRisk_dirac]

@[simp] lemma bayesBinaryRisk_zero_left : bayesBinaryRisk 0 ν π = 0 :=
  le_antisymm ((bayesBinaryRisk_le_min _ _ _).trans (by simp)) zero_le'

@[simp] lemma bayesBinaryRisk_zero_right : bayesBinaryRisk μ 0 π = 0 :=
  le_antisymm ((bayesBinaryRisk_le_min _ _ _).trans (by simp)) zero_le'

@[simp] lemma bayesBinaryRisk_zero_prior : bayesBinaryRisk μ ν 0 = 0 :=
  le_antisymm ((bayesBinaryRisk_le_min _ _ _).trans (by simp)) zero_le'

lemma bayesBinaryRisk_ne_top (μ ν : Measure 𝓧) [IsFiniteMeasure μ]
    (π : Measure Bool) [IsFiniteMeasure π] :
    bayesBinaryRisk μ ν π ≠ ∞ := by
  refine lt_top_iff_ne_top.mp ((bayesBinaryRisk_le_min μ ν π).trans_lt ?_)
  exact min_lt_iff.mpr <| Or.inl <| ENNReal.mul_lt_top (measure_lt_top π _) (measure_lt_top μ _)

lemma bayesBinaryRisk_of_measure_true_eq_zero (μ ν : Measure 𝓧) (hπ : π {true} = 0) :
    bayesBinaryRisk μ ν π = 0 := by
  refine le_antisymm ?_ (zero_le _)
  convert bayesBinaryRisk_le_min μ ν π
  simp [hπ]

lemma bayesBinaryRisk_of_measure_false_eq_zero (μ ν : Measure 𝓧) (hπ : π {false} = 0) :
    bayesBinaryRisk μ ν π = 0 := by
  refine le_antisymm ?_ (zero_le _)
  convert bayesBinaryRisk_le_min μ ν π
  simp [hπ]

lemma bayesBinaryRisk_symm (μ ν : Measure 𝓧) (π : Measure Bool) :
    bayesBinaryRisk μ ν π = bayesBinaryRisk ν μ (π.map Bool.not) := by
  have : (Bool.not ⁻¹' {true}) = {false} := by ext x; simp
  have h1 : (π.map Bool.not) {true} = π {false} := by
    rw [Measure.map_apply (by exact fun _ a ↦ a) (by trivial), this]
  have : (Bool.not ⁻¹' {false}) = {true} := by ext x; simp
  have h2 : (π.map Bool.not) {false} = π {true} := by
    rw [Measure.map_apply (by exact fun _ a ↦ a) (by trivial), this]
  simp_rw [bayesBinaryRisk_eq, h1, h2, add_comm, iInf_subtype']
  -- from this point on the proof is basically a change of variable inside the iInf,
  -- to do this I define an equivalence between `Subtype IsMarkovKernel` and itself through
  -- the `Bool.not` operation, maybe it can be shortened or something can be separated as
  -- a different lemma, but I'm not sure how useful this would be
  let e : (Kernel 𝓧 Bool) ≃ (Kernel 𝓧 Bool) := by
    have h_id : (Kernel.deterministic Bool.not (fun _ a ↦ a)).comap Bool.not (fun _ a ↦ a)
        = Kernel.id := by
      ext x : 1
      simp_rw [Kernel.comap_apply, Kernel.deterministic_apply, Kernel.id_apply, Bool.not_not]
    refine ⟨fun κ ↦ (Kernel.deterministic Bool.not (fun _ a ↦ a)) ∘ₖ κ,
      fun κ ↦ (Kernel.deterministic Bool.not (fun _ a ↦ a)) ∘ₖ κ, fun κ ↦ ?_, fun κ ↦ ?_⟩ <;>
    · dsimp
      ext x : 1
      rw [← Kernel.comp_assoc, Kernel.comp_deterministic_eq_comap, h_id, Kernel.id_comp]
  let e' : (Subtype (@IsMarkovKernel 𝓧 Bool _ _)) ≃ (Subtype (@IsMarkovKernel 𝓧 Bool _ _)) := by
    refine ⟨fun ⟨κ, _⟩ ↦ ⟨e κ, ?_⟩, fun ⟨κ, _⟩ ↦ ⟨e.symm κ, ?_⟩, fun κ ↦ by simp, fun κ ↦ by simp⟩
      <;> simp only [Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, e] <;> infer_instance
  rw [← Equiv.iInf_comp e']
  congr with κ
  simp only [Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, e', e]
  have h3 b : Set.indicator {true} (1 : Bool → ℝ≥0∞) b.not = Set.indicator {false} 1 b := by
    cases b <;> simp
  have h4 b : Set.indicator {false} (1 : Bool → ℝ≥0∞) b.not = Set.indicator {true} 1 b := by
    cases b <;> simp
  congr 2 <;>
  · rw [Measure.bind_apply (by trivial) (Kernel.aemeasurable _),
      Measure.bind_apply (by trivial) (Kernel.aemeasurable _)]
    congr with x
    rw [Kernel.comp_apply']
    simp only [Measure.dirac_apply' _ (show MeasurableSet {true} by trivial),
      Measure.dirac_apply' _ (show MeasurableSet {false} by trivial), Kernel.deterministic_apply]
    swap; trivial
    simp [h3, h4]

lemma bayesianRisk_binary_of_deterministic_indicator (μ ν : Measure 𝓧) (π : Measure Bool)
    {E : Set 𝓧} (hE : MeasurableSet E) :
    bayesianRisk binaryLoss (boolKernel μ ν)
      (Kernel.deterministic (fun x ↦ Bool.ofNat (E.indicator 1 x))
        (Measurable.of_discrete.comp' (measurable_one.indicator hE))) π
      = π {false} * μ E + π {true} * ν Eᶜ := by
  have h_meas : Measurable fun x ↦ Bool.ofNat (E.indicator 1 x) :=
    Measurable.of_discrete.comp' (measurable_one.indicator hE)
  have h1 : (fun x ↦ Bool.ofNat (E.indicator 1 x)) ⁻¹' {false} = Eᶜ := by
    ext; simp [Bool.ofNat]
  have h2 : (fun x ↦ Bool.ofNat (E.indicator 1 x)) ⁻¹' {true} = E := by
    ext; simp [Bool.ofNat]
  rw [bayesianRisk, Bool.lintegral_bool, mul_comm (π {false}), mul_comm (π {true})]
  simp only [risk_binaryLoss_false, risk_binaryLoss_true]
  simp_rw [Measure.deterministic_comp_eq_map, Measure.map_apply h_meas trivial, h1, h2]

lemma bayesBinaryRisk_eq_iInf_measurableSet (μ ν : Measure 𝓧) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    bayesBinaryRisk μ ν π = ⨅ E, ⨅ (_ : MeasurableSet E), π {false} * μ E + π {true} * ν Eᶜ := by
  apply le_antisymm
  · simp_rw [le_iInf_iff, bayesBinaryRisk, bayesRiskPrior]
    intro E hE
    rw [← bayesianRisk_binary_of_deterministic_indicator _ _ _ hE]
    exact iInf_le_of_le _ (iInf_le _ (Kernel.isMarkovKernel_deterministic _))
  · let E := {x | π {false} * (∂μ/∂boolKernel μ ν ∘ₘ π) x
      ≤ π {true} * (∂ν/∂boolKernel μ ν ∘ₘ π) x}
    have hE : MeasurableSet E := measurableSet_le (by fun_prop) (by fun_prop)
    rw [bayesBinaryRisk, ← IsGenBayesEstimator.isBayesEstimator
      (binaryGenBayesEstimator_isGenBayesEstimator μ ν π) .of_discrete, IsGenBayesEstimator.kernel]
    simp_rw [binaryGenBayesEstimator]
    rw [bayesianRisk_binary_of_deterministic_indicator _ _ _ hE]
    exact iInf_le_of_le E (iInf_le _ hE)

lemma bayesBinaryRisk_eq_lintegral_min (μ ν : Measure 𝓧) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    bayesBinaryRisk μ ν π = ∫⁻ x, min (π {false} * μ.rnDeriv (boolKernel μ ν ∘ₘ π) x)
      (π {true} * ν.rnDeriv (boolKernel μ ν ∘ₘ π) x) ∂(boolKernel μ ν ∘ₘ π) := by
  simp [bayesBinaryRisk, bayesRiskPrior_eq_of_hasGenBayesEstimator_binary .of_discrete,
    iInf_bool_eq, binaryLoss]

end ProbabilityTheory
