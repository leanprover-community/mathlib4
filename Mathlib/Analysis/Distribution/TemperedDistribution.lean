/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Distribution.FourierSchwartz
public import Mathlib.Analysis.LocallyConvex.PointwiseConvergence
public import Mathlib.MeasureTheory.Function.Holder

/-!
# TemperedDistribution

## Main definitions

* `TemperedDistribution E F`: The space `𝓢(E, ℂ) →L[ℂ] F` equipped with the pointwise
convergence topology.
* `MeasureTheory.Measure.toTemperedDistribution`: Every measure of temperate growth is a tempered
distribution.
* `Function.HasTemperateGrowth.toTemperedDistribution`: Every function of temperate growth is a
tempered distribution.
* `SchwartzMap.toTemperedDistributionCLM`: The canonical map from `𝓢` to `𝓢'` as a continuous linear
map.
* `MeasureTheory.Lp.toTemperedDistribution`: Every `Lp` function is a tempered distribution.
* `TemperedDistribution.mulLeftCLM`: Multiplication with temperate growth function as a continuous
linear map.
* `TemperedDistribution.fourierTransformCLM`: The Fourier transform on tempered distributions.

## Notation
* `𝓢'(E, F)`: The space of tempered distributions `TemperedDistribution E F` scoped in
`SchwartzMap`
-/

@[expose] public noncomputable section

noncomputable section

open SchwartzMap ContinuousLinearMap MeasureTheory MeasureTheory.Measure

open scoped Nat NNReal ContDiff

variable {E F F₁ F₂ : Type*}

section definition

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℂ F]

variable (E F) in
/-- The space of tempered distribution is the space of continuous linear maps from the Schwartz to
a normed space, equipped with the topology of pointwise convergence. -/
abbrev TemperedDistribution := 𝓢(E, ℂ) →Lₚₜ[ℂ] F
/- Since mathlib is missing quite a few results that show that continuity of linear maps and
convergence of sequences can be checked for strong duals of Fréchet-Montel spaces pointwise, we
use the pointwise topology for now and not the strong topology. The pointwise topology is
conventially used in PDE texts, but has the downside that it is not barrelled, hence the uniform
boundedness principle does not hold. -/

@[inherit_doc]
scoped[SchwartzMap] notation "𝓢'(" E ", " F ")" => TemperedDistribution E F

end definition

/-! ### Embeddings into tempered distributions -/

section Embeddings

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℂ F]

namespace MeasureTheory.Measure

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure E := by volume_tac) [hμ : μ.HasTemperateGrowth]

set_option backward.privateInPublic true in
/-- Every temperate growth measure defines a tempered distribution. -/
def toTemperedDistribution : 𝓢'(E, ℂ) :=
  toPointwiseConvergenceCLM _ _ _ _ (integralCLM ℂ μ)

set_option backward.privateInPublic true in
@[simp]
theorem toTemperedDistribution_apply (g : 𝓢(E, ℂ)) :
    μ.toTemperedDistribution g = ∫ (x : E), g x ∂μ := by
  rfl

end MeasureTheory.Measure

namespace Function.HasTemperateGrowth

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure E := by volume_tac) [hμ : μ.HasTemperateGrowth]

set_option backward.privateInPublic true in
/-- A function of temperate growth `f` defines a tempered distribution via integration, namely
`g ↦ ∫ (x : E), g x • f x ∂μ`. -/
def toTemperedDistribution {f : E → F} (hf : f.HasTemperateGrowth) : 𝓢'(E, F) :=
    toPointwiseConvergenceCLM _ _ _ _ ((integralCLM ℂ μ) ∘L (bilinLeftCLM (lsmul ℂ ℂ) hf))

set_option backward.privateInPublic true in
@[simp]
theorem toTemperedDistribution_apply {f : E → F} (hf : f.HasTemperateGrowth) (g : 𝓢(E, ℂ)) :
    toTemperedDistribution μ hf g = ∫ (x : E), g x • f x ∂μ := rfl

end Function.HasTemperateGrowth

namespace SchwartzMap

section MeasurableSpace

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

variable (E F) in
/-- The canonical embedding of `𝓢(E, F)` into `𝓢'(E, F)` as a continuous linear map. -/
def toTemperedDistributionCLM (μ : Measure E := by volume_tac) [hμ : μ.HasTemperateGrowth] :
    𝓢(E, F) →L[ℂ] 𝓢'(E, F) where
  toFun f := toPointwiseConvergenceCLM _ _ _ _ <| integralCLM ℂ μ ∘L pairing (lsmul ℂ ℂ).flip f
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  cont := PointwiseConvergenceCLM.continuous_of_continuous_eval
    fun g ↦ (integralCLM ℂ μ).cont.comp <| pairing_continuous_left (lsmul ℂ ℂ).flip g

@[simp]
theorem toTemperedDistributionCLM_apply_apply (μ : Measure E := by volume_tac)
    [hμ : μ.HasTemperateGrowth] (f : 𝓢(E, F)) (g : 𝓢(E, ℂ)) :
    toTemperedDistributionCLM E F μ f g = ∫ (x : E), g x • f x ∂μ := by
  simp [toTemperedDistributionCLM, comp_apply _]

end MeasurableSpace

section MeasureSpace

variable [MeasureSpace E] [BorelSpace E] [SecondCountableTopology E]
  [(volume (α := E)).HasTemperateGrowth]

instance instCoeToTemperedDistribution :
    Coe 𝓢(E, F) 𝓢'(E, F) where
  coe := toTemperedDistributionCLM E F volume

theorem coe_apply (f : 𝓢(E, F)) (g : 𝓢(E, ℂ)) :
    (f : 𝓢'(E, F)) g = ∫ (x : E), g x • f x :=
  toTemperedDistributionCLM_apply_apply volume f g

end MeasureSpace

end SchwartzMap

namespace MeasureTheory.Lp

open scoped ENNReal

variable [CompleteSpace F]

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [hμ : μ.HasTemperateGrowth]

/-- Define a tempered distribution from a L^p function. -/
def toTemperedDistribution {p : ℝ≥0∞}
    [hp : Fact (1 ≤ p)] (f : Lp F p μ) : 𝓢'(E, F) :=
  haveI := ENNReal.HolderConjugate.inv_one_sub_inv' hp.out
  haveI : Fact (1 ≤ (1 - p⁻¹)⁻¹) := by simp [fact_iff]
  toPointwiseConvergenceCLM _ _ _ _ <|
    (lsmul ℂ ℂ).flip.lpPairing μ p (1 - p⁻¹)⁻¹ f ∘L toLpCLM ℂ ℂ (1 - p⁻¹)⁻¹ μ

@[simp]
theorem toTemperedDistribution_apply {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (f : Lp F p μ)
    (g : 𝓢(E, ℂ)) :
    toTemperedDistribution f g = ∫ (x : E), g x • f x ∂μ := by
  simp only [toTemperedDistribution, toPointwiseConvergenceCLM_apply, comp_apply _, toLpCLM_apply,
    lpPairing_eq_integral, lsmul_flip_apply, toSpanSingleton_apply]
  apply integral_congr_ae
  filter_upwards [g.coeFn_toLp (1 - p⁻¹)⁻¹ μ] with x hg
  rw [hg]

instance instCoeDep {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (f : Lp F p μ) :
    CoeDep (Lp F p μ) f 𝓢'(E, F) where
  coe := toTemperedDistribution f

@[simp]
theorem toTemperedDistribution_toLp_eq [SecondCountableTopology E] {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]
    (f : 𝓢(E, F)) : ((f.toLp p μ) : 𝓢'(E, F)) = f.toTemperedDistributionCLM E F μ := by
  ext g
  simp only [Lp.toTemperedDistribution_apply, toTemperedDistributionCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp p μ] with x hf
  rw [hf]

variable (F) in
/-- The natural embedding of L^p into tempered distributions. -/
def toTemperedDistributionCLM (μ : Measure E := by volume_tac) [μ.HasTemperateGrowth]
    (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] :
    Lp F p μ →L[ℂ] 𝓢'(E, F) where
  toFun := toTemperedDistribution
  map_add' f g := by simp [Lp.toTemperedDistribution]
  map_smul' a f := by simp [Lp.toTemperedDistribution]
  cont := by
    apply PointwiseConvergenceCLM.continuous_of_continuous_eval
    intro g
    haveI : Fact (1 ≤ (1 - p⁻¹)⁻¹) := by simp [fact_iff]
    have hpq : ENNReal.HolderConjugate p (1 - p⁻¹)⁻¹ :=
      ENNReal.HolderConjugate.inv_one_sub_inv' hp.out
    exact (((lsmul ℂ ℂ (E := F)).flip.lpPairing μ p (1 - p⁻¹)⁻¹).flip (g.toLp (1 - p⁻¹)⁻¹ μ)).cont

@[simp]
theorem toTemperedDistributionCLM_apply {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (f : Lp F p μ) :
    toTemperedDistributionCLM F μ p f = f := rfl

variable [FiniteDimensional ℝ E] [IsLocallyFiniteMeasure μ]

theorem ker_toTemperedDistributionCLM_eq_bot {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] :
    (MeasureTheory.Lp.toTemperedDistributionCLM F μ p).ker = ⊥ := by
  rw [LinearMap.ker_eq_bot', ContinuousLinearMap.coe_coe]
  intro f hf
  rw [eq_zero_iff_ae_eq_zero]
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
  · exact (Lp.memLp f).locallyIntegrable hp.elim
  · intro g g_smooth g_cpt
    have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_cpt.comp_left rfl
    have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
    calc
      _ = toTemperedDistributionCLM F μ p f (hg₁.toSchwartzMap hg₂) := by simp
      _ = _ := by simp [hf]

end MeasureTheory.Lp

end Embeddings

namespace TemperedDistribution

section Multiplication

variable [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℝ E] [NormedSpace ℂ F]

variable (F) in
/-- Multiplication with a temperate growth function as a continuous linear map on `𝓢'(E, F)`. -/
def smulLeftCLM (g : E → ℂ) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  PointwiseConvergenceCLM.precomp _ (SchwartzMap.smulLeftCLM ℂ g)

@[simp]
theorem smulLeftCLM_apply_apply (g : E → ℂ) (f : 𝓢'(E, F)) (f' : 𝓢(E, ℂ)) :
    smulLeftCLM F g f f' = f (SchwartzMap.smulLeftCLM ℂ g f') := by
  rfl

@[simp]
theorem smulLeftCLM_const (c : ℂ) (f : 𝓢'(E, F)) : smulLeftCLM F (fun _ : E ↦  c) f = c • f := by
  ext1; simp

@[simp]
theorem smulLeftCLM_smulLeftCLM_apply {g₁ g₂ : E → ℂ} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢'(E, F)) :
    smulLeftCLM F g₂ (smulLeftCLM F g₁ f) = smulLeftCLM F (g₁ * g₂) f := by
  ext; simp [hg₁, hg₂]

theorem smulLeftCLM_compL_smulLeftCLM {g₁ g₂ : E → ℂ} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    smulLeftCLM F g₂ ∘L smulLeftCLM F g₁ = smulLeftCLM F (g₁ * g₂) := by
  ext1 f
  simp [hg₁, hg₂]

end Multiplication

/-! ### Fourier transform -/

section Fourier

open FourierTransform

variable [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [NormedSpace ℂ F]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

variable (E F) in
/-- The Fourier transform on tempered distributions as a continuous linear map. -/
def fourierTransformCLM : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  PointwiseConvergenceCLM.precomp F (SchwartzMap.fourierTransformCLM ℂ)

instance instFourierTransform : FourierTransform 𝓢'(E, F) 𝓢'(E, F) where
  fourier := fourierTransformCLM E F

@[simp]
theorem fourierTransformCLM_apply (f : 𝓢'(E, F)) :
  fourierTransformCLM E F f = 𝓕 f := rfl

@[simp]
theorem fourierTransform_apply (f : 𝓢'(E, F)) (g : 𝓢(E, ℂ)) : 𝓕 f g = f (𝓕 g) := rfl

variable (E F) in
/-- The inverse Fourier transform on tempered distributions as a continuous linear map. -/
def fourierTransformInvCLM : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  PointwiseConvergenceCLM.precomp F (SchwartzMap.fourierTransformCLE ℂ).symm.toContinuousLinearMap

instance instFourierTransformInv : FourierTransformInv 𝓢'(E, F) 𝓢'(E, F) where
  fourierInv := fourierTransformInvCLM E F

@[simp]
theorem fourierTransformInvCLM_apply (f : 𝓢'(E, F)) :
    fourierTransformInvCLM E F f = 𝓕⁻ f := rfl

@[simp]
theorem fourierTransformInv_apply (f : 𝓢'(E, F)) (g : 𝓢(E, ℂ)) : 𝓕⁻ f g = f (𝓕⁻ g) := rfl

instance instFourierPair : FourierPair 𝓢'(E, F) 𝓢'(E, F) where
  fourierInv_fourier_eq f := by ext; simp

instance instFourierPairInv : FourierInvPair 𝓢'(E, F) 𝓢'(E, F) where
  fourier_fourierInv_eq f := by ext; simp

variable [CompleteSpace F]

/-- The distributional Fourier transform and the classical Fourier transform coincide on
`𝓢(E, F)`. -/
theorem fourierTransform_toTemperedDistributionCLM_eq (f : 𝓢(E, F)) :
    𝓕 (f : 𝓢'(E, F)) = 𝓕 f := by
  ext g
  simpa using integral_fourier_smul_eq g f

/-- The distributional inverse Fourier transform and the classical inverse Fourier transform
coincide on `𝓢(E, F)`. -/
theorem fourierTransformInv_toTemperedDistributionCLM_eq (f : 𝓢(E, F)) :
    𝓕⁻ (f : 𝓢'(E, F)) = 𝓕⁻ f := calc
  _ = 𝓕⁻ (toTemperedDistributionCLM E F volume (𝓕 (𝓕⁻ f))) := by
    congr; exact (fourier_fourierInv_eq f).symm
  _ = 𝓕⁻ (𝓕 (toTemperedDistributionCLM E F volume (𝓕⁻ f))) := by
    rw [fourierTransform_toTemperedDistributionCLM_eq]
  _ = _ := fourierInv_fourier_eq _

end Fourier

end TemperedDistribution
