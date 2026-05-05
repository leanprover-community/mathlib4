/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

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
* `TemperedDistribution.instLineDeriv`: The directional derivative on tempered distributions.
* `TemperedDistribution.fourierTransformCLM`: The Fourier transform on tempered distributions.

## Notation
* `𝓢'(E, F)`: The space of tempered distributions `TemperedDistribution E F` scoped in
  `SchwartzMap`
-/

@[expose] public noncomputable section

open SchwartzMap ContinuousLinearMap MeasureTheory MeasureTheory.Measure

open scoped Nat NNReal ContDiff

variable {ι 𝕜 E F F₁ F₂ : Type*}

section definition

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℂ F]

variable (E F) in
/-- The space of tempered distribution is the space of continuous linear maps from the Schwartz to
a normed space, equipped with the topology of pointwise convergence. -/
abbrev TemperedDistribution := 𝓢(E, ℂ) →Lₚₜ[ℂ] F
/- Since mathlib is missing quite a few results that show that continuity of linear maps and
convergence of sequences can be checked for strong duals of Fréchet-Montel spaces pointwise, we
use the pointwise topology for now and not the strong topology. The pointwise topology is
conventionally used in PDE texts, but has the downside that it is not barrelled, hence the uniform
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

set_option backward.isDefEq.respectTransparency false in
variable (E F) in
/-- The canonical embedding of `𝓢(E, F)` into `𝓢'(E, F)` as a continuous linear map. -/
def toTemperedDistributionCLM (μ : Measure E := by volume_tac) [hμ : μ.HasTemperateGrowth] :
    𝓢(E, F) →L[ℂ] 𝓢'(E, F) where
  toFun f := toPointwiseConvergenceCLM _ _ _ _ <| integralCLM ℂ μ ∘L pairing (lsmul ℂ ℂ).flip f
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  cont := PointwiseConvergenceCLM.continuous_of_continuous_eval
    fun g ↦ (integralCLM ℂ μ).cont.comp <| pairing_continuous_left (lsmul ℂ ℂ).flip g

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
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

/-! ### Scalar multiplication with temperate growth functions -/

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
theorem smulLeftCLM_const (c : ℂ) (f : 𝓢'(E, F)) : smulLeftCLM F (fun _ : E ↦ c) f = c • f := by
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

theorem smulLeftCLM_smul {g : E → ℂ} (hg : g.HasTemperateGrowth) (c : ℂ) :
    smulLeftCLM F (c • g) = c • smulLeftCLM F g := by
  ext f u
  simp [SchwartzMap.smulLeftCLM_smul hg]

theorem smulLeftCLM_add {g₁ g₂ : E → ℂ} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    smulLeftCLM F (g₁ + g₂) = smulLeftCLM F g₁ + smulLeftCLM F g₂ := by
  ext f u
  simp [SchwartzMap.smulLeftCLM_add hg₁ hg₂]

theorem smulLeftCLM_sub {g₁ g₂ : E → ℂ} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    smulLeftCLM F (g₁ - g₂) = smulLeftCLM F g₁ - smulLeftCLM F g₂ := by
  ext f u
  simp [SchwartzMap.smulLeftCLM_sub hg₁ hg₂]

theorem smulLeftCLM_neg {g : E → ℂ} (hg : g.HasTemperateGrowth) :
    smulLeftCLM F (-g) = -smulLeftCLM F g := by
  ext f u
  simp [SchwartzMap.smulLeftCLM_neg hg]

theorem smulLeftCLM_sum {g : ι → E → ℂ} {s : Finset ι} (hg : ∀ i ∈ s, (g i).HasTemperateGrowth) :
    smulLeftCLM F (fun x ↦ ∑ i ∈ s, g i x) = ∑ i ∈ s, smulLeftCLM F (g i) := by
  ext f u
  simp [SchwartzMap.smulLeftCLM_sum hg]

open ENNReal MeasureTheory

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [hμ : μ.HasTemperateGrowth]
  [CompleteSpace F]

/-- Coercion of the product of two `Lp` functions to a tempered distribution is equal to the left
multiplication if the left factor is a function of temperate growth. -/
theorem _root_.MeasureTheory.Lp.toTemperedDistribution_smul_eq {p q r : ℝ≥0∞} [p.HolderTriple q r]
    [Fact (1 ≤ q)] [Fact (1 ≤ r)] {g : E → ℂ} (hg₁ : g.HasTemperateGrowth) (hg₂ : MemLp g p μ)
    (f : Lp F q μ) :
    ((hg₂.toLp _) • f : Lp F r μ) = smulLeftCLM F g f := by
  ext u
  simp only [Lp.toTemperedDistribution_apply, smulLeftCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_lpSMul (r := r) (hg₂.toLp _) f, hg₂.coeFn_toLp] with x hg hg'
  simp [hg, hg', hg₁, smul_smul, mul_comm]

end Multiplication

/-! ### Derivatives -/

section deriv

variable [NormedAddCommGroup F] [NormedSpace ℂ F]

variable (F) in
/-- The 1-dimensional derivative on tempered distribution as a continuous `ℂ`-linear map. -/
def derivCLM : 𝓢'(ℝ, F) →L[ℂ] 𝓢'(ℝ, F) :=
  PointwiseConvergenceCLM.precomp F (-SchwartzMap.derivCLM ℂ ℂ)

@[simp]
theorem derivCLM_apply_apply (f : 𝓢'(ℝ, F)) (g : 𝓢(ℝ, ℂ)) :
    derivCLM F f g = f (-SchwartzMap.derivCLM ℂ ℂ g) := rfl

variable [RCLike 𝕜] [NormedSpace 𝕜 F]

variable (𝕜) in
theorem derivCLM_toTemperedDistributionCLM_eq (f : 𝓢(ℝ, F)) :
    derivCLM F (f : 𝓢'(ℝ, F)) = SchwartzMap.derivCLM 𝕜 F f := by
  ext1 g
  simp [integral_smul_deriv_right_eq_neg_left, integral_neg]

end deriv

section lineDeriv

open LineDeriv

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℂ F]

/-- The partial derivative (or directional derivative) in the direction `m : E` as a
continuous linear map on tempered distributions. -/
instance instLineDeriv : LineDeriv E 𝓢'(E, F) 𝓢'(E, F) where
  lineDerivOp m f := PointwiseConvergenceCLM.precomp F (-lineDerivOpCLM ℂ 𝓢(E, ℂ) m) f

@[simp]
theorem lineDerivOp_apply_apply (f : 𝓢'(E, F)) (g : 𝓢(E, ℂ)) (m : E) :
    ∂_{m} f g = f (- ∂_{m} g) := rfl

instance : LineDerivAdd E 𝓢'(E, F) 𝓢'(E, F) where
  lineDerivOp_add m := (PointwiseConvergenceCLM.precomp F (-lineDerivOpCLM ℂ 𝓢(E, ℂ) m)).map_add
  lineDerivOp_left_add x y f := by
    ext u
    simp [lineDerivOp_left_add, UniformConvergenceCLM.add_apply, add_comm]

instance : LineDerivSMul ℂ E 𝓢'(E, F) 𝓢'(E, F) where
  lineDerivOp_smul m := (PointwiseConvergenceCLM.precomp F (-lineDerivOpCLM ℂ 𝓢(E, ℂ) m)).map_smul

instance : LineDerivSMul ℝ E 𝓢'(E, F) 𝓢'(E, F) where
  lineDerivOp_smul m :=
    (PointwiseConvergenceCLM.precomp F (-lineDerivOpCLM ℂ 𝓢(E, ℂ) m)).map_smul_of_tower

set_option backward.isDefEq.respectTransparency false in
instance : LineDerivLeftSMul ℝ E 𝓢'(E, F) 𝓢'(E, F) where
  lineDerivOp_left_smul r x f := by
    ext u
    simp [lineDerivOp_left_smul, map_smul_of_tower f]

instance : ContinuousLineDeriv E 𝓢'(E, F) 𝓢'(E, F) where
  continuous_lineDerivOp m :=
    (PointwiseConvergenceCLM.precomp F (-lineDerivOpCLM ℂ 𝓢(E, ℂ) m)).continuous

theorem lineDerivOpCLM_eq (m : E) : lineDerivOpCLM ℂ 𝓢'(E, F) m =
  PointwiseConvergenceCLM.precomp F (-lineDerivOpCLM ℂ 𝓢(E, ℂ) m) := rfl

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

theorem lineDerivOp_toTemperedDistributionCLM_eq (f : 𝓢(E, F)) (m : E) :
    ∂_{m} (toTemperedDistributionCLM E F μ f) = toTemperedDistributionCLM E F μ (∂_{m} f) := by
  ext1 g
  simp [integral_smul_lineDerivOp_right_eq_neg_left g f, integral_neg]

end lineDeriv

/-! ### Laplacian-/

section Laplacian

open Laplacian LineDeriv
open scoped SchwartzMap

variable [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℂ F]

instance : Laplacian 𝓢'(E, F) 𝓢'(E, F) where
  laplacian := LineDeriv.laplacianCLM ℝ E 𝓢'(E, F)

@[simp]
theorem laplacianCLM_apply (f : 𝓢'(E, F)) : laplacianCLM ℂ E 𝓢'(E, F) f = Δ f := by
  simp [laplacianCLM, laplacian]

theorem laplacian_eq_sum [Fintype ι] (b : OrthonormalBasis ι ℝ E) (f : 𝓢'(E, F)) :
    Δ f = ∑ i, ∂_{b i} (∂_{b i} f) := LineDeriv.laplacianCLM_eq_sum b f

@[simp]
theorem laplacian_apply_apply (f : 𝓢'(E, F)) (u : 𝓢(E, ℂ)) : (Δ f) u = f (Δ u) := by
  simp [laplacian_eq_sum (stdOrthonormalBasis ℝ E),
    SchwartzMap.laplacian_eq_sum (stdOrthonormalBasis ℝ E),
    UniformConvergenceCLM.sum_apply, map_neg, neg_neg]

variable [MeasurableSpace E] [BorelSpace E]

/-- The distributional Laplacian and the classical Laplacian coincide on `𝓢(E, F)`. -/
@[simp]
theorem laplacian_toTemperedDistributionCLM_eq (f : 𝓢(E, F)) :
    Δ (f : 𝓢'(E, F)) = Δ f := by
  ext u
  simp [SchwartzMap.integral_smul_laplacian_right_eq_left]

end Laplacian

/-! ### Fourier transform -/

section Fourier

open FourierTransform

variable [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [NormedSpace ℂ F]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

instance instFourierTransform : FourierTransform 𝓢'(E, F) 𝓢'(E, F) where
  fourier := PointwiseConvergenceCLM.precomp F (fourierCLM ℂ 𝓢(E, ℂ))

instance instFourierAdd : FourierAdd 𝓢'(E, F) 𝓢'(E, F) where
  fourier_add := (PointwiseConvergenceCLM.precomp F (fourierCLM ℂ 𝓢(E, ℂ))).map_add

instance instFourierSMul : FourierSMul ℂ 𝓢'(E, F) 𝓢'(E, F) where
  fourier_smul := (PointwiseConvergenceCLM.precomp F (fourierCLM ℂ 𝓢(E, ℂ))).map_smul

instance instContinuousFourier : ContinuousFourier 𝓢'(E, F) 𝓢'(E, F) where
  continuous_fourier := (PointwiseConvergenceCLM.precomp F (fourierCLM ℂ 𝓢(E, ℂ))).cont

@[simp]
theorem fourier_apply (f : 𝓢'(E, F)) (g : 𝓢(E, ℂ)) : 𝓕 f g = f (𝓕 g) := rfl

@[deprecated (since := "2026-01-06")]
alias fourierTransformCLM := FourierTransform.fourierCLM

@[deprecated (since := "2026-01-06")]
alias fourierTransformCLM_apply := FourierTransform.fourierCLM_apply

@[deprecated (since := "2026-01-06")]
alias fourierTransform_apply := fourier_apply

instance instFourierTransformInv : FourierTransformInv 𝓢'(E, F) 𝓢'(E, F) where
  fourierInv := PointwiseConvergenceCLM.precomp F (fourierInvCLM ℂ 𝓢(E, ℂ))

instance instFourierInvAdd : FourierInvAdd 𝓢'(E, F) 𝓢'(E, F) where
  fourierInv_add := (PointwiseConvergenceCLM.precomp F (fourierInvCLM ℂ 𝓢(E, ℂ))).map_add

instance instFourierInvSMul : FourierInvSMul ℂ 𝓢'(E, F) 𝓢'(E, F) where
  fourierInv_smul := (PointwiseConvergenceCLM.precomp F (fourierInvCLM ℂ 𝓢(E, ℂ))).map_smul

instance instContinuousFourierInv : ContinuousFourierInv 𝓢'(E, F) 𝓢'(E, F) where
  continuous_fourierInv := (PointwiseConvergenceCLM.precomp F (fourierInvCLM ℂ 𝓢(E, ℂ))).cont

@[simp]
theorem fourierInv_apply (f : 𝓢'(E, F)) (g : 𝓢(E, ℂ)) : 𝓕⁻ f g = f (𝓕⁻ g) := rfl

@[deprecated (since := "2026-01-06")]
alias fourierTransformInvCLM := FourierTransform.fourierInvCLM

@[deprecated (since := "2026-01-06")]
alias fourierTransformInvCLM_apply := FourierTransform.fourierInvCLM_apply

@[deprecated (since := "2026-01-06")]
alias fourierTransformInv_apply := fourierInv_apply

instance instFourierPair : FourierPair 𝓢'(E, F) 𝓢'(E, F) where
  fourierInv_fourier_eq f := by ext; simp

instance instFourierPairInv : FourierInvPair 𝓢'(E, F) 𝓢'(E, F) where
  fourier_fourierInv_eq f := by ext; simp

section embedding

variable [CompleteSpace F]

/-- The distributional Fourier transform and the classical Fourier transform coincide on
`𝓢(E, F)`. -/
theorem fourier_toTemperedDistributionCLM_eq (f : 𝓢(E, F)) :
    𝓕 (f : 𝓢'(E, F)) = 𝓕 f := by
  ext g
  simpa using integral_fourier_smul_eq g f

@[deprecated (since := "2026-01-14")]
alias fourierTransform_toTemperedDistributionCLM_eq := fourier_toTemperedDistributionCLM_eq

/-- The distributional inverse Fourier transform and the classical inverse Fourier transform
coincide on `𝓢(E, F)`. -/
theorem fourierInv_toTemperedDistributionCLM_eq (f : 𝓢(E, F)) :
    𝓕⁻ (f : 𝓢'(E, F)) = 𝓕⁻ f := calc
  _ = 𝓕⁻ (toTemperedDistributionCLM E F volume (𝓕 (𝓕⁻ f))) := by
    congr; exact (fourier_fourierInv_eq f).symm
  _ = 𝓕⁻ (𝓕 (toTemperedDistributionCLM E F volume (𝓕⁻ f))) := by
    rw [fourier_toTemperedDistributionCLM_eq]
  _ = _ := fourierInv_fourier_eq _

@[deprecated (since := "2026-01-14")]
alias fourierTransformInv_toTemperedDistributionCLM_eq := fourierInv_toTemperedDistributionCLM_eq

end embedding

open LineDeriv Real

/- The line derivative in direction `m` of the Fourier transform is given by the Fourier transform
of the multiplication with `-(2 * π * Complex.I) • (inner ℝ · m)`. -/
theorem lineDerivOp_fourier_eq (f : 𝓢'(E, F)) (m : E) :
    ∂_{m} (𝓕 f) = 𝓕 (- (2 * π * Complex.I) • smulLeftCLM F (inner ℝ · m) f) := by
  ext u
  have : (inner ℝ · m).HasTemperateGrowth := by fun_prop
  simp [SchwartzMap.fourier_lineDerivOp_eq, ← smulLeftCLM_ofReal ℂ this]

/- The Fourier transform of line derivative in direction `m` is given by multiplication of
`(2 * π * Complex.I) • (inner ℝ · m)` with the Fourier transform. -/
theorem fourier_lineDerivOp_eq (f : 𝓢'(E, F)) (m : E) :
    𝓕 (∂_{m} f) = (2 * π * Complex.I) • smulLeftCLM F (inner ℝ · m) (𝓕 f) := by
  ext u
  have : (inner ℝ · m).HasTemperateGrowth := by fun_prop
  simp [SchwartzMap.lineDerivOp_fourier_eq, ← smulLeftCLM_ofReal ℂ this]

/- The line derivative in direction `m` of the inverse Fourier transform is given by the inverse
Fourier transform of the multiplication with `(2 * π * Complex.I) • (inner ℝ · m)`. -/
theorem lineDerivOp_fourierInv_eq (f : 𝓢'(E, F)) (m : E) :
    ∂_{m} (𝓕⁻ f) = 𝓕⁻ ((2 * π * Complex.I) • smulLeftCLM F (inner ℝ · m) f) := by
  ext u
  have : (inner ℝ · m).HasTemperateGrowth := by fun_prop
  simp [SchwartzMap.fourierInv_lineDerivOp_eq, ← smulLeftCLM_ofReal ℂ this]

/- The inverse Fourier transform of line derivative in direction `m` is given by multiplication of
`-(2 * π * Complex.I) • (inner ℝ · m)` with the inverse Fourier transform. -/
theorem fourierInv_lineDerivOp_eq (f : 𝓢'(E, F)) (m : E) :
    𝓕⁻ (∂_{m} f) = -(2 * π * Complex.I) • smulLeftCLM F (inner ℝ · m) (𝓕⁻ f) := by
  ext u
  have : (inner ℝ · m).HasTemperateGrowth := by fun_prop
  simp [SchwartzMap.lineDerivOp_fourierInv_eq, ← smulLeftCLM_ofReal ℂ this]

end Fourier

section DiracDelta

variable [NormedAddCommGroup E]

section definition

variable [NormedSpace ℝ E]

/-- The Dirac delta distribution -/
def delta (x : E) : 𝓢'(E, ℂ) :=
  toPointwiseConvergenceCLM _ _ _ _ <|
    (BoundedContinuousFunction.evalCLM ℂ x).comp (toBoundedContinuousFunctionCLM ℂ E ℂ)

@[deprecated (since := "2025-12-23")]
noncomputable alias _root_.SchwartzMap.delta := delta

@[simp]
theorem delta_apply (x : E) (f : 𝓢(E, ℂ)) : delta x f = f x :=
  rfl

@[deprecated (since := "2025-12-23")]
alias _root_.SchwartzMap.delta_apply := delta_apply

open MeasureTheory MeasureTheory.Measure

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Dirac measure considered as a tempered distribution is the delta distribution. -/
@[simp]
theorem toTemperedDistribution_dirac_eq_delta (x : E) :
  (dirac x).toTemperedDistribution = delta x := by aesop

@[deprecated (since := "2025-12-23")]
alias _root_.SchwartzMap.integralCLM_dirac_eq_delta := toTemperedDistribution_dirac_eq_delta

end definition

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open FourierTransform

/-- The Fourier transform of the delta distribution is equal to the volume.

Informally, this is usually represented as `𝓕 δ = 1`. -/
theorem fourier_delta_zero : 𝓕 (delta (0 : E)) = volume.toTemperedDistribution := by
  ext f
  simp [SchwartzMap.fourier_coe, Real.fourier_eq]

end DiracDelta

end TemperedDistribution
