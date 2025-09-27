/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.Holder

/-!
# TemperedDistribution

## Main definitions

* `TemperedDistribution 𝕜 E F V`: The space `𝓢(E, F) →L[𝕜] V` with the weak operator topology
* `TemperedDistribution.derivCLM`: The one-dimensional distributional derivative
* `TemperedDistribution.pderivCLM`: Partial distributional derivatives
* `SchwartzMap.toTemperedDistributionCLM`: The canonical embedding of `𝓢(E, F)` into
`𝓢'(𝕜, E, F →L[𝕜] V, V)`.
* `Function.HasTemperateGrowth.toTemperedDistribution`: Every function of temperate growth is a
tempered distribution.
* `MeasureTheory.Measure.HasTemperateGrowth`: Every measure of temperate growth is a tempered
distribution.

## Main statements

* `derivCLM_toTemperedDistributionCLM_eq`: The equality of the distributional derivative and the
classical derivative.

## Notation

* `𝓢'(𝕜, E, F, V)`: The space of tempered distributions `TemperedDistribution 𝕜 E F V` localized
in `SchwartzSpace`



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

noncomputable section

open SchwartzMap ContinuousLinearMap
open MeasureTheory MeasureTheory.Measure

open scoped Nat NNReal ContDiff

variable {𝕜 𝕜' D E F G V : Type*}

variable [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup V]

section definition

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace 𝕜 V] [NormedSpace 𝕜 F]
variable (𝕜 E F V)

abbrev TemperedDistribution := 𝓢(E, F) →WOT[𝕜] V

scoped[SchwartzMap] notation "𝓢'(" 𝕜 ", " E ", " F ", " V ")" => TemperedDistribution 𝕜 E F V

end definition

section DiracDelta

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace 𝕜 V] [NormedSpace 𝕜 F]

variable (𝕜 F) in
/-- The Dirac delta distribution -/
def delta' (x : E) : 𝓢'(𝕜, E, F, F) :=
  ContinuousLinearMap.toWOT 𝕜 𝓢(E, F) F
    ((BoundedContinuousFunction.evalCLM 𝕜 x).comp (toBoundedContinuousFunctionCLM 𝕜 E F))

@[simp]
theorem delta'_apply (x₀ : E) (f : 𝓢(E, F)) : delta' 𝕜 F x₀ f = f x₀ :=
  rfl

end DiracDelta

namespace SchwartzMap

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace 𝕜 V] [NormedSpace 𝕜 F]

theorem hasTemperateGrowth (f : 𝓢(E, F)) : Function.HasTemperateGrowth f := by
  constructor
  · exact smooth f ⊤
  intro n
  rcases f.decay 0 n with ⟨C, Cpos, hC⟩
  use 0, C
  intro x
  specialize hC x
  simp only [pow_zero, one_mul, mul_one] at hC ⊢
  assumption

section pairing

variable [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]

def pairingLM : 𝓢(E, F) →ₗ[𝕜] 𝓢(E, F →L[𝕜] V) →L[𝕜] 𝓢(E, V) where
  toFun f := bilinLeftCLM (.id 𝕜 _) f.hasTemperateGrowth
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

theorem pairingLM_apply (f : 𝓢(E, F)) (g : 𝓢(E, F →L[𝕜] V)) :
  pairingLM f g = fun x => g x (f x) := rfl

@[simp]
theorem pairingLM_apply_apply (f : 𝓢(E, F)) (g : 𝓢(E, F →L[𝕜] V)) (x : E) :
  pairingLM f g x = g x (f x) := rfl

end pairing

open scoped ENNReal
open MeasureTheory

section integration_by_parts

variable [NormedSpace ℝ V]

theorem memLp_of_bilin (L : E →L[ℝ] F →L[ℝ] V) (f : 𝓢(ℝ, E)) (g : 𝓢(ℝ, F)) (p : ℝ≥0∞) :
    MemLp (fun x ↦ L (f x) (g x)) p := by
  exact MeasureTheory.MemLp.of_bilin (r := p) (L · ·) ‖L‖₊ (f.memLp p) (g.memLp ∞)
    (L.aestronglyMeasurable_comp₂ (f.memLp p).1 (g.memLp ∞).1) (.of_forall fun _ ↦ L.le_opNorm₂ _ _)

theorem hasDerivAt (f : 𝓢(ℝ, F)) (x : ℝ) : HasDerivAt f (deriv f x) x := by
  simp only [hasDerivAt_deriv_iff]
  exact f.differentiableAt

theorem integral_bilinear_deriv_right_eq_neg_left (f : 𝓢(ℝ, E)) (g : 𝓢(ℝ, F))
    (L : E →L[ℝ] F →L[ℝ] V) :
    ∫ (x : ℝ), (L (f x)) (deriv g x) = -∫ (x : ℝ), (L (deriv f x)) (g x) := by
  apply MeasureTheory.integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable f.hasDerivAt
    g.hasDerivAt
  all_goals rw [← memLp_one_iff_integrable]
  · exact (memLp_of_bilin L f (derivCLM ℝ g) 1)
  · exact (memLp_of_bilin L (derivCLM ℝ f) g 1)
  · exact (memLp_of_bilin L f g 1)

theorem integral_clm_comp_deriv_right_eq_neg_left (f : 𝓢(ℝ, F)) (g : 𝓢(ℝ, F →L[𝕜] V)) :
    ∫ (x : ℝ), (g x) (deriv f x) = -∫ (x : ℝ), (deriv g x) (f x) :=
  integral_bilinear_deriv_right_eq_neg_left g f
    ((ContinuousLinearMap.id 𝕜 (F →L[𝕜] V)).bilinearRestrictScalars ℝ)

end integration_by_parts

end SchwartzMap

section pairingCLM


variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace 𝕜 V] [NormedSpace 𝕜 F]
variable [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]


def pairingCLM (g : 𝓢(E, F →L[𝕜] V)) : 𝓢(E, F) →L[𝕜] 𝓢(E, V) :=
  mkCLM (fun f => pairingLM f g)
  (fun _ _ _ => by simp only [map_add, ContinuousLinearMap.add_apply, SchwartzMap.add_apply,
    pairingLM_apply_apply])
  (fun _ _ _ => by simp only [map_smul, coe_smul', Pi.smul_apply, SchwartzMap.smul_apply,
    pairingLM_apply_apply, RingHom.id_apply])
  (fun f => by
    apply ((ContinuousLinearMap.restrictScalarsL _ F _ ℝ ℝ).contDiff.fun_comp
      (g.smooth ⊤)).clm_apply (f.smooth ⊤))
  (by
      intro (k, n)
      simp only [pairingLM_apply]
      use Finset.Iic (k, n), (Finset.card (Finset.range (n+1))) • ((2 ^ n) *
        (((Finset.Iic (0, n)).sup (schwartzSeminormFamily 𝕜 _ _)) g) * (2 ^ k)), by positivity
      intro f x
      have := ((ContinuousLinearMap.id 𝕜 (F →L[𝕜] V)).bilinearRestrictScalars
          ℝ).norm_iteratedFDeriv_le_of_bilinear_of_le_one (g.smooth ⊤) (f.smooth ⊤) x (n := n) (by
        simp only [WithTop.le_def, WithTop.coe_eq_coe, forall_eq', le_top, and_true]
        use n
        simp only [WithTop.coe_natCast]) (by simp only [norm_bilinearRestrictScalars, norm_id_le])
      simp only [bilinearRestrictScalars_apply_apply, coe_id', id_eq] at this
      grw [this]
      rw [Finset.mul_sum, smul_mul_assoc]
      apply Finset.sum_le_card_nsmul
      intro i hi
      simp only [Finset.mem_range] at hi
      have hg : ‖iteratedFDeriv ℝ i g x‖ ≤
          ((Finset.Iic (0, n)).sup (schwartzSeminormFamily 𝕜 _ _)) g := by
        grw [norm_iteratedFDeriv_le_seminorm 𝕜 g]
        rw [← schwartzSeminormFamily_apply]
        apply Seminorm.le_finset_sup_apply
        simp only [Finset.mem_Iic, Prod.mk_le_mk, le_refl, true_and]
        exact Nat.le_of_lt_succ hi
      grw [Nat.choose_le_two_pow _ _, hg]
      move_mul [((Finset.Iic (0, n)).sup (schwartzSeminormFamily 𝕜 _ _)) g]
      apply mul_le_mul_of_nonneg_right _ (apply_nonneg _ _)
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      move_mul [2 ^ n]
      have hf : ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖ ≤
          ((Finset.Iic (k, n)).sup (schwartzSeminormFamily 𝕜 _ _)) f := by
        grw [le_seminorm 𝕜]
        rw [← schwartzSeminormFamily_apply]
        apply Seminorm.le_finset_sup_apply
        simp only [Finset.mem_Iic, Prod.mk_le_mk, le_refl, tsub_le_iff_right,
          le_add_iff_nonneg_right, zero_le, and_self]
      grw [hf]
      move_mul [((Finset.Iic (k, n)).sup (schwartzSeminormFamily 𝕜 _ _)) f]
      apply mul_le_mul_of_nonneg_right _ (apply_nonneg _ _)
      exact le_mul_of_one_le_right (pow_nonneg zero_le_two _) (one_le_pow₀ one_le_two))

end pairingCLM

section measure_theory

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace 𝕜 V] [NormedSpace 𝕜 F]
variable [MeasurableSpace E] {μ : Measure E} [hμ : μ.HasTemperateGrowth]
variable [BorelSpace E] [SecondCountableTopology E]

variable (𝕜 F μ) in
def MeasureTheory.Measure.toTemperedDistribution : 𝓢'(𝕜, E, F, F) :=
  (toWOT _ _ _) (integralCLM 𝕜 μ)

variable (𝕜) in
@[simp]
theorem MeasureTheory.Measure.toTemperedDistribution_apply (g : 𝓢(E, F)) :
    Measure.toTemperedDistribution 𝕜 F μ g = ∫ (x : E), g x ∂μ := by
  rfl

end measure_theory

namespace Function.HasTemperateGrowth

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace 𝕜 V] [NormedSpace 𝕜 F]
variable [MeasurableSpace E] {μ : Measure E} [hμ : μ.HasTemperateGrowth]
variable [BorelSpace E] [SecondCountableTopology E]

variable [NormedSpace ℝ V]

variable (𝕜 V) in
def toTemperedDistribution {f : E → F} (hf : f.HasTemperateGrowth) : 𝓢'(𝕜, E, F →L[𝕜] V, V) :=
    (ContinuousLinearMap.toWOT _ _ _) ((integralCLM 𝕜 μ) ∘L (bilinLeftCLM (.id 𝕜 _) hf))

@[simp]
theorem toTemperedDistribution_apply {f : E → F} (hf : f.HasTemperateGrowth) (g : 𝓢(E, F →L[𝕜] V)) :
    toTemperedDistribution 𝕜 V (μ := μ) hf g = ∫ (x : E), (g x) (f x) ∂μ := by
  rfl

end Function.HasTemperateGrowth

section LpSpace

namespace MeasureTheory.Lp

variable [NormedSpace ℝ E] [NormedSpace 𝕜 V] [NormedSpace 𝕜 F]
variable [MeasurableSpace E] {μ : Measure E} [hμ : μ.HasTemperateGrowth]
variable [BorelSpace E] [SecondCountableTopology E]
variable [NormedSpace ℝ V] [CompleteSpace V]

theorem foo (p : ENNReal) [hp : Fact (1 ≤ p)] : p.HolderConjugate (1 - p⁻¹)⁻¹ := by
  rw [ENNReal.holderConjugate_iff]
  simp only [inv_inv]
  refine add_tsub_cancel_of_le ?_
  simpa only [ENNReal.inv_le_one] using hp.elim

/-- Create a tempered distribution from a L^p function.

This is a helper definition with unnecessary parameters. -/
def toTemperedDistribution_aux (p q : ENNReal) (hp : Fact (1 ≤ p)) (hq : Fact (1 ≤ q))
    (hpq : ENNReal.HolderConjugate p q) (f : Lp F p μ) :
    𝓢'(𝕜, E, F →L[𝕜] V, V) :=
  (ContinuousLinearMap.toWOT _ _ _)
    (((ContinuousLinearMap.id 𝕜 (F →L[𝕜] V)).flip.lpPairing μ p q f) ∘L (toLpCLM 𝕜 (F →L[𝕜] V) q μ))

variable (𝕜 V) in
/-- Create a tempered distribution from a L^p function. -/
def toTemperedDistribution {p : ENNReal} [hp : Fact (1 ≤ p)] (f : Lp F p μ) :
    𝓢'(𝕜, E, F →L[𝕜] V, V) :=
  toTemperedDistribution_aux p ((1 - p⁻¹)⁻¹) hp (by simp [fact_iff]) (foo p) f

@[simp]
theorem toTemperedDistribution_apply {p : ENNReal} [hp : Fact (1 ≤ p)] (f : Lp F p μ)
    (g : 𝓢(E, F →L[𝕜] V)) :
    (toTemperedDistribution 𝕜 V f) g = ∫ (x : E), ((g.toLp (1 - p⁻¹)⁻¹ μ) x) (f x) ∂μ := by
  unfold Lp.toTemperedDistribution Lp.toTemperedDistribution_aux
  simp [toWOT_apply, lpPairing_eq_integral]

variable (𝕜 F V μ) in
/-- The natural embedding of L^p into tempered distributions. -/
def toTemperedDistributionCLM (p : ENNReal) [hp : Fact (1 ≤ p)] :
    Lp F p μ →L[𝕜] 𝓢'(𝕜, E, F →L[𝕜] V, V) where
  toFun := toTemperedDistribution 𝕜 V
  map_add' f g := by
    ext x
    unfold Lp.toTemperedDistribution Lp.toTemperedDistribution_aux
    simp only [map_add, add_comp, ContinuousLinearMapWOT.add_apply]
  map_smul' a f := by
    ext x
    unfold Lp.toTemperedDistribution Lp.toTemperedDistribution_aux
    simp
  cont := by
    apply ContinuousLinearMapWOT.continuous_of_dual_apply_continuous
    intro g y
    apply y.cont.comp
    set q := (1 - p⁻¹)⁻¹
    have hq : Fact (1 ≤ q) := by simp [q, fact_iff]
    have hpq : ENNReal.HolderConjugate p q := foo p
    exact (((ContinuousLinearMap.id 𝕜 (F →L[𝕜] V)).flip.lpPairing μ p q).flip (g.toLp q μ)).cont

@[simp]
theorem toTemperedDistributionCLM_apply {p : ENNReal} [hp : Fact (1 ≤ p)] (f : Lp F p μ) :
    toTemperedDistributionCLM 𝕜 F V μ p f = toTemperedDistribution 𝕜 V f := rfl

end MeasureTheory.Lp

end LpSpace

namespace SchwartzMap

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace 𝕜 V] [NormedSpace 𝕜 F]
variable [MeasurableSpace E]
variable [BorelSpace E] [SecondCountableTopology E]

variable [NormedSpace ℝ V]

variable (𝕜 E F V) in
def toTemperedDistributionCLM (μ : Measure E := by volume_tac) [hμ : μ.HasTemperateGrowth] :
    𝓢(E, F) →L[𝕜] 𝓢'(𝕜, E, F →L[𝕜] V, V) where
  toFun f := (toWOT _ _ _) ((integralCLM 𝕜 μ) ∘L (pairingLM f))
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  cont := by
    apply ContinuousLinearMapWOT.continuous_of_dual_apply_continuous
    intro g y
    exact y.cont.comp ((integralCLM 𝕜 μ).cont.comp (pairingCLM g).cont)

variable (f : 𝓢(E, F)) (g : 𝓢(E, F →L[𝕜] V)) (x : E)

@[simp]
theorem toTemperedDistributionCLM_apply_apply (μ : Measure E := by volume_tac)
    [hμ : μ.HasTemperateGrowth] (f : 𝓢(E, F)) (g : 𝓢(E, F →L[𝕜] V)) :
    toTemperedDistributionCLM 𝕜 E F V μ f g = ∫ (x : E), (g x) (f x) ∂μ := by
  rfl

end SchwartzMap

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace 𝕜 V] [NormedSpace 𝕜 F]

def mkCLM (A : (𝓢(E, F) →L[𝕜] V) →ₗ[𝕜] (𝓢(E, F) →L[𝕜] V))
  (hbound : ∀ (f : 𝓢(E, F)) (a : V →L[𝕜] 𝕜), ∃ (s : Finset (𝓢(E, F) × (V →L[𝕜] 𝕜))) (C : ℝ≥0),
  ∀ (B : 𝓢(E, F) →L[𝕜] V), ∃ (g : 𝓢(E, F)) (b : V →L[𝕜] 𝕜) (_hb : (g, b) ∈ s),
  ‖a ((A B) f)‖ ≤ C • ‖b (B g)‖) : 𝓢'(𝕜, E, F, V) →L[𝕜] 𝓢'(𝕜, E, F, V) where
  __ := (toWOT _ _ _).toLinearMap.comp (A.comp (toWOT _ _ _).symm.toLinearMap)
  cont := by
    apply Seminorm.continuous_from_bounded ContinuousLinearMapWOT.withSeminorms
      ContinuousLinearMapWOT.withSeminorms
    intro (f, a)
    rcases hbound f a with ⟨s, C, h⟩
    use s, C
    rw [← Seminorm.finset_sup_smul]
    intro B
    rcases h ((toWOT _ _ _).symm B) with ⟨g, b, hb, h'⟩
    refine le_trans ?_ (Seminorm.le_finset_sup_apply hb)
    unfold ContinuousLinearMapWOT.seminormFamily
    simpa using h'

section deriv


variable [NormedSpace ℝ E]

/-- The 1-dimensional derivative on Schwartz space as a continuous `𝕜`-linear map. -/
def derivCLM : 𝓢'(𝕜, ℝ, F, V) →L[𝕜] 𝓢'(𝕜, ℝ, F, V) :=
  mkCLM
    {toFun f := f.comp (-SchwartzMap.derivCLM 𝕜), map_add' f g := by simp [add_comm],
      map_smul' := by simp}
    (by
      intro f a
      use {(SchwartzMap.derivCLM 𝕜 f, a)}, 1
      exact fun _ ↦ ⟨SchwartzMap.derivCLM 𝕜 f, a, by simp, by simp⟩)

@[simp]
theorem derivCLM_apply_apply (f : 𝓢'(𝕜, ℝ, F, V)) (g : 𝓢(ℝ, F)) :
    derivCLM f g = f (-derivCLM 𝕜 g) := rfl

open scoped ENNReal

variable [NormedSpace ℝ V]

/-- The distributional derivative and the classical derivative coincide on `𝓢(ℝ, F)`. -/
theorem derivCLM_toTemperedDistributionCLM_eq (f : 𝓢(ℝ, F)) :
    derivCLM (toTemperedDistributionCLM 𝕜 ℝ F V volume f) =
    toTemperedDistributionCLM 𝕜 ℝ F V volume (SchwartzMap.derivCLM 𝕜 f) := by
  ext
  simp [integral_clm_comp_deriv_right_eq_neg_left, integral_neg]

end deriv

section pderiv

variable (𝕜) in
def TemperedDistribution.pderivCLM (m : E) : 𝓢'(𝕜, E, F, V) →L[𝕜] 𝓢'(𝕜, E, F, V) :=
  mkCLM
    {toFun f := f.comp (-SchwartzMap.pderivCLM 𝕜 m), map_add' f g := by simp [add_comm],
      map_smul' := by simp }
    (by
      intro f a
      use {(SchwartzMap.pderivCLM 𝕜 m f, a)}, 1
      exact fun _ ↦ ⟨SchwartzMap.pderivCLM 𝕜 m f, a, by simp, by simp⟩)

lemma pderivCLM_apply (m : E) (f : 𝓢'(𝕜, E, F, V)) (g : 𝓢(E, F)) :
    TemperedDistribution.pderivCLM 𝕜 m f g = f (-SchwartzMap.pderivCLM 𝕜 m g) := by rfl

end pderiv

section fourier

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]

def fourierTransformCLM : 𝓢'(𝕜, H, E, V) →L[𝕜] 𝓢'(𝕜, H, E, V) :=
  mkCLM
    {toFun f := f.comp (SchwartzMap.fourierTransformCLM 𝕜), map_add' f g := by simp,
      map_smul' := by simp}
    (by
      intro f x
      use {(SchwartzMap.fourierTransformCLM 𝕜 f, x)}, 1
      simp)

@[simp]
theorem fourierTransformCLM_apply_apply (f : 𝓢'(𝕜, H, E, V)) (g : 𝓢(H, E)) :
    fourierTransformCLM f g = f (g.fourierTransformCLM 𝕜) := rfl

variable (f : 𝓢(H, E))

variable [NormedSpace ℂ V]
variable [CompleteSpace E] [CompleteSpace V]

/-- The distributional Fourier transform and the classical Fourier transform coincide on
`𝓢(ℝ, F)`. -/
theorem fourierTransformCLM_toTemperedDistributionCLM_eq (f : 𝓢(H, E)) :
    _root_.fourierTransformCLM (toTemperedDistributionCLM ℂ H E V volume f) =
    toTemperedDistributionCLM ℂ H E V volume (f.fourierTransformCLM ℂ) := by
  ext g
  congr 1
  exact integral_bilin_fourierIntegral_eq_flip g f (.id ℂ _)

example : fourierTransformCLM (delta' 𝕜 E (0 : H)) = volume.toTemperedDistribution 𝕜 E := by
  ext f x
  simp [Real.fourierIntegral_eq]

end fourier
