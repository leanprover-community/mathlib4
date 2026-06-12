/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Probability.Independence.Basic

/-!
# Probability density function

This file defines the probability density function of random variables, by which we mean
measurable functions taking values in a Borel space. The probability density function is defined
as the Radon–Nikodym derivative of the law of `X`. In particular, a measurable function `f`
is said to the probability density function of a random variable `X` if for all measurable
sets `S`, `ℙ(X ∈ S) = ∫ x in S, f x dx`. Probability density functions are one way of describing
the distribution of a random variable, and are useful for calculating probabilities and
finding moments (although the latter is better achieved with moment-generating functions).

This file also defines the continuous uniform distribution and proves some properties about
random variables with this distribution.

## Main definitions

* `MeasureTheory.HasPDF` : A random variable `X : Ω → E` is said to `HasPDF` with
  respect to the measure `ℙ` on `Ω` and `μ` on `E` if the push-forward measure of `ℙ` along `X`
  is absolutely continuous with respect to `μ` and they `HaveLebesgueDecomposition`.
* `MeasureTheory.pdf` : If `X` is a random variable that `HasPDF X ℙ μ`, then `pdf X`
  is the Radon–Nikodym derivative of the push-forward measure of `ℙ` along `X` with respect to `μ`.
* `MeasureTheory.pdf.IsUniform` : A random variable `X` is said to follow the uniform
  distribution if it has a constant probability density function with a compact, non-null support.

## Main results

* `MeasureTheory.pdf.integral_pdf_smul` : Law of the unconscious statistician,
  i.e. if a random variable `X : Ω → E` has pdf `f`, then `𝔼(g(X)) = ∫ x, f x • g x dx` for
  all measurable `g : E → F`.
* `MeasureTheory.pdf.integral_mul_eq_integral` : A real-valued random variable `X` with
  pdf `f` has expectation `∫ x, x * f x dx`.
* `MeasureTheory.pdf.IsUniform.integral_eq` : If `X` follows the uniform distribution with
  its pdf having support `s`, then `X` has expectation `(λ s)⁻¹ * ∫ x in s, x dx` where `λ`
  is the Lebesgue measure.

## TODO

Ultimately, we would also like to define characteristic functions to describe distributions as
it exists for all random variables. However, to define this, we will need Fourier transforms
which we currently do not have.
-/

@[expose] public section


open scoped MeasureTheory NNReal ENNReal

open TopologicalSpace MeasureTheory Measure ProbabilityTheory

noncomputable section

namespace MeasureTheory

variable {Ω E : Type*} [MeasurableSpace E]

/-- A random variable `X : Ω → E` is said to have a probability density function (`HasPDF`)
with respect to the measure `ℙ` on `Ω` and `μ` on `E`
if the push-forward measure of `ℙ` along `X` is absolutely continuous with respect to `μ`
and they have a Lebesgue decomposition (`HaveLebesgueDecomposition`). -/
class HasPDF {m : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω) (μ : Measure E := by volume_tac) :
    Prop where
  protected aemeasurable' : AEMeasurable X ℙ
  protected haveLebesgueDecomposition' : (map X ℙ).HaveLebesgueDecomposition μ
  protected absolutelyContinuous' : map X ℙ ≪ μ

section HasPDF

variable {_ : MeasurableSpace Ω} {X Y : Ω → E} {ℙ : Measure Ω} {μ : Measure E}

theorem hasPDF_iff :
    HasPDF X ℙ μ ↔ AEMeasurable X ℙ ∧ (map X ℙ).HaveLebesgueDecomposition μ ∧ map X ℙ ≪ μ :=
  ⟨fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩⟩

theorem hasPDF_iff_of_aemeasurable (hX : AEMeasurable X ℙ) :
    HasPDF X ℙ μ ↔ (map X ℙ).HaveLebesgueDecomposition μ ∧ map X ℙ ≪ μ := by
  rw [hasPDF_iff]
  simp only [hX, true_and]

variable (X ℙ μ) in
theorem HasPDF.aemeasurable [HasPDF X ℙ μ] : AEMeasurable X ℙ := HasPDF.aemeasurable' μ

instance HasPDF.haveLebesgueDecomposition [HasPDF X ℙ μ] : (map X ℙ).HaveLebesgueDecomposition μ :=
  HasPDF.haveLebesgueDecomposition'

theorem HasPDF.absolutelyContinuous [HasPDF X ℙ μ] : map X ℙ ≪ μ := HasPDF.absolutelyContinuous'

/-- A random variable that `HasPDF` is quasi-measure-preserving. -/
theorem HasPDF.quasiMeasurePreserving_of_measurable (X : Ω → E) (ℙ : Measure Ω) (μ : Measure E)
    [HasPDF X ℙ μ] (h : Measurable X) : QuasiMeasurePreserving X ℙ μ :=
  { measurable := h
    absolutelyContinuous := HasPDF.absolutelyContinuous .. }

theorem HasPDF.congr (hXY : X =ᵐ[ℙ] Y) [hX : HasPDF X ℙ μ] : HasPDF Y ℙ μ :=
  ⟨(HasPDF.aemeasurable X ℙ μ).congr hXY, ℙ.map_congr hXY ▸ hX.haveLebesgueDecomposition,
    ℙ.map_congr hXY ▸ hX.absolutelyContinuous⟩

theorem HasPDF.congr_iff (hXY : X =ᵐ[ℙ] Y) : HasPDF X ℙ μ ↔ HasPDF Y ℙ μ :=
  ⟨fun _ ↦ HasPDF.congr hXY, fun _ ↦ HasPDF.congr hXY.symm⟩

/-- X `HasPDF` if there is a pdf `f` such that `map X ℙ = μ.withDensity f`. -/
theorem hasPDF_of_map_eq_withDensity (hX : AEMeasurable X ℙ) (f : E → ℝ≥0∞) (hf : AEMeasurable f μ)
    (h : map X ℙ = μ.withDensity f) : HasPDF X ℙ μ := by
  refine ⟨hX, ?_, ?_⟩ <;> rw [h]
  · rw [withDensity_congr_ae hf.ae_eq_mk]
    exact haveLebesgueDecomposition_withDensity μ hf.measurable_mk
  · exact withDensity_absolutelyContinuous μ f

end HasPDF

/-- If `X` is a random variable, then `pdf X ℙ μ`
is the Radon–Nikodym derivative of the push-forward measure of `ℙ` along `X` with respect to `μ`. -/
def pdf {_ : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω) (μ : Measure E := by volume_tac) :
    E → ℝ≥0∞ :=
  (map X ℙ).rnDeriv μ

theorem pdf_def {_ : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E} {X : Ω → E} :
    pdf X ℙ μ = (map X ℙ).rnDeriv μ := rfl

theorem pdf_of_not_aemeasurable {_ : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E}
    {X : Ω → E} (hX : ¬AEMeasurable X ℙ) : pdf X ℙ μ =ᵐ[μ] 0 := by
  rw [pdf_def, map_of_not_aemeasurable hX]
  exact rnDeriv_zero μ

theorem pdf_of_not_haveLebesgueDecomposition {_ : MeasurableSpace Ω} {ℙ : Measure Ω}
    {μ : Measure E} {X : Ω → E} (h : ¬(map X ℙ).HaveLebesgueDecomposition μ) : pdf X ℙ μ = 0 :=
  rnDeriv_of_not_haveLebesgueDecomposition h

theorem aemeasurable_of_pdf_ne_zero {m : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E}
    (X : Ω → E) (h : ¬pdf X ℙ μ =ᵐ[μ] 0) : AEMeasurable X ℙ := by
  contrapose h
  exact pdf_of_not_aemeasurable h

theorem hasPDF_of_pdf_ne_zero {m : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E} {X : Ω → E}
    (hac : map X ℙ ≪ μ) (hpdf : ¬pdf X ℙ μ =ᵐ[μ] 0) : HasPDF X ℙ μ := by
  refine ⟨?_, ?_, hac⟩
  · exact aemeasurable_of_pdf_ne_zero X hpdf
  · contrapose hpdf
    have := pdf_of_not_haveLebesgueDecomposition hpdf
    filter_upwards using congrFun this

@[fun_prop]
theorem measurable_pdf {m : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω)
    (μ : Measure E := by volume_tac) : Measurable (pdf X ℙ μ) := by
  exact measurable_rnDeriv _ _

theorem withDensity_pdf_le_map {_ : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω)
    (μ : Measure E := by volume_tac) : μ.withDensity (pdf X ℙ μ) ≤ map X ℙ :=
  withDensity_rnDeriv_le _ _

theorem setLIntegral_pdf_le_map {m : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω)
    (μ : Measure E := by volume_tac) (s : Set E) :
    ∫⁻ x in s, pdf X ℙ μ x ∂μ ≤ map X ℙ s := by
  apply (withDensity_apply_le _ s).trans
  exact withDensity_pdf_le_map _ _ _ s

theorem map_eq_withDensity_pdf {m : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω)
    (μ : Measure E := by volume_tac) [hX : HasPDF X ℙ μ] :
    map X ℙ = μ.withDensity (pdf X ℙ μ) := by
  rw [pdf_def, withDensity_rnDeriv_eq _ _ hX.absolutelyContinuous]

theorem map_eq_setLIntegral_pdf {m : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω)
    (μ : Measure E := by volume_tac) [hX : HasPDF X ℙ μ] {s : Set E}
    (hs : MeasurableSet s) : map X ℙ s = ∫⁻ x in s, pdf X ℙ μ x ∂μ := by
  rw [← withDensity_apply _ hs, map_eq_withDensity_pdf X ℙ μ]

namespace pdf

variable {m : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E}

protected theorem congr {X Y : Ω → E} (hXY : X =ᵐ[ℙ] Y) : pdf X ℙ μ = pdf Y ℙ μ := by
  rw [pdf_def, pdf_def, map_congr hXY]

theorem lintegral_eq_measure_univ {X : Ω → E} [HasPDF X ℙ μ] :
    ∫⁻ x, pdf X ℙ μ x ∂μ = ℙ Set.univ := by
  rw [← setLIntegral_univ, ← map_eq_setLIntegral_pdf X ℙ μ MeasurableSet.univ,
    map_apply_of_aemeasurable (HasPDF.aemeasurable X ℙ μ) MeasurableSet.univ, Set.preimage_univ]

theorem eq_of_map_eq_withDensity [IsFiniteMeasure ℙ] {X : Ω → E} [HasPDF X ℙ μ] (f : E → ℝ≥0∞)
    (hmf : AEMeasurable f μ) : map X ℙ = μ.withDensity f ↔ pdf X ℙ μ =ᵐ[μ] f := by
  rw [map_eq_withDensity_pdf X ℙ μ]
  apply withDensity_eq_iff (measurable_pdf X ℙ μ).aemeasurable hmf
  rw [lintegral_eq_measure_univ]
  exact measure_ne_top _ _

theorem eq_of_map_eq_withDensity' [SigmaFinite μ] {X : Ω → E} [HasPDF X ℙ μ] (f : E → ℝ≥0∞)
    (hmf : AEMeasurable f μ) : map X ℙ = μ.withDensity f ↔ pdf X ℙ μ =ᵐ[μ] f :=
  map_eq_withDensity_pdf X ℙ μ ▸
    withDensity_eq_iff_of_sigmaFinite (measurable_pdf X ℙ μ).aemeasurable hmf

nonrec theorem ae_lt_top [IsFiniteMeasure ℙ] {μ : Measure E} {X : Ω → E} :
    ∀ᵐ x ∂μ, pdf X ℙ μ x < ∞ :=
  rnDeriv_lt_top (map X ℙ) μ

nonrec theorem ofReal_toReal_ae_eq [IsFiniteMeasure ℙ] {X : Ω → E} :
    (fun x => ENNReal.ofReal (pdf X ℙ μ x).toReal) =ᵐ[μ] pdf X ℙ μ :=
  ofReal_toReal_ae_eq ae_lt_top

section IntegralPDFMul

/-- **The Law of the Unconscious Statistician** for nonnegative random variables. -/
theorem lintegral_pdf_mul {X : Ω → E} [HasPDF X ℙ μ] {f : E → ℝ≥0∞}
    (hf : AEMeasurable f μ) : ∫⁻ x, pdf X ℙ μ x * f x ∂μ = ∫⁻ x, f (X x) ∂ℙ := by
  rw [pdf_def,
    ← lintegral_map' (hf.mono_ac HasPDF.absolutelyContinuous) (HasPDF.aemeasurable X ℙ μ),
    lintegral_rnDeriv_mul HasPDF.absolutelyContinuous hf]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem integrable_pdf_smul_iff [IsFiniteMeasure ℙ] {X : Ω → E} [HasPDF X ℙ μ] {f : E → F}
    (hf : AEStronglyMeasurable f μ) :
    Integrable (fun x => (pdf X ℙ μ x).toReal • f x) μ ↔ Integrable (fun x => f (X x)) ℙ := by
  rw [← Function.comp_def,
    ← integrable_map_measure (hf.mono_ac HasPDF.absolutelyContinuous) (HasPDF.aemeasurable X ℙ μ),
    map_eq_withDensity_pdf X ℙ μ, pdf_def, integrable_rnDeriv_smul_iff HasPDF.absolutelyContinuous]
  rw [withDensity_rnDeriv_eq _ _ HasPDF.absolutelyContinuous]

/-- **The Law of the Unconscious Statistician**: Given a random variable `X` and a measurable
function `f`, `f ∘ X` is a random variable with expectation `∫ x, pdf X x • f x ∂μ`
where `μ` is a measure on the codomain of `X`. -/
theorem integral_pdf_smul [IsFiniteMeasure ℙ] {X : Ω → E} [HasPDF X ℙ μ] {f : E → F}
    (hf : AEStronglyMeasurable f μ) : ∫ x, (pdf X ℙ μ x).toReal • f x ∂μ = ∫ x, f (X x) ∂ℙ := by
  rw [← integral_map (HasPDF.aemeasurable X ℙ μ) (hf.mono_ac HasPDF.absolutelyContinuous),
    map_eq_withDensity_pdf X ℙ μ, pdf_def, integral_rnDeriv_smul HasPDF.absolutelyContinuous,
    withDensity_rnDeriv_eq _ _ HasPDF.absolutelyContinuous]

end IntegralPDFMul

section

variable {F : Type*} [MeasurableSpace F] {ν : Measure F} (X : Ω → E) [HasPDF X ℙ μ] {g : E → F}

/-- A random variable that `HasPDF` transformed under a `QuasiMeasurePreserving`
map also `HasPDF` if `(map g (map X ℙ)).HaveLebesgueDecomposition μ`.

`quasiMeasurePreserving_hasPDF` is more useful in the case we are working with a
probability measure and a real-valued random variable. -/
theorem quasiMeasurePreserving_hasPDF (hg : QuasiMeasurePreserving g μ ν)
    (hmap : (map g (map X ℙ)).HaveLebesgueDecomposition ν) : HasPDF (g ∘ X) ℙ ν := by
  have hgm : AEMeasurable g (map X ℙ) := hg.aemeasurable.mono_ac HasPDF.absolutelyContinuous
  rw [hasPDF_iff, ← AEMeasurable.map_map_of_aemeasurable hgm (HasPDF.aemeasurable X ℙ μ)]
  refine ⟨hg.measurable.comp_aemeasurable (HasPDF.aemeasurable _ _ μ), hmap, ?_⟩
  exact (HasPDF.absolutelyContinuous.map hg.1).trans hg.2

theorem quasiMeasurePreserving_hasPDF' [SFinite ℙ] [SigmaFinite ν]
    (hg : QuasiMeasurePreserving g μ ν) : HasPDF (g ∘ X) ℙ ν :=
  quasiMeasurePreserving_hasPDF X hg inferInstance

end

section Real

variable {X : Ω → ℝ}

nonrec theorem _root_.Real.hasPDF_iff [SFinite ℙ] :
    HasPDF X ℙ ↔ AEMeasurable X ℙ ∧ map X ℙ ≪ volume := by
  rw [hasPDF_iff, and_iff_right (inferInstance : HaveLebesgueDecomposition _ _)]

/-- A real-valued random variable `X` `HasPDF X ℙ λ` (where `λ` is the Lebesgue measure) if and
only if the push-forward measure of `ℙ` along `X` is absolutely continuous with respect to `λ`. -/
nonrec theorem _root_.Real.hasPDF_iff_of_aemeasurable [SFinite ℙ] (hX : AEMeasurable X ℙ) :
    HasPDF X ℙ ↔ map X ℙ ≪ volume := by
  rw [Real.hasPDF_iff, and_iff_right hX]

variable [IsFiniteMeasure ℙ]

/-- If `X` is a real-valued random variable that has pdf `f`, then the expectation of `X` equals
`∫ x, x * f x ∂λ` where `λ` is the Lebesgue measure. -/
theorem integral_mul_eq_integral [HasPDF X ℙ] : ∫ x, x * (pdf X ℙ volume x).toReal = ∫ x, X x ∂ℙ :=
  calc
    _ = ∫ x, (pdf X ℙ volume x).toReal * x := by congr with x; exact mul_comm _ _
    _ = _ := integral_pdf_smul measurable_id.aestronglyMeasurable

theorem hasFiniteIntegral_mul {f : ℝ → ℝ} {g : ℝ → ℝ≥0∞} (hg : pdf X ℙ =ᵐ[volume] g)
    (hgi : ∫⁻ x, ‖f x‖ₑ * g x ≠ ∞) :
    HasFiniteIntegral fun x => f x * (pdf X ℙ volume x).toReal := by
  rw [hasFiniteIntegral_iff_enorm]
  have : (fun x => ‖f x‖ₑ * g x) =ᵐ[volume] fun x => ‖f x * (pdf X ℙ volume x).toReal‖ₑ := by
    refine ae_eq_trans ((ae_eq_refl _).fun_mul (ae_eq_trans hg.symm ofReal_toReal_ae_eq.symm)) ?_
    simp_rw [← smul_eq_mul, enorm_smul, smul_eq_mul]
    refine .fun_mul (ae_eq_refl _) ?_
    simp only [Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ae_eq_refl]
  rwa [lt_top_iff_ne_top, ← lintegral_congr_ae this]

end Real

section TwoVariables

variable {F : Type*} [MeasurableSpace F] {ν : Measure F} {X : Ω → E} {Y : Ω → F}

/-- Random variables are independent iff their joint density is a product of marginal densities. -/
theorem indepFun_iff_pdf_prod_eq_pdf_mul_pdf
    [IsFiniteMeasure ℙ] [SigmaFinite μ] [SigmaFinite ν] [HasPDF (fun ω ↦ (X ω, Y ω)) ℙ (μ.prod ν)] :
    IndepFun X Y ℙ ↔
      pdf (fun ω ↦ (X ω, Y ω)) ℙ (μ.prod ν) =ᵐ[μ.prod ν] fun z ↦ pdf X ℙ μ z.1 * pdf Y ℙ ν z.2 := by
  have : HasPDF X ℙ μ := quasiMeasurePreserving_hasPDF' (μ := μ.prod ν) (fun ω ↦ (X ω, Y ω))
    quasiMeasurePreserving_fst
  have : HasPDF Y ℙ ν := quasiMeasurePreserving_hasPDF' (μ := μ.prod ν) (fun ω ↦ (X ω, Y ω))
    quasiMeasurePreserving_snd
  have h₀ : (ℙ.map X).prod (ℙ.map Y) =
      (μ.prod ν).withDensity fun z ↦ pdf X ℙ μ z.1 * pdf Y ℙ ν z.2 :=
    prod_eq fun s t hs ht ↦ by rw [withDensity_apply _ (hs.prod ht), ← prod_restrict,
      lintegral_prod_mul (measurable_pdf X ℙ μ).aemeasurable (measurable_pdf Y ℙ ν).aemeasurable,
      map_eq_setLIntegral_pdf X ℙ μ hs, map_eq_setLIntegral_pdf Y ℙ ν ht]
  rw [indepFun_iff_map_prod_eq_prod_map_map (HasPDF.aemeasurable X ℙ μ) (HasPDF.aemeasurable Y ℙ ν),
    ← eq_of_map_eq_withDensity, h₀]
  exact (((measurable_pdf X ℙ μ).comp measurable_fst).mul
    ((measurable_pdf Y ℙ ν).comp measurable_snd)).aemeasurable

end TwoVariables

end pdf

end MeasureTheory

section Group

namespace ProbabilityTheory

variable {Ω G : Type*} {mΩ : MeasurableSpace Ω} {ℙ : Measure Ω} [Group G] {mG : MeasurableSpace G}
  [MeasurableMul₂ G] [MeasurableInv G] {μ : Measure G} [IsMulLeftInvariant μ] {X Y : Ω → G}

@[to_additive]
theorem IndepFun.mul_hasPDF' [SFinite μ] [HasPDF X ℙ μ] [HasPDF Y ℙ μ]
    (σX : SigmaFinite (ℙ.map X)) (σY : SigmaFinite (ℙ.map Y)) (hXY : IndepFun X Y ℙ) :
    HasPDF (X * Y) ℙ μ := by
  have : AEMeasurable X ℙ := HasPDF.aemeasurable' μ
  have : AEMeasurable Y ℙ := HasPDF.aemeasurable' μ
  rw [hasPDF_iff_of_aemeasurable (by fun_prop),
    hXY.map_mul_eq_map_mconv_map₀' (by fun_prop) (by fun_prop) σX σY]
  refine ⟨?_, mconv_absolutelyContinuous HasPDF.absolutelyContinuous⟩
  apply HaveLebesgueDecomposition.mconv <;> exact HasPDF.absolutelyContinuous

@[to_additive]
theorem IndepFun.mul_hasPDF [SFinite μ] [HasPDF X ℙ μ] [HasPDF Y ℙ μ] [IsFiniteMeasure ℙ]
  (hXY : IndepFun X Y ℙ) : HasPDF (X * Y) ℙ μ := by
  apply hXY.mul_hasPDF' <;> apply IsFiniteMeasure.toSigmaFinite

@[to_additive]
theorem IndepFun.pdf_mul_eq_mlconvolution_pdf' [SigmaFinite μ] [HasPDF X ℙ μ] [HasPDF Y ℙ μ]
    (σX : SigmaFinite (ℙ.map X)) (σY : SigmaFinite (ℙ.map Y)) (hXY : IndepFun X Y ℙ) :
    pdf (X * Y) ℙ μ =ᵐ[μ] pdf X ℙ μ ⋆ₘₗ[μ] pdf Y ℙ μ := by
  rw [pdf, hXY.map_mul_eq_map_mconv_map₀' (HasPDF.aemeasurable' μ) (HasPDF.aemeasurable' μ) σX σY]
  apply rnDeriv_mconv' <;> exact HasPDF.absolutelyContinuous

@[to_additive]
theorem IndepFun.pdf_mul_eq_mlconvolution_pdf [SFinite μ] [HasPDF X ℙ μ] [HasPDF Y ℙ μ]
    [IsFiniteMeasure ℙ] (hXY : IndepFun X Y ℙ) :
    pdf (X * Y) ℙ μ =ᵐ[μ] pdf X ℙ μ ⋆ₘₗ[μ] pdf Y ℙ μ := by
  rw [pdf, hXY.map_mul_eq_map_mconv_map₀ (HasPDF.aemeasurable' μ) (HasPDF.aemeasurable' μ)]
  apply rnDeriv_mconv <;> exact HasPDF.absolutelyContinuous

end ProbabilityTheory

end Group
