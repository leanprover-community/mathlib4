/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.MeasureTheory.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Probability.Independence.Basic

#align_import probability.density from "leanprover-community/mathlib"@"c14c8fcde993801fca8946b0d80131a1a81d1520"

/-!
# Probability density function

This file defines the probability density function of random variables, by which we mean
measurable functions taking values in a Borel space. In particular, a measurable function `f`
is said to the probability density function of a random variable `X` if for all measurable
sets `S`, `ℙ(X ∈ S) = ∫ x in S, f x dx`. Probability density functions are one way of describing
the distribution of a random variable, and are useful for calculating probabilities and
finding moments (although the latter is better achieved with moment generating functions).

This file also defines the continuous uniform distribution and proves some properties about
random variables with this distribution.

## Main definitions

* `MeasureTheory.HasPDF` : A random variable `X : Ω → E` is said to `HasPDF` with
  respect to the measure `ℙ` on `Ω` and `μ` on `E` if there exists a measurable function `f`
  such that the push-forward measure of `ℙ` along `X` equals `μ.withDensity f`.
* `MeasureTheory.pdf` : If `X` is a random variable that `HasPDF X ℙ μ`, then `pdf X`
  is the measurable function `f` such that the push-forward measure of `ℙ` along `X` equals
  `μ.withDensity f`.
* `MeasureTheory.pdf.IsUniform` : A random variable `X` is said to follow the uniform
  distribution if it has a constant probability density function with a compact, non-null support.

## Main results

* `MeasureTheory.pdf.integral_fun_mul_eq_integral` : Law of the unconscious statistician,
  i.e. if a random variable `X : Ω → E` has pdf `f`, then `𝔼(g(X)) = ∫ x, g x * f x dx` for
  all measurable `g : E → ℝ`.
* `MeasureTheory.pdf.integral_mul_eq_integral` : A real-valued random variable `X` with
  pdf `f` has expectation `∫ x, x * f x dx`.
* `MeasureTheory.pdf.IsUniform.integral_eq` : If `X` follows the uniform distribution with
  its pdf having support `s`, then `X` has expectation `(λ s)⁻¹ * ∫ x in s, x dx` where `λ`
  is the Lebesgue measure.

## TODOs

Ultimately, we would also like to define characteristic functions to describe distributions as
it exists for all random variables. However, to define this, we will need Fourier transforms
which we currently do not have.
-/


open scoped Classical MeasureTheory NNReal ENNReal

open TopologicalSpace MeasureTheory.Measure

noncomputable section

namespace MeasureTheory

variable {Ω E : Type*} [MeasurableSpace E]

/-- A random variable `X : Ω → E` is said to `HasPDF` with respect to the measure `ℙ` on `Ω` and
`μ` on `E` if there exists a measurable function `f` such that the push-forward measure of `ℙ`
along `X` equals `μ.withDensity f`. -/
class HasPDF {m : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω)
    (μ : Measure E := by volume_tac) : Prop where
  -- porting note: TODO: split into fields `Measurable` and `exists_pdf`
  pdf' : Measurable X ∧ ∃ f : E → ℝ≥0∞, Measurable f ∧ map X ℙ = μ.withDensity f
#align measure_theory.has_pdf MeasureTheory.HasPDF

@[measurability]
theorem HasPDF.measurable {_ : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω)
    (μ : Measure E := by volume_tac) [hX : HasPDF X ℙ μ] :
    Measurable X :=
  hX.pdf'.1
#align measure_theory.has_pdf.measurable MeasureTheory.HasPDF.measurable

/-- If `X` is a random variable that `HasPDF X ℙ μ`, then `pdf X` is the measurable function `f`
such that the push-forward measure of `ℙ` along `X` equals `μ.withDensity f`. -/
def pdf {_ : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω) (μ : Measure E := by volume_tac) :
    E → ℝ≥0∞ :=
  if hX : HasPDF X ℙ μ then Classical.choose hX.pdf'.2 else 0
#align measure_theory.pdf MeasureTheory.pdf

theorem pdf_undef {m : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E} {X : Ω → E}
    (h : ¬HasPDF X ℙ μ) : pdf X ℙ μ = 0 := by simp only [pdf, dif_neg h]
#align measure_theory.pdf_undef MeasureTheory.pdf_undef

theorem hasPDF_of_pdf_ne_zero {m : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E} {X : Ω → E}
    (h : pdf X ℙ μ ≠ 0) : HasPDF X ℙ μ := by
  by_contra hpdf
  simp [pdf, hpdf] at h
#align measure_theory.has_pdf_of_pdf_ne_zero MeasureTheory.hasPDF_of_pdf_ne_zero

theorem pdf_eq_zero_of_not_measurable {_ : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E}
    {X : Ω → E} (hX : ¬Measurable X) : pdf X ℙ μ = 0 :=
  pdf_undef fun hpdf => hX hpdf.pdf'.1
#align measure_theory.pdf_eq_zero_of_not_measurable MeasureTheory.pdf_eq_zero_of_not_measurable

theorem measurable_of_pdf_ne_zero {m : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E}
    (X : Ω → E) (h : pdf X ℙ μ ≠ 0) : Measurable X := by
  by_contra hX
  exact h (pdf_eq_zero_of_not_measurable hX)
#align measure_theory.measurable_of_pdf_ne_zero MeasureTheory.measurable_of_pdf_ne_zero

@[measurability]
theorem measurable_pdf {m : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω)
    (μ : Measure E := by volume_tac) : Measurable (pdf X ℙ μ) := by
  unfold pdf
  split_ifs with h
  exacts [(Classical.choose_spec h.1.2).1, measurable_zero]
#align measure_theory.measurable_pdf MeasureTheory.measurable_pdf

theorem map_eq_withDensity_pdf {m : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω)
    (μ : Measure E := by volume_tac) [hX : HasPDF X ℙ μ] :
    Measure.map X ℙ = μ.withDensity (pdf X ℙ μ) := by
  simp only [pdf, dif_pos hX]
  exact (Classical.choose_spec hX.pdf'.2).2
#align measure_theory.map_eq_with_density_pdf MeasureTheory.map_eq_withDensity_pdf

theorem map_eq_set_lintegral_pdf {m : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω)
    (μ : Measure E := by volume_tac) [hX : HasPDF X ℙ μ] {s : Set E}
    (hs : MeasurableSet s) : Measure.map X ℙ s = ∫⁻ x in s, pdf X ℙ μ x ∂μ := by
  rw [← withDensity_apply _ hs, map_eq_withDensity_pdf X ℙ μ]
#align measure_theory.map_eq_set_lintegral_pdf MeasureTheory.map_eq_set_lintegral_pdf

namespace pdf

variable {m : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E}

theorem lintegral_eq_measure_univ {X : Ω → E} [HasPDF X ℙ μ] :
    ∫⁻ x, pdf X ℙ μ x ∂μ = ℙ Set.univ := by
  rw [← set_lintegral_univ, ← map_eq_set_lintegral_pdf X ℙ μ MeasurableSet.univ,
    Measure.map_apply (HasPDF.measurable X ℙ μ) MeasurableSet.univ, Set.preimage_univ]
#align measure_theory.pdf.lintegral_eq_measure_univ MeasureTheory.pdf.lintegral_eq_measure_univ

theorem unique [IsFiniteMeasure ℙ] {X : Ω → E} [HasPDF X ℙ μ] (f : E → ℝ≥0∞)
    (hmf : AEMeasurable f μ) : ℙ.map X = μ.withDensity f ↔ pdf X ℙ μ =ᵐ[μ] f := by
  rw [map_eq_withDensity_pdf X ℙ μ]
  apply withDensity_eq_iff (measurable_pdf X ℙ μ).aemeasurable hmf
  rw [lintegral_eq_measure_univ]
  exact measure_ne_top _ _

theorem unique' [SigmaFinite μ] {X : Ω → E} [HasPDF X ℙ μ] (f : E → ℝ≥0∞) (hmf : AEMeasurable f μ) :
    ℙ.map X = μ.withDensity f ↔ pdf X ℙ μ =ᵐ[μ] f :=
  map_eq_withDensity_pdf X ℙ μ ▸
    withDensity_eq_iff_of_sigmaFinite (measurable_pdf X ℙ μ).aemeasurable hmf

nonrec theorem ae_lt_top [IsFiniteMeasure ℙ] {μ : Measure E} {X : Ω → E} :
    ∀ᵐ x ∂μ, pdf X ℙ μ x < ∞ := by
  by_cases hpdf : HasPDF X ℙ μ
  · haveI := hpdf
    refine' ae_lt_top (measurable_pdf X ℙ μ) _
    rw [lintegral_eq_measure_univ]
    exact measure_ne_top _ _
  · simp [pdf, hpdf]
#align measure_theory.pdf.ae_lt_top MeasureTheory.pdf.ae_lt_top

nonrec theorem ofReal_toReal_ae_eq [IsFiniteMeasure ℙ] {X : Ω → E} :
    (fun x => ENNReal.ofReal (pdf X ℙ μ x).toReal) =ᵐ[μ] pdf X ℙ μ :=
  ofReal_toReal_ae_eq ae_lt_top
#align measure_theory.pdf.of_real_to_real_ae_eq MeasureTheory.pdf.ofReal_toReal_ae_eq

theorem integrable_iff_integrable_mul_pdf [IsFiniteMeasure ℙ] {X : Ω → E} [HasPDF X ℙ μ] {f : E → ℝ}
    (hf : Measurable f) :
    Integrable (fun x => f (X x)) ℙ ↔ Integrable (fun x => f x * (pdf X ℙ μ x).toReal) μ := by
  -- porting note: using `erw` because `rw` doesn't recognize `(f <| X ·)` as `f ∘ X`
  -- https://github.com/leanprover-community/mathlib4/issues/5164
  erw [← integrable_map_measure hf.aestronglyMeasurable (HasPDF.measurable X ℙ μ).aemeasurable,
    map_eq_withDensity_pdf X ℙ μ, integrable_withDensity_iff (measurable_pdf _ _ _) ae_lt_top]
#align measure_theory.pdf.integrable_iff_integrable_mul_pdf MeasureTheory.pdf.integrable_iff_integrable_mul_pdf

/-- **The Law of the Unconscious Statistician**: Given a random variable `X` and a measurable
function `f`, `f ∘ X` is a random variable with expectation `∫ x, f x * pdf X ∂μ`
where `μ` is a measure on the codomain of `X`. -/
theorem integral_fun_mul_eq_integral [IsFiniteMeasure ℙ] {X : Ω → E} [HasPDF X ℙ μ] {f : E → ℝ}
    (hf : Measurable f) : ∫ x, f x * (pdf X ℙ μ x).toReal ∂μ = ∫ x, f (X x) ∂ℙ := by
  by_cases hpdf : Integrable (fun x => f x * (pdf X ℙ μ x).toReal) μ
  · rw [← integral_map (HasPDF.measurable X ℙ μ).aemeasurable hf.aestronglyMeasurable,
      map_eq_withDensity_pdf X ℙ μ, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hpdf,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part,
      lintegral_withDensity_eq_lintegral_mul _ (measurable_pdf X ℙ μ) hf.neg.ennreal_ofReal,
      lintegral_withDensity_eq_lintegral_mul _ (measurable_pdf X ℙ μ) hf.ennreal_ofReal]
    · congr 2
      · have : ∀ x, ENNReal.ofReal (f x * (pdf X ℙ μ x).toReal) =
            ENNReal.ofReal (pdf X ℙ μ x).toReal * ENNReal.ofReal (f x) := fun x ↦ by
          rw [mul_comm, ENNReal.ofReal_mul ENNReal.toReal_nonneg]
        simp_rw [this]
        exact lintegral_congr_ae (Filter.EventuallyEq.mul ofReal_toReal_ae_eq (ae_eq_refl _))
      · have :
          ∀ x,
            ENNReal.ofReal (-(f x * (pdf X ℙ μ x).toReal)) =
              ENNReal.ofReal (pdf X ℙ μ x).toReal * ENNReal.ofReal (-f x) := by
          intro x
          rw [neg_mul_eq_neg_mul, mul_comm, ENNReal.ofReal_mul ENNReal.toReal_nonneg]
        simp_rw [this]
        exact lintegral_congr_ae (Filter.EventuallyEq.mul ofReal_toReal_ae_eq (ae_eq_refl _))
    · refine' ⟨hf.aestronglyMeasurable, _⟩
      rw [HasFiniteIntegral,
        lintegral_withDensity_eq_lintegral_mul _ (measurable_pdf _ _ _)
          hf.nnnorm.coe_nnreal_ennreal]
      have : (fun x => (pdf X ℙ μ * fun x => (‖f x‖₊ : ℝ≥0∞)) x) =ᵐ[μ]
          fun x => ‖f x * (pdf X ℙ μ x).toReal‖₊ := by
        simp_rw [← smul_eq_mul, nnnorm_smul, ENNReal.coe_mul]
        rw [smul_eq_mul, mul_comm]
        refine' Filter.EventuallyEq.mul (ae_eq_refl _) (ae_eq_trans ofReal_toReal_ae_eq.symm _)
        simp only [Real.ennnorm_eq_ofReal ENNReal.toReal_nonneg, ae_eq_refl]
      rw [lintegral_congr_ae this]
      exact hpdf.2
  · rw [integral_undef hpdf, integral_undef]
    rwa [← integrable_iff_integrable_mul_pdf hf] at hpdf
#align measure_theory.pdf.integral_fun_mul_eq_integral MeasureTheory.pdf.integral_fun_mul_eq_integral

theorem map_absolutelyContinuous {X : Ω → E} [HasPDF X ℙ μ] : map X ℙ ≪ μ := by
  rw [map_eq_withDensity_pdf X ℙ μ]; exact withDensity_absolutelyContinuous _ _
#align measure_theory.pdf.map_absolutely_continuous MeasureTheory.pdf.map_absolutelyContinuous

/-- A random variable that `HasPDF` is quasi-measure preserving. -/
theorem to_quasiMeasurePreserving {X : Ω → E} [HasPDF X ℙ μ] : QuasiMeasurePreserving X ℙ μ :=
  { measurable := HasPDF.measurable X ℙ μ
    absolutelyContinuous := map_absolutelyContinuous }
#align measure_theory.pdf.to_quasi_measure_preserving MeasureTheory.pdf.to_quasiMeasurePreserving

theorem haveLebesgueDecomposition_of_hasPDF {X : Ω → E} [hX' : HasPDF X ℙ μ] :
    (map X ℙ).HaveLebesgueDecomposition μ :=
  ⟨⟨⟨0, pdf X ℙ μ⟩, by
      simp only [zero_add, measurable_pdf X ℙ μ, true_and_iff, MutuallySingular.zero_left,
        map_eq_withDensity_pdf X ℙ μ]⟩⟩
#align measure_theory.pdf.have_lebesgue_decomposition_of_has_pdf MeasureTheory.pdf.haveLebesgueDecomposition_of_hasPDF

theorem hasPDF_iff {X : Ω → E} :
    HasPDF X ℙ μ ↔ Measurable X ∧ (map X ℙ).HaveLebesgueDecomposition μ ∧ map X ℙ ≪ μ := by
  constructor
  · intro hX'
    exact ⟨hX'.pdf'.1, haveLebesgueDecomposition_of_hasPDF, map_absolutelyContinuous⟩
  · rintro ⟨hX, h_decomp, h⟩
    haveI := h_decomp
    refine' ⟨⟨hX, (Measure.map X ℙ).rnDeriv μ, measurable_rnDeriv _ _, _⟩⟩
    rwa [withDensity_rnDeriv_eq]
#align measure_theory.pdf.has_pdf_iff MeasureTheory.pdf.hasPDF_iff

theorem hasPDF_iff_of_measurable {X : Ω → E} (hX : Measurable X) :
    HasPDF X ℙ μ ↔ (map X ℙ).HaveLebesgueDecomposition μ ∧ map X ℙ ≪ μ := by
  rw [hasPDF_iff]
  simp only [hX, true_and]
#align measure_theory.pdf.has_pdf_iff_of_measurable MeasureTheory.pdf.hasPDF_iff_of_measurable

section

variable {F : Type*} [MeasurableSpace F] {ν : Measure F}

/-- A random variable that `HasPDF` transformed under a `QuasiMeasurePreserving`
map also `HasPDF` if `(map g (map X ℙ)).HaveLebesgueDecomposition μ`.

`quasiMeasurePreserving_hasPDF` is more useful in the case we are working with a
probability measure and a real-valued random variable. -/
theorem quasiMeasurePreserving_hasPDF {X : Ω → E} [HasPDF X ℙ μ] {g : E → F}
    (hg : QuasiMeasurePreserving g μ ν) (hmap : (map g (map X ℙ)).HaveLebesgueDecomposition ν) :
    HasPDF (g ∘ X) ℙ ν := by
  rw [hasPDF_iff, ← map_map hg.measurable (HasPDF.measurable X ℙ μ)]
  refine' ⟨hg.measurable.comp (HasPDF.measurable X ℙ μ), hmap, _⟩
  rw [map_eq_withDensity_pdf X ℙ μ]
  refine' AbsolutelyContinuous.mk fun s hsm hs => _
  rw [map_apply hg.measurable hsm, withDensity_apply _ (hg.measurable hsm)]
  have := hg.absolutelyContinuous hs
  rw [map_apply hg.measurable hsm] at this
  exact set_lintegral_measure_zero _ _ this
#align measure_theory.pdf.quasi_measure_preserving_has_pdf MeasureTheory.pdf.quasiMeasurePreserving_hasPDF

theorem quasiMeasurePreserving_hasPDF' [IsFiniteMeasure ℙ] [SigmaFinite ν] {X : Ω → E}
    [HasPDF X ℙ μ] {g : E → F} (hg : QuasiMeasurePreserving g μ ν) : HasPDF (g ∘ X) ℙ ν :=
  quasiMeasurePreserving_hasPDF hg inferInstance
#align measure_theory.pdf.quasi_measure_preserving_has_pdf' MeasureTheory.pdf.quasiMeasurePreserving_hasPDF'

end

section Real

variable [IsFiniteMeasure ℙ] {X : Ω → ℝ}

/-- A real-valued random variable `X` `HasPDF X ℙ λ` (where `λ` is the Lebesgue measure) if and
only if the push-forward measure of `ℙ` along `X` is absolutely continuous with respect to `λ`. -/
nonrec theorem _root_.Real.hasPDF_iff_of_measurable (hX : Measurable X) :
    HasPDF X ℙ ↔ map X ℙ ≪ volume := by
  rw [hasPDF_iff_of_measurable hX]
  exact and_iff_right inferInstance
#align measure_theory.pdf.real.has_pdf_iff_of_measurable Real.hasPDF_iff_of_measurable

theorem _root_.Real.hasPDF_iff : HasPDF X ℙ ↔ Measurable X ∧ map X ℙ ≪ volume := by
  by_cases hX : Measurable X
  · rw [Real.hasPDF_iff_of_measurable hX, iff_and_self]
    exact fun _ => hX
  · exact ⟨fun h => False.elim (hX h.pdf'.1), fun h => False.elim (hX h.1)⟩
#align measure_theory.pdf.real.has_pdf_iff Real.hasPDF_iff

/-- If `X` is a real-valued random variable that has pdf `f`, then the expectation of `X` equals
`∫ x, x * f x ∂λ` where `λ` is the Lebesgue measure. -/
theorem integral_mul_eq_integral [HasPDF X ℙ] : ∫ x, x * (pdf X ℙ volume x).toReal = ∫ x, X x ∂ℙ :=
  integral_fun_mul_eq_integral measurable_id
#align measure_theory.pdf.integral_mul_eq_integral MeasureTheory.pdf.integral_mul_eq_integral

theorem hasFiniteIntegral_mul {f : ℝ → ℝ} {g : ℝ → ℝ≥0∞} (hg : pdf X ℙ =ᵐ[volume] g)
    (hgi : ∫⁻ x, ‖f x‖₊ * g x ≠ ∞) :
    HasFiniteIntegral fun x => f x * (pdf X ℙ volume x).toReal := by
  rw [HasFiniteIntegral]
  have : (fun x => ↑‖f x‖₊ * g x) =ᵐ[volume] fun x => ‖f x * (pdf X ℙ volume x).toReal‖₊ := by
    refine' ae_eq_trans (Filter.EventuallyEq.mul (ae_eq_refl fun x => (‖f x‖₊ : ℝ≥0∞))
      (ae_eq_trans hg.symm ofReal_toReal_ae_eq.symm)) _
    simp_rw [← smul_eq_mul, nnnorm_smul, ENNReal.coe_mul, smul_eq_mul]
    refine' Filter.EventuallyEq.mul (ae_eq_refl _) _
    simp only [Real.ennnorm_eq_ofReal ENNReal.toReal_nonneg, ae_eq_refl]
  rwa [lt_top_iff_ne_top, ← lintegral_congr_ae this]
#align measure_theory.pdf.has_finite_integral_mul MeasureTheory.pdf.hasFiniteIntegral_mul

end Real

section

/-! **Uniform Distribution** -/

/-- A random variable `X` has uniform distribution if it has a probability density function `f`
with support `s` such that `f = (μ s)⁻¹ 1ₛ` a.e. where `1ₛ` is the indicator function for `s`. -/
def IsUniform {_ : MeasurableSpace Ω} (X : Ω → E) (support : Set E) (ℙ : Measure Ω)
    (μ : Measure E := by volume_tac) :=
  pdf X ℙ μ =ᵐ[μ] support.indicator ((μ support)⁻¹ • (1 : E → ℝ≥0∞))
#align measure_theory.pdf.is_uniform MeasureTheory.pdf.IsUniform

namespace IsUniform

theorem hasPDF {m : MeasurableSpace Ω} {X : Ω → E} {ℙ : Measure Ω} {μ : Measure E} {s : Set E}
    (hns : μ s ≠ 0) (hnt : μ s ≠ ∞) (hu : IsUniform X s ℙ μ) : HasPDF X ℙ μ :=
  hasPDF_of_pdf_ne_zero
    (by
      intro hpdf
      simp only [IsUniform, hpdf] at hu
      suffices μ (s ∩ Function.support ((μ s)⁻¹ • (1 : E → ℝ≥0∞))) = 0 by
        have heq : Function.support ((μ s)⁻¹ • (1 : E → ℝ≥0∞)) = Set.univ := by
          ext x
          rw [Function.mem_support]
          simp [hnt]
        rw [heq, Set.inter_univ] at this
        exact hns this
      exact Set.indicator_ae_eq_zero.1 hu.symm)
#align measure_theory.pdf.is_uniform.has_pdf MeasureTheory.pdf.IsUniform.hasPDF

theorem pdf_toReal_ae_eq {_ : MeasurableSpace Ω} {X : Ω → E} {ℙ : Measure Ω} {μ : Measure E}
    {s : Set E} (hX : IsUniform X s ℙ μ) :
    (fun x => (pdf X ℙ μ x).toReal) =ᵐ[μ] fun x =>
      (s.indicator ((μ s)⁻¹ • (1 : E → ℝ≥0∞)) x).toReal :=
  Filter.EventuallyEq.fun_comp hX ENNReal.toReal
#align measure_theory.pdf.is_uniform.pdf_to_real_ae_eq MeasureTheory.pdf.IsUniform.pdf_toReal_ae_eq

theorem measure_preimage {m : MeasurableSpace Ω} {X : Ω → E} {ℙ : Measure Ω} {μ : Measure E}
    {s : Set E} (hns : μ s ≠ 0) (hnt : μ s ≠ ∞) (hms : MeasurableSet s) (hu : IsUniform X s ℙ μ)
    {A : Set E} (hA : MeasurableSet A) : ℙ (X ⁻¹' A) = μ (s ∩ A) / μ s := by
  haveI := hu.hasPDF hns hnt
  rw [← Measure.map_apply (HasPDF.measurable X ℙ μ) hA, map_eq_set_lintegral_pdf X ℙ μ hA,
    lintegral_congr_ae hu.restrict]
  simp only [hms, hA, lintegral_indicator, Pi.smul_apply, Pi.one_apply, Algebra.id.smul_eq_mul,
    mul_one, lintegral_const, restrict_apply', Set.univ_inter]
  rw [ENNReal.div_eq_inv_mul]
#align measure_theory.pdf.is_uniform.measure_preimage MeasureTheory.pdf.IsUniform.measure_preimage

theorem isProbabilityMeasure {m : MeasurableSpace Ω} {X : Ω → E} {ℙ : Measure Ω} {μ : Measure E}
    {s : Set E} (hns : μ s ≠ 0) (hnt : μ s ≠ ∞) (hms : MeasurableSet s) (hu : IsUniform X s ℙ μ) :
    IsProbabilityMeasure ℙ :=
  ⟨by
    have : X ⁻¹' Set.univ = Set.univ := by simp only [Set.preimage_univ]
    rw [← this, hu.measure_preimage hns hnt hms MeasurableSet.univ, Set.inter_univ,
      ENNReal.div_self hns hnt]⟩
#align measure_theory.pdf.is_uniform.is_probability_measure MeasureTheory.pdf.IsUniform.isProbabilityMeasure

variable {X : Ω → ℝ} {s : Set ℝ} (hms : MeasurableSet s) (hns : volume s ≠ 0)

theorem mul_pdf_integrable [IsFiniteMeasure ℙ] (hcs : IsCompact s) (huX : IsUniform X s ℙ) :
    Integrable fun x : ℝ => x * (pdf X ℙ volume x).toReal := by
  by_cases hsupp : volume s = ∞
  · have : pdf X ℙ =ᵐ[volume] 0 := by
      refine' ae_eq_trans huX _
      simp [hsupp, ae_eq_refl]
    refine' Integrable.congr (integrable_zero _ _ _) _
    rw [(by simp : (fun x => 0 : ℝ → ℝ) = fun x => x * (0 : ℝ≥0∞).toReal)]
    refine'
      Filter.EventuallyEq.mul (ae_eq_refl _) (Filter.EventuallyEq.fun_comp this.symm ENNReal.toReal)
  constructor -- porting note: `refine` was failing, don't know why
  · exact aestronglyMeasurable_id.mul
      (measurable_pdf X ℙ).aemeasurable.ennreal_toReal.aestronglyMeasurable
  refine' hasFiniteIntegral_mul huX _
  set ind := (volume s)⁻¹ • (1 : ℝ → ℝ≥0∞)
  have : ∀ x, ↑‖x‖₊ * s.indicator ind x = s.indicator (fun x => ‖x‖₊ * ind x) x := fun x =>
    (s.indicator_mul_right (fun x => ↑‖x‖₊) ind).symm
  simp only [this, lintegral_indicator _ hms, mul_one, Algebra.id.smul_eq_mul, Pi.one_apply,
    Pi.smul_apply]
  rw [lintegral_mul_const _ measurable_nnnorm.coe_nnreal_ennreal]
  refine' (ENNReal.mul_lt_top (set_lintegral_lt_top_of_isCompact hsupp hcs continuous_nnnorm).ne
    (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.mpr hns)).ne).ne
#align measure_theory.pdf.is_uniform.mul_pdf_integrable MeasureTheory.pdf.IsUniform.mul_pdf_integrable

/-- A real uniform random variable `X` with support `s` has expectation
`(λ s)⁻¹ * ∫ x in s, x ∂λ` where `λ` is the Lebesgue measure. -/
theorem integral_eq (hnt : volume s ≠ ∞) (huX : IsUniform X s ℙ) :
    ∫ x, X x ∂ℙ = (volume s)⁻¹.toReal * ∫ x in s, x := by
  haveI := hasPDF hns hnt huX
  haveI := huX.isProbabilityMeasure hns hnt hms
  rw [← integral_mul_eq_integral]
  rw [integral_congr_ae (Filter.EventuallyEq.mul (ae_eq_refl _) (pdf_toReal_ae_eq huX))]
  have :
    ∀ x,
      x * (s.indicator ((volume s)⁻¹ • (1 : ℝ → ℝ≥0∞)) x).toReal =
        x * s.indicator ((volume s)⁻¹.toReal • (1 : ℝ → ℝ)) x := by
    refine' fun x => congr_arg ((· * ·) x) _
    by_cases hx : x ∈ s
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_not_mem hx]
  simp_rw [this, ← s.indicator_mul_right fun x => x, integral_indicator hms]
  change ∫ x in s, x * (volume s)⁻¹.toReal • (1 : ℝ) = _
  rw [integral_mul_right, mul_comm, smul_eq_mul, mul_one]
#align measure_theory.pdf.is_uniform.integral_eq MeasureTheory.pdf.IsUniform.integral_eq

end IsUniform

end

section TwoVariables

open ProbabilityTheory

variable {F : Type*} [MeasurableSpace F] {ν : Measure F} {X : Ω → E} {Y : Ω → F}

/-- Random variables are independent iff their joint density is a product of marginal densities. -/
theorem indepFun_iff_pdf_prod_eq_pdf_mul_pdf
    [IsFiniteMeasure ℙ] [SigmaFinite μ] [SigmaFinite ν] [HasPDF (fun ω ↦ (X ω, Y ω)) ℙ (μ.prod ν)] :
    IndepFun X Y ℙ ↔
      pdf (fun ω ↦ (X ω, Y ω)) ℙ (μ.prod ν) =ᵐ[μ.prod ν] fun z ↦ pdf X ℙ μ z.1 * pdf Y ℙ ν z.2 := by
  have : HasPDF X ℙ μ := quasiMeasurePreserving_hasPDF' (μ := μ.prod ν) (X := fun ω ↦ (X ω, Y ω))
    quasiMeasurePreserving_fst
  have : HasPDF Y ℙ ν := quasiMeasurePreserving_hasPDF' (μ := μ.prod ν) (X := fun ω ↦ (X ω, Y ω))
    quasiMeasurePreserving_snd
  have h₀ : (ℙ.map X).prod (ℙ.map Y) =
      (μ.prod ν).withDensity fun z ↦ pdf X ℙ μ z.1 * pdf Y ℙ ν z.2 :=
    prod_eq fun s t hs ht ↦ by rw [withDensity_apply _ (hs.prod ht), ← prod_restrict,
      lintegral_prod_mul (measurable_pdf X ℙ μ).aemeasurable (measurable_pdf Y ℙ ν).aemeasurable,
      map_eq_set_lintegral_pdf X ℙ μ hs, map_eq_set_lintegral_pdf Y ℙ ν ht]
  rw [indepFun_iff_map_prod_eq_prod_map_map (HasPDF.measurable X ℙ μ) (HasPDF.measurable Y ℙ ν),
    ← unique, h₀]
  exact (((measurable_pdf X ℙ μ).comp measurable_fst).mul
    ((measurable_pdf Y ℙ ν).comp measurable_snd)).aemeasurable

end TwoVariables

end pdf

end MeasureTheory
