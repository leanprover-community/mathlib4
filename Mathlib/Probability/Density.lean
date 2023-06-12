/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying

! This file was ported from Lean 3 source module probability.density
! leanprover-community/mathlib commit fd5edc43dc4f10b85abfe544b88f82cf13c5f844
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Decomposition.RadonNikodym
import Mathbin.MeasureTheory.Measure.Haar.OfBasis

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

* `measure_theory.has_pdf` : A random variable `X : Ω → E` is said to `has_pdf` with
  respect to the measure `ℙ` on `Ω` and `μ` on `E` if there exists a measurable function `f`
  such that the push-forward measure of `ℙ` along `X` equals `μ.with_density f`.
* `measure_theory.pdf` : If `X` is a random variable that `has_pdf X ℙ μ`, then `pdf X`
  is the measurable function `f` such that the push-forward measure of `ℙ` along `X` equals
  `μ.with_density f`.
* `measure_theory.pdf.uniform` : A random variable `X` is said to follow the uniform
  distribution if it has a constant probability density function with a compact, non-null support.

## Main results

* `measure_theory.pdf.integral_fun_mul_eq_integral` : Law of the unconscious statistician,
  i.e. if a random variable `X : Ω → E` has pdf `f`, then `𝔼(g(X)) = ∫ x, g x * f x dx` for
  all measurable `g : E → ℝ`.
* `measure_theory.pdf.integral_mul_eq_integral` : A real-valued random variable `X` with
  pdf `f` has expectation `∫ x, x * f x dx`.
* `measure_theory.pdf.uniform.integral_eq` : If `X` follows the uniform distribution with
  its pdf having support `s`, then `X` has expectation `(λ s)⁻¹ * ∫ x in s, x dx` where `λ`
  is the Lebesgue measure.

## TODOs

Ultimately, we would also like to define characteristic functions to describe distributions as
it exists for all random variables. However, to define this, we will need Fourier transforms
which we currently do not have.
-/


noncomputable section

open scoped Classical MeasureTheory NNReal ENNReal

namespace MeasureTheory

open TopologicalSpace MeasureTheory.Measure

variable {Ω E : Type _} [MeasurableSpace E]

/-- A random variable `X : Ω → E` is said to `has_pdf` with respect to the measure `ℙ` on `Ω` and
`μ` on `E` if there exists a measurable function `f` such that the push-forward measure of `ℙ`
along `X` equals `μ.with_density f`. -/
class HasPdf {m : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω)
    (μ : Measure E := by exact MeasureTheory.MeasureSpace.volume) : Prop where
  pdf' : Measurable X ∧ ∃ f : E → ℝ≥0∞, Measurable f ∧ map X ℙ = μ.withDensity f
#align measure_theory.has_pdf MeasureTheory.HasPdf

@[measurability]
theorem HasPdf.measurable {m : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω)
    (μ : Measure E := by exact MeasureTheory.MeasureSpace.volume) [hX : HasPdf X ℙ μ] :
    Measurable X :=
  hX.pdf'.1
#align measure_theory.has_pdf.measurable MeasureTheory.HasPdf.measurable

/-- If `X` is a random variable that `has_pdf X ℙ μ`, then `pdf X` is the measurable function `f`
such that the push-forward measure of `ℙ` along `X` equals `μ.with_density f`. -/
def pdf {m : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω)
    (μ : Measure E := by exact MeasureTheory.MeasureSpace.volume) :=
  if hX : HasPdf X ℙ μ then Classical.choose hX.pdf'.2 else 0
#align measure_theory.pdf MeasureTheory.pdf

theorem pdf_undef {m : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E} {X : Ω → E}
    (h : ¬HasPdf X ℙ μ) : pdf X ℙ μ = 0 := by simp only [pdf, dif_neg h]
#align measure_theory.pdf_undef MeasureTheory.pdf_undef

theorem hasPdf_of_pdf_ne_zero {m : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E} {X : Ω → E}
    (h : pdf X ℙ μ ≠ 0) : HasPdf X ℙ μ := by
  by_contra hpdf
  rw [pdf, dif_neg hpdf] at h 
  exact hpdf (False.ndrec (has_pdf X ℙ μ) (h rfl))
#align measure_theory.has_pdf_of_pdf_ne_zero MeasureTheory.hasPdf_of_pdf_ne_zero

theorem pdf_eq_zero_of_not_measurable {m : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E}
    {X : Ω → E} (hX : ¬Measurable X) : pdf X ℙ μ = 0 :=
  pdf_undef fun hpdf => hX hpdf.pdf'.1
#align measure_theory.pdf_eq_zero_of_not_measurable MeasureTheory.pdf_eq_zero_of_not_measurable

theorem measurable_of_pdf_ne_zero {m : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E}
    (X : Ω → E) (h : pdf X ℙ μ ≠ 0) : Measurable X := by by_contra hX;
  exact h (pdf_eq_zero_of_not_measurable hX)
#align measure_theory.measurable_of_pdf_ne_zero MeasureTheory.measurable_of_pdf_ne_zero

@[measurability]
theorem measurable_pdf {m : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω)
    (μ : Measure E := by exact MeasureTheory.MeasureSpace.volume) : Measurable (pdf X ℙ μ) :=
  by
  by_cases hX : has_pdf X ℙ μ
  · rw [pdf, dif_pos hX]
    exact (Classical.choose_spec hX.pdf'.2).1
  · rw [pdf, dif_neg hX]
    exact measurable_zero
#align measure_theory.measurable_pdf MeasureTheory.measurable_pdf

theorem map_eq_withDensity_pdf {m : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω)
    (μ : Measure E := by exact MeasureTheory.MeasureSpace.volume) [hX : HasPdf X ℙ μ] :
    Measure.map X ℙ = μ.withDensity (pdf X ℙ μ) :=
  by
  rw [pdf, dif_pos hX]
  exact (Classical.choose_spec hX.pdf'.2).2
#align measure_theory.map_eq_with_density_pdf MeasureTheory.map_eq_withDensity_pdf

theorem map_eq_set_lintegral_pdf {m : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω)
    (μ : Measure E := by exact MeasureTheory.MeasureSpace.volume) [hX : HasPdf X ℙ μ] {s : Set E}
    (hs : MeasurableSet s) : Measure.map X ℙ s = ∫⁻ x in s, pdf X ℙ μ x ∂μ := by
  rw [← with_density_apply _ hs, map_eq_with_density_pdf X ℙ μ]
#align measure_theory.map_eq_set_lintegral_pdf MeasureTheory.map_eq_set_lintegral_pdf

namespace Pdf

variable {m : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E}

theorem lintegral_eq_measure_univ {X : Ω → E} [HasPdf X ℙ μ] : ∫⁻ x, pdf X ℙ μ x ∂μ = ℙ Set.univ :=
  by
  rw [← set_lintegral_univ, ← map_eq_set_lintegral_pdf X ℙ μ MeasurableSet.univ,
    measure.map_apply (has_pdf.measurable X ℙ μ) MeasurableSet.univ, Set.preimage_univ]
#align measure_theory.pdf.lintegral_eq_measure_univ MeasureTheory.pdf.lintegral_eq_measure_univ

theorem ae_lt_top [IsFiniteMeasure ℙ] {μ : Measure E} {X : Ω → E} : ∀ᵐ x ∂μ, pdf X ℙ μ x < ∞ :=
  by
  by_cases hpdf : has_pdf X ℙ μ
  · haveI := hpdf
    refine' ae_lt_top (measurable_pdf X ℙ μ) _
    rw [lintegral_eq_measure_univ]
    exact (measure_lt_top _ _).Ne
  · rw [pdf, dif_neg hpdf]
    exact Filter.eventually_of_forall fun x => WithTop.zero_lt_top
#align measure_theory.pdf.ae_lt_top MeasureTheory.pdf.ae_lt_top

theorem ofReal_toReal_ae_eq [IsFiniteMeasure ℙ] {X : Ω → E} :
    (fun x => ENNReal.ofReal (pdf X ℙ μ x).toReal) =ᵐ[μ] pdf X ℙ μ :=
  ofReal_toReal_ae_eq ae_lt_top
#align measure_theory.pdf.of_real_to_real_ae_eq MeasureTheory.pdf.ofReal_toReal_ae_eq

theorem integrable_iff_integrable_mul_pdf [IsFiniteMeasure ℙ] {X : Ω → E} [HasPdf X ℙ μ] {f : E → ℝ}
    (hf : Measurable f) :
    Integrable (fun x => f (X x)) ℙ ↔ Integrable (fun x => f x * (pdf X ℙ μ x).toReal) μ :=
  by
  rw [← integrable_map_measure hf.ae_strongly_measurable (has_pdf.measurable X ℙ μ).AEMeasurable,
    map_eq_with_density_pdf X ℙ μ, integrable_with_density_iff (measurable_pdf _ _ _) ae_lt_top]
  infer_instance
#align measure_theory.pdf.integrable_iff_integrable_mul_pdf MeasureTheory.pdf.integrable_iff_integrable_mul_pdf

/-- **The Law of the Unconscious Statistician**: Given a random variable `X` and a measurable
function `f`, `f ∘ X` is a random variable with expectation `∫ x, f x * pdf X ∂μ`
where `μ` is a measure on the codomain of `X`. -/
theorem integral_fun_mul_eq_integral [IsFiniteMeasure ℙ] {X : Ω → E} [HasPdf X ℙ μ] {f : E → ℝ}
    (hf : Measurable f) : ∫ x, f x * (pdf X ℙ μ x).toReal ∂μ = ∫ x, f (X x) ∂ℙ :=
  by
  by_cases hpdf : integrable (fun x => f x * (pdf X ℙ μ x).toReal) μ
  · rw [← integral_map (has_pdf.measurable X ℙ μ).AEMeasurable hf.ae_strongly_measurable,
      map_eq_with_density_pdf X ℙ μ, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hpdf,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part,
      lintegral_with_density_eq_lintegral_mul _ (measurable_pdf X ℙ μ) hf.neg.ennreal_of_real,
      lintegral_with_density_eq_lintegral_mul _ (measurable_pdf X ℙ μ) hf.ennreal_of_real]
    · congr 2
      · have :
          ∀ x,
            ENNReal.ofReal (f x * (pdf X ℙ μ x).toReal) =
              ENNReal.ofReal (pdf X ℙ μ x).toReal * ENNReal.ofReal (f x) :=
          by
          intro x
          rw [mul_comm, ENNReal.ofReal_mul ENNReal.toReal_nonneg]
        simp_rw [this]
        exact lintegral_congr_ae (Filter.EventuallyEq.mul of_real_to_real_ae_eq (ae_eq_refl _))
      · have :
          ∀ x,
            ENNReal.ofReal (-(f x * (pdf X ℙ μ x).toReal)) =
              ENNReal.ofReal (pdf X ℙ μ x).toReal * ENNReal.ofReal (-f x) :=
          by
          intro x
          rw [neg_mul_eq_neg_mul, mul_comm, ENNReal.ofReal_mul ENNReal.toReal_nonneg]
        simp_rw [this]
        exact lintegral_congr_ae (Filter.EventuallyEq.mul of_real_to_real_ae_eq (ae_eq_refl _))
    · refine' ⟨hf.ae_strongly_measurable, _⟩
      rw [has_finite_integral,
        lintegral_with_density_eq_lintegral_mul _ (measurable_pdf _ _ _)
          hf.nnnorm.coe_nnreal_ennreal]
      have :
        (fun x => (pdf X ℙ μ * fun x => ↑‖f x‖₊) x) =ᵐ[μ] fun x => ‖f x * (pdf X ℙ μ x).toReal‖₊ :=
        by
        simp_rw [← smul_eq_mul, nnnorm_smul, ENNReal.coe_mul]
        rw [smul_eq_mul, mul_comm]
        refine' Filter.EventuallyEq.mul (ae_eq_refl _) (ae_eq_trans of_real_to_real_ae_eq.symm _)
        convert ae_eq_refl _
        ext1 x
        exact Real.ennnorm_eq_ofReal ENNReal.toReal_nonneg
      rw [lintegral_congr_ae this]
      exact hpdf.2
  · rw [integral_undef hpdf, integral_undef]
    rwa [← integrable_iff_integrable_mul_pdf hf] at hpdf 
    all_goals infer_instance
#align measure_theory.pdf.integral_fun_mul_eq_integral MeasureTheory.pdf.integral_fun_mul_eq_integral

theorem map_absolutelyContinuous {X : Ω → E} [HasPdf X ℙ μ] : map X ℙ ≪ μ := by
  rw [map_eq_with_density_pdf X ℙ μ]; exact with_density_absolutely_continuous _ _
#align measure_theory.pdf.map_absolutely_continuous MeasureTheory.pdf.map_absolutelyContinuous

/-- A random variable that `has_pdf` is quasi-measure preserving. -/
theorem to_quasiMeasurePreserving {X : Ω → E} [HasPdf X ℙ μ] : QuasiMeasurePreserving X ℙ μ :=
  { Measurable := HasPdf.measurable X ℙ μ
    AbsolutelyContinuous := map_absolutelyContinuous }
#align measure_theory.pdf.to_quasi_measure_preserving MeasureTheory.pdf.to_quasiMeasurePreserving

theorem haveLebesgueDecomposition_of_hasPdf {X : Ω → E} [hX' : HasPdf X ℙ μ] :
    (map X ℙ).HaveLebesgueDecomposition μ :=
  ⟨⟨⟨0, pdf X ℙ μ⟩, by
      simp only [zero_add, measurable_pdf X ℙ μ, true_and_iff, mutually_singular.zero_left,
        map_eq_with_density_pdf X ℙ μ]⟩⟩
#align measure_theory.pdf.have_lebesgue_decomposition_of_has_pdf MeasureTheory.pdf.haveLebesgueDecomposition_of_hasPdf

theorem hasPdf_iff {X : Ω → E} :
    HasPdf X ℙ μ ↔ Measurable X ∧ (map X ℙ).HaveLebesgueDecomposition μ ∧ map X ℙ ≪ μ :=
  by
  constructor
  · intro hX'
    exact ⟨hX'.pdf'.1, have_lebesgue_decomposition_of_has_pdf, map_absolutely_continuous⟩
  · rintro ⟨hX, h_decomp, h⟩
    haveI := h_decomp
    refine' ⟨⟨hX, (measure.map X ℙ).rnDeriv μ, measurable_rn_deriv _ _, _⟩⟩
    rwa [with_density_rn_deriv_eq]
#align measure_theory.pdf.has_pdf_iff MeasureTheory.pdf.hasPdf_iff

theorem hasPdf_iff_of_measurable {X : Ω → E} (hX : Measurable X) :
    HasPdf X ℙ μ ↔ (map X ℙ).HaveLebesgueDecomposition μ ∧ map X ℙ ≪ μ := by rw [has_pdf_iff];
  simp only [hX, true_and_iff]
#align measure_theory.pdf.has_pdf_iff_of_measurable MeasureTheory.pdf.hasPdf_iff_of_measurable

section

variable {F : Type _} [MeasurableSpace F] {ν : Measure F}

/-- A random variable that `has_pdf` transformed under a `quasi_measure_preserving`
map also `has_pdf` if `(map g (map X ℙ)).have_lebesgue_decomposition μ`.

`quasi_measure_preserving_has_pdf'` is more useful in the case we are working with a
probability measure and a real-valued random variable. -/
theorem quasiMeasurePreserving_hasPdf {X : Ω → E} [HasPdf X ℙ μ] {g : E → F}
    (hg : QuasiMeasurePreserving g μ ν) (hmap : (map g (map X ℙ)).HaveLebesgueDecomposition ν) :
    HasPdf (g ∘ X) ℙ ν :=
  by
  rw [has_pdf_iff, ← map_map hg.measurable (has_pdf.measurable X ℙ μ)]
  refine' ⟨hg.measurable.comp (has_pdf.measurable X ℙ μ), hmap, _⟩
  rw [map_eq_with_density_pdf X ℙ μ]
  refine' absolutely_continuous.mk fun s hsm hs => _
  rw [map_apply hg.measurable hsm, with_density_apply _ (hg.measurable hsm)]
  have := hg.absolutely_continuous hs
  rw [map_apply hg.measurable hsm] at this 
  exact set_lintegral_measure_zero _ _ this
#align measure_theory.pdf.quasi_measure_preserving_has_pdf MeasureTheory.pdf.quasiMeasurePreserving_hasPdf

theorem quasiMeasurePreserving_has_pdf' [IsFiniteMeasure ℙ] [SigmaFinite ν] {X : Ω → E}
    [HasPdf X ℙ μ] {g : E → F} (hg : QuasiMeasurePreserving g μ ν) : HasPdf (g ∘ X) ℙ ν :=
  quasiMeasurePreserving_hasPdf hg inferInstance
#align measure_theory.pdf.quasi_measure_preserving_has_pdf' MeasureTheory.pdf.quasiMeasurePreserving_has_pdf'

end

section Real

variable [IsFiniteMeasure ℙ] {X : Ω → ℝ}

/-- A real-valued random variable `X` `has_pdf X ℙ λ` (where `λ` is the Lebesgue measure) if and
only if the push-forward measure of `ℙ` along `X` is absolutely continuous with respect to `λ`. -/
theorem Real.hasPdf_iff_of_measurable (hX : Measurable X) : HasPdf X ℙ ↔ map X ℙ ≪ volume :=
  by
  rw [has_pdf_iff_of_measurable hX, and_iff_right_iff_imp]
  exact fun h => inferInstance
#align measure_theory.pdf.real.has_pdf_iff_of_measurable MeasureTheory.pdf.Real.hasPdf_iff_of_measurable

theorem Real.hasPdf_iff : HasPdf X ℙ ↔ Measurable X ∧ map X ℙ ≪ volume :=
  by
  by_cases hX : Measurable X
  · rw [real.has_pdf_iff_of_measurable hX, iff_and_self]
    exact fun h => hX
    infer_instance
  · exact ⟨fun h => False.elim (hX h.pdf'.1), fun h => False.elim (hX h.1)⟩
#align measure_theory.pdf.real.has_pdf_iff MeasureTheory.pdf.Real.hasPdf_iff

/-- If `X` is a real-valued random variable that has pdf `f`, then the expectation of `X` equals
`∫ x, x * f x ∂λ` where `λ` is the Lebesgue measure. -/
theorem integral_mul_eq_integral [HasPdf X ℙ] : ∫ x, x * (pdf X ℙ volume x).toReal = ∫ x, X x ∂ℙ :=
  integral_fun_mul_eq_integral measurable_id
#align measure_theory.pdf.integral_mul_eq_integral MeasureTheory.pdf.integral_mul_eq_integral

theorem hasFiniteIntegral_mul {f : ℝ → ℝ} {g : ℝ → ℝ≥0∞} (hg : pdf X ℙ =ᵐ[volume] g)
    (hgi : ∫⁻ x, ‖f x‖₊ * g x ≠ ∞) : HasFiniteIntegral fun x => f x * (pdf X ℙ volume x).toReal :=
  by
  rw [has_finite_integral]
  have : (fun x => ↑‖f x‖₊ * g x) =ᵐ[volume] fun x => ‖f x * (pdf X ℙ volume x).toReal‖₊ :=
    by
    refine'
      ae_eq_trans
        (Filter.EventuallyEq.mul (ae_eq_refl fun x => ‖f x‖₊)
          (ae_eq_trans hg.symm of_real_to_real_ae_eq.symm))
        _
    simp_rw [← smul_eq_mul, nnnorm_smul, ENNReal.coe_mul, smul_eq_mul]
    refine' Filter.EventuallyEq.mul (ae_eq_refl _) _
    convert ae_eq_refl _
    ext1 x
    exact Real.ennnorm_eq_ofReal ENNReal.toReal_nonneg
  rwa [lt_top_iff_ne_top, ← lintegral_congr_ae this]
#align measure_theory.pdf.has_finite_integral_mul MeasureTheory.pdf.hasFiniteIntegral_mul

end Real

section

/-! **Uniform Distribution** -/


/-- A random variable `X` has uniform distribution if it has a probability density function `f`
with support `s` such that `f = (μ s)⁻¹ 1ₛ` a.e. where `1ₛ` is the indicator function for `s`. -/
def IsUniform {m : MeasurableSpace Ω} (X : Ω → E) (support : Set E) (ℙ : Measure Ω)
    (μ : Measure E := by exact MeasureTheory.MeasureSpace.volume) :=
  pdf X ℙ μ =ᵐ[μ] support.indicator ((μ support)⁻¹ • 1)
#align measure_theory.pdf.is_uniform MeasureTheory.pdf.IsUniform

namespace IsUniform

theorem hasPdf {m : MeasurableSpace Ω} {X : Ω → E} {ℙ : Measure Ω} {μ : Measure E} {s : Set E}
    (hns : μ s ≠ 0) (hnt : μ s ≠ ∞) (hu : IsUniform X s ℙ μ) : HasPdf X ℙ μ :=
  hasPdf_of_pdf_ne_zero
    (by
      intro hpdf
      rw [is_uniform, hpdf] at hu 
      suffices μ (s ∩ Function.support ((μ s)⁻¹ • 1)) = 0
        by
        have heq : Function.support ((μ s)⁻¹ • (1 : E → ℝ≥0∞)) = Set.univ :=
          by
          ext x
          rw [Function.mem_support]
          simp [hnt]
        rw [HEq, Set.inter_univ] at this 
        exact hns this
      exact MeasureTheory.Set.indicator_ae_eq_zero hu.symm)
#align measure_theory.pdf.is_uniform.has_pdf MeasureTheory.pdf.IsUniform.hasPdf

theorem pdf_toReal_ae_eq {m : MeasurableSpace Ω} {X : Ω → E} {ℙ : Measure Ω} {μ : Measure E}
    {s : Set E} (hX : IsUniform X s ℙ μ) :
    (fun x => (pdf X ℙ μ x).toReal) =ᵐ[μ] fun x =>
      (s.indicator ((μ s)⁻¹ • (1 : E → ℝ≥0∞)) x).toReal :=
  Filter.EventuallyEq.fun_comp hX ENNReal.toReal
#align measure_theory.pdf.is_uniform.pdf_to_real_ae_eq MeasureTheory.pdf.IsUniform.pdf_toReal_ae_eq

theorem measure_preimage {m : MeasurableSpace Ω} {X : Ω → E} {ℙ : Measure Ω} {μ : Measure E}
    {s : Set E} (hns : μ s ≠ 0) (hnt : μ s ≠ ∞) (hms : MeasurableSet s) (hu : IsUniform X s ℙ μ)
    {A : Set E} (hA : MeasurableSet A) : ℙ (X ⁻¹' A) = μ (s ∩ A) / μ s :=
  by
  haveI := hu.has_pdf hns hnt
  rw [← measure.map_apply (has_pdf.measurable X ℙ μ) hA, map_eq_set_lintegral_pdf X ℙ μ hA,
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

include hms hns

theorem mul_pdf_integrable [IsFiniteMeasure ℙ] (hcs : IsCompact s) (huX : IsUniform X s ℙ) :
    Integrable fun x : ℝ => x * (pdf X ℙ volume x).toReal :=
  by
  by_cases hsupp : volume s = ∞
  · have : pdf X ℙ =ᵐ[volume] 0 := by
      refine' ae_eq_trans huX _
      simp [hsupp]
    refine' integrable.congr (integrable_zero _ _ _) _
    rw [(by simp : (fun x => 0 : ℝ → ℝ) = fun x => x * (0 : ℝ≥0∞).toReal)]
    refine'
      Filter.EventuallyEq.mul (ae_eq_refl _) (Filter.EventuallyEq.fun_comp this.symm ENNReal.toReal)
  refine'
    ⟨ae_strongly_measurable_id.mul
        (measurable_pdf X ℙ).AEMeasurable.ennreal_toReal.AEStronglyMeasurable,
      _⟩
  refine' has_finite_integral_mul huX _
  set ind := (volume s)⁻¹ • (1 : ℝ → ℝ≥0∞) with hind
  have : ∀ x, ↑‖x‖₊ * s.indicator ind x = s.indicator (fun x => ‖x‖₊ * ind x) x := fun x =>
    (s.indicator_mul_right (fun x => ↑‖x‖₊) ind).symm
  simp only [this, lintegral_indicator _ hms, hind, mul_one, Algebra.id.smul_eq_mul, Pi.one_apply,
    Pi.smul_apply]
  rw [lintegral_mul_const _ measurable_nnnorm.coe_nnreal_ennreal]
  ·
    refine'
      (ENNReal.mul_lt_top (set_lintegral_lt_top_of_is_compact hsupp hcs continuous_nnnorm).Ne
          (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.mpr hns)).Ne).Ne
  · infer_instance
#align measure_theory.pdf.is_uniform.mul_pdf_integrable MeasureTheory.pdf.IsUniform.mul_pdf_integrable

/-- A real uniform random variable `X` with support `s` has expectation
`(λ s)⁻¹ * ∫ x in s, x ∂λ` where `λ` is the Lebesgue measure. -/
theorem integral_eq (hnt : volume s ≠ ∞) (huX : IsUniform X s ℙ) :
    ∫ x, X x ∂ℙ = (volume s)⁻¹.toReal * ∫ x in s, x :=
  by
  haveI := has_pdf hns hnt huX
  haveI := huX.is_probability_measure hns hnt hms
  rw [← integral_mul_eq_integral]
  rw [integral_congr_ae (Filter.EventuallyEq.mul (ae_eq_refl _) (pdf_to_real_ae_eq huX))]
  have :
    ∀ x,
      x * (s.indicator ((volume s)⁻¹ • (1 : ℝ → ℝ≥0∞)) x).toReal =
        x * s.indicator ((volume s)⁻¹.toReal • (1 : ℝ → ℝ)) x :=
    by
    refine' fun x => congr_arg ((· * ·) x) _
    by_cases hx : x ∈ s
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_not_mem hx]
  simp_rw [this, ← s.indicator_mul_right fun x => x, integral_indicator hms]
  change ∫ x in s, x * (volume s)⁻¹.toReal • 1 ∂volume = _
  rw [integral_mul_right, mul_comm, Algebra.id.smul_eq_mul, mul_one]
#align measure_theory.pdf.is_uniform.integral_eq MeasureTheory.pdf.IsUniform.integral_eq

end IsUniform

end

end Pdf

end MeasureTheory

