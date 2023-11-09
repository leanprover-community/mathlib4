/-
Copyright (c) 2023 Claus Clausen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claus Clausen
-/

import Mathlib.Probability.Density
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Cdf

/-! # Uniform distributions over ℝ

Define the Uniform Measure over Intervals on the reals

## Main definitions
* `uniformPdfReal`: the function `a b x ↦ 1/(abs (b-a))` for `x ∈ uIcc a b` or `0` else, which is
  the probability density function of a uniform distribution on the Interval `[(a ⊓ b), (a ⊔ b)]`).
* `uniformPdf`: `ℝ≥0∞`-valued pdf, `uniformPdf a b x = ENNReal.ofReal (uniformPdfReal a b x)`.
* `uniformMeasure`: The uniform measure on `ℝ` defined by `a` and `b`.
* `uniformCdfReal`: the Cdf given by the Definition of CDF in
  `ProbabilityTheory.Cdf` on the `uniformPdf`.

## Main results
* `uniformCdf_eq`: Proof that the `uniformCdfReal` given by the Definition equals the known function
  given as `a b x → min ((x- (a ⊓ b))/((a ⊔ b) - (a ⊓ b))) 1` for `(a ⊓ b) ≤ x` or `0` else.
-/

open scoped ENNReal NNReal Real

open MeasureTheory Measure Set Filter

noncomputable
def uniformPdfReal (a b x : ℝ) : ℝ :=
  indicator (uIcc a b) (fun _ => 1/(abs (b-a))) x

noncomputable
def uniformPdf (a b x : ℝ) : ℝ≥0∞ :=
 ENNReal.ofReal (uniformPdfReal a b x)

lemma uniformPdf_eq (a b x : ℝ) : uniformPdf a b x =
    ENNReal.ofReal (if x ∈ Icc (a ⊓ b) (a ⊔ b) then (fun x => 1 / abs (b - a)) x else 0) := by
    unfold uniformPdf uniformPdfReal indicator uIcc
    congr

/- Copied from exponential distribution-/
lemma lintegral_split_bounded {y z : ℝ}(f : ℝ → ENNReal) ( hzy : z ≤ y) :
    ∫⁻ (x : ℝ) in Iic y, f x  =  (∫⁻ (x : ℝ) in Iio z, f x) +  ∫⁻ (x : ℝ) in Icc z y, f x := by
  rw [(Iio_union_Icc_eq_Iic  hzy).symm, lintegral_union measurableSet_Icc]
  rw [Set.disjoint_iff];
  rintro x ⟨h1 : (x < _), h2, _ ⟩;
  linarith

/-- The uniform Pdf is measurable-/
lemma measurable_uniformPdfReal (a b : ℝ) : Measurable (uniformPdfReal a b) := by
  unfold uniformPdfReal; refine Measurable.ite ?hp measurable_const ?hg;
  · simp only [ge_iff_le, setOf_mem_eq]; exact measurableSet_uIcc
  · exact measurable_const


/-- The uniform Pdf is strongly measurable-/
lemma stronglyMeasurable_uniformPdfReal (a b : ℝ) :
    StronglyMeasurable (uniformPdfReal a b) :=
  (measurable_uniformPdfReal a b).stronglyMeasurable

lemma split_uniformLintegral : (∫⁻ (x : ℝ), uniformPdf a b x) =
    (∫⁻ (x : ℝ) in Iio (a ⊓ b) , uniformPdf a b x) + (∫⁻ (x : ℝ) in uIcc a b, uniformPdf a b x) +
    (∫⁻ (x : ℝ) in Ioi (a ⊔ b), uniformPdf a b x) := by
  have union : Iio (a ⊓ b) ∪ uIcc a b ∪ Ioi (a ⊔ b) = univ := by
    ext x; unfold uIcc; simp
  rw [←set_lintegral_univ, ←lintegral_union measurableSet_uIcc,
      ←lintegral_union measurableSet_Ioi, union]
  · unfold uIcc; simp
  · unfold uIcc
    rw [Set.disjoint_iff]
    intro _
    simp only [mem_inter_iff, mem_Iio, lt_inf_iff, mem_Icc, inf_le_iff, le_sup_iff,
        mem_empty_iff_false, and_imp]
    intro hxa hxb habx _; rcases habx <;> linarith

@[simp]
lemma Iio_eq_zero : (∫⁻ (x : ℝ) in Iio (a ⊓ b) , uniformPdf a b x) = 0 := by
  rw [set_lintegral_congr_fun measurableSet_Iio];
  · exact lintegral_zero
  · apply ae_of_all
    unfold uniformPdf uniformPdfReal uIcc indicator
    rintro x (hxab : x < _)
    rw [if_neg, ENNReal.ofReal_zero]
    rintro ⟨ _, _ ⟩ ; linarith

@[simp]
lemma Ioi_eq_zero : (∫⁻ (x : ℝ) in Ioi (a ⊔ b) , uniformPdf a b x) = 0 := by
  rw [set_lintegral_congr_fun measurableSet_Ioi];
  · exact lintegral_zero;
  · apply ae_of_all
    unfold uniformPdf uniformPdfReal uIcc indicator
    rintro x (hxab : (_ < x))
    rw [if_neg, ENNReal.ofReal_zero]
    rintro ⟨ _, _ ⟩ ; linarith

/-- The integral of the uniform PDF is equal to integrating over `uIcc a b`-/
lemma carrier_of_uniformlintegral : (∫⁻ (x : ℝ), uniformPdf a b x) =
    (∫⁻ (x : ℝ) in uIcc a b, uniformPdf a b x) := by
  rw [split_uniformLintegral]; simp only [ge_iff_le, Iio_eq_zero, zero_add, Ioi_eq_zero, add_zero]

lemma lintegral_uniformPdfReal_eq_one (a b : ℝ) (hab : a ≠ b) :
    ∫⁻ (x : ℝ), uniformPdf a b x = 1 := by
  rw [carrier_of_uniformlintegral]
  unfold uniformPdf uniformPdfReal indicator uIcc
  rw [set_lintegral_congr_fun measurableSet_Icc (ae_of_all _  (fun _ hx => by rw [if_pos hx])),
      @set_lintegral_const, Real.volume_Icc, one_div, LatticeOrderedGroup.sup_sub_inf_eq_abs_sub,
      <-ENNReal.ofReal_mul' (abs_nonneg (b - a)), inv_mul_cancel ?neq, ENNReal.ofReal_one]
  exact ne_iff_lt_or_gt.mpr (Or.inr (abs_pos.mpr (sub_ne_zero.mpr hab.symm)))

/-- the uniform PDF integrates to 1-/
lemma lintegral_uniformPdf_eq_one (a b : ℝ) (hab : a ≠ b) :
    ∫⁻ (x : ℝ), uniformPdf a b x = 1 := by
  exact lintegral_uniformPdfReal_eq_one a b hab

/-- Measure defined by the exponential Distribution -/
noncomputable
def uniformMeasure (a b : ℝ) (hab : a ≠ b ) : Measure ℝ :=
   volume.withDensity (uniformPdf a b)

instance instIsProbabilityMeasureUniform (a b : ℝ) (hab : a ≠ b ) :
    IsProbabilityMeasure (uniformMeasure a b hab) where
  measure_univ := by unfold uniformMeasure; simp [lintegral_uniformPdf_eq_one a b hab]

/-- Cdf -/
noncomputable
def uniformCdfReal (a b : ℝ) (hab : a ≠ b ) : StieltjesFunction :=
  ProbabilityTheory.cdf (uniformMeasure a b hab)

lemma uniformCdf_eq_Lintegral (a b : ℝ) (hab : a ≠ b) :
    ((uniformCdfReal a b hab)) = fun x => ENNReal.toReal (∫⁻ x in (Iic x), (uniformPdf a b x)) := by
  unfold uniformCdfReal uniformPdf
  ext x
  rw [ProbabilityTheory.cdf_eq_toReal]
  simp only [uniformMeasure, measurableSet_Iic, withDensity_apply, uniformPdf]

lemma uniformCdf_eq_zero (x : ℝ) (hx: x < a ⊓ b) : ((uniformCdfReal a b hab) x) = 0 := by
  rw [uniformCdf_eq_Lintegral];
  dsimp [uniformPdf, uniformPdfReal, indicator, uIcc];
  rw [set_lintegral_congr_fun measurableSet_Iic, lintegral_zero]; rfl
  apply ae_of_all
  rintro y  (hy : y ≤ _)
  rw [if_neg _, ENNReal.ofReal_zero]
  rintro ⟨ _, _ ⟩; linarith

lemma uniformCdf_eq_fromInf (x : ℝ) (h : a ⊓ b ≤ x) : ((uniformCdfReal a b hab) x) =
     ENNReal.toReal (∫⁻ (x' : ℝ) in Icc (a ⊓ b) x, uniformPdf a b x')  := by
  rw [uniformCdf_eq_Lintegral]; dsimp
  rw [lintegral_split_bounded _ h];
  simp only [ge_iff_le, Iio_eq_zero, inf_le_iff, gt_iff_lt, lt_inf_iff, zero_add]

lemma uniformCdf_eq_toSup (x : ℝ) (h : a ⊔ b ≤ x) : ((uniformCdfReal a b hab) x) =
    ENNReal.toReal (∫⁻ (x' : ℝ) in Icc (a ⊓ b) (a ⊔ b), uniformPdf a b x') := by
  rw [uniformCdf_eq_fromInf _ (le_trans inf_le_sup h), (Icc_union_Ioc_eq_Icc inf_le_sup h).symm,
      lintegral_union measurableSet_Ioc ?dis]
  have : ∫⁻ (a_1 : ℝ) in Ioc (a ⊔ b) x, uniformPdf a b a_1 = 0 := by
    unfold uniformPdf uniformPdfReal indicator uIcc
    rw [set_lintegral_congr_fun measurableSet_Ioc, lintegral_zero]
    apply ae_of_all
    rintro x' ⟨(hx' : _ < x'),_ ⟩
    rw [if_neg, ENNReal.ofReal_zero]
    rintro ⟨_, _⟩; linarith
  simp [this]
  rw [Set.disjoint_iff]
  rintro x ⟨⟨_, h2⟩, ⟨h3, _⟩⟩; linarith

lemma uniformCdf_eq {a b : ℝ} (hab : a ≠ b) : (uniformCdfReal a b hab) =
    fun x => ite ((a ⊓ b) ≤ x) (min ((x- (a ⊓ b))/((a ⊔ b) - (a ⊓ b))) 1) 0 := by
  ext top; by_cases (top < (a ⊓ b))
  · rw [if_neg (by linarith)]; exact uniformCdf_eq_zero top h
  by_cases h' : top ≤ (a ⊔ b)
  · push_neg at h
    rw [uniformCdf_eq_fromInf _ h];
    unfold uniformPdf uniformPdfReal indicator uIcc;
    · simp only [ge_iff_le, inf_le_iff, gt_iff_lt, lt_inf_iff, le_sup_iff, inf_le_left, inf_le_right, or_self,
        not_true, sup_lt_iff, lt_self_iff_false, false_and, and_false, and_self, mem_Icc]
      rw [set_lintegral_congr_fun measurableSet_Icc (g := (fun _ =>ENNReal.ofReal (1 / ((a ⊔ b) - (a ⊓ b)))))]
      rw [if_pos (by simp at h; exact h)]
      rw [min_eq_left]
      simp only [ge_iff_le, inf_le_iff, gt_iff_lt, lt_inf_iff, lintegral_const, MeasurableSet.univ,
        Measure.restrict_apply, univ_inter, Real.volume_Icc, ENNReal.toReal_mul, inv_nonneg, sub_nonneg, le_sup_iff,
        inf_le_left, inf_le_right, or_self, ENNReal.toReal_ofReal]
      simp only [ge_iff_le, one_div, inv_nonneg, sub_nonneg, le_sup_iff, inf_le_left, inf_le_right, or_self,
        ENNReal.toReal_ofReal, inf_le_iff]
      rw [@inv_mul_eq_div, ENNReal.toReal_ofReal]; linarith
      rw [div_le_one]; linarith;
      simp only [ge_iff_le, sub_pos, lt_sup_iff, inf_lt_left, not_le, inf_lt_right, lt_or_lt_iff_ne];
      exact id (Ne.symm hab)
      apply ae_of_all; rintro x ⟨hab, htop⟩
      rw [if_pos]; rw [@LatticeOrderedGroup.sup_sub_inf_eq_abs_sub]
      simp at hab; simp at h'; constructor; exact hab; rcases h'; left; linarith; right; linarith
  · push_neg at h'
    rw [uniformCdf_eq_toSup _ h'.le]
    unfold uniformPdf uniformPdfReal indicator uIcc;
    rw [set_lintegral_congr_fun measurableSet_Icc (g := (fun _ =>ENNReal.ofReal (1 / ((a ⊔ b) - (a ⊓ b)))))]
    · rw [if_pos (by push_neg at h; exact h)]
      simp only [ge_iff_le, le_sup_iff, inf_le_left, inf_le_right, or_self, not_true, gt_iff_lt, lt_inf_iff, sup_lt_iff,
        lt_self_iff_false, false_and, and_false, and_self, one_div, lintegral_const, MeasurableSet.univ, Measure.restrict_apply,
        univ_inter, Real.volume_Icc, ENNReal.toReal_mul, inv_nonneg, sub_nonneg, ENNReal.toReal_ofReal, ne_eq]
      rw [inv_mul_cancel, min_eq_right];
      rw [one_le_div];
      · simp only [ge_iff_le, tsub_le_iff_right, sub_add_cancel]; exact le_of_lt h';
      rw [@sub_pos]; exact inf_lt_sup.mpr hab
      rw [@sub_ne_zero]; apply (ne_of_lt (inf_lt_sup.mpr hab)).symm
    apply ae_of_all; intro x hx; rw [if_pos hx, @LatticeOrderedGroup.sup_sub_inf_eq_abs_sub]
