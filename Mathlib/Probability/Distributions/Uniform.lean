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
  indicator (uIcc a b) (fun _ ↦ 1/(abs (b-a))) x

noncomputable
def uniformPdf (a b x : ℝ) : ℝ≥0∞ :=
 ENNReal.ofReal (uniformPdfReal a b x)

lemma uniformPdf_eq (a b : ℝ) : uniformPdf a b =
    fun x ↦ ENNReal.ofReal (if x ∈ Icc (a ⊓ b) (a ⊔ b) then (fun x ↦ 1 / abs (b - a)) x else 0) := by
    ext x; unfold uniformPdf uniformPdfReal indicator uIcc; congr

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
  rw [set_lintegral_congr_fun measurableSet_Icc (ae_of_all _  (fun _ hx ↦ by rw [if_pos hx])),
      set_lintegral_const, Real.volume_Icc, one_div, LatticeOrderedGroup.sup_sub_inf_eq_abs_sub,
      <-ENNReal.ofReal_mul' (abs_nonneg (b - a)), inv_mul_cancel ?neq, ENNReal.ofReal_one]
  exact ne_iff_lt_or_gt.mpr (Or.inr (abs_pos.mpr (sub_ne_zero.mpr hab.symm)))

/-- the uniform PDF integrates to 1-/
lemma lintegral_uniformPdf_eq_one (a b : ℝ) (hab : a ≠ b) :
    ∫⁻ (x : ℝ), uniformPdf a b x = 1 := by
  exact lintegral_uniformPdfReal_eq_one a b hab

/-- Measure defined by the exponential Distribution -/
noncomputable
def uniformMeasure (a b : ℝ) : Measure ℝ :=
  if a = b then Measure.dirac a else volume.withDensity (uniformPdf a b)

instance instIsProbabilityMeasureUniform (a b : ℝ) :
    IsProbabilityMeasure (uniformMeasure a b) where
  measure_univ := by
    unfold uniformMeasure;
    split_ifs with hab
    . exact measure_univ
    . simp [lintegral_uniformPdf_eq_one a b hab]



/-- Cdf -/
noncomputable
def uniformCdfReal (a b : ℝ) : StieltjesFunction :=
  ProbabilityTheory.cdf (uniformMeasure a b)

lemma uniformCdf_eq_Lintegral {a b : ℝ} (hab : a ≠ b) :
    ((uniformCdfReal a b)) = fun x ↦ ENNReal.toReal (∫⁻ x in (Iic x), (uniformPdf a b x)) := by
  unfold uniformCdfReal uniformPdf
  ext x
  rw [ProbabilityTheory.cdf_eq_toReal]
  simp only [uniformMeasure, if_neg hab, measurableSet_Iic, withDensity_apply, uniformPdf]

lemma uniformCdf_eq_dirac {a b : ℝ} (hab : a = b) :
    ((uniformCdfReal a b)) = fun x ↦ ENNReal.toReal (if a ≤ x then 1 else 0) := by
  unfold uniformCdfReal
  ext x
  rw [ProbabilityTheory.cdf_eq_toReal]
  simp only [uniformMeasure, if_pos hab, measurableSet_Iic, dirac_apply', mem_Iic, not_le, indicator];
  rw [ENNReal.toReal_eq_toReal_iff]; left; rfl


lemma uniformCdf_eq_zero (x : ℝ) (hx: x < a ⊓ b) : ((uniformCdfReal a b) x) = 0 := by
  by_cases hab : a = b
  · rw [uniformCdf_eq_dirac hab]
    dsimp
    rw[if_neg (by simp at hx; linarith)]; rfl
  rw [uniformCdf_eq_Lintegral hab];
  dsimp [uniformPdf, uniformPdfReal, indicator, uIcc];
  rw [set_lintegral_congr_fun measurableSet_Iic, lintegral_zero]; rfl
  apply ae_of_all
  rintro y  (hy : y ≤ _)
  rw [if_neg _, ENNReal.ofReal_zero]
  rintro ⟨ _, _ ⟩; linarith

lemma uniformCdf_eq_fromInf (x : ℝ) (h : a ⊓ b ≤ x) (hab : a ≠ b) : ((uniformCdfReal a b) x) =
    ENNReal.toReal (∫⁻ (x' : ℝ) in Icc (a ⊓ b) x, uniformPdf a b x')  := by
  rw [uniformCdf_eq_Lintegral hab]; dsimp
  rw [lintegral_split_bounded _ h];
  simp only [ge_iff_le, Iio_eq_zero, inf_le_iff, gt_iff_lt, lt_inf_iff, zero_add]

lemma uniformCdf_eq_toSup (x : ℝ) (h : a ⊔ b ≤ x) (hab : a ≠ b) : ((uniformCdfReal a b) x) =
    ENNReal.toReal (∫⁻ (x' : ℝ) in Icc (a ⊓ b) (a ⊔ b), uniformPdf a b x') := by
  rw [uniformCdf_eq_fromInf _ (le_trans inf_le_sup h) hab, (Icc_union_Ioc_eq_Icc inf_le_sup h).symm,
      lintegral_union measurableSet_Ioc]
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

lemma uniformCdf_eq' {a b : ℝ} (hab : a ≠ b) : (uniformCdfReal a b) = fun x ↦
    if ((a ⊓ b) ≤ x) then if x < (a ⊔ b) then (x- (a ⊓ b))/((a ⊔ b) - (a ⊓ b)) else 1 else 0 := by
  ext top; split_ifs with h h'<;> push_neg at *
  · rw [uniformCdf_eq_fromInf _ h hab]
    unfold uniformPdf uniformPdfReal indicator uIcc
    rw [set_lintegral_congr_fun measurableSet_Icc (g := fun _ ↦ ENNReal.ofReal (1 / (a ⊔ b - a ⊓ b)))]
    · simp only [inv_nonneg, sub_nonneg, le_sup_iff, inf_le_left, inf_le_right, one_div,
      lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter, Real.volume_Icc,
      ENNReal.toReal_mul, mem_Icc, ENNReal.toReal_ofReal, ENNReal.toReal_ofReal]
      rw [inv_mul_eq_div, ENNReal.toReal_ofReal]; linarith
    · apply ae_of_all; rintro x ⟨hab, htop⟩
      rw [if_pos ⟨hab, by linarith⟩, LatticeOrderedGroup.sup_sub_inf_eq_abs_sub]
  · rw [uniformCdf_eq_toSup _ h' hab]
    unfold uniformPdf uniformPdfReal indicator uIcc
    rw [set_lintegral_congr_fun measurableSet_Icc (g := fun _ ↦ ENNReal.ofReal (1 / (a ⊔ b - a ⊓ b)))]
    · simp [inv_mul_cancel (sub_ne_zero.2 (ne_of_lt (inf_lt_sup.mpr hab)).symm)]
    · apply ae_of_all; intro x hx; rw [if_pos hx, LatticeOrderedGroup.sup_sub_inf_eq_abs_sub]
  . exact uniformCdf_eq_zero top h

lemma uniformCdf_eq (a b : ℝ) : uniformCdfReal a b =
    if a = b then fun x ↦ ENNReal.toReal (if a ≤ x then 1 else 0)
    else fun x ↦ if ((a ⊓ b) ≤ x) then if x < (a ⊔ b) then (x- (a ⊓ b))/((a ⊔ b) - (a ⊓ b)) else 1 else 0 := by
  split_ifs with hab; exact uniformCdf_eq_dirac hab; exact uniformCdf_eq' hab
