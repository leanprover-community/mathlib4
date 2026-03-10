/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-! # Interactions of the continuous functional calculus with the real and imaginary part -/

public section

open Complex ComplexStarModule

variable {A : Type*} [TopologicalSpace A]

section NonUnital

variable [NonUnitalRing A] [StarRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [StarModule ℂ A] [NonUnitalContinuousFunctionalCalculus ℂ A IsStarNormal]

set_option backward.isDefEq.respectTransparency false in
lemma cfcₙ_re_id (a : A) (ha : IsStarNormal a := by cfc_tac) :
    cfcₙ (re · : ℂ → ℂ) a = ℜ a := by
  conv_rhs => rw [realPart_apply_coe, ← cfcₙ_id' ℂ a, ← cfcₙ_star, ← cfcₙ_add .., ← cfcₙ_smul ..]
  refine cfcₙ_congr fun x hx ↦ ?_
  rw [Complex.re_eq_add_conj, ← smul_one_smul ℂ 2⁻¹]
  simp [div_eq_inv_mul]

lemma cfcₙ_im_id (a : A) (ha : IsStarNormal a := by cfc_tac) :
    cfcₙ (im · : ℂ → ℂ) a = ℑ a := by
  suffices cfcₙ (fun z : ℂ ↦ re z + I * im z) a = ℜ a + I • ℑ a by
    rw [cfcₙ_add .., cfcₙ_const_mul .., cfcₙ_re_id a] at this
    simpa
  simp [mul_comm I, re_add_im, cfcₙ_id' .., realPart_add_I_smul_imaginaryPart]

lemma quasispectrum_realPart (a : A) (ha : IsStarNormal a := by cfc_tac) :
    quasispectrum ℂ (ℜ a : A) = (fun x ↦ (re x : ℂ)) '' (quasispectrum ℂ a) := by
  rw [← cfcₙ_re_id a, cfcₙ_map_quasispectrum ..]

-- fails to find `IsScalarTower ℝ ℂ A`.
set_option backward.isDefEq.respectTransparency false in
lemma quasispectrum_realPart' (a : A) (ha : IsStarNormal a := by cfc_tac) :
    quasispectrum ℝ (ℜ a : A) = re '' (quasispectrum ℂ a) := by
  simp [← (ℜ a).2.quasispectrumRestricts.image, quasispectrum_realPart a, Set.image_image]

lemma quasispectrum_imaginaryPart (a : A) (ha : IsStarNormal a := by cfc_tac) :
    quasispectrum ℂ (ℑ a : A) = (fun x ↦ (im x : ℂ)) '' (quasispectrum ℂ a) := by
  rw [← cfcₙ_im_id a, cfcₙ_map_quasispectrum ..]

-- fails to find `IsScalarTower ℝ ℂ A`.
set_option backward.isDefEq.respectTransparency false in
lemma quasispectrum_imaginaryPart' (a : A) (ha : IsStarNormal a := by cfc_tac) :
    quasispectrum ℝ (ℑ a : A) = im '' (quasispectrum ℂ a) := by
  simp [← (ℑ a).2.quasispectrumRestricts.image, quasispectrum_imaginaryPart a, Set.image_image]

variable [ContinuousMapZero.UniqueHom ℂ A]

lemma cfcₙ_realPart (f : ℂ → ℂ) (a : A)
    (hf : ContinuousOn f (quasispectrum ℂ (ℜ a : A)) := by cfc_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : IsStarNormal a := by cfc_tac) :
    cfcₙ f (ℜ a : A) = cfcₙ (fun x ↦ f (re x)) a := by
  rw [quasispectrum_realPart a] at hf
  rw [← cfcₙ_re_id a, ← cfcₙ_comp' ..]

lemma cfcₙ_imaginaryPart (f : ℂ → ℂ) (a : A)
    (hf : ContinuousOn f (quasispectrum ℂ (ℑ a : A)) := by cfc_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : IsStarNormal a := by cfc_tac) :
    cfcₙ f (ℑ a : A) = cfcₙ (fun x ↦ f (im x)) a := by
  rw [quasispectrum_imaginaryPart a] at hf
  rw [← cfcₙ_im_id a, ← cfcₙ_comp' ..]

variable [T2Space A]

lemma cfcₙ_comp_re (f : ℝ → ℝ) (a : A)
    (hf : ContinuousOn f (quasispectrum ℝ (ℜ a : A)) := by cfc_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : IsStarNormal a := by cfc_tac) :
    cfcₙ (fun x : ℂ ↦ f (re x)) a = cfcₙ f (ℜ a : A) := by
  have : ContinuousOn (fun x ↦ (f x.re) : ℂ → ℂ) ((re · : ℂ → ℂ) '' quasispectrum ℂ a) := by
    rw [quasispectrum_realPart' a] at hf
    refine continuous_ofReal.comp_continuousOn <| hf.comp (by fun_prop) ?_
    simpa [Set.mapsTo_image_iff, Function.comp_def] using Set.mapsTo_image ..
  conv_rhs =>
    rw [cfcₙ_real_eq_complex, ← cfcₙ_re_id a, ← cfcₙ_comp' ..]
    simp

lemma cfcₙ_comp_im (f : ℝ → ℝ) (a : A) (hf : ContinuousOn f (quasispectrum ℝ (ℑ a : A)))
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : IsStarNormal a := by cfc_tac) :
    cfcₙ (fun x : ℂ ↦ f (im x)) a = cfcₙ f (ℑ a : A) := by
  have : ContinuousOn (fun x ↦ (f x.re) : ℂ → ℂ) ((im · : ℂ → ℂ) '' quasispectrum ℂ a) := by
    rw [quasispectrum_imaginaryPart' a] at hf
    refine continuous_ofReal.comp_continuousOn <| hf.comp (by fun_prop) ?_
    simpa [Set.mapsTo_image_iff, Function.comp_def] using Set.mapsTo_image ..
  conv_rhs =>
    rw [cfcₙ_real_eq_complex, ← cfcₙ_im_id a, ← cfcₙ_comp' ..]
    simp

end NonUnital

section Unital

variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  [ContinuousFunctionalCalculus ℂ A IsStarNormal]

set_option backward.isDefEq.respectTransparency false in
lemma cfc_re_id (a : A) (hp : IsStarNormal a := by cfc_tac) :
    cfc (re · : ℂ → ℂ) a = ℜ a := by
  conv_rhs => rw [realPart_apply_coe, ← cfc_id' ℂ a, ← cfc_star, ← cfc_add .., ← cfc_smul ..]
  refine cfc_congr fun x hx ↦ ?_
  rw [Complex.re_eq_add_conj, ← smul_one_smul ℂ 2⁻¹]
  simp [div_eq_inv_mul]

lemma cfc_im_id (a : A) (hp : IsStarNormal a := by cfc_tac) :
    cfc (im · : ℂ → ℂ) a = ℑ a := by
  suffices cfc (fun z : ℂ ↦ re z + I * im z) a = ℜ a + I • ℑ a by
    rw [cfc_add .., cfc_const_mul .., cfc_re_id a] at this
    simpa
  simp [mul_comm I, re_add_im, cfc_id' .., realPart_add_I_smul_imaginaryPart]

lemma spectrum_realPart (a : A) (ha : IsStarNormal a := by cfc_tac) :
    spectrum ℂ (ℜ a : A) = (fun x ↦ (re x : ℂ)) '' (spectrum ℂ a) := by
  rw [← cfc_re_id a, cfc_map_spectrum ..]

set_option backward.isDefEq.respectTransparency false in
lemma spectrum_realPart' (a : A) (ha : IsStarNormal a := by cfc_tac) :
    spectrum ℝ (ℜ a : A) = re '' (spectrum ℂ a) := by
  simp [← (ℜ a).2.spectrumRestricts.image, spectrum_realPart a, Set.image_image]

lemma spectrum_imaginaryPart (a : A) (ha : IsStarNormal a := by cfc_tac) :
    spectrum ℂ (ℑ a : A) = (fun x ↦ (im x : ℂ)) '' (spectrum ℂ a) := by
  rw [← cfc_im_id a, cfc_map_spectrum ..]

set_option backward.isDefEq.respectTransparency false in
lemma spectrum_imaginaryPart' (a : A) (ha : IsStarNormal a := by cfc_tac) :
    spectrum ℝ (ℑ a : A) = im '' (spectrum ℂ a) := by
  simp [← (ℑ a).2.spectrumRestricts.image, spectrum_imaginaryPart a, Set.image_image]

variable [ContinuousMap.UniqueHom ℂ A]

lemma cfc_realPart (f : ℂ → ℂ) (a : A) (hf : ContinuousOn f (spectrum ℂ (ℜ a : A)) := by cfc_tac)
    (ha : IsStarNormal a := by cfc_tac) :
    cfc f (ℜ a : A) = cfc (fun x ↦ f (re x)) a := by
  rw [spectrum_realPart a] at hf
  rw [← cfc_re_id a, ← cfc_comp' ..]

lemma cfc_imaginaryPart (f : ℂ → ℂ) (a : A)
    (hf : ContinuousOn f (spectrum ℂ (ℑ a : A)) := by cfc_tac)
    (ha : IsStarNormal a := by cfc_tac) :
    cfc f (ℑ a : A) = cfc (fun x ↦ f (im x)) a := by
  rw [spectrum_imaginaryPart a] at hf
  rw [← cfc_im_id a, ← cfc_comp' ..]

variable [T2Space A]

lemma cfc_comp_re (f : ℝ → ℝ) (a : A)
    (hf : ContinuousOn f (spectrum ℝ (ℜ a : A)) := by cfc_tac)
    (ha : IsStarNormal a := by cfc_tac) :
    cfc (fun x : ℂ ↦ f (re x)) a = cfc f (ℜ a : A) := by
  have : ContinuousOn (fun x ↦ (f x.re) : ℂ → ℂ) ((re · : ℂ → ℂ) '' spectrum ℂ a) := by
    rw [spectrum_realPart' a] at hf
    refine continuous_ofReal.comp_continuousOn <| hf.comp (by fun_prop) ?_
    simpa [Set.mapsTo_image_iff, Function.comp_def] using Set.mapsTo_image ..
  conv_rhs =>
    rw [cfc_real_eq_complex, ← cfc_re_id a, ← cfc_comp' ..]
    simp

lemma cfc_comp_im (f : ℝ → ℝ) (a : A) (hf : ContinuousOn f (spectrum ℝ (ℑ a : A)))
    (ha : IsStarNormal a := by cfc_tac) :
    cfc (fun x : ℂ ↦ f (im x)) a = cfc f (ℑ a : A) := by
  have : ContinuousOn (fun x ↦ (f x.re) : ℂ → ℂ) ((im · : ℂ → ℂ) '' spectrum ℂ a) := by
    rw [spectrum_imaginaryPart' a] at hf
    refine continuous_ofReal.comp_continuousOn <| hf.comp (by fun_prop) ?_
    simpa [Set.mapsTo_image_iff, Function.comp_def] using Set.mapsTo_image ..
  conv_rhs =>
    rw [cfc_real_eq_complex, ← cfc_im_id a, ← cfc_comp' ..]
    simp

end Unital
