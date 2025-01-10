/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow
import Mathlib.Topology.ContinuousMap.ContinuousSqrt

/-! # Facts about star-ordered rings that depend on the continuous functional calculus

This file contains various basic facts about star-ordered rings (i.e. mainly C⋆-algebras)
that depend on the continuous functional calculus.

We also put an order instance on `A⁺¹ := Unitization ℂ A` when `A` is a C⋆-algebra via
the spectral order.

## Main theorems

* `IsSelfAdjoint.le_algebraMap_norm_self` and `IsSelfAdjoint.le_algebraMap_norm_self`,
  which respectively show that `a ≤ algebraMap ℝ A ‖a‖` and `-(algebraMap ℝ A ‖a‖) ≤ a` in a
  C⋆-algebra.
* `mul_star_le_algebraMap_norm_sq` and `star_mul_le_algebraMap_norm_sq`, which give similar
  statements for `a * star a` and `star a * a`.
* `CStarAlgebra.norm_le_norm_of_nonneg_of_le`: in a non-unital C⋆-algebra, if `0 ≤ a ≤ b`, then
  `‖a‖ ≤ ‖b‖`.
* `CStarAlgebra.conjugate_le_norm_smul`: in a non-unital C⋆-algebra, we have that
  `star a * b * a ≤ ‖b‖ • (star a * a)` (and a primed version for the `a * b * star a` case).
* `CStarAlgebra.inv_le_inv_iff`: in a unital C⋆-algebra, `b⁻¹ ≤ a⁻¹` iff `a ≤ b`.

## Tags

continuous functional calculus, normal, selfadjoint
-/

open scoped NNReal CStarAlgebra

local notation "σₙ" => quasispectrum

theorem cfc_tsub {A : Type*} [TopologicalSpace A] [Ring A] [PartialOrder A] [StarRing A]
    [StarOrderedRing A] [Algebra ℝ A] [TopologicalRing A]
    [ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
    [UniqueContinuousFunctionalCalculus ℝ A] [NonnegSpectrumClass ℝ A] (f g : ℝ≥0 → ℝ≥0)
    (a : A) (hfg : ∀ x ∈ spectrum ℝ≥0 a, g x ≤ f x) (ha : 0 ≤ a := by cfc_tac)
    (hf : ContinuousOn f (spectrum ℝ≥0 a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum ℝ≥0 a) := by cfc_cont_tac) :
    cfc (fun x ↦ f x - g x) a = cfc f a - cfc g a := by
  have ha' := SpectrumRestricts.nnreal_of_nonneg ha
  have : (spectrum ℝ a).EqOn (fun x ↦ ((f x.toNNReal - g x.toNNReal : ℝ≥0) : ℝ))
      (fun x ↦ f x.toNNReal - g x.toNNReal) :=
    fun x hx ↦ NNReal.coe_sub <| hfg _ <| ha'.apply_mem hx
  rw [cfc_nnreal_eq_real, cfc_nnreal_eq_real, cfc_nnreal_eq_real, cfc_congr this]
  refine cfc_sub _ _ a ?_ ?_
  all_goals
    exact continuous_subtype_val.comp_continuousOn <|
      ContinuousOn.comp ‹_› continuous_real_toNNReal.continuousOn <| ha'.image ▸ Set.mapsTo_image ..

theorem cfcₙ_tsub {A : Type*} [TopologicalSpace A] [NonUnitalRing A] [PartialOrder A] [StarRing A]
    [StarOrderedRing A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [TopologicalRing A]
    [NonUnitalContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
    [UniqueNonUnitalContinuousFunctionalCalculus ℝ A] [NonnegSpectrumClass ℝ A] (f g : ℝ≥0 → ℝ≥0)
    (a : A) (hfg : ∀ x ∈ σₙ ℝ≥0 a, g x ≤ f x) (ha : 0 ≤ a := by cfc_tac)
    (hf : ContinuousOn f (σₙ ℝ≥0 a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (hg : ContinuousOn g (σₙ ℝ≥0 a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac) :
    cfcₙ (fun x ↦ f x - g x) a = cfcₙ f a - cfcₙ g a := by
  have ha' := QuasispectrumRestricts.nnreal_of_nonneg ha
  have : (σₙ ℝ a).EqOn (fun x ↦ ((f x.toNNReal - g x.toNNReal : ℝ≥0) : ℝ))
      (fun x ↦ f x.toNNReal - g x.toNNReal) :=
    fun x hx ↦ NNReal.coe_sub <| hfg _ <| ha'.apply_mem hx
  rw [cfcₙ_nnreal_eq_real, cfcₙ_nnreal_eq_real, cfcₙ_nnreal_eq_real, cfcₙ_congr this]
  refine cfcₙ_sub _ _ a ?_ (by simpa) ?_
  all_goals
    exact continuous_subtype_val.comp_continuousOn <|
      ContinuousOn.comp ‹_› continuous_real_toNNReal.continuousOn <| ha'.image ▸ Set.mapsTo_image ..

namespace Unitization

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

instance instPartialOrder : PartialOrder A⁺¹ :=
    CStarAlgebra.spectralOrder _

instance instStarOrderedRing : StarOrderedRing A⁺¹ :=
    CStarAlgebra.spectralOrderedRing _

lemma inr_le_iff (a b : A) (ha : IsSelfAdjoint a := by cfc_tac)
    (hb : IsSelfAdjoint b := by cfc_tac) :
    (a : A⁺¹) ≤ (b : A⁺¹) ↔ a ≤ b := by
  -- TODO: prove the more general result for star monomorphisms and use it here.
  rw [← sub_nonneg, ← sub_nonneg (a := b), StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _,
    ← inr_sub ℂ b a, ← Unitization.quasispectrum_eq_spectrum_inr' ℝ ℂ]
  exact StarOrderedRing.nonneg_iff_quasispectrum_nonneg _ |>.symm

@[simp, norm_cast]
lemma inr_nonneg_iff {a : A} : 0 ≤ (a : A⁺¹) ↔ 0 ≤ a := by
  by_cases ha : IsSelfAdjoint a
  · exact inr_zero ℂ (A := A) ▸ inr_le_iff 0 a
  · refine ⟨?_, ?_⟩
    all_goals refine fun h ↦ (ha ?_).elim
    · exact isSelfAdjoint_inr (R := ℂ) |>.mp <| .of_nonneg h
    · exact .of_nonneg h

lemma nnreal_cfcₙ_eq_cfc_inr (a : A) (f : ℝ≥0 → ℝ≥0)
    (hf₀ : f 0 = 0 := by cfc_zero_tac) : cfcₙ f a = cfc f (a : A⁺¹) :=
  cfcₙ_eq_cfc_inr inr_nonneg_iff ..

end Unitization

/-- `cfc_le_iff` only applies to a scalar ring where `R` is an actual `Ring`, and not a `Semiring`.
However, this theorem still holds for `ℝ≥0` as long as the algebra `A` itself is an `ℝ`-algebra. -/
lemma cfc_nnreal_le_iff {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [PartialOrder A]
    [StarOrderedRing A] [Algebra ℝ A] [TopologicalRing A] [NonnegSpectrumClass ℝ A]
    [ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
    [UniqueContinuousFunctionalCalculus ℝ A]
    (f : ℝ≥0 → ℝ≥0) (g : ℝ≥0 → ℝ≥0) (a : A)
    (ha_spec : SpectrumRestricts a ContinuousMap.realToNNReal)
    (hf : ContinuousOn f (spectrum ℝ≥0 a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum ℝ≥0 a) := by cfc_cont_tac)
    (ha : 0 ≤ a := by cfc_tac) :
    cfc f a ≤ cfc g a ↔ ∀ x ∈ spectrum ℝ≥0 a, f x ≤ g x := by
  have hf' := hf.ofReal_map_toNNReal <| ha_spec.image ▸ Set.mapsTo_image ..
  have hg' := hg.ofReal_map_toNNReal <| ha_spec.image ▸ Set.mapsTo_image ..
  rw [cfc_nnreal_eq_real, cfc_nnreal_eq_real, cfc_le_iff ..]
  simp [NNReal.coe_le_coe, ← ha_spec.image]

open ContinuousFunctionalCalculus in
/-- In a unital `ℝ`-algebra `A` with a continuous functional calculus, an element `a : A` is larger
than some `algebraMap ℝ A r` if and only if every element of the `ℝ`-spectrum is nonnegative. -/
lemma CFC.exists_pos_algebraMap_le_iff {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A]
    [PartialOrder A] [StarOrderedRing A] [Algebra ℝ A] [NonnegSpectrumClass ℝ A] [Nontrivial A]
    [ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
    {a : A} (ha : IsSelfAdjoint a := by cfc_tac) :
    (∃ r > 0, algebraMap ℝ A r ≤ a) ↔ (∀ x ∈ spectrum ℝ a, 0 < x) := by
  have h_cpct : IsCompact (spectrum ℝ a) := isCompact_iff_compactSpace.mpr inferInstance
  simp_rw [algebraMap_le_iff_le_spectrum (a := a)]
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨r, hr, hr_le⟩
    exact (hr.trans_le <| hr_le · ·)
  · obtain ⟨r, hr, hr_min⟩ := h_cpct.exists_isMinOn (spectrum_nonempty ℝ a ha) continuousOn_id
    exact ⟨r, h _ hr, hr_min⟩

section CStar_unital

variable {A : Type*} [CStarAlgebra A]

section StarOrderedRing

variable [PartialOrder A] [StarOrderedRing A]

lemma IsSelfAdjoint.le_algebraMap_norm_self {a : A} (ha : IsSelfAdjoint a := by cfc_tac) :
    a ≤ algebraMap ℝ A ‖a‖ := by
  by_cases nontriv : Nontrivial A
  · refine le_algebraMap_of_spectrum_le fun r hr => ?_
    calc r ≤ ‖r‖ := Real.le_norm_self r
      _ ≤ ‖a‖ := spectrum.norm_le_norm_of_mem hr
  · rw [not_nontrivial_iff_subsingleton] at nontriv
    simp

lemma IsSelfAdjoint.neg_algebraMap_norm_le_self {a : A} (ha : IsSelfAdjoint a := by cfc_tac) :
    - (algebraMap ℝ A ‖a‖) ≤ a := by
  have : - a ≤ algebraMap ℝ A ‖a‖ := by
    rw [← norm_neg]
    exact IsSelfAdjoint.le_algebraMap_norm_self (neg ha)
  exact neg_le.mp this

lemma CStarAlgebra.mul_star_le_algebraMap_norm_sq {a : A} :
    a * star a ≤ algebraMap ℝ A (‖a‖ ^ 2) := by
  have : a * star a ≤ algebraMap ℝ A ‖a * star a‖ := IsSelfAdjoint.le_algebraMap_norm_self
  rwa [CStarRing.norm_self_mul_star, ← pow_two] at this

lemma CStarAlgebra.star_mul_le_algebraMap_norm_sq {a : A} :
    star a * a ≤ algebraMap ℝ A (‖a‖ ^ 2) := by
  have : star a * a ≤ algebraMap ℝ A ‖star a * a‖ := IsSelfAdjoint.le_algebraMap_norm_self
  rwa [CStarRing.norm_star_mul_self, ← pow_two] at this

end StarOrderedRing

lemma IsSelfAdjoint.toReal_spectralRadius_eq_norm {a : A} (ha : IsSelfAdjoint a) :
    (spectralRadius ℝ a).toReal = ‖a‖ := by
  simp [ha.spectrumRestricts.spectralRadius_eq, ha.spectralRadius_eq_nnnorm]

namespace CStarAlgebra

lemma norm_or_neg_norm_mem_spectrum [Nontrivial A] {a : A}
    (ha : IsSelfAdjoint a := by cfc_tac) : ‖a‖ ∈ spectrum ℝ a ∨ -‖a‖ ∈ spectrum ℝ a := by
  have ha' : SpectrumRestricts a Complex.reCLM := ha.spectrumRestricts
  rw [← ha.toReal_spectralRadius_eq_norm]
  exact Real.spectralRadius_mem_spectrum_or (ha'.image ▸ (spectrum.nonempty a).image _)

variable [PartialOrder A] [StarOrderedRing A]

lemma nnnorm_mem_spectrum_of_nonneg [Nontrivial A] {a : A} (ha : 0 ≤ a := by cfc_tac) :
    ‖a‖₊ ∈ spectrum ℝ≥0 a := by
  have : IsSelfAdjoint a := .of_nonneg ha
  convert NNReal.spectralRadius_mem_spectrum (a := a) ?_ (.nnreal_of_nonneg ha)
  · simp [this.spectrumRestricts.spectralRadius_eq, this.spectralRadius_eq_nnnorm]
  · exact this.spectrumRestricts.image ▸ (spectrum.nonempty a).image _

lemma norm_mem_spectrum_of_nonneg [Nontrivial A] {a : A} (ha : 0 ≤ a := by cfc_tac) :
    ‖a‖ ∈ spectrum ℝ a := by
  simpa using spectrum.algebraMap_mem ℝ <| nnnorm_mem_spectrum_of_nonneg ha

lemma norm_le_iff_le_algebraMap (a : A) {r : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a := by cfc_tac) :
    ‖a‖ ≤ r ↔ a ≤ algebraMap ℝ A r := by
  rw [le_algebraMap_iff_spectrum_le]
  obtain (h | _) := subsingleton_or_nontrivial A
  · simp [Subsingleton.elim a 0, hr]
  · exact ⟨fun h x hx ↦ Real.le_norm_self x |>.trans (spectrum.norm_le_norm_of_mem hx) |>.trans h,
      fun h ↦ h ‖a‖ <| norm_mem_spectrum_of_nonneg⟩

lemma nnnorm_le_iff_of_nonneg (a : A) (r : ℝ≥0) (ha : 0 ≤ a := by cfc_tac) :
    ‖a‖₊ ≤ r ↔ a ≤ algebraMap ℝ≥0 A r := by
  rw [← NNReal.coe_le_coe]
  exact norm_le_iff_le_algebraMap a r.2

lemma norm_le_one_iff_of_nonneg (a : A) (ha : 0 ≤ a := by cfc_tac) :
    ‖a‖ ≤ 1 ↔ a ≤ 1 := by
  simpa using norm_le_iff_le_algebraMap a zero_le_one

lemma nnnorm_le_one_iff_of_nonneg (a : A) (ha : 0 ≤ a := by cfc_tac) :
    ‖a‖₊ ≤ 1 ↔ a ≤ 1 := by
  rw [← NNReal.coe_le_coe]
  exact norm_le_one_iff_of_nonneg a

lemma norm_le_natCast_iff_of_nonneg (a : A) (n : ℕ) (ha : 0 ≤ a := by cfc_tac) :
    ‖a‖ ≤ n ↔ a ≤ n := by
  simpa using norm_le_iff_le_algebraMap a n.cast_nonneg

lemma nnnorm_le_natCast_iff_of_nonneg (a : A) (n : ℕ) (ha : 0 ≤ a := by cfc_tac) :
    ‖a‖₊ ≤ n ↔ a ≤ n := by
  simpa using nnnorm_le_iff_of_nonneg a n


section Icc

open Set

lemma mem_Icc_algebraMap_iff_norm_le {x : A} {r : ℝ} (hr : 0 ≤ r) :
    x ∈ Icc 0 (algebraMap ℝ A r) ↔ 0 ≤ x ∧ ‖x‖ ≤ r := by
  rw [mem_Icc, and_congr_right_iff, iff_comm]
  exact (norm_le_iff_le_algebraMap _ hr ·)

lemma mem_Icc_algebraMap_iff_nnnorm_le {x : A} {r : ℝ≥0} :
    x ∈ Icc 0 (algebraMap ℝ≥0 A r) ↔ 0 ≤ x ∧ ‖x‖₊ ≤ r :=
  mem_Icc_algebraMap_iff_norm_le (hr := r.2)

lemma mem_Icc_iff_norm_le_one {x : A} :
    x ∈ Icc 0 1 ↔ 0 ≤ x ∧ ‖x‖ ≤ 1 := by
  simpa only [map_one] using mem_Icc_algebraMap_iff_norm_le zero_le_one (A := A)

lemma mem_Icc_iff_nnnorm_le_one {x : A} :
    x ∈ Icc 0 1 ↔ 0 ≤ x ∧ ‖x‖₊ ≤ 1 :=
  mem_Icc_iff_norm_le_one

end Icc

end CStarAlgebra

section Inv

open CFC

variable [PartialOrder A] [StarOrderedRing A]

-- TODO : relate everything in this section to strict positivity

lemma CFC.conjugate_rpow_neg_one_half {a : A} (h₀ : IsUnit a) (ha : 0 ≤ a := by cfc_tac) :
    a ^ (-(1 / 2) : ℝ) * a * a ^ (-(1 / 2) : ℝ) = 1 := by
  lift a to Aˣ using h₀
  nth_rw 2 [← rpow_one (a : A)]
  simp only [← rpow_add (a.zero_not_mem_spectrum ℝ≥0)]
  norm_num
  exact rpow_zero _

/-- In a unital C⋆-algebra, if `a` is nonnegative and invertible, and `a ≤ b`, then `b` is
invertible. -/
lemma CStarAlgebra.isUnit_of_le {a b : A} (h₀ : IsUnit a) (ha : 0 ≤ a := by cfc_tac)
    (hab : a ≤ b) : IsUnit b := by
  rw [← spectrum.zero_not_mem_iff ℝ≥0] at h₀ ⊢
  nontriviality A
  have hb := (show 0 ≤ a from ha).trans hab
  rw [zero_not_mem_iff, SpectrumRestricts.nnreal_lt_iff (.nnreal_of_nonneg ‹_›),
    NNReal.coe_zero, ← CFC.exists_pos_algebraMap_le_iff] at h₀ ⊢
  peel h₀ with r hr _
  exact this.trans hab

lemma le_iff_norm_sqrt_mul_rpow {a b : A} (hbu : IsUnit b) (ha : 0 ≤ a) (hb : 0 ≤ (b : A)) :
    a ≤ b ↔ ‖sqrt a * (b : A) ^ (-(1 / 2) : ℝ)‖ ≤ 1 := by
  lift b to Aˣ using hbu
  have hbab : 0 ≤ (b : A) ^ (-(1 / 2) : ℝ) * a * (b : A) ^ (-(1 / 2) : ℝ) :=
    conjugate_nonneg_of_nonneg ha rpow_nonneg
  #adaptation_note /-- 2024-11-10 added `(R := A)` -/
  conv_rhs =>
    rw [← sq_le_one_iff₀ (norm_nonneg _), sq, ← CStarRing.norm_star_mul_self, star_mul,
      IsSelfAdjoint.of_nonneg (R := A) sqrt_nonneg, IsSelfAdjoint.of_nonneg rpow_nonneg,
      ← mul_assoc, mul_assoc _ _ (sqrt a), sqrt_mul_sqrt_self a,
      CStarAlgebra.norm_le_one_iff_of_nonneg _ hbab]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · calc
      _ ≤ ↑b ^ (-(1 / 2) : ℝ) * (b : A) * ↑b ^ (-(1 / 2) : ℝ) :=
        IsSelfAdjoint.of_nonneg rpow_nonneg |>.conjugate_le_conjugate h
      _ = 1 := conjugate_rpow_neg_one_half b.isUnit
  · calc
      a = (sqrt ↑b * ↑b ^ (-(1 / 2) : ℝ)) * a * (↑b ^ (-(1 / 2) : ℝ) * sqrt ↑b) := by
        simp only [CFC.sqrt_eq_rpow .., ← CFC.rpow_add (b.zero_not_mem_spectrum ℝ≥0)]
        norm_num
        simp [CFC.rpow_zero (b : A)]
      _ = sqrt ↑b * (↑b ^ (-(1 / 2) : ℝ) * a * ↑b ^ (-(1 / 2) : ℝ)) * sqrt ↑b := by
        simp only [mul_assoc]
      _ ≤ b := conjugate_le_conjugate_of_nonneg h sqrt_nonneg |>.trans <| by
        simp [CFC.sqrt_mul_sqrt_self (b : A)]

lemma le_iff_norm_sqrt_mul_sqrt_inv {a : A} {b : Aˣ} (ha : 0 ≤ a) (hb : 0 ≤ (b : A)) :
    a ≤ b ↔ ‖sqrt a * sqrt (↑b⁻¹ : A)‖ ≤ 1 := by
  rw [CFC.sqrt_eq_rpow (a := (↑b⁻¹ : A)), ← CFC.rpow_neg_one_eq_inv b,
    CFC.rpow_rpow (b : A) _ _ (by simp) (by norm_num), le_iff_norm_sqrt_mul_rpow b.isUnit ha hb]
  norm_num

namespace CStarAlgebra

/-- In a unital C⋆-algebra, if `0 ≤ a ≤ b` and `a` and `b` are units, then `b⁻¹ ≤ a⁻¹`. -/
protected lemma inv_le_inv {a b : Aˣ} (ha : 0 ≤ (a : A))
    (hab : (a : A) ≤ b) : (↑b⁻¹ : A) ≤ a⁻¹ := by
  have hb := ha.trans hab
  have hb_inv : (0 : A) ≤ b⁻¹ := inv_nonneg_of_nonneg b hb
  have ha_inv : (0 : A) ≤ a⁻¹ := inv_nonneg_of_nonneg a ha
  rw [le_iff_norm_sqrt_mul_sqrt_inv ha hb, ← sq_le_one_iff₀ (norm_nonneg _), sq,
    ← CStarRing.norm_star_mul_self] at hab
  rw [le_iff_norm_sqrt_mul_sqrt_inv hb_inv ha_inv, inv_inv, ← sq_le_one_iff₀ (norm_nonneg _), sq,
    ← CStarRing.norm_self_mul_star]
  rwa [star_mul, IsSelfAdjoint.of_nonneg sqrt_nonneg,
    IsSelfAdjoint.of_nonneg sqrt_nonneg] at hab ⊢

/-- In a unital C⋆-algebra, if `0 ≤ a` and `0 ≤ b` and `a` and `b` are units, then `a⁻¹ ≤ b⁻¹`
if and only if `b ≤ a`. -/
protected lemma inv_le_inv_iff {a b : Aˣ} (ha : 0 ≤ (a : A)) (hb : 0 ≤ (b : A)) :
    (↑a⁻¹ : A) ≤ b⁻¹ ↔ (b : A) ≤ a :=
  ⟨CStarAlgebra.inv_le_inv (inv_nonneg_of_nonneg a ha), CStarAlgebra.inv_le_inv hb⟩

lemma inv_le_iff {a b : Aˣ} (ha : 0 ≤ (a : A)) (hb : 0 ≤ (↑b : A)) :
    (↑a⁻¹ : A) ≤ b ↔ (↑b⁻¹ : A) ≤ a := by
  simpa using CStarAlgebra.inv_le_inv_iff ha (inv_nonneg_of_nonneg b hb)

lemma le_inv_iff {a b : Aˣ} (ha : 0 ≤ (a : A)) (hb : 0 ≤ (↑b : A)) :
    a ≤ (↑b⁻¹ : A) ↔ b ≤ (↑a⁻¹ : A) := by
  simpa using CStarAlgebra.inv_le_inv_iff (inv_nonneg_of_nonneg a ha) hb

lemma one_le_inv_iff_le_one {a : Aˣ} (ha : 0 ≤ (a : A)) :
    1 ≤ (↑a⁻¹ : A) ↔ a ≤ 1 := by
  simpa using CStarAlgebra.le_inv_iff (a := 1) (by simp) ha

lemma inv_le_one_iff_one_le {a : Aˣ} (ha : 0 ≤ (a : A)) :
    (↑a⁻¹ : A) ≤ 1 ↔ 1 ≤ a := by
  simpa using CStarAlgebra.inv_le_iff ha (b := 1) (by simp)

lemma inv_le_one {a : Aˣ} (ha : 1 ≤ a) : (↑a⁻¹ : A) ≤ 1 :=
  CStarAlgebra.inv_le_one_iff_one_le (zero_le_one.trans ha) |>.mpr ha

lemma le_one_of_one_le_inv {a : Aˣ} (ha : 1 ≤ (↑a⁻¹ : A)) : (a : A) ≤ 1 := by
  simpa using CStarAlgebra.inv_le_one ha

lemma rpow_neg_one_le_rpow_neg_one {a b : A} (ha : 0 ≤ a) (hab : a ≤ b) (hau : IsUnit a) :
    b ^ (-1 : ℝ) ≤ a ^ (-1 : ℝ) := by
  lift b to Aˣ using isUnit_of_le hau ha hab
  lift a to Aˣ using hau
  rw [rpow_neg_one_eq_inv a ha, rpow_neg_one_eq_inv b (ha.trans hab)]
  exact CStarAlgebra.inv_le_inv ha hab

lemma rpow_neg_one_le_one {a : A} (ha : 1 ≤ a) : a ^ (-1 : ℝ) ≤ 1 := by
  lift a to Aˣ using isUnit_of_le isUnit_one zero_le_one ha
  rw [rpow_neg_one_eq_inv a (zero_le_one.trans ha)]
  exact inv_le_one ha

end CStarAlgebra

end Inv

end CStar_unital

section CStar_nonunital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace CStarAlgebra

open ComplexOrder in
instance instNonnegSpectrumClassComplexNonUnital : NonnegSpectrumClass ℂ A where
  quasispectrum_nonneg_of_nonneg a ha x hx := by
    rw [Unitization.quasispectrum_eq_spectrum_inr' ℂ ℂ a] at hx
    exact spectrum_nonneg_of_nonneg (Unitization.inr_nonneg_iff.mpr ha) hx

lemma norm_le_norm_of_nonneg_of_le {a b : A} (ha : 0 ≤ a := by cfc_tac) (hab : a ≤ b) :
    ‖a‖ ≤ ‖b‖ := by
  suffices ∀ a b : A⁺¹, 0 ≤ a → a ≤ b → ‖a‖ ≤ ‖b‖ by
    have hb := ha.trans hab
    simpa only [ge_iff_le, Unitization.norm_inr] using
      this a b (by simpa) (by rwa [Unitization.inr_le_iff a b])
  intro a b ha hab
  have hb_nonneg : 0 ≤ b := ha.trans hab
  have : 0 ≤ a := by cfc_tac
  have h₂ : cfc (id : ℝ → ℝ) a ≤ cfc (fun _ => ‖b‖) a := by
    calc _ = a := by rw [cfc_id ℝ a]
      _ ≤ cfc id b := (cfc_id ℝ b) ▸ hab
      _ ≤ cfc (fun _ => ‖b‖) b := by
          refine cfc_mono fun x hx => ?_
          calc x = ‖x‖ := (Real.norm_of_nonneg (spectrum_nonneg_of_nonneg hb_nonneg hx)).symm
            _ ≤ ‖b‖ := spectrum.norm_le_norm_of_mem hx
      _ = _ := by rw [cfc_const _ _, cfc_const _ _]
  rw [cfc_le_iff id (fun _ => ‖b‖) a] at h₂
  exact h₂ ‖a‖ <| norm_mem_spectrum_of_nonneg ha

theorem nnnorm_le_nnnorm_of_nonneg_of_le {a : A} {b : A} (ha : 0 ≤ a := by cfc_tac) (hab : a ≤ b) :
    ‖a‖₊ ≤ ‖b‖₊ :=
  norm_le_norm_of_nonneg_of_le ha hab

lemma conjugate_le_norm_smul {a b : A} (hb : IsSelfAdjoint b := by cfc_tac) :
    star a * b * a ≤ ‖b‖ • (star a * a) := by
  suffices ∀ a b : A⁺¹, IsSelfAdjoint b → star a * b * a ≤ ‖b‖ • (star a * a) by
    rw [← Unitization.inr_le_iff _ _ (by aesop) ((IsSelfAdjoint.all _).smul (.star_mul_self a))]
    simpa [Unitization.norm_inr] using this a b <| hb.inr ℂ
  intro a b hb
  calc
    star a * b * a ≤ star a * (algebraMap ℝ A⁺¹ ‖b‖) * a :=
      conjugate_le_conjugate hb.le_algebraMap_norm_self _
    _ = ‖b‖ • (star a * a) := by simp [Algebra.algebraMap_eq_smul_one]

lemma conjugate_le_norm_smul' {a b : A} (hb : IsSelfAdjoint b := by cfc_tac) :
    a * b * star a ≤ ‖b‖ • (a * star a) := by
  have h₁ : a * b * star a = star (star a) * b * star a := by simp
  have h₂ : a * star a = star (star a) * star a := by simp
  simp only [h₁, h₂]
  exact conjugate_le_norm_smul

/-- The set of nonnegative elements in a C⋆-algebra is closed. -/
lemma isClosed_nonneg : IsClosed {a : A | 0 ≤ a} := by
  suffices IsClosed {a : A⁺¹ | 0 ≤ a} by
    rw [Unitization.isometry_inr (𝕜 := ℂ) |>.isClosedEmbedding.isClosed_iff_image_isClosed]
    convert this.inter <| (Unitization.isometry_inr (𝕜 := ℂ)).isClosedEmbedding.isClosed_range
    ext a
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_range, ← exists_and_left]
    congr! 2 with x
    exact and_congr_left fun h ↦ by simp [← h]
  simp only [nonneg_iff_isSelfAdjoint_and_spectrumRestricts,
    and_congr_right (SpectrumRestricts.nnreal_iff_nnnorm · le_rfl), Set.setOf_and]
  refine isClosed_eq ?_ ?_ |>.inter <| isClosed_le ?_ ?_
  all_goals fun_prop

instance : OrderClosedTopology A where
  isClosed_le' := isClosed_le_of_isClosed_nonneg isClosed_nonneg

section Icc

open Unitization Set Metric

lemma inr_mem_Icc_iff_norm_le {x : A} :
    (x : A⁺¹) ∈ Icc 0 1 ↔ 0 ≤ x ∧ ‖x‖ ≤ 1 := by
  simp only [mem_Icc, inr_nonneg_iff, and_congr_right_iff]
  rw [← norm_inr (𝕜 := ℂ), ← inr_nonneg_iff, iff_comm]
  exact (norm_le_one_iff_of_nonneg _ ·)

lemma inr_mem_Icc_iff_nnnorm_le {x : A} :
    (x : A⁺¹) ∈ Icc 0 1 ↔ 0 ≤ x ∧ ‖x‖₊ ≤ 1 :=
  inr_mem_Icc_iff_norm_le

lemma preimage_inr_Icc_zero_one :
    ((↑) : A → A⁺¹) ⁻¹' Icc 0 1 = {x : A | 0 ≤ x} ∩ closedBall 0 1 := by
  ext
  simp [- mem_Icc, inr_mem_Icc_iff_norm_le]

end Icc

end CStarAlgebra

end CStar_nonunital

section Pow

namespace CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma pow_nonneg {a : A} (ha : 0 ≤ a := by cfc_tac) (n : ℕ) : 0 ≤ a ^ n := by
  rw [← cfc_pow_id (R := ℝ≥0) a]
  exact cfc_nonneg_of_predicate

lemma pow_monotone {a : A} (ha : 1 ≤ a) : Monotone (a ^ · : ℕ → A) := by
  have ha' : 0 ≤ a := zero_le_one.trans ha
  intro n m hnm
  simp only
  rw [← cfc_pow_id (R := ℝ) a, ← cfc_pow_id (R := ℝ) a, cfc_le_iff ..]
  rw [CFC.one_le_iff (R := ℝ) a] at ha
  peel ha with x hx _
  exact pow_le_pow_right₀ (ha x hx) hnm

lemma pow_antitone {a : A} (ha₀ : 0 ≤ a := by cfc_tac) (ha₁ : a ≤ 1) :
    Antitone (a ^ · : ℕ → A) := by
  intro n m hnm
  simp only
  rw [← cfc_pow_id (R := ℝ) a, ← cfc_pow_id (R := ℝ) a, cfc_le_iff ..]
  rw [CFC.le_one_iff (R := ℝ) a] at ha₁
  peel ha₁ with x hx _
  exact pow_le_pow_of_le_one (spectrum_nonneg_of_nonneg ha₀ hx) (ha₁ x hx) hnm

end CStarAlgebra

end Pow
