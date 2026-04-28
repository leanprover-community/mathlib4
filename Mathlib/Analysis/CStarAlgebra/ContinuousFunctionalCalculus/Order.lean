/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Topology.ContinuousMap.ContinuousSqrt

import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

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

public section

open scoped NNReal CStarAlgebra

local notation "σₙ" => quasispectrum

theorem cfc_tsub {A : Type*} [TopologicalSpace A] [Ring A] [PartialOrder A] [StarRing A]
    [StarOrderedRing A] [Algebra ℝ A] [IsTopologicalRing A] [T2Space A]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    [NonnegSpectrumClass ℝ A] (f g : ℝ≥0 → ℝ≥0)
    (a : A) (hfg : ∀ x ∈ spectrum ℝ≥0 a, g x ≤ f x) (ha : 0 ≤ a := by cfc_tac)
    (hf : ContinuousOn f (spectrum ℝ≥0 a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum ℝ≥0 a) := by cfc_cont_tac) :
    cfc (fun x ↦ f x - g x) a = cfc f a - cfc g a := by
  have ha' := SpectrumRestricts.nnreal_of_nonneg ha
  have : (spectrum ℝ a).EqOn (fun x ↦ ((f x.toNNReal - g x.toNNReal : ℝ≥0) : ℝ))
      (fun x ↦ f x.toNNReal - g x.toNNReal) :=
    fun x hx ↦ NNReal.coe_sub <| hfg _ <| ha'.apply_mem hx
  rw [cfc_nnreal_eq_real .., cfc_nnreal_eq_real .., cfc_nnreal_eq_real .., cfc_congr this]
  refine cfc_sub _ _ a ?_ ?_
  all_goals
    exact continuous_subtype_val.comp_continuousOn <|
      ContinuousOn.comp ‹_› continuous_real_toNNReal.continuousOn <| ha'.image ▸ Set.mapsTo_image ..

theorem cfcₙ_tsub {A : Type*} [TopologicalSpace A] [NonUnitalRing A] [PartialOrder A] [StarRing A]
    [StarOrderedRing A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    [IsTopologicalRing A] [T2Space A] [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    [NonnegSpectrumClass ℝ A] (f g : ℝ≥0 → ℝ≥0)
    (a : A) (hfg : ∀ x ∈ σₙ ℝ≥0 a, g x ≤ f x) (ha : 0 ≤ a := by cfc_tac)
    (hf : ContinuousOn f (σₙ ℝ≥0 a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (hg : ContinuousOn g (σₙ ℝ≥0 a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac) :
    cfcₙ (fun x ↦ f x - g x) a = cfcₙ f a - cfcₙ g a := by
  have ha' := QuasispectrumRestricts.nnreal_of_nonneg ha
  have : (σₙ ℝ a).EqOn (fun x ↦ ((f x.toNNReal - g x.toNNReal : ℝ≥0) : ℝ))
      (fun x ↦ f x.toNNReal - g x.toNNReal) :=
    fun x hx ↦ NNReal.coe_sub <| hfg _ <| ha'.apply_mem hx
  rw [cfcₙ_nnreal_eq_real .., cfcₙ_nnreal_eq_real .., cfcₙ_nnreal_eq_real .., cfcₙ_congr this]
  refine cfcₙ_sub _ _ a ?_ (by simpa) ?_
  all_goals
    exact continuous_subtype_val.comp_continuousOn <|
      ContinuousOn.comp ‹_› continuous_real_toNNReal.continuousOn <| ha'.image ▸ Set.mapsTo_image ..

namespace Unitization

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

noncomputable instance instPartialOrder : PartialOrder A⁺¹ :=
    CStarAlgebra.spectralOrder _

instance instStarOrderedRing : StarOrderedRing A⁺¹ :=
    CStarAlgebra.spectralOrderedRing _

set_option backward.isDefEq.respectTransparency false in
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

lemma convexOn_of_convexOn_inr_comp {f : A → A} {s : Set A}
    (hf : ∀ x, IsSelfAdjoint (f x))
    (hf₂ : ConvexOn ℝ s (Unitization.inr (R := ℂ) ∘ f)) : ConvexOn ℝ s f := by
  refine ⟨hf₂.1, ?_⟩
  intro x hx y hy a b ha hb hab
  rw [← Unitization.inr_le_iff _ _]
  simpa using hf₂.2 hx hy ha hb hab

lemma concaveOn_of_concaveOn_inr_comp {f : A → A} {s : Set A}
    (hf : ∀ x, IsSelfAdjoint (f x))
    (hf₂ : ConcaveOn ℝ s (Unitization.inr (R := ℂ) ∘ f)) : ConcaveOn ℝ s f := by
  refine ⟨hf₂.1, ?_⟩
  intro x hx y hy a b ha hb hab
  rw [← Unitization.inr_le_iff _ _]
  simpa using hf₂.2 hx hy ha hb hab

alias ⟨LE.le.of_inr, LE.le.inr⟩ := inr_nonneg_iff

set_option backward.isDefEq.respectTransparency false in
lemma nnreal_cfcₙ_eq_cfc_inr (a : A) (f : ℝ≥0 → ℝ≥0)
    (hf₀ : f 0 = 0 := by cfc_zero_tac) : cfcₙ f a = cfc f (a : A⁺¹) :=
  cfcₙ_eq_cfc_inr inr_nonneg_iff ..

lemma sqrt_inr {a : A} : CFC.sqrt (a : A⁺¹) = (↑(CFC.sqrt a) : A⁺¹) := by
  by_cases ha : 0 ≤ a <;> have ha' := by rwa [← Unitization.inr_nonneg_iff] at ha
  · rw [CFC.sqrt_eq_iff .., ← inr_mul, CFC.sqrt_mul_sqrt_self a]
  · rw [CFC.sqrt, CFC.sqrt, cfcₙ_apply_of_not_predicate _ ha,
      cfcₙ_apply_of_not_predicate _ ha', inr_zero]

end Unitization

/-- `cfc_le_iff` only applies to a scalar ring where `R` is an actual `Ring`, and not a `Semiring`.
However, this theorem still holds for `ℝ≥0` as long as the algebra `A` itself is an `ℝ`-algebra. -/
lemma cfc_nnreal_le_iff {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [PartialOrder A]
    [StarOrderedRing A] [Algebra ℝ A] [IsTopologicalRing A] [NonnegSpectrumClass ℝ A]
    [T2Space A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    (f : ℝ≥0 → ℝ≥0) (g : ℝ≥0 → ℝ≥0) (a : A)
    (ha_spec : SpectrumRestricts a ContinuousMap.realToNNReal)
    (hf : ContinuousOn f (spectrum ℝ≥0 a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum ℝ≥0 a) := by cfc_cont_tac)
    (ha : 0 ≤ a := by cfc_tac) :
    cfc f a ≤ cfc g a ↔ ∀ x ∈ spectrum ℝ≥0 a, f x ≤ g x := by
  have hf' := hf.ofReal_map_toNNReal <| ha_spec.image ▸ Set.mapsTo_image ..
  have hg' := hg.ofReal_map_toNNReal <| ha_spec.image ▸ Set.mapsTo_image ..
  rw [cfc_nnreal_eq_real .., cfc_nnreal_eq_real .., cfc_le_iff ..]
  simp [NNReal.coe_le_coe, ← ha_spec.image]

open ContinuousFunctionalCalculus in
/-- In a unital `ℝ`-algebra `A` with a continuous functional calculus, an element `a : A` is larger
than some `algebraMap ℝ A r` if and only if every element of the `ℝ`-spectrum is nonnegative. -/
lemma CFC.exists_pos_algebraMap_le_iff {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A]
    [PartialOrder A] [StarOrderedRing A] [Algebra ℝ A] [NonnegSpectrumClass ℝ A] [Nontrivial A]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    {a : A} (ha : IsSelfAdjoint a := by cfc_tac) :
    (∃ r > 0, algebraMap ℝ A r ≤ a) ↔ (∀ x ∈ spectrum ℝ a, 0 < x) := by
  have h_cpct : IsCompact (spectrum ℝ a) := isCompact_iff_compactSpace.mpr inferInstance
  simp_rw [algebraMap_le_iff_le_spectrum (a := a)]
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨r, hr, hr_le⟩
    exact (hr.trans_le <| hr_le · ·)
  · obtain ⟨r, hr, hr_min⟩ := h_cpct.exists_isMinOn
      (ContinuousFunctionalCalculus.spectrum_nonempty a ha) continuousOn_id
    exact ⟨r, h _ hr, hr_min⟩

section CStar_unital

variable {A : Type*} [CStarAlgebra A]

section StarOrderedRing

variable [PartialOrder A] [StarOrderedRing A]

lemma IsSelfAdjoint.le_algebraMap_norm_self {a : A} (ha : IsSelfAdjoint a := by cfc_tac) :
    a ≤ algebraMap ℝ A ‖a‖ := by
  by_cases! nontriv : Nontrivial A
  · refine le_algebraMap_of_spectrum_le fun r hr => ?_
    calc r ≤ ‖r‖ := Real.le_norm_self r
      _ ≤ ‖a‖ := spectrum.norm_le_norm_of_mem hr
  · simp

lemma IsSelfAdjoint.neg_algebraMap_norm_le_self {a : A} (ha : IsSelfAdjoint a := by cfc_tac) :
    -(algebraMap ℝ A ‖a‖) ≤ a := by
  rw [neg_le, ← norm_neg]
  exact ha.neg.le_algebraMap_norm_self

lemma CStarAlgebra.mul_star_le_algebraMap_norm_sq {a : A} :
    a * star a ≤ algebraMap ℝ A (‖a‖ ^ 2) := by
  have : a * star a ≤ algebraMap ℝ A ‖a * star a‖ := IsSelfAdjoint.le_algebraMap_norm_self
  rwa [CStarRing.norm_self_mul_star, ← pow_two] at this

lemma CStarAlgebra.star_mul_le_algebraMap_norm_sq {a : A} :
    star a * a ≤ algebraMap ℝ A (‖a‖ ^ 2) := by
  have : star a * a ≤ algebraMap ℝ A ‖star a * a‖ := IsSelfAdjoint.le_algebraMap_norm_self
  rwa [CStarRing.norm_star_mul_self, ← pow_two] at this

end StarOrderedRing

set_option backward.isDefEq.respectTransparency false in
lemma IsSelfAdjoint.toReal_spectralRadius_eq_norm {a : A} (ha : IsSelfAdjoint a) :
    (spectralRadius ℝ a).toReal = ‖a‖ := by
  simp [ha.spectrumRestricts.spectralRadius_eq, ha.spectralRadius_eq_nnnorm]

namespace CStarAlgebra

set_option backward.isDefEq.respectTransparency false in
lemma norm_or_neg_norm_mem_spectrum [Nontrivial A] {a : A}
    (ha : IsSelfAdjoint a := by cfc_tac) : ‖a‖ ∈ spectrum ℝ a ∨ -‖a‖ ∈ spectrum ℝ a := by
  have ha' : SpectrumRestricts a Complex.reCLM := ha.spectrumRestricts
  rw [← ha.toReal_spectralRadius_eq_norm]
  exact Real.spectralRadius_mem_spectrum_or (ha'.image ▸ (spectrum.nonempty a).image _)

variable [PartialOrder A] [StarOrderedRing A]

set_option backward.isDefEq.respectTransparency false in
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

lemma CFC.conjugate_rpow_neg_one_half (a : A) (ha : IsStrictlyPositive a := by cfc_tac) :
    a ^ (-(1 / 2) : ℝ) * a * a ^ (-(1 / 2) : ℝ) = 1 := by
  lift a to Aˣ using ha.isUnit
  nth_rw 2 [← rpow_one (a : A)]
  simp only [← rpow_add a.isUnit]
  norm_num
  exact rpow_zero _

set_option backward.isDefEq.respectTransparency false in
/-- In a unital C⋆-algebra, if `a` is strictly positive, and `a ≤ b`, then `b` is
invertible. -/
lemma CStarAlgebra.isUnit_of_le (a : A) {b : A} (hab : a ≤ b)
    (h : IsStrictlyPositive a := by cfc_tac) : IsUnit b := by
  nontriviality A
  rw [← spectrum.zero_notMem_iff ℝ]
  obtain ⟨r, hr, hr_le⟩ : ∃ r > 0, (algebraMap ℝ A) r ≤ a :=
    (exists_pos_algebraMap_le_iff h.isSelfAdjoint).2 fun x hx ↦ h.spectrum_pos hx
  exact fun h0 ↦ not_le_of_gt hr <| (algebraMap_le_iff_le_spectrum <| .of_nonneg <|
    h.nonneg.trans hab).1 (hr_le.trans hab) 0 h0

lemma le_iff_norm_sqrt_mul_rpow (a b : A) (ha : 0 ≤ a := by cfc_tac)
    (hb : IsStrictlyPositive b := by cfc_tac) :
    a ≤ b ↔ ‖sqrt a * (b : A) ^ (-(1 / 2) : ℝ)‖ ≤ 1 := by
  lift b to Aˣ using hb.isUnit
  have hbab : 0 ≤ (b : A) ^ (-(1 / 2) : ℝ) * a * (b : A) ^ (-(1 / 2) : ℝ) :=
    conjugate_nonneg_of_nonneg ha rpow_nonneg
  conv_rhs =>
    rw [← sq_le_one_iff₀ (norm_nonneg _), sq, ← CStarRing.norm_star_mul_self, star_mul,
      IsSelfAdjoint.of_nonneg (sqrt_nonneg a), IsSelfAdjoint.of_nonneg rpow_nonneg,
      ← mul_assoc, mul_assoc _ _ (sqrt a), sqrt_mul_sqrt_self a,
      CStarAlgebra.norm_le_one_iff_of_nonneg _ hbab]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · calc
      _ ≤ ↑b ^ (-(1 / 2) : ℝ) * (b : A) * ↑b ^ (-(1 / 2) : ℝ) :=
        IsSelfAdjoint.of_nonneg rpow_nonneg |>.conjugate_le_conjugate h
      _ = 1 := conjugate_rpow_neg_one_half (b : A)
  · calc
      a = (sqrt ↑b * ↑b ^ (-(1 / 2) : ℝ)) * a * (↑b ^ (-(1 / 2) : ℝ) * sqrt ↑b) := by
        simp only [CFC.sqrt_eq_rpow .., ← CFC.rpow_add b.isUnit]
        norm_num
        simp [CFC.rpow_zero (b : A)]
      _ = sqrt ↑b * (↑b ^ (-(1 / 2) : ℝ) * a * ↑b ^ (-(1 / 2) : ℝ)) * sqrt ↑b := by
        simp only [mul_assoc]
      _ ≤ b := conjugate_le_conjugate_of_nonneg h (sqrt_nonneg _) |>.trans <| by
        simp [CFC.sqrt_mul_sqrt_self (b : A)]

lemma le_iff_norm_sqrt_mul_sqrt_inv {a : A} {b : Aˣ} (ha : 0 ≤ a) (hb : 0 ≤ (b : A)) :
    a ≤ b ↔ ‖sqrt a * sqrt (↑b⁻¹ : A)‖ ≤ 1 := by
  rw [CFC.sqrt_eq_rpow (a := (↑b⁻¹ : A)), ← CFC.rpow_neg_one_eq_inv b,
    CFC.rpow_rpow (b : A) _ _ (by simp),
    le_iff_norm_sqrt_mul_rpow a (hb := b.isUnit.isStrictlyPositive hb)]
  simp

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
  rwa [star_mul, IsSelfAdjoint.of_nonneg (sqrt_nonneg _),
    IsSelfAdjoint.of_nonneg (sqrt_nonneg _)] at hab ⊢

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

lemma rpow_neg_one_le_rpow_neg_one {a b : A} (hab : a ≤ b)
    (ha : IsStrictlyPositive a := by cfc_tac) :
    b ^ (-1 : ℝ) ≤ a ^ (-1 : ℝ) := by
  lift b to Aˣ using isUnit_of_le a hab
  lift a to Aˣ using ha.isUnit
  rw [rpow_neg_one_eq_inv a, rpow_neg_one_eq_inv b (ha.nonneg.trans hab)]
  exact CStarAlgebra.inv_le_inv ha.nonneg hab

lemma rpow_neg_one_le_one {a : A} (ha : 1 ≤ a) : a ^ (-1 : ℝ) ≤ 1 := by
  lift a to Aˣ using isUnit_of_le 1 ha
  rw [rpow_neg_one_eq_inv a (zero_le_one.trans ha)]
  exact inv_le_one ha

protected lemma _root_.IsStrictlyPositive.of_le {a b : A} (ha : IsStrictlyPositive a)
    (hab : a ≤ b) : IsStrictlyPositive b :=
  ⟨ha.nonneg.trans hab, CStarAlgebra.isUnit_of_le a hab⟩

theorem _root_.IsStrictlyPositive.add_nonneg {a b : A}
    (ha : IsStrictlyPositive a) (hb : 0 ≤ b) : IsStrictlyPositive (a + b) :=
  IsStrictlyPositive.of_le ha ((le_add_iff_nonneg_right a).mpr hb)

theorem _root_.IsStrictlyPositive.nonneg_add {a b : A}
    (ha : 0 ≤ a) (hb : IsStrictlyPositive b) : IsStrictlyPositive (a + b) :=
  add_comm a b ▸ hb.add_nonneg ha

@[grind ←, aesop 90% apply]
lemma _root_.isStrictlyPositive_add {a b : A}
    (h : IsStrictlyPositive a ∧ 0 ≤ b ∨ 0 ≤ a ∧ IsStrictlyPositive b) :
    IsStrictlyPositive (a + b) := by
  grind [IsStrictlyPositive.add_nonneg, IsStrictlyPositive.nonneg_add]

lemma antitoneOn_ringInverse : AntitoneOn Ring.inverse {a : A | IsStrictlyPositive a} := by
  intro a (apos : IsStrictlyPositive a) b (bpos : IsStrictlyPositive b) hab
  rw [Ring.inverse_of_isUnit (by grind), Ring.inverse_of_isUnit (by grind)]
  exact CStarAlgebra.inv_le_inv (Units.isStrictlyPositive_iff.mp apos) hab

open Ring in
@[gcongr]
lemma ringInverse_le_ringInverse {a b : A} (hab : a ≤ b) (ha : IsStrictlyPositive a := by cfc_tac) :
    b⁻¹ʳ ≤ a⁻¹ʳ :=
  antitoneOn_ringInverse ha (IsStrictlyPositive.of_le ha hab) hab

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
  have hb : 0 ≤ b := ha.trans hab
  exact (norm_le_iff_le_algebraMap a (norm_nonneg _) ha).2 <| hab.trans <|
    IsSelfAdjoint.le_algebraMap_norm_self (.of_nonneg hb)

theorem nnnorm_le_nnnorm_of_nonneg_of_le {a : A} {b : A} (ha : 0 ≤ a := by cfc_tac) (hab : a ≤ b) :
    ‖a‖₊ ≤ ‖b‖₊ :=
  norm_le_norm_of_nonneg_of_le ha hab

set_option backward.isDefEq.respectTransparency false in
lemma star_left_conjugate_le_norm_smul {a b : A} (hb : IsSelfAdjoint b := by cfc_tac) :
    star a * b * a ≤ ‖b‖ • (star a * a) := by
  suffices ∀ a b : A⁺¹, IsSelfAdjoint b → star a * b * a ≤ ‖b‖ • (star a * a) by
    rw [← Unitization.inr_le_iff _ _ (by aesop) ((IsSelfAdjoint.all _).smul (.star_mul_self a))]
    simpa [Unitization.norm_inr] using this a b <| hb.inr ℂ
  intro a b hb
  calc
    star a * b * a ≤ star a * (algebraMap ℝ A⁺¹ ‖b‖) * a :=
      star_left_conjugate_le_conjugate hb.le_algebraMap_norm_self _
    _ = ‖b‖ • (star a * a) := by simp [Algebra.algebraMap_eq_smul_one]

@[deprecated (since := "2025-10-20")] alias conjugate_le_norm_smul :=
  star_left_conjugate_le_norm_smul

lemma star_right_conjugate_le_norm_smul {a b : A} (hb : IsSelfAdjoint b := by cfc_tac) :
    a * b * star a ≤ ‖b‖ • (a * star a) := by
  simpa using star_left_conjugate_le_norm_smul (a := star a)

@[deprecated (since := "2025-10-20")] alias conjugate_le_norm_smul' :=
  star_right_conjugate_le_norm_smul

/-- The set of nonnegative elements in a C⋆-algebra is closed. -/
lemma isClosed_nonneg : IsClosed {a : A | 0 ≤ a} := by
  suffices IsClosed {a : A⁺¹ | 0 ≤ a} by
    rw [Unitization.isometry_inr (𝕜 := ℂ) |>.isClosedEmbedding.isClosed_iff_image_isClosed]
    convert this.inter <| (Unitization.isometry_inr (𝕜 := ℂ)).isClosedEmbedding.isClosed_range
    ext a
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_range, ← exists_and_left]
    congr! 2 with x
    exact and_congr_left fun h ↦ by simp [← h]
  simp only [nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts,
    and_congr_right (SpectrumRestricts.nnreal_iff_nnnorm · le_rfl), Set.setOf_and]
  refine isClosed_eq ?_ ?_ |>.inter <| isClosed_le ?_ ?_
  all_goals fun_prop

instance : OrderClosedTopology A where
  isClosed_le' := isClosed_le_of_isClosed_nonneg isClosed_nonneg

open Unitization in
lemma convexOn_cfcₙ_of_convexOn_cfc {f : ℝ → ℝ} {s : Set A}
    (hf : ConvexOn ℝ (inr (R := ℂ) '' s) (cfc f)) : ConvexOn ℝ s (cfcₙ f) := by
  let inrl : A →ₗ[ℝ] A⁺¹ := inrHom ℝ ℂ A
  by_cases hf₀ : f 0 = 0
  case neg =>
    have : (cfcₙ f : A → A) = fun _ => 0 := by
      ext x
      simp [cfcₙ_apply_of_not_map_zero _ hf₀]
    rw [this]
    refine convexOn_const _ ?_
    have : Convex ℝ (inrl ⁻¹' (inrl '' s)) := Convex.linear_preimage hf.1 _
    rwa [Set.preimage_image_eq _ inrHom_injective] at this
  refine convexOn_of_convexOn_inr_comp (fun _ => IsSelfAdjoint.cfcₙ) ?_
  have h₁ : inr (R := ℂ) ∘ (cfcₙ f) = fun x : A => ((cfcₙ f x : A) : A⁺¹) := rfl
  have h₂ : (fun x : A => ((cfcₙ f x : A) : A⁺¹))
      = fun x : A => cfc f (x : A⁺¹) := by ext1; rw [real_cfcₙ_eq_cfc_inr ..]; rfl
  rw [h₁, h₂]
  have h₃ : ConvexOn ℝ (inrl ⁻¹' (inrl '' s)) ((cfc f) ∘ inrl) :=
    ConvexOn.comp_linearMap (g := inrl) hf
  rwa [Set.preimage_image_eq _ inrHom_injective] at h₃

open Unitization in
lemma concaveOn_cfcₙ_of_concaveOn_cfc {f : ℝ → ℝ} {s : Set A}
    (hf : ConcaveOn ℝ (inr (R := ℂ) '' s) (cfc f)) : ConcaveOn ℝ s (cfcₙ f) := by
  have : ConcaveOn ℝ s (- -cfcₙ f) := by
    rw [← cfcₙ_neg' f]
    refine (convexOn_cfcₙ_of_convexOn_cfc ?_).neg
    rw [cfc_neg']
    exact hf.neg
  simpa using this

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
  simp [-mem_Icc, inr_mem_Icc_iff_norm_le]

lemma inr_map_Ici_zero : inr '' (Ici (0 : A)) ⊆ Ici (0 : A⁺¹) := by
  rintro - ⟨a, ha, rfl⟩
  exact Unitization.inr_nonneg_iff.mpr ha

end Icc

end CStarAlgebra

open CStarAlgebra Unitization CFC in
lemma IsStarProjection.mul_right_and_mul_left_of_nonneg_of_le {a e : A}
    (he : IsStarProjection e) (ha : 0 ≤ a) (hae : a ≤ e) : a * e = a ∧ e * a = a := by
  suffices a * e = a from
    ⟨this, by simpa [ha.star_eq, he.isSelfAdjoint.star_eq] using congr(star $this)⟩
  suffices ∀ a e : A⁺¹, IsStarProjection e → 0 ≤ a → a ≤ e → a * e = a from
    mod_cast this a e he.inr ha.inr (inr_le_iff a e |>.mpr hae)
  intro a e he ha hae
  suffices sqrt a * (1 - e : A⁺¹) = 0 by
    simpa [← mul_assoc, sqrt_mul_sqrt_self a, mul_sub, sub_eq_zero, eq_comm (a := a)]
      using congr(sqrt a * $this)
  rw [← norm_eq_zero, ← sq_eq_zero_iff, ← norm_star_mul_mul_self_of_nonneg, norm_eq_zero]
  refine le_antisymm ?_ <| star_left_conjugate_nonneg ha _
  grw [star_left_conjugate_le_conjugate hae (1 - e), mul_assoc, he.mul_one_sub_self, mul_zero]

lemma IsStarProjection.conjugate_of_nonneg_of_le {a e : A} (he : IsStarProjection e)
    (ha : 0 ≤ a) (hae : a ≤ e) : e * a * e = a := by
  grind [he.mul_right_and_mul_left_of_nonneg_of_le ha hae]

end CStar_nonunital

section Pow

namespace CStarAlgebra

variable {A : Type*} {B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

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
