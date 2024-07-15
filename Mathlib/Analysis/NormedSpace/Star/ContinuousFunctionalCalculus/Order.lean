/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.NormedSpace.Star.ContinuousFunctionalCalculus.Instances
import Mathlib.Topology.ContinuousFunction.StarOrdered
import Mathlib.Analysis.NormedSpace.Star.Unitization

/-! # Facts about star-ordered rings that depend on the continuous functional calculus

This file contains various basic facts about star-ordered rings (i.e. mainly C⋆-algebras)
that depend on the continuous functional calculus.

We also put an order instance on `Unitization ℂ A` when `A` is a C⋆-algebra via
the spectral order.

## Main theorems

* `IsSelfAdjoint.le_algebraMap_norm_self` and `IsSelfAdjoint.le_algebraMap_norm_self`,
  which respectively show that `a ≤ algebraMap ℝ A ‖a‖` and `-(algebraMap ℝ A ‖a‖) ≤ a` in a
  C⋆-algebra.
* `mul_star_le_algebraMap_norm_sq` and `star_mul_le_algebraMap_norm_sq`, which give similar
  statements for `a * star a` and `star a * a`.
* `CstarRing.norm_le_norm_of_nonneg_of_le`: in a non-unital C⋆-algebra, if `a ≤ b`, then
  `‖a‖ ≤ ‖b‖`.
* `CstarRing.conjugate_le_norm_smul`: in a non-unital C⋆-algebra, we have that
  `star a * b * a ≤ ‖b‖ • (star a * a)` (and a primed version for the `a * b * star a` case).

## Tags

continuous functional calculus, normal, selfadjoint
-/

open scoped NNReal

namespace Unitization

variable {A : Type*} [NonUnitalNormedRing A] [CompleteSpace A] [Nontrivial A]
  [PartialOrder A] [StarRing A] [StarOrderedRing A] [CstarRing A] [NormedSpace ℂ A] [StarModule ℂ A]
  [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]

instance instPartialOrder : PartialOrder (Unitization ℂ A) := CstarRing.spectralOrder _

instance instStarOrderedRing : StarOrderedRing (Unitization ℂ A) := CstarRing.spectralOrderedRing _

lemma inr_le_iff (a b : A) (ha : IsSelfAdjoint a := by cfc_tac)
    (hb : IsSelfAdjoint b := by cfc_tac) :
    (a : Unitization ℂ A) ≤ (b : Unitization ℂ A) ↔ a ≤ b := by
  -- TODO: prove the more general result for star monomorphisms and use it here.
  rw [← sub_nonneg, ← sub_nonneg (a := b), StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _,
    ← inr_sub ℂ b a, ← Unitization.quasispectrum_eq_spectrum_inr' ℝ ℂ]
  exact StarOrderedRing.nonneg_iff_quasispectrum_nonneg _ |>.symm

@[simp, norm_cast]
lemma inr_nonneg_iff {a : A} : 0 ≤ (a : Unitization ℂ A) ↔ 0 ≤ a := by
  by_cases ha : IsSelfAdjoint a
  · exact inr_zero ℂ (A := A) ▸ inr_le_iff 0 a
  · refine ⟨?_, ?_⟩
    all_goals refine fun h ↦ (ha ?_).elim
    · exact isSelfAdjoint_inr (R := ℂ) |>.mp <| .of_nonneg h
    · exact .of_nonneg h

end Unitization

section generic

variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [PartialOrder A]
  [Algebra ℂ A] [ContinuousFunctionalCalculus ℂ (IsStarNormal : A → Prop)]
  [NonnegSpectrumClass ℝ A]

lemma IsSelfAdjoint.coe_mem_spectrum_complex {a : A} {x : ℝ} (ha : IsSelfAdjoint a := by cfc_tac) :
    (x : ℂ) ∈ spectrum ℂ a ↔ x ∈ spectrum ℝ a := by
  simp [← ha.spectrumRestricts.algebraMap_image]

lemma coe_mem_spectrum_real_of_nonneg {a : A} {x : ℝ≥0} (ha : 0 ≤ a := by cfc_tac) :
    (x : ℝ) ∈ spectrum ℝ a ↔ x ∈ spectrum ℝ≥0 a := by
  have hsr : SpectrumRestricts a ContinuousMap.realToNNReal :=
    SpectrumRestricts.nnreal_of_nonneg ha
  simp only [← hsr.algebraMap_image, Set.mem_image]
  refine ⟨fun ⟨z, hz₁, hz₂⟩ => ?_, fun h => ⟨x, h, rfl⟩⟩
  rwa [← NNReal.coe_injective hz₂]

end generic

section Cstar_unital

variable {A : Type*} [NormedRing A] [StarRing A] [CstarRing A] [CompleteSpace A]
variable [NormedAlgebra ℂ A] [StarModule ℂ A] [PartialOrder A] [StarOrderedRing A]

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

lemma CstarRing.mul_star_le_algebraMap_norm_sq {a : A} : a * star a ≤ algebraMap ℝ A (‖a‖ ^ 2) := by
  have : a * star a ≤ algebraMap ℝ A ‖a * star a‖ := IsSelfAdjoint.le_algebraMap_norm_self
  rwa [CstarRing.norm_self_mul_star, ← pow_two] at this

lemma CstarRing.star_mul_le_algebraMap_norm_sq {a : A} : star a * a ≤ algebraMap ℝ A (‖a‖ ^ 2) := by
  have : star a * a ≤ algebraMap ℝ A ‖star a * a‖ := IsSelfAdjoint.le_algebraMap_norm_self
  rwa [CstarRing.norm_star_mul_self, ← pow_two] at this

lemma CstarRing.norm_mem_spectrum_of_nonneg [Nontrivial A] {a : A} (ha : 0 ≤ a := by cfc_tac) :
    ‖a‖ ∈ spectrum ℝ a := by
  have ha' : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha
  obtain ⟨z, hz₁, hz₂⟩ := spectrum.exists_nnnorm_eq_spectralRadius a
  rw [ha'.spectralRadius_eq_nnnorm] at hz₂
  have hz₂' : ‖z‖ = ‖a‖ := by
    have := congr_arg ENNReal.toReal hz₂
    simpa only [toReal_coe_nnnorm] using this
  rw [← hz₂']
  have hz₃ : z = z.re := ha'.mem_spectrum_eq_re hz₁
  rw [hz₃, ha'.coe_mem_spectrum_complex] at hz₁
  have hz₄ : 0 ≤ z.re := spectrum_nonneg_of_nonneg ha hz₁
  have : z.re = ‖z‖ := by
    rw [hz₃]
    simp only [Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs]
    apply Eq.symm
    rwa [abs_eq_self]
  rwa [← this]

lemma CstarRing.nnnorm_mem_spectrum_of_nonneg [Nontrivial A] {a : A} (ha : 0 ≤ a := by cfc_tac) :
    ‖a‖₊ ∈ spectrum ℝ≥0 a := by
  rw [← coe_mem_spectrum_real_of_nonneg ha, coe_nnnorm]
  exact norm_mem_spectrum_of_nonneg ha

/-- Note that this is an auxiliary lemma used to prove the more general statement
`norm_le_norm_of_nonneg_of_le` which also holds in the non-unital case. -/
lemma CstarRing.norm_le_norm_of_nonneg_of_le_unital [Nontrivial A] {a b : A} (ha : 0 ≤ a)
    (hab : a ≤ b) : ‖a‖ ≤ ‖b‖ := by
  have ha' : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha
  have hb : IsSelfAdjoint b := IsSelfAdjoint.of_nonneg <| ha.trans hab
  have hb_nonneg : 0 ≤ b := ha.trans hab
  have h₂ : cfc (id : ℝ → ℝ) a ≤ cfc (fun _ => ‖b‖) a := by
    calc _ = a := by rw [cfc_id ℝ a ha']
      _ ≤ b := hab
      _ = cfc id b := (cfc_id ℝ b hb).symm
      _ ≤ cfc (fun _ => ‖b‖) b := by
          refine cfc_mono fun x hx => ?_
          calc x = ‖x‖ := (Real.norm_of_nonneg (spectrum_nonneg_of_nonneg hb_nonneg hx)).symm
            _ ≤ ‖b‖ := spectrum.norm_le_norm_of_mem hx
      _ = algebraMap ℝ A ‖b‖ := by rw [cfc_const _ _ hb]
      _ = _ := by rw [cfc_const _ _]
  rw [cfc_le_iff id (fun _ => ‖b‖) a (by fun_prop) (by fun_prop) ha'] at h₂
  exact h₂ ‖a‖ <| norm_mem_spectrum_of_nonneg ha

/-- Note that this is an auxiliary lemma used to prove the more general statement
`conjugate_le_norm_mul` which also holds in the non-unital case. -/
lemma CstarRing.conjugate_le_norm_mul_unital [Nontrivial A] {a b : A} (hb : IsSelfAdjoint b) :
    star a * b * a ≤ ‖b‖ • (star a * a) := by
  calc star a * b * a ≤ star a * (algebraMap ℝ A ‖b‖) * a := by
        refine conjugate_le_conjugate ?_ _
        refine le_algebraMap_of_spectrum_le fun x hx => ?_
        calc x ≤ ‖x‖ := by exact Real.le_norm_self x
          _ ≤ ‖b‖ := by exact spectrum.norm_le_norm_of_mem hx
    _ = ‖b‖ • (star a * a) := by simp [Algebra.algebraMap_eq_smul_one]

end Cstar_unital

section Cstar_nonunital

variable {A : Type*} [NonUnitalNormedRing A] [CompleteSpace A] [Nontrivial A]
  [PartialOrder A] [StarRing A] [StarOrderedRing A] [CstarRing A] [NormedSpace ℂ A] [StarModule ℂ A]
  [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]

lemma CstarRing.norm_le_norm_of_nonneg_of_le {a b : A} (ha : 0 ≤ a := by cfc_tac) (hab : a ≤ b) :
    ‖a‖ ≤ ‖b‖ := by
  suffices ∀ a b : Unitization ℂ A, 0 ≤ a → a ≤ b → ‖a‖ ≤ ‖b‖ by
    have hb := ha.trans hab
    simpa [Unitization.norm_inr] using this a b (by simpa) (by rwa [Unitization.inr_le_iff a b])
  intro a b ha hab
  have hb_nonneg : 0 ≤ b := ha.trans hab
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

lemma CstarRing.conjugate_le_norm_smul {a b : A} (hb : IsSelfAdjoint b := by cfc_tac) :
    star a * b * a ≤ ‖b‖ • (star a * a) := by
  -- We use the corresponding fact for unital C⋆-algebras and apply it to the unitization
  let a' : Unitization ℂ A := .inr a
  let b' : Unitization ℂ A := .inr b
  have hb' : IsSelfAdjoint b' := by exact IsSelfAdjoint.inr ℂ hb
  have hmain : star a' * b' * a' ≤ ‖b'‖ • (star a' * a') :=
    conjugate_le_norm_mul_unital hb' (A := Unitization ℂ A)
  have h₁ : IsSelfAdjoint (star a * b * a) := by exact IsSelfAdjoint.conjugate' hb a
  have h₂ : IsSelfAdjoint (‖b‖ • (star a * a)) :=
    IsSelfAdjoint.smul (by exact rfl) (IsSelfAdjoint.star_mul_self a)
  rw [← Unitization.inr_le_iff h₁ h₂]
  simp only [Unitization.inr_mul, Unitization.inr_star, Unitization.inr_smul]
  simpa only [b', Unitization.norm_inr] using hmain

lemma CstarRing.conjugate_le_norm_smul' {a b : A} (hb : IsSelfAdjoint b := by cfc_tac) :
    a * b * star a ≤ ‖b‖ • (a * star a) := by
  have h₁ : a * b * star a = star (star a) * b * star a := by simp
  have h₂ : a * star a = star (star a) * star a := by simp
  simp only [h₁, h₂]
  exact conjugate_le_norm_smul

end Cstar_nonunital
