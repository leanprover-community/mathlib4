/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar, Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection

/-!

# Projections in C⋆-algebras

Here we collect results about projections specific to C⋆-algebras.

## Main results

+ `isStarProjection_iff_isIdempotentElem_and_isStarNormal`: star projections are precisely
  idempotent normal elements.
+ `IsStarProjection.le_tfae`: for star projections `p` and `q`, the following are equivalent:
  - `p ≤ q`
  - `q * p = p`
  - `p * q = p`
  - `q - p` is a star projection
  - `q - p` is an idempotent element

-/
set_option backward.defeqAttrib.useBackward true

public section

open scoped CStarAlgebra

section NonUnital
variable {A : Type*} [TopologicalSpace A] [NonUnitalRing A] [StarRing A]

lemma isStarProjection_iff_quasispectrum_subset_and_isSelfAdjoint [Module ℝ A] [IsScalarTower ℝ A A]
    [SMulCommClass ℝ A A] [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint] {p : A} :
    IsStarProjection p ↔ quasispectrum ℝ p ⊆ {0, 1} ∧ IsSelfAdjoint p :=
  (isStarProjection_iff p).eq ▸
    and_congr_left_iff.mpr fun h ↦ isIdempotentElem_iff_quasispectrum_subset ℝ p h

section Normal
variable [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [NonUnitalContinuousFunctionalCalculus ℂ A IsStarNormal]

/-- An idempotent element in a non-unital C⋆-algebra is self-adjoint iff it is normal. -/
theorem IsIdempotentElem.isSelfAdjoint_iff_isStarNormal {p : A} (hp : IsIdempotentElem p) :
    IsSelfAdjoint p ↔ IsStarNormal p := by
  simp only [isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts,
    QuasispectrumRestricts.real_iff, and_iff_left_iff_imp]
  intro h x hx
  rcases hp.quasispectrum_subset _ hx with (hx | hx) <;> simp [Set.mem_singleton_iff.mp hx]

/-- An element in a non-unital C⋆-algebra is a star projection
if and only if it is idempotent and normal. -/
theorem isStarProjection_iff_isIdempotentElem_and_isStarNormal {p : A} :
    IsStarProjection p ↔ IsIdempotentElem p ∧ IsStarNormal p :=
  (isStarProjection_iff p).eq ▸ and_congr_right_iff.eq ▸ fun h => h.isSelfAdjoint_iff_isStarNormal

theorem isStarProjection_iff_quasispectrum_subset_and_isStarNormal {p : A} :
    IsStarProjection p ↔ quasispectrum ℂ p ⊆ {0, 1} ∧ IsStarNormal p :=
  isStarProjection_iff_isIdempotentElem_and_isStarNormal (p := p).eq ▸
    and_congr_left_iff.mpr fun h ↦ isIdempotentElem_iff_quasispectrum_subset ℂ p h

end Normal
end NonUnital

section Unital
variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A]

lemma isStarProjection_iff_spectrum_subset_and_isSelfAdjoint [Algebra ℝ A]
    [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint] {p : A} :
    IsStarProjection p ↔ spectrum ℝ p ⊆ {0, 1} ∧ IsSelfAdjoint p :=
  (isStarProjection_iff p).eq ▸
    and_congr_left_iff.mpr fun h ↦ isIdempotentElem_iff_spectrum_subset ℝ p h

theorem isStarProjection_iff_spectrum_subset_and_isStarNormal [Algebra ℂ A]
    [NonUnitalContinuousFunctionalCalculus ℂ A IsStarNormal] {p : A} :
    IsStarProjection p ↔ spectrum ℂ p ⊆ {0, 1} ∧ IsStarNormal p :=
  isStarProjection_iff_isIdempotentElem_and_isStarNormal (p := p).eq ▸
    and_congr_left_iff.mpr fun h ↦ isIdempotentElem_iff_spectrum_subset ℂ p h

end Unital

namespace IsStarProjection

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {p q : A}

open CFC in
lemma le_tfae (hp : IsStarProjection p) (hq : IsStarProjection q) :
  List.TFAE
    [p ≤ q,
    q * p = p,
    p * q = p,
    IsStarProjection (q - p),
    IsIdempotentElem (q - p)] := by
  tfae_have 1 → 2 := fun h ↦ (hq.mul_right_and_mul_left_of_nonneg_of_le hp.nonneg h).2
  tfae_have 2 → 3 := fun h ↦ by
    simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $h)
  tfae_have 3 → 4 := hp.sub_of_mul_eq_left hq
  tfae_have 4 → 1 := fun h ↦ by simpa using h.nonneg
  tfae_have 4 ↔ 5 := by simp [isStarProjection_iff, hq.isSelfAdjoint.sub hp.isSelfAdjoint]
  tfae_finish

lemma le_iff_mul_eq_right (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p ≤ q ↔ q * p = p :=
  hp.le_tfae hq |>.out 0 1

lemma le_iff_mul_eq_left (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p ≤ q ↔ p * q = p :=
  hp.le_tfae hq |>.out 0 2

lemma le_iff_sub (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p ≤ q ↔ IsStarProjection (q - p) :=
  hp.le_tfae hq |>.out 0 3

lemma le_iff_idempotent_sub (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p ≤ q ↔ IsIdempotentElem (q - p) :=
  hp.le_tfae hq |>.out 0 4

lemma commute_of_le (hp : IsStarProjection p) (hq : IsStarProjection q) (h : p ≤ q) :
    Commute p q := by
  rw [commute_iff_eq, hp.le_iff_mul_eq_right hq |>.mp h, hp.le_iff_mul_eq_left hq |>.mp h]

end IsStarProjection
