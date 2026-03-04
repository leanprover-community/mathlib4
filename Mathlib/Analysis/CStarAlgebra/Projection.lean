/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar, Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

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

public section

open scoped CStarAlgebra

section Normal

variable {A : Type*} [TopologicalSpace A]
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [NonUnitalContinuousFunctionalCalculus ℂ A IsStarNormal]

/-- An idempotent element in a non-unital C⋆-algebra is self-adjoint iff it is normal. -/
theorem IsIdempotentElem.isSelfAdjoint_iff_isStarNormal {p : A} (hp : IsIdempotentElem p) :
    IsSelfAdjoint p ↔ IsStarNormal p := by
  simp only [isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts,
    QuasispectrumRestricts.real_iff, and_iff_left_iff_imp]
  intro h x hx
  rcases hp.quasispectrum_subset hx with (hx | hx) <;> simp [Set.mem_singleton_iff.mp hx]

/-- An element in a non-unital C⋆-algebra is a star projection
if and only if it is idempotent and normal. -/
theorem isStarProjection_iff_isIdempotentElem_and_isStarNormal {p : A} :
    IsStarProjection p ↔ IsIdempotentElem p ∧ IsStarNormal p :=
  (isStarProjection_iff p).eq ▸ and_congr_right_iff.eq ▸ fun h => h.isSelfAdjoint_iff_isStarNormal

end Normal

namespace IsStarProjection

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {p q : A}

set_option backward.isDefEq.respectTransparency false in
open CFC in
lemma le_tfae (hp : IsStarProjection p) (hq : IsStarProjection q) :
  List.TFAE
    [p ≤ q,
    q * p = p,
    p * q = p,
    IsStarProjection (q - p),
    IsIdempotentElem (q - p)] := by
  tfae_have 1 → 2 := fun h ↦ by
    have key : p * (q - p) * p = 0 := by
      simp only [sub_mul, mul_sub, hp.isIdempotentElem.eq, sub_eq_zero]
      refine le_antisymm ?_ <| by
        simpa [hp.isIdempotentElem.eq] using conjugate_le_conjugate_of_nonneg h hp.nonneg
      have := by simpa [hp.inr.isIdempotentElem.eq, ← Unitization.inr_mul]
        using conjugate_le_conjugate_of_nonneg hq.inr.le_one (hp.inr (R := ℂ)).nonneg
      rwa [← Unitization.inr_le_iff (p * q * p) p ?_ hp.isSelfAdjoint]
      exact hp.isSelfAdjoint.conjugate_nonneg hq.nonneg |>.isSelfAdjoint
    rw [← norm_eq_zero, hp.isSelfAdjoint.norm_mul_mul_self_of_nonneg _ (by simpa),
      sq_eq_zero_iff, norm_eq_zero] at key
    simpa [← mul_assoc, CFC.sqrt_mul_sqrt_self (q - p) (by simpa),
      sub_mul, sub_eq_zero, hp.isIdempotentElem.eq] using congr(CFC.sqrt (q - p) * $key)
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
