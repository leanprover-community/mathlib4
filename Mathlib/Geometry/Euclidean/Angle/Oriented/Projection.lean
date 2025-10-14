/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Projection

/-!
# Oriented angles and orthogonal projection.

This file proves lemmas relating to oriented angles involving orthogonal projections.

-/


namespace EuclideanGeometry

open Module
open scoped Real

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P] [hd2 : Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

lemma oangle_self_orthogonalProjection (p : P) {p' : P} {s : AffineSubspace ℝ P}
    [s.direction.HasOrthogonalProjection] (hp : p ∉ s) (h : p' ∈ s)
    (hp' : haveI : Nonempty s := ⟨p', h⟩; p' ≠ orthogonalProjection s p) :
    haveI : Nonempty s := ⟨p', h⟩
    ∡ p (orthogonalProjection s p) p' = (π / 2 : ℝ) ∨
      ∡ p (orthogonalProjection s p) p' = (-π / 2 : ℝ) := by
  haveI : Nonempty s := ⟨p', h⟩
  have hpne : p ≠ orthogonalProjection s p := Ne.symm (orthogonalProjection_eq_self_iff.not.2 hp)
  have ha := oangle_eq_angle_or_eq_neg_angle hpne hp'
  rw [angle_self_orthogonalProjection p h] at ha
  rwa [neg_div]

lemma oangle_orthogonalProjection_self (p : P) {p' : P} {s : AffineSubspace ℝ P}
    [s.direction.HasOrthogonalProjection] (hp : p ∉ s) (h : p' ∈ s)
    (hp' : haveI : Nonempty s := ⟨p', h⟩; p' ≠ orthogonalProjection s p) :
    haveI : Nonempty s := ⟨p', h⟩
    ∡ p' (orthogonalProjection s p) p = (π / 2 : ℝ) ∨
      ∡ p' (orthogonalProjection s p) p = (-π / 2 : ℝ) := by
  rw [oangle_rev, neg_eq_iff_eq_neg, neg_eq_iff_eq_neg, or_comm, ← Real.Angle.coe_neg, neg_div,
    neg_neg, ← Real.Angle.coe_neg, ← neg_div]
  exact oangle_self_orthogonalProjection p hp h hp'

lemma two_zsmul_oangle_self_orthogonalProjection (p : P) {p' : P} {s : AffineSubspace ℝ P}
    [s.direction.HasOrthogonalProjection] (hp : p ∉ s) (h : p' ∈ s)
    (hp' : haveI : Nonempty s := ⟨p', h⟩; p' ≠ orthogonalProjection s p) :
    haveI : Nonempty s := ⟨p', h⟩
    (2 : ℤ) • ∡ p (orthogonalProjection s p) p' = π := by
  rw [Real.Angle.two_zsmul_eq_pi_iff]
  exact oangle_self_orthogonalProjection p hp h hp'

lemma two_zsmul_oangle_orthogonalProjection_self (p : P) {p' : P} {s : AffineSubspace ℝ P}
    [s.direction.HasOrthogonalProjection] (hp : p ∉ s) (h : p' ∈ s)
    (hp' : haveI : Nonempty s := ⟨p', h⟩; p' ≠ orthogonalProjection s p) :
    haveI : Nonempty s := ⟨p', h⟩
    (2 : ℤ) • ∡ p' (orthogonalProjection s p) p = π := by
  rw [Real.Angle.two_zsmul_eq_pi_iff]
  exact oangle_orthogonalProjection_self p hp h hp'

end EuclideanGeometry
