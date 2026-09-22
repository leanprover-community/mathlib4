/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Geometry.Euclidean.Volume.Def
public import Mathlib.Geometry.Euclidean.Incenter

import Mathlib.Geometry.Euclidean.Volume.Basic

/-!

# Incenters, excenters, and volumes of simplices

This file explores the interaction between incenters, excenters, and volumes of simplices. It shows
that the volumes of faces are weights to characterize excenters, and the volume of the simplex can
be calculated using exradius.

## Main declarations
* `Affine.Simplex.excenterWeightsFace` are volumes of faces attached with a sign. These are
  proportional to `Affine.Simplex.excenterWeights`. (See
  `Affine.Simplex.excenterWeights_eq_excenterWeightsFace_div`)
* `Affine.Simplex.ExcenterExists.volume_eq_exradius_mul`: the volume of the simplex is the product
  of `Affine.Simplex.exradius` and the sum of `Affine.Simplex.excenterWeightsFace`, divided by
  the dimension.
* `Affine.Simplex.volume_eq_inradius_mul`: the volume of the simplex is the product of
  `Affine.Simplex.inradius` and the surface area, divided by the dimension.

-/

@[expose] public section

namespace Affine.Simplex

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] {n : ℕ} [NeZero n]

/--
Similar to `Affine.Simplex.excenterWeightsUnnorm`, these are unnormalized weights whose affine
combination gives an excenter with the signs determined by the given set of indices. It is defined
as the volume of the `Affine.Simplex.faceOpposite` attached with a sign.
-/
noncomputable def excenterWeightsFace (s : Simplex ℝ P n) (signs : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) : ℝ :=
  (if i ∈ signs then -1 else 1) * (s.faceOpposite i).volume

theorem excenterWeightsFace_ne_zero (s : Simplex ℝ P n)
    (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    s.excenterWeightsFace signs i ≠ 0 := by
  unfold excenterWeightsFace
  positivity

@[simp]
theorem excenterWeightsFace_empty_apply (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    s.excenterWeightsFace ∅ i = (s.faceOpposite i).volume := by
  simp [excenterWeightsFace]

theorem excenterWeightsFace_eq_volume_mul_excenterWeightsUnnorm (s : Simplex ℝ P n)
    (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    s.excenterWeightsFace signs i = n * s.volume * s.excenterWeightsUnnorm signs i := by
  rw [s.volume_eq i, excenterWeightsUnnorm, excenterWeightsFace]
  field [‹NeZero n›.ne]

theorem excenterWeightsFace_reindex {m : ℕ} [NeZero m] (s : Simplex ℝ P n)
    (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m + 1))) :
    (s.reindex e).excenterWeightsFace signs =
    s.excenterWeightsFace (Finset.map e.symm.toEmbedding signs) ∘ e.symm := by
  have h : n = m := by simpa using Fin.equiv_iff_eq.mp ⟨e⟩
  ext
  simp [excenterWeightsFace_eq_volume_mul_excenterWeightsUnnorm, excenterWeightsUnnorm_reindex, h]

@[simp]
theorem excenterWeightsFace_map {P₂ : Type*} [MetricSpace P₂] [NormedAddTorsor V P₂]
    (s : Simplex ℝ P n) (f : P →ᵃⁱ[ℝ] P₂) :
    (s.map f.toAffineMap f.injective).excenterWeightsFace = s.excenterWeightsFace := by
  ext
  simp [excenterWeightsFace]

@[simp]
theorem excenterWeightsFace_restrict (s : Simplex ℝ P n) (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).excenterWeightsFace = s.excenterWeightsFace := by
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  ext
  simp [excenterWeightsFace, faceOpposite_restrict]

theorem excenterExists_iff_sum_excenterWeightsFace_ne_zero (s : Simplex ℝ P n)
    (signs : Finset (Fin (n + 1))) :
    s.ExcenterExists signs ↔ ∑ i, s.excenterWeightsFace signs i ≠ 0 := by
  simp [excenterWeightsFace_eq_volume_mul_excenterWeightsUnnorm, ← Finset.mul_sum,
    ExcenterExists, ‹NeZero n›.ne, s.volume_pos.ne']

theorem excenterWeights_eq_excenterWeightsFace_div (s : Simplex ℝ P n)
    (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    s.excenterWeights signs i =
      s.excenterWeightsFace signs i / ∑ j, s.excenterWeightsFace signs j := by
  simp_rw [excenterWeightsFace_eq_volume_mul_excenterWeightsUnnorm, ← Finset.mul_sum,
    excenterWeights, Pi.smul_apply, smul_eq_mul]
  field [‹NeZero n›.ne]

theorem ExcenterExists.volume_eq_exradius_mul {s : Simplex ℝ P n} {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) :
    s.volume = (↑n)⁻¹ * s.exradius signs * |∑ i, s.excenterWeightsFace signs i| := by
  have : |∑ i, s.excenterWeightsUnnorm signs i| ≠ 0 := by simpa [ExcenterExists] using h
  simp_rw [excenterWeightsFace_eq_volume_mul_excenterWeightsUnnorm, ← Finset.mul_sum, abs_mul,
    exradius_eq_abs_inv_sum, abs_inv, Nat.abs_cast, abs_of_nonneg s.volume_pos.le]
  field [‹NeZero n›.ne]

theorem volume_eq_inradius_mul (s : Simplex ℝ P n) :
    s.volume = (↑n)⁻¹ * s.inradius * ∑ i, (s.faceOpposite i).volume := by
  have : 0 < ∑ x, (s.faceOpposite x).volume := by positivity
  simpa [abs_of_nonneg this.le] using s.excenterExists_empty.volume_eq_exradius_mul

end Affine.Simplex
