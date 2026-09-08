/-
Copyright (c) 2026 Laurance Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurance Lau
-/
module

public import Mathlib.Analysis.Normed.Affine.Simplex
public import Mathlib.Geometry.Euclidean.MongePoint

/-!
# Equilateral simplices in Euclidean space

This file proves properties of equilateral simplices in Euclidean space,
particularly that the centroid, circumcenter, and Monge point coincide.

## TODO
- The incenter also coincides.
- Theorems in the converse direction.

-/

@[expose] public section

namespace Affine.Simplex

open AffineSubspace EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] {n : ℕ} {i j k : Fin (n + 1)} {s : Simplex ℝ P n}

/-- The circumcenter lies on the perpendicular bisector of any two points. -/
lemma circumcenter_mem_perpBisector :
    s.circumcenter ∈ perpBisector (s.points i) (s.points j) := by
  simp only [mem_perpBisector_iff_dist_eq, dist_circumcenter_eq_circumradius']

namespace Equilateral

lemma equilateral_faceOpposite [NeZero n] (h : s.Equilateral) : (s.faceOpposite i).Equilateral := by
  obtain ⟨r, hr⟩ := h
  use r
  aesop

/-- Any point lies on the perpendicular bisector of any two other points. -/
lemma mem_perpBisector (h : s.Equilateral) (hij : i ≠ j) (hik : i ≠ k) :
    s.points i ∈ perpBisector (s.points j) (s.points k) := by
  obtain ⟨r, hr⟩ := h
  simp_all only [ne_eq, mem_perpBisector_iff_dist_eq, not_false_eq_true]

section Center

/-- The distance between any point and the centroid is constant. -/
lemma dist_centroid (h : s.Equilateral) :
    dist (s.points i) s.centroid = dist (s.points j) s.centroid := by
  obtain ⟨r, hr⟩ := h
  have mul_sq_norm_eq i : (n + 1) * ‖s.points i -ᵥ s.centroid‖ ^ 2 =
      n * r ^ 2 - ∑ k, ‖s.points k -ᵥ s.centroid‖ ^ 2 := by
    have : ∑ l, inner ℝ (s.points i -ᵥ s.centroid) (s.points l -ᵥ s.centroid) = 0 := by
      simp [← inner_sum, s.centroid_weighted_vsub_eq_zero]
    have h l (hl : l ∈ Finset.univ.erase i) :
        2 * inner ℝ (s.points i -ᵥ s.centroid) (s.points l -ᵥ s.centroid) =
          ‖s.points i -ᵥ s.centroid‖ ^ 2 + ‖s.points l -ᵥ s.centroid‖ ^ 2 - r ^ 2 := by
      grind [hr i l (Finset.ne_of_mem_erase hl).symm, dist_eq_norm_vsub,
        vsub_sub_vsub_cancel_right (s.points i) (s.points l) s.centroid, norm_sub_sq_real]
    have := Finset.sum_congr rfl h
    simp [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib] at this
    grind
  rw [dist_eq_norm_vsub, dist_eq_norm_vsub, ← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    ← mul_right_inj' n.cast_add_one_ne_zero, mul_sq_norm_eq, mul_sq_norm_eq]

/-- The centroid is the circumcenter. -/
lemma centroid_eq_circumcenter (h : s.Equilateral) : s.centroid = s.circumcenter :=
    s.eq_circumcenter_of_dist_eq s.centroid_mem_affineSpan (r := dist (s.points 0) s.centroid)
      fun _ ↦ h.dist_centroid

/-- The centroid is the Monge point. -/
lemma centroid_eq_mongePoint (h : s.Equilateral) : s.centroid = s.mongePoint := by
  simp [mongePoint, h.centroid_eq_circumcenter]

/-- The circumcenter is the Monge point. -/
lemma circumcenter_eq_mongePoint (h : s.Equilateral) : s.circumcenter = s.mongePoint :=
  h.centroid_eq_circumcenter.symm.trans h.centroid_eq_mongePoint

end Center

end Equilateral

end Affine.Simplex
