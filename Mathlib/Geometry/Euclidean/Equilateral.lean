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

namespace Affine

variable {R V P : Type*} [RCLike R] [NormedAddCommGroup V] [InnerProductSpace R V] [MetricSpace P]
  [NormedAddTorsor V P]

namespace Simplex

variable {n : ℕ} {i j k : Fin (n + 1)} {s : Simplex R P n}

lemma sum_inner_vsub_centroid (i : Fin (n + 1)) :
    ∑ l, inner R (s.points i -ᵥ s.centroid) (s.points l -ᵥ s.centroid) = 0 := by
  simp [← inner_sum, s.centroid_weighted_vsub_eq_zero]

open AffineSubspace

variable [InnerProductSpace ℝ V] {s : Simplex ℝ P n}

/-- The circumcenter lies on the perpendicular bisector of any two points. -/
lemma circumcenter_mem_perpBisector :
    s.circumcenter ∈ perpBisector (s.points i) (s.points j) := by
  simp only [mem_perpBisector_iff_dist_eq, dist_circumcenter_eq_circumradius']

namespace Equilateral

/-- Any point lies on the perpendicular bisector of any two other points. -/
lemma mem_perpBisector (h : s.Equilateral) (hij : i ≠ j) (hik : i ≠ k) :
    s.points i ∈ perpBisector (s.points j) (s.points k) :=
  mem_perpBisector_iff_dist_eq.2 (h.dist_eq hij hik)

section Center

lemma dist_centroid_sq_eq (h : s.Equilateral) (hjk : j ≠ k) : dist (s.points i) s.centroid ^ 2 =
    (n * dist (s.points j) (s.points k) ^ 2 - ∑ k, dist (s.points k) s.centroid ^ 2) / (n + 1) := by
  obtain ⟨r, hr⟩ := h
  have h l (hl : l ∈ Finset.univ.erase i) :
      2 * inner ℝ (s.points i -ᵥ s.centroid) (s.points l -ᵥ s.centroid) =
        ‖s.points i -ᵥ s.centroid‖ ^ 2 + ‖s.points l -ᵥ s.centroid‖ ^ 2 - r ^ 2 := by
    grind [hr i l (Finset.ne_of_mem_erase hl).symm, dist_eq_norm_vsub, vsub_sub_vsub_cancel_right,
      norm_sub_sq_real]
  have := Finset.sum_congr rfl h
  simp [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib] at this
  grind [dist_eq_norm_vsub, s.sum_inner_vsub_centroid i]

/-- The distance between any point and the centroid is constant. -/
lemma dist_centroid_eq (h : s.Equilateral) :
    dist (s.points i) s.centroid = dist (s.points j) s.centroid := by
  by_cases hij : i = j
  · rw [hij]
  · rw [← sq_eq_sq₀ dist_nonneg dist_nonneg, h.dist_centroid_sq_eq hij, h.dist_centroid_sq_eq hij]

/-- The centroid is the circumcenter. -/
lemma centroid_eq_circumcenter (h : s.Equilateral) : s.centroid = s.circumcenter :=
  s.eq_circumcenter_of_dist_eq s.centroid_mem_affineSpan (r := dist (s.points 0) s.centroid)
    fun _ ↦ h.dist_centroid_eq

/-- The centroid is the Monge point. -/
lemma centroid_eq_mongePoint (h : s.Equilateral) : s.centroid = s.mongePoint := by
  simp [mongePoint, h.centroid_eq_circumcenter]

/-- The circumcenter is the Monge point. -/
lemma circumcenter_eq_mongePoint (h : s.Equilateral) : s.circumcenter = s.mongePoint :=
  h.centroid_eq_circumcenter.symm.trans h.centroid_eq_mongePoint

end Center

end Equilateral

end Simplex

namespace Triangle

variable {i j k : Fin 3} [InnerProductSpace ℝ V] {t : Triangle ℝ P}

/-- The centroid is the orthocenter. -/
lemma centroid_eq_orthocenter (h : t.Equilateral) : t.centroid = t.orthocenter :=
  h.centroid_eq_mongePoint

/-- The circumcenter is the orthocenter. -/
lemma circumcenter_eq_orthocenter (h : t.Equilateral) : t.circumcenter = t.orthocenter :=
  h.circumcenter_eq_mongePoint

end Triangle

end Affine
