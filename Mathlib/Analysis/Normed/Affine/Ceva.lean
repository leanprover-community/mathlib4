/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.LinearAlgebra.AffineSpace.Ceva

/-!
# Ceva's theorem.

This file proves various versions of Ceva's theorem in a `NormedAddTorsor`.

## References

* https://en.wikipedia.org/wiki/Ceva%27s_theorem

-/

@[expose] public section


open scoped Affine

variable {𝕜 V P : Type*} [SeminormedAddCommGroup V] [NormedField 𝕜] [NormedSpace 𝕜 V]

namespace Affine.Triangle

variable [PseudoMetricSpace P] [NormedAddTorsor V P] in
/-- **Ceva's theorem** for a triangle, expressed in terms of multiplying distances. -/
lemma prod_dist_eq_prod_dist_of_mem_line_of_mem_line {t : Triangle 𝕜 P} {p : Fin 3 → P} {p' : P}
    (hp : ∀ i : Fin 3, p i ∈ line[𝕜, t.points (i + 1), t.points (i + 2)])
    (hp' : ∀ i : Fin 3, p' ∈ line[𝕜, t.points i, p i]) :
    ∏ i, dist (t.points (i + 1)) (p i) = ∏ i, dist (p i) (t.points (i + 2)) := by
  simp_rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hp
  choose r hr using hp
  simp_rw [← hr] at hp'
  simp_rw [← hr, dist_lineMap_right, dist_left_lineMap, Finset.prod_mul_distrib, ← norm_prod,
    prod_eq_prod_one_sub_of_mem_line_point_lineMap hp']

variable [MetricSpace P] [NormedAddTorsor V P] in
/-- **Ceva's theorem** for a triangle, expressed using division of distances. -/
lemma prod_dist_div_dist_eq_one_of_mem_line_of_mem_line {t : Triangle 𝕜 P} {p : Fin 3 → P} {p' : P}
    (hp0 : ∀ i, p i ≠ t.points (i + 1))
    (hp : ∀ i : Fin 3, p i ∈ line[𝕜, t.points (i + 1), t.points (i + 2)])
    (hp' : ∀ i : Fin 3, p' ∈ line[𝕜, t.points i, p i]) :
    ∏ i, dist (t.points (i + 1)) (p i) / dist (p i) (t.points (i + 2)) = 1 := by
  simp_rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hp
  choose r hr using hp
  simp_rw [← hr] at hp'
  simp_rw [← hr, dist_lineMap_right, dist_left_lineMap, Finset.prod_div_distrib,
    Finset.prod_mul_distrib, ← norm_prod]
  rw [mul_div_mul_right]
  · rw [← norm_div, ← Finset.prod_div_distrib]
    have hr0 : ∀ i, r i ≠ 0 := by
      intro i hri
      apply hp0 i
      simpa [hri] using (hr i).symm
    rw [prod_div_one_sub_eq_one_of_mem_line_point_lineMap hr0 hp', norm_one]
  · rw [Finset.prod_ne_zero_iff]
    rintro i -
    rw [dist_ne_zero]
    exact t.independent.injective.ne (by grind)

end Affine.Triangle
