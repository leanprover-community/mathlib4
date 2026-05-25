/-
Copyright (c) 2026 Chu Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chu Zheng
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.LinearAlgebra.AffineSpace.Menelaus
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Menelaus' theorem.

This file proves of Menelaus' theorem in a `NormedAddTorsor`.

## References

* https://en.wikipedia.org/wiki/Menelaus%27_theorem

-/

public section

open scoped Affine

variable {𝕜 V P : Type*} [SeminormedAddCommGroup V] [NormedField 𝕜] [NormedSpace 𝕜 V]

namespace Affine.Triangle

variable [PseudoMetricSpace P] [NormedAddTorsor V P] in
/-- **Menelaus' theorem** for a triangle, expressed in terms of multiplying distances. -/
theorem prod_dist_eq_prod_dist_of_mem_line_of_collinear {t : Triangle 𝕜 P} {p : Fin 3 → P}
    (hp : ∀ i : Fin 3, p i ∈ line[𝕜, t.points (i + 1), t.points (i + 2)])
    (hcol : Collinear 𝕜 {p 0, p 1, p 2}) :
    ∏ i, dist (t.points (i + 1)) (p i) = ∏ i, dist (p i) (t.points (i + 2)) := by
  simp_rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hp
  choose r hr using hp
  have h:= (t.prod_eq_neg_prod_one_sub_iff_collinear_iff_of_lineMap hr).mpr hcol
  simp_rw [← hr, dist_lineMap_right, dist_left_lineMap, Finset.prod_mul_distrib, ← norm_prod]
  rw [h, norm_neg]

variable [MetricSpace P] [NormedAddTorsor V P] in
/-- **Menelaus' theorem** for a triangle, expressed using division of distances. -/
theorem prod_dist_div_dist_eq_one_of_mem_line_of_collinear {t : Triangle 𝕜 P} {p : Fin 3 → P}
    (hp0 : ∀ i, p i ≠ t.points (i + 2))
    (hp : ∀ i : Fin 3, p i ∈ line[𝕜, t.points (i + 1), t.points (i + 2)])
    (hcol : Collinear 𝕜 {p 0, p 1, p 2}) :
    ∏ i, dist (t.points (i + 1)) (p i) / dist (p i) (t.points (i + 2)) = 1 := by
  have h := prod_dist_eq_prod_dist_of_mem_line_of_collinear hp hcol
  rw [Finset.prod_div_distrib, h, div_self]
  exact Finset.prod_ne_zero_iff.2 fun i _ ↦ by grind [dist_ne_zero]

end Affine.Triangle
