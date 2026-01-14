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
    (hp0 : ∀ i, p i ≠ t.points (i + 2))
    (hp : ∀ i : Fin 3, p i ∈ line[𝕜, t.points (i + 1), t.points (i + 2)])
    (hp' : ∀ i : Fin 3, p' ∈ line[𝕜, t.points i, p i]) :
    ∏ i, dist (t.points (i + 1)) (p i) / dist (p i) (t.points (i + 2)) = 1 := by
  have aux (i) : dist (p i) (t.points (i + 2)) ≠ 0 := by simpa using hp0 i
  have key := prod_dist_eq_prod_dist_of_mem_line_of_mem_line hp hp'
  rw [Fin.prod_univ_three] at key ⊢
  rw [Fin.prod_univ_three] at key
  have := aux 0
  have := aux 1
  have := aux 2
  field_simp
  exact key

end Affine.Triangle
