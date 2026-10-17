/-
Copyright (c) 2026 Chu Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chu Zheng
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.LinearAlgebra.AffineSpace.Menelaus
public import Mathlib.Analysis.Convex.Between

/-!
# Menelaus' theorem.

This file proves Menelaus' theorem in a `NormedAddTorsor`.

## References

* https://en.wikipedia.org/wiki/Menelaus%27_theorem

-/

public section

open scoped Affine BigOperators

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
  have h := (t.prod_eq_neg_prod_one_sub_iff_collinear_of_lineMap hr).mpr hcol
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

section LinearOrderedField

variable {k E P : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [Module k E] [AddTorsor E P]

private lemma div_one_sub_nonneg_iff_wbtw {a b : P} {r : k} (hab : a ≠ b) :
    0 ≤ r / (1 - r) ↔ Wbtw k (V := E) a (AffineMap.lineMap a b r) b := by
  rw [wbtw_lineMap_iff, or_iff_right hab, Set.mem_Icc]
  constructor
  · intro h
    grind [div_nonneg_iff]
  · rintro ⟨hr0, hr1⟩
    exact div_nonneg hr0 (sub_nonneg.mpr hr1)

private lemma div_one_sub_neg_iff_not_wbtw {a b : P} {r : k} (hab : a ≠ b) :
    r / (1 - r) < 0 ↔ ¬ Wbtw k (V := E) a (AffineMap.lineMap a b r) b := by
  rw [← iff_not_comm, not_lt]
  symm
  exact div_one_sub_nonneg_iff_wbtw hab

end LinearOrderedField

section LinearOrderedRing

variable {k : Type*} [CommRing k] [LinearOrder k] [IsStrictOrderedRing k]

open SignType

private lemma prod_neg_of_odd_ncard {ι : Type*} [Fintype ι] {q : ι → k}
    (hne : ∀ i, q i ≠ 0) (hodd : Odd ({i : ι | q i < 0}.ncard)) :
    ∏ i, q i < 0 := by
  classical
  have hfilter : Finset.univ.filter (fun i => q i < 0) = {i : ι | q i < 0}.toFinset := by grind
  have hodd' : Odd (Finset.univ.filter (fun i => q i < 0)).card := by
    grind [← Set.ncard_eq_toFinset_card']
  refine sign_eq_neg_one_iff.mp ?_
  calc
    sign (∏ i, q i) = ∏ i, sign (q i) := map_prod (signHom : k →*₀ SignType) q Finset.univ
    _ = ∏ i, if q i < 0 then (-1 : SignType) else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hneg : q i < 0
      · simp [sign_neg hneg, hneg]
      · have hpos : 0 < q i := lt_of_le_of_ne (le_of_not_gt hneg) (hne i).symm
        simp [sign_pos hpos, hneg]
    _ = (-1 : SignType) ^ (Finset.univ.filter (fun i => q i < 0)).card := by
      rw [Finset.prod_ite]
      simp [Finset.prod_const]
    _ = (-1 : SignType) := SignType.pow_odd (-1 : SignType) hodd'

end LinearOrderedRing

section Real

variable {V P : Type*}
variable [SeminormedAddCommGroup V] [NormedSpace ℝ V]
variable [MetricSpace P] [NormedAddTorsor V P]

/-- The converse to **Menelaus' theorem** for a triangle, expressed as an equality of products.
The odd cardinality assumption records that an odd number of the points lie outside the
corresponding closed segments.
-/
theorem collinear_of_prod_dist_eq_prod_dist_of_odd_card
    {t : Triangle ℝ P} {p : Fin 3 → P}
    (hp : ∀ i, p i ∈ line[ℝ, t.points (i + 1), t.points (i + 2)])
    (hodd : Odd ({i : Fin 3 | ¬ Wbtw ℝ (t.points (i + 1)) (p i) (t.points (i + 2))}.ncard))
    (hprod : (∏ i, dist (t.points (i + 1)) (p i)) = ∏ i, dist (p i) (t.points (i + 2))) :
    Collinear ℝ {p 0, p 1, p 2} := by
  simp_rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hp
  choose r hr using hp
  have hside_ne (i : Fin 3) : t.points (i + 1) ≠ t.points (i + 2) := by
    intro h
    have hidx : (i + 1 : Fin 3) ≠ (i + 2 : Fin 3) := by fin_cases i <;> simp
    exact hidx (t.independent.injective h)
  by_cases hprod_ne : (∏ i, dist (p i) (t.points (i + 2))) ≠ 0
  · have hprod_div : ∏ i, dist (t.points (i + 1)) (p i) / dist (p i) (t.points (i + 2)) = 1 := by
      grind [Finset.prod_div_distrib]
    let q : Fin 3 → ℝ := fun i => r i / (1 - r i)
    have hratio (i : Fin 3) :
        dist (t.points (i + 1)) (p i) / dist (p i) (t.points (i + 2)) = ‖q i‖ := by
      rw [← hr i, dist_left_lineMap, dist_lineMap_right, norm_div]
      field_simp [dist_ne_zero.mpr (hside_ne i)]
    have hnormprod : ∏ i, ‖q i‖ = 1 := by grind
    have hq_ne (i : Fin 3) : q i ≠ 0 := by
      have hprod_ne : (∏ i, ‖q i‖) ≠ 0 := by grind
      have hnorm_ne : ‖q i‖ ≠ 0 := (Finset.prod_ne_zero_iff.mp hprod_ne) i (Finset.mem_univ i)
      grind [norm_eq_zero]
    have hneg_iff (i : Fin 3) : q i < 0 ↔ ¬ Wbtw ℝ (t.points (i + 1)) (p i) (t.points (i + 2)) := by
      change r i / (1 - r i) < 0 ↔ ¬ Wbtw ℝ (V := V) (t.points (i + 1)) (p i) (t.points (i + 2))
      grind [div_one_sub_neg_iff_not_wbtw]
    have hset : {i : Fin 3 | ¬ Wbtw ℝ (t.points (i + 1)) (p i) (t.points (i + 2))} =
        {i : Fin 3 | q i < 0} := by grind
    have hqprod_neg : ∏ i, q i < 0 := by grind [prod_neg_of_odd_ncard]
    have hqprod_norm : ‖∏ i, q i‖ = 1 := by grind [norm_prod]
    have hqprod_eq_neg_one : ∏ i, q i = -1 := by grind [Real.norm_eq_abs, abs_of_neg hqprod_neg]
    have hone_sub_ne (i : Fin 3) : 1 - r i ≠ 0 := by grind
    have hden_ne : ∏ i, (1 - r i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hone_sub_ne i
    have hmenelaus : ∏ i, r i = - ∏ i, (1 - r i) := by
      have h := hqprod_eq_neg_one
      simp only [q, Finset.prod_div_distrib] at h
      grind
    exact (t.prod_eq_neg_prod_one_sub_iff_collinear_of_lineMap hr).mp hmenelaus
  · have hprod_right : (∏ i, dist (p i) (t.points (i + 2))) = 0 := by grind
    have hprod_left : (∏ i, dist (t.points (i + 1)) (p i)) = 0 := by grind
    obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hprod_right
    obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hprod_left
    rw [dist_eq_zero] at hi hj
    have hri : r i = 1 := by
      apply (AffineMap.lineMap_eq_right_iff.mp ?_).resolve_left (hside_ne i)
      grind
    have hrj : r j = 0 := by
      apply (AffineMap.lineMap_eq_left_iff.mp ?_).resolve_left (hside_ne j)
      grind
    apply (t.prod_eq_neg_prod_one_sub_iff_collinear_of_lineMap hr).mp
    grind [Finset.prod_eq_zero]

/-- The converse to **Menelaus' theorem** for a triangle, expressed using division of distances. -/
theorem collinear_of_prod_dist_div_dist_eq_one_of_odd_card
    {t : Triangle ℝ P} {p : Fin 3 → P}
    (hp : ∀ i, p i ∈ line[ℝ, t.points (i + 1), t.points (i + 2)])
    (hodd : Odd ({i : Fin 3 | ¬ Wbtw ℝ (t.points (i + 1)) (p i) (t.points (i + 2))}.ncard))
    (hprod : ∏ i, dist (t.points (i + 1)) (p i) / dist (p i) (t.points (i + 2)) = 1) :
    Collinear ℝ {p 0, p 1, p 2} := by
  rw [Finset.prod_div_distrib] at hprod
  have hprod_ne : (∏ i, dist (p i) (t.points (i + 2))) ≠ 0 := by grind
  exact collinear_of_prod_dist_eq_prod_dist_of_odd_card hp hodd <|
    (div_eq_one_iff_eq hprod_ne).mp hprod

/-- The distance form of the converse to **Menelaus' theorem** is an equivalence when the
points do not coincide with the corresponding second vertex. -/
theorem prod_dist_div_dist_eq_one_iff_collinear_of_mem_line_of_odd_card
    {t : Triangle ℝ P} {p : Fin 3 → P}
    (hp0 : ∀ i, p i ≠ t.points (i + 2))
    (hp : ∀ i, p i ∈ line[ℝ, t.points (i + 1), t.points (i + 2)])
    (hodd : Odd ({i : Fin 3 | ¬ Wbtw ℝ (t.points (i + 1)) (p i) (t.points (i + 2))}.ncard)) :
    (∏ i, dist (t.points (i + 1)) (p i) / dist (p i) (t.points (i + 2)) = 1) ↔
      Collinear ℝ {p 0, p 1, p 2} :=
  ⟨collinear_of_prod_dist_div_dist_eq_one_of_odd_card hp hodd,
    prod_dist_div_dist_eq_one_of_mem_line_of_collinear hp0 hp⟩

/-- The distance form of **Menelaus' theorem**, expressed as an equality of products. -/
theorem prod_dist_eq_prod_dist_iff_collinear_of_mem_line_of_odd_card
    {t : Triangle ℝ P} {p : Fin 3 → P}
    (hp : ∀ i, p i ∈ line[ℝ, t.points (i + 1), t.points (i + 2)])
    (hodd : Odd ({i : Fin 3 | ¬ Wbtw ℝ (t.points (i + 1)) (p i) (t.points (i + 2))}.ncard)) :
    (∏ i, dist (t.points (i + 1)) (p i)) =
      (∏ i, dist (p i) (t.points (i + 2))) ↔ Collinear ℝ {p 0, p 1, p 2} :=
  ⟨collinear_of_prod_dist_eq_prod_dist_of_odd_card hp hodd,
    prod_dist_eq_prod_dist_of_mem_line_of_collinear hp⟩

end Real

end Affine.Triangle
