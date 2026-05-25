/-
Copyright (c) 2026 Chu Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chu Zheng
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
/-!
# Menelaus' theorem.

This file proves various versions of Menelaus' theorem.

## References

* https://en.wikipedia.org/wiki/Menelaus%27_theorem
-/

public section

open scoped Affine

variable {k V P ι : Type*}

namespace Affine.Triangle

section CommRing

variable [CommRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/-- **Menelaus' theorem** for three points on the sidelines of a triangle, expressed by a
product identity for their line-map parameters. -/
theorem prod_eq_neg_prod_one_sub_of_lineMap_of_mem_line {t : Triangle k P} {r : Fin 3 → k}
    {p : Fin 3 → P} (hp : ∀ i : Fin 3,
      AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) (r i) = p i)
    (hcol : p 0 ∈ line[k, p 1, p 2]) :
    ∏ i, r i = - ∏ i, (1 - r i) := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hcol
  obtain ⟨c, hc⟩ := hcol
  simp_rw [← hp] at hc
  let w0 : Fin 3 → k := Finset.affineCombinationLineMapWeights 1 2 (r 0)
  let w1 : Fin 3 → k := Finset.affineCombinationLineMapWeights 2 0 (r 1)
  let w2 : Fin 3 → k := Finset.affineCombinationLineMapWeights 0 1 (r 2)
  have hw0 : ∑ i, w0 i = 1 := by grind [Finset.univ.sum_affineCombinationLineMapWeights]
  have hw1 : ∑ i, w1 i = 1 := by grind [Finset.univ.sum_affineCombinationLineMapWeights]
  have hw2 : ∑ i, w2 i = 1 := by grind [Finset.univ.sum_affineCombinationLineMapWeights]
  have hw12 : ∑ i, AffineMap.lineMap w1 w2 c i = 1 := by
    simp [AffineMap.lineMap_apply_module, Finset.sum_add_distrib, ← Finset.mul_sum, hw1, hw2]
  have hEq := (t.independent.affineCombination_eq_iff_eq hw12 hw0).1 <| by
    rw [← Finset.lineMap_affineCombination]
    simpa [w0, w1, w2] using hc
  have h0 : (1 - c) * r 1 + c * (1 - r 2) = 0 := by
    simpa [w0, w1, w2, AffineMap.lineMap_apply_module] using hEq 0 (by simp)
  have h1 : c * r 2 = 1 - r 0 := by
    simpa [w0, w1, w2, AffineMap.lineMap_apply_module] using hEq 1 (by simp)
  rw [Fin.prod_univ_three, Fin.prod_univ_three]
  grind

end CommRing

section Field

variable [Field k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/-- **Menelaus' theorem** for three collinear points on the sidelines of a triangle. -/
theorem prod_eq_neg_prod_one_sub_of_lineMap_of_collinear {t : Triangle k P} {r : Fin 3 → k}
    {p : Fin 3 → P} (hp : ∀ i : Fin 3,
      AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) (r i) = p i)
    (hcol : Collinear k {p 0, p 1, p 2}) :
    ∏ i, r i = - ∏ i, (1 - r i) := by
  by_cases hp12 : p 1 = p 2
  · let w1 : Fin 3 → k := Finset.affineCombinationLineMapWeights 2 0 (r 1)
    let w2 : Fin 3 → k := Finset.affineCombinationLineMapWeights 0 1 (r 2)
    have hw1 : ∑ i, w1 i = 1 := by grind [Finset.univ.sum_affineCombinationLineMapWeights]
    have hw2 : ∑ i, w2 i = 1 := by grind [Finset.univ.sum_affineCombinationLineMapWeights]
    have hcomb : Finset.univ.affineCombination k t.points w1 =
        Finset.univ.affineCombination k t.points w2 := by
      have h1: Finset.univ.affineCombination k t.points w1 = p 1 := by simpa [w1] using hp 1
      have h2: Finset.univ.affineCombination k t.points w2 = p 2 := by simpa [w2] using hp 2
      grind
    have hEq := (t.independent.affineCombination_eq_iff_eq hw1 hw2).1 hcomb
    have hr2 : r 2 = 0 := by simpa [w1, w2] using (hEq 1 (by simp)).symm
    have hr1 : r 1 = 1 := by
      have h2 : 1 - r 1 = 0 := by simpa [w1, w2] using hEq 2 (by simp)
      grind
    simp [Fin.prod_univ_three, hr1, hr2]
  · have h' : p 0 ∈ line[k, p 1, p 2] := by grind[ hcol.mem_affineSpan_of_mem_of_ne]
    exact t.prod_eq_neg_prod_one_sub_of_lineMap_of_mem_line hp h'

private lemma aux_menelaus_inv {t : Triangle k P} {r : Fin 3 → k} {p : Fin 3 → P} (hr2 : r 2 ≠ 0)
    (hp : ∀ i : Fin 3, AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) (r i) = p i)
    (h_prod_eq : ∏ i, r i = - ∏ i, (1 - r i)) :
    p 0 ∈ line[k, p 1, p 2] := by
  let w0 : Fin 3 → k := Finset.affineCombinationLineMapWeights 1 2 (r 0)
  let w1 : Fin 3 → k := Finset.affineCombinationLineMapWeights 2 0 (r 1)
  let w2 : Fin 3 → k := Finset.affineCombinationLineMapWeights 0 1 (r 2)
  let c : k := (1 - r 0) / r 2
  have hw0 : ∑ i, w0 i = 1 := by grind [Finset.univ.sum_affineCombinationLineMapWeights]
  have hw1 : ∑ i, w1 i = 1 := by grind [Finset.univ.sum_affineCombinationLineMapWeights]
  have hw2 : ∑ i, w2 i = 1 := by grind [Finset.univ.sum_affineCombinationLineMapWeights]
  have hpoly : 1 - r 0 - r 1 - r 2 + r 0 * r 1 + r 0 * r 2 + r 1 * r 2 = 0 := by
    grind [Fin.prod_univ_three, mul_assoc]
  have hc0 : (1 - c) * r 1 + c * (1 - r 2) = 0 := by grind
  have hc1 : c * r 2 = 1 - r 0 := by grind
  have hweights : ∀ i ∈ Finset.univ, w0 i = AffineMap.lineMap (w1 i) (w2 i) c := by
    intro i _
    fin_cases i
    · simpa [w0, w1, w2, c, AffineMap.lineMap_apply_module, smul_eq_mul] using hc0.symm
    · simpa [w0, w1, w2, c, AffineMap.lineMap_apply_module, smul_eq_mul] using hc1.symm
    · have hc2 : (1 - c) * (1 - r 1) = r 0 := by grind
      simpa [w0, w1, w2, c, AffineMap.lineMap_apply_module, smul_eq_mul] using hc2.symm
  have hcomb : Finset.univ.affineCombination k t.points w0 =
      AffineMap.lineMap (Finset.univ.affineCombination k t.points w1)
        (Finset.univ.affineCombination k t.points w2) c := by
    exact (t.independent.affineCombination_eq_lineMap_iff_weight_lineMap hw0 hw1 hw2 c).2 hweights
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  refine ⟨c, ?_⟩
  simp_rw [← hp 0, ← hp 1, ← hp 2]
  simpa [w0, w1, w2] using hcomb.symm

/-- The converse to **Menelaus' theorem** for three points on the sidelines of a triangle. -/
theorem collinear_of_lineMap_of_prod_eq_neg_prod_one_sub {t : Triangle k P} {r : Fin 3 → k}
    {p : Fin 3 → P}
    (hp : ∀ i : Fin 3, AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) (r i) = p i)
    (h_prod_eq : ∏ i, r i = - ∏ i, (1 - r i)) :
    Collinear k {p 0, p 1, p 2} := by
  by_cases hp12 : p 1 = p 2
  · simpa [hp12, Set.pair_comm, Set.insert_comm] using collinear_pair k (p 0) (p 1)
  · refine collinear_insert_of_mem_affineSpan_pair ?_
    by_cases hr2 : r 2 = 0
    · have hr1 : r 1 ≠ 1 := by
        intro hr1
        apply hp12
        rw [← hp 1, ← hp 2, hr1, hr2]
        simp
      have : (1 - r 0) * (1 - r 1) = 0 := by grind [Fin.prod_univ_three]
      have hr0 : r 0 = 1 := by grind
      have hp1_line : p 1 ∈ line[k, t.points 2, t.points 0] := by
        grind [AffineMap.lineMap_mem_affineSpan_pair]
      have hp2_line : p 2 ∈ line[k, t.points 2, t.points 0] := by
        rw [← hp 2, hr2, AffineMap.lineMap_apply_zero]
        grind [right_mem_affineSpan_pair]
      have hline : line[k, p 1, p 2] = line[k, t.points 2, t.points 0] :=
        affineSpan_pair_eq_of_mem_of_mem_of_ne hp1_line hp2_line hp12
      rw [hline, ← hp 0, hr0, AffineMap.lineMap_apply_one]
      exact left_mem_affineSpan_pair (k := k) (t.points 2) (t.points 0)
    · exact t.aux_menelaus_inv hr2 hp h_prod_eq

/-- **Menelaus' theorem**, full affine-parameter version. -/
theorem prod_eq_neg_prod_one_sub_iff_collinear_iff_of_lineMap {t : Triangle k P} {r : Fin 3 → k}
    {p : Fin 3 → P}
    (hp : ∀ i : Fin 3, AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) (r i) = p i) :
    ∏ i, r i = - ∏ i, (1 - r i) ↔ Collinear k {p 0, p 1, p 2} := by
  exact ⟨t.collinear_of_lineMap_of_prod_eq_neg_prod_one_sub hp,
    t.prod_eq_neg_prod_one_sub_of_lineMap_of_collinear hp⟩

end Field

end Affine.Triangle
