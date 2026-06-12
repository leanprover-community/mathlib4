/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Basis
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Analysis.Convex.stdSimplex

/-!
# Standard simplices

This file constructs simplices from bases and relates them to the standard simplex.

## Main definitions

* `Affine.Simplex.mkOfAffineBasis`: the simplex whose vertices are the points of an affine basis.
* `Affine.Simplex.mkOfBasis`: the simplex in a module whose vertices are `0` together with the
  vectors of a basis.
* `Affine.stdSimplex`: the simplex in `Fin n → k` whose vertices are `0` and the standard basis
  vectors, i.e. the simplex obtained by applying `Affine.Simplex.mkOfBasis` to `Pi.basisFun`.

## Main results

* `Affine.Simplex.mem_closedInterior_mkOfAffineBasis_iff`: membership in the closed interior of
  `Affine.Simplex.mkOfAffineBasis b` is characterised by the barycentric coordinates of `b`.
* `Affine.Simplex.closedInterior_eq`: the closed interior of `Affine.stdSimplex` is the "corner"
  region `{x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}`.

The relationship between `Affine.stdSimplex` and the standard simplex `stdSimplex ℝ (Fin n)` is
established in `Mathlib/Analysis/Convex/StdSimplex.lean`.
-/

@[expose] public section

noncomputable section

open Finset Function Module
open scoped Affine

variable {n : ℕ}
variable {k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AffineSpace V P]

section ofBasis

open Affine

namespace Affine.Simplex

/-- The simplex in `P` whose vertices are the points of an affine basis indexed by
`Fin (n + 1)`. -/
def mkOfAffineBasis (b : AffineBasis (Fin (n + 1)) k P) : Simplex k P n := mk b b.ind

/-- The simplex in `V` whose vertices are `0` together with the vectors of a basis indexed by
`Fin n`. -/
def mkOfBasis (b : Basis (Fin n) k V) : Simplex k V n :=
  mk (Fin.cons 0 b) <| by
    rw [affineIndependent_iff_linearIndependent_vsub k (Fin.cons 0 (⇑b)) 0,
      ← linearIndependent_equiv' (finSuccAboveEquiv 0) (g := b) ?_]
    · exact b.linearIndependent
    · ext j
      simp [finSuccAboveEquiv_apply]

@[simp] lemma mkOfAffineBasis_points (b : AffineBasis (Fin (n + 1)) k P) :
    (mkOfAffineBasis b).points = ⇑b :=
  rfl

lemma affineSpan_range_mkOfAffineBasis_points (b : AffineBasis (Fin (n + 1)) k P) :
    affineSpan k (Set.range (mkOfAffineBasis b).points) = ⊤ := by
  rw [mkOfAffineBasis_points]
  exact b.tot

/-- A point lies in `(mkOfAffineBasis b).setInterior I` iff all of its barycentric coordinates
with respect to `b` lie in `I`. -/
lemma mem_setInterior_mkOfAffineBasis_iff {I : Set k} (b : AffineBasis (Fin (n + 1)) k P)
    {x : P} : x ∈ (mkOfAffineBasis b).setInterior I ↔ ∀ i, b.coord i x ∈ I := by
  conv_lhs => rw [← b.affineCombination_coord_eq_self x]
  exact affineCombination_mem_setInterior_iff (b.sum_coord_apply_eq_one x)

/-- A point lies in the interior of `mkOfAffineBasis b` iff all of its barycentric coordinates
with respect to `b` lie in `Set.Ioo 0 1`. -/
lemma mem_interior_mkOfAffineBasis_iff [PartialOrder k] (b : AffineBasis (Fin (n + 1)) k P)
    {x : P} : x ∈ (mkOfAffineBasis b).interior ↔ ∀ i, b.coord i x ∈ Set.Ioo 0 1 :=
  mem_setInterior_mkOfAffineBasis_iff b

/-- A point lies in the closed interior of `mkOfAffineBasis b` iff all of its barycentric
coordinates with respect to `b` lie in `Set.Icc 0 1`. -/
lemma mem_closedInterior_mkOfAffineBasis_iff [PartialOrder k] (b : AffineBasis (Fin (n + 1)) k P)
    {x : P} : x ∈ (mkOfAffineBasis b).closedInterior ↔ ∀ i, b.coord i x ∈ Set.Icc 0 1 :=
  mem_setInterior_mkOfAffineBasis_iff b

lemma mkOfBasis_points (b : Basis (Fin n) k V) : (mkOfBasis b).points = Fin.cons 0 ⇑b :=
  rfl

@[simp] lemma mkOfBasis_points_zero (b : Basis (Fin n) k V) : (mkOfBasis b).points 0 = 0 :=
  rfl

@[simp] lemma mkOfBasis_points_succ (b : Basis (Fin n) k V) (i : Fin n) :
    (mkOfBasis b).points i.succ = b i :=
  rfl

lemma range_mkOfBasis_points (b : Basis (Fin n) k V) :
    Set.range (mkOfBasis b).points = insert 0 (Set.range ⇑b) := by
  rw [mkOfBasis_points, Fin.range_cons]

lemma affineSpan_range_mkOfBasis_points (b : Basis (Fin n) k V) :
    affineSpan k (Set.range (mkOfBasis b).points) = ⊤ := SetLike.coe_injective <| by
  rw [range_mkOfBasis_points, affineSpan_insert_zero, b.span_eq]
  simp

end Affine.Simplex

end ofBasis

section stdAffineSimplex

variable (n) (k)

namespace Affine

open Affine Affine.Simplex

/-- The simplex in `Fin n → k` whose vertices are `0` and the standard basis vectors. -/
def stdSimplex : Simplex k (Fin n → k) n := mkOfBasis <| Pi.basisFun k (Fin n)

namespace stdSimplex

/-- The points of `stdSimplex` at successor indices are the standard basis vectors. -/
lemma points_succ (i : Fin n) :
    (Affine.stdSimplex n k).points i.succ = Pi.single i (1 : k) := by
  simp [Affine.stdSimplex]

/-- `stdSimplex n k` is the solid, full-dimensional simplex in `kⁿ`: its closed interior is the
"corner" region `{x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}` (vertices `0` and the standard basis). -/
lemma closedInterior_eq [PartialOrder k] [IsOrderedRing k] :
    (Affine.stdSimplex n k).closedInterior
      = {x : Fin n → k | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} := by
  ext x
  have hw : ∑ i, Fin.cons (1 - ∑ i, x i) x i = 1 := by simp
  have hx : Finset.univ.affineCombination k (Affine.stdSimplex n k).points
      (Fin.cons (1 - ∑ i, x i) x) = x := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hw]
    simp [Fin.sum_univ_succ, Affine.stdSimplex, ← Pi.single_smul', Finset.univ_sum_single]
  conv_lhs => rw [← hx]
  rw [affineCombination_mem_closedInterior_iff hw, Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Set.mem_Icc, Set.mem_setOf_eq]
  have hle : ∀ i, (∀ j, 0 ≤ x j) → x i ≤ ∑ j, x j :=
    fun i h => Finset.single_le_sum (fun j _ => h j) (Finset.mem_univ i)
  grind [Finset.sum_nonneg, sub_nonneg, sub_le_self]

/-- The vertices of the face of `Affine.stdSimplex` opposite the vertex `0` are the standard
basis vectors. -/
lemma range_faceOpposite_zero_points [NeZero n] : Set.range ((stdSimplex n ℝ).faceOpposite 0).points
    = Set.range (fun i : Fin n => Pi.single i (1 : ℝ)) := by
  rw [range_faceOpposite_points]
  ext x
  simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hi
    rw [points_succ]
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    refine ⟨j.succ, Fin.succ_ne_zero j, ?_⟩
    rw [points_succ]

/-- The closed interior of the face of `Affine.stdSimplex` opposite the vertex `0` is the
standard simplex `stdSimplex ℝ (Fin n)`. -/
lemma faceOpposite_zero_eq_stdSimplex [NeZero n] :
    ((Affine.stdSimplex n ℝ).faceOpposite 0).closedInterior = _root_.stdSimplex ℝ (Fin n) := by
  rw [← convexHull_eq_closedInterior, range_faceOpposite_zero_points]
  exact convexHull_rangle_single_eq_stdSimplex ℝ (Fin n)

end stdSimplex

end Affine

end stdAffineSimplex
