/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.LinearAlgebra.AffineSpace.Basis
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
public import Mathlib.LinearAlgebra.StdBasis

/-!
# Standard simplices

This file constructs simplices from bases and defines the standard affine simplex as the simplex
constructed from the standard basis, namely `Pi.basisFun`.

## Main definitions

* `AffineBasis.toSimplex`: the simplex whose vertices are the points of an affine basis.
* `Module.Basis.toSimplex`: the simplex in a module whose vertices are `0` together with the
  vectors of a basis.
* `Affine.StdSimplex`: the simplex in `Fin n → k` whose vertices are `0` and the
  standard basis vectors, i.e. the simplex obtained by applying `Module.Basis.toSimplex` to
  `Pi.basisFun`.
-/

@[expose] public noncomputable section

open Finset Function Module Affine Affine.Simplex
open scoped Affine

variable {n : ℕ}
variable {k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/-- The simplex in `P` whose vertices are the points of an affine basis indexed by
`Fin (n + 1)`. -/
def AffineBasis.toSimplex (b : AffineBasis (Fin (n + 1)) k P) : Simplex k P n :=
  Affine.Simplex.mk b b.ind

/-- The simplex in `V` whose vertices are `0` together with the vectors of a basis indexed by
`Fin n`. -/
abbrev Module.Basis.toSimplex (b : Basis (Fin n) k V) : Simplex k V n := b.toAffineBasis.toSimplex

namespace AffineBasis

@[simp]
lemma toSimplex_points (b : AffineBasis (Fin (n + 1)) k P) :
    (b.toSimplex).points = ⇑b := rfl

lemma affineSpan_range_toSimplex (b : AffineBasis (Fin (n + 1)) k P) :
    affineSpan k (Set.range b.toSimplex.points) = ⊤ := by
  rw [b.toSimplex_points]
  exact b.tot

lemma mem_setInterior_toSimplex {I : Set k} (b : AffineBasis (Fin (n + 1)) k P)
    {x : P} : x ∈ b.toSimplex.setInterior I ↔ ∀ i, b.coord i x ∈ I := by
  conv_lhs => rw [← b.affineCombination_coord_eq_self x]
  exact affineCombination_mem_setInterior_iff (b.sum_coord_apply_eq_one x)

lemma mem_interior_toSimplex_iff [PartialOrder k] (b : AffineBasis (Fin (n + 1)) k P)
    {x : P} : x ∈ b.toSimplex.interior ↔ ∀ i, b.coord i x ∈ Set.Ioo 0 1 :=
  mem_setInterior_toSimplex b

lemma mem_closedInterior_toSimplex_iff [PartialOrder k] (b : AffineBasis (Fin (n + 1)) k P)
    {x : P} : x ∈ b.toSimplex.closedInterior ↔ ∀ i, b.coord i x ∈ Set.Icc 0 1 :=
  mem_setInterior_toSimplex b

end AffineBasis

namespace Affine

open Affine Affine.Simplex Set Pi

variable (n) (k)

/-- The simplex in `Fin n → k` whose vertices are `0` and the standard basis vectors. -/
def StdSimplex : Simplex k (Fin n → k) n := (basisFun k (Fin n)).toSimplex

namespace StdSimplex

/-- The points of `stdSimplex` at successor indices are the standard basis vectors. -/
lemma points_succ (i : Fin n) :
    (Affine.StdSimplex n k).points i.succ = Pi.single i (1 : k) := by
  simp [Affine.StdSimplex]

/-- The closed interior of `Affine.stdSimplex n k` is the filled-in standard `n`-simplex: the
"corner" region `{x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}` (vertices `0` and the standard basis). -/
lemma closedInterior_eq [PartialOrder k] [IsOrderedRing k] :
    (Affine.StdSimplex n k).closedInterior
      = {x : Fin n → k | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} := by
  ext x
  have hw : ∑ i, Fin.cons (1 - ∑ i, x i) x i = 1 := by simp
  have hx : Finset.univ.affineCombination k (Affine.StdSimplex n k).points
      (Fin.cons (1 - ∑ i, x i) x) = x := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hw]
    simp [Fin.sum_univ_succ, Affine.StdSimplex, ← Pi.single_smul', Finset.univ_sum_single]
  conv_lhs => rw [← hx]
  rw [affineCombination_mem_closedInterior_iff hw]
  refine ⟨fun h => ⟨fun i => (h i.succ).1, sub_nonneg.mp (h 0).1⟩, ?_⟩
  · rintro ⟨hpos, hsum⟩
    intro i
    induction i using Fin.cases with
    | zero => simpa using ⟨hsum, Fintype.sum_nonneg hpos⟩
    | succ i =>
      simpa using ⟨hpos i, (single_le_sum (fun i a ↦ hpos i) <| Finset.mem_univ i).trans hsum⟩

/-- The vertices of the face of `Affine.stdSimplex` opposite the vertex `0` are the standard
basis vectors. -/
lemma range_faceOpposite_zero_points [NeZero n] :
    range ((StdSimplex n k).faceOpposite 0).points = range (fun i : Fin n => single i 1) := by
  rw [range_faceOpposite_points]
  ext x
  simp only [mem_image, mem_compl_iff, mem_singleton_iff, Set.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hi
    rw [points_succ]
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    refine ⟨j.succ, Fin.succ_ne_zero j, ?_⟩
    rw [points_succ]

end StdSimplex

end Affine
