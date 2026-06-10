/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Basis
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Analysis.Convex.StdSimplex

@[expose] public section

noncomputable section

open Finset Function Module
open scoped Affine

variable {n : ℕ}
variable {k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AffineSpace V P]

section ofBasis

open Affine

namespace Affine.Simplex


def mkOfAffineBasis (b : AffineBasis (Fin (n + 1)) k P) : Simplex k P n := mk b b.ind

def mkOfBasis (b : Basis (Fin n) k V) : Simplex k V n :=
    mk (Fin.cons 0 b) <| by
  rw [affineIndependent_iff_linearIndependent_vsub k (Fin.cons 0 (⇑b)) 0,
    ← linearIndependent_equiv' (finSuccAboveEquiv 0) (g := b) ?_]
  · exact b.linearIndependent
  · ext j
    simp [finSuccAboveEquiv_apply]

end Affine.Simplex

end ofBasis

section stdAffineSimplex

variable (n) (k)

namespace Affine

open Affine Affine.Simplex

def stdSimplex : Simplex k ((Fin n) → k) n := mkOfBasis <| Pi.basisFun k (Fin n)

-- def stdSimplex_solid : Simplex k (Fin (n + 1) → k) n := (stdSimplex (n + 1) k).faceOpposite 0

namespace Simplex

/-- The points of `stdSimplex` at successor indices are the standard basis vectors. -/
lemma points_succ (i : Fin n) :
    (Affine.stdSimplex n k).points i.succ = Pi.single i (1 : k) := by
  simp [Affine.stdSimplex, mkOfBasis]

/-- `stdSimplex n k` is the solid, full-dimensional simplex in `kⁿ`: its closed interior is the
"corner" region `{x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}` (vertices `0` and the standard basis). -/
lemma closedInterior_eq [PartialOrder k] [IsOrderedRing k] :
    (Affine.stdSimplex n k).closedInterior
      = {x : Fin n → k | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} := by
  have h0 : (Affine.stdSimplex n k).points 0 = 0 := by simp [Affine.stdSimplex, mkOfBasis]
  ext x
  set w : Fin (n + 1) → k := Fin.cons (1 - ∑ i, x i) x with hwdef
  have hw : ∑ i, w i = 1 := by rw [hwdef, Fin.sum_cons]; abel
  have hx : Finset.univ.affineCombination k (Affine.stdSimplex n k).points w = x := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hw, Fin.sum_univ_succ, h0,
      smul_zero, zero_add]
    simp only [hwdef, Fin.cons_succ, points_succ]
    have hterm : ∀ i : Fin n, x i • Pi.single i (1 : k) = Pi.single i (x i) := fun i => by
      rw [← Pi.single_smul', smul_eq_mul, mul_one]
    simp_rw [hterm]
    exact Finset.univ_sum_single x
  conv_lhs => rw [← hx]
  rw [affineCombination_mem_closedInterior_iff hw, Set.mem_setOf_eq]
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · have hi := Set.mem_Icc.mp (h i.succ)
      rw [hwdef, Fin.cons_succ] at hi
      exact hi.1
    · have h0' := (Set.mem_Icc.mp (h 0)).1
      rw [hwdef, Fin.cons_zero] at h0'
      exact sub_nonneg.mp h0'
  · rintro ⟨hpos, hsum⟩ i
    rw [Set.mem_Icc]
    induction i using Fin.cases with
    | zero =>
      rw [hwdef, Fin.cons_zero]
      exact ⟨sub_nonneg.mpr hsum, sub_le_self 1 (Finset.sum_nonneg fun i _ => hpos i)⟩
    | succ j =>
      rw [hwdef, Fin.cons_succ]
      exact ⟨hpos j,
        le_trans (Finset.single_le_sum (fun i _ => hpos i) (Finset.mem_univ j)) hsum⟩

variable [NeZero n]

lemma range_faceOpposite_zero_points : Set.range ((Affine.stdSimplex n ℝ).faceOpposite 0).points
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

lemma faceOpposite_zero_eq_stdSimplex :
    ((Affine.stdSimplex n ℝ).faceOpposite 0).closedInterior = _root_.stdSimplex ℝ (Fin n) := by
  rw [← convexHull_eq_closedInterior, range_faceOpposite_zero_points]
  exact convexHull_rangle_single_eq_stdSimplex ℝ (Fin n)

end Simplex

end Affine

end stdAffineSimplex
