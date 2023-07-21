/-
Copyright (c) 2023 Mohanad ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/

import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Rank of Matrix when left or right multiplied by invertible matrix.
Rank is unaffected by left or right multiplication by an invertible matrix -/

open Matrix BigOperators

namespace Matrix

lemma rank_mul_IsUnit {m n R: Type}
  -- [Fintype m] -- not needed according to linter
  [Fintype n][DecidableEq n][CommRing R]
  (A: Matrix n n R)(B: Matrix m n R)(hA: IsUnit A.det):
  (B⬝A).rank = B.rank := by
  rw [Matrix.rank, mulVecLin_mul, LinearMap.range_comp_of_range_eq_top, ←Matrix.rank ]
  rw [LinearMap.range_eq_top]
  intros x
  use ((A⁻¹).mulVecLin x)
  rw [mulVecLin_apply, mulVecLin_apply, mulVec_mulVec, mul_nonsing_inv, one_mulVec]
  exact hA

lemma rank_IsUnit_mul {m n R: Type}
  [Fintype m][Fintype n][DecidableEq m][Field R]
  (A: Matrix m m R)(B: Matrix m n R)(hA: IsUnit A.det):
  (A⬝B).rank = B.rank := by
  suffices h: LinearMap.ker ((A⬝B).mulVecLin) = LinearMap.ker (B.mulVecLin)
  have hB := LinearMap.finrank_range_add_finrank_ker (B.mulVecLin)
  rw [← LinearMap.finrank_range_add_finrank_ker ((A⬝B).mulVecLin), h, add_left_inj] at hB
  rw [Matrix.rank, Matrix.rank, hB]
  rw [mulVecLin_mul, LinearMap.ker_comp_of_ker_eq_bot]
  rw [LinearMap.ker_eq_bot]
  simp_rw [Function.Injective, mulVecLin_apply]
  intros x y h
  replace h := congr_arg (fun x => Matrix.mulVec (A⁻¹) x)  h
  simp_rw [mulVec_mulVec, nonsing_inv_mul A hA, one_mulVec] at h
  exact h

end Matrix
