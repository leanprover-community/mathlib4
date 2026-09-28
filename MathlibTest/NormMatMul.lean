module

import Mathlib.Tactic.NormMatMul

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Polynomial.Basic

/-! # Tests for the `norm_matmul` simproc -/

open Matrix

example : (!![1 / 2, 1; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ) * !![2, 0; 1, 1] = !![2, 1; 3, 3] := by
  simp only [norm_matmul]

example : (!![1, 2, 3; 4, 5, 6] : Matrix (Fin 2) (Fin 3) ℂ) *
    (!![1, 0; 0, 1; 1, 1] : Matrix (Fin 3) (Fin 2) ℂ) = !![4, 5; 10, 11] := by
  simp only [norm_matmul]

-- chains normalize inside-out
example : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ) * !![1, 1; 0, 1] * !![1, 1; 0, 1] =
    !![1, 3; 0, 1] := by
  simp only [norm_matmul]

-- degenerate dimensions
example : (!![,,,] : Matrix (Fin 0) (Fin 3) ℚ) *
    (!![1, 2; 3, 4; 5, 6] : Matrix (Fin 3) (Fin 2) ℚ) = !![,,] := by
  simp only [norm_matmul]

example : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℚ) * !![;;] = !![;;] := by
  simp only [norm_matmul]

example : (!![;;] : Matrix (Fin 2) (Fin 0) ℚ) * (!![,,] : Matrix (Fin 0) (Fin 2) ℚ) =
    !![0, 0; 0, 0] := by
  simp only [norm_matmul]

example : (!![3] : Matrix (Fin 1) (Fin 1) ℚ) * !![4] = !![12] := by
  simp only [norm_matmul]

-- a ring without division, and negative entries
example : (!![1, -2; -3, 4] : Matrix (Fin 2) (Fin 2) ℤ) * !![-5, 6; 7, -8] =
    !![-19, 22; 43, -50] := by
  simp only [norm_matmul]

-- symbolic entries: the sums of products stay as terms, and the numeric parts are normalized
example (c : ℚ) : !![c, 1; 0, 1] * !![1, 0; 1, 1] = !![c + 1, 1; 1, 1] := by
  simp only [norm_matmul]; norm_num

-- entries in a polynomial ring, closed entrywise by `polynomial`. `ring_nf` also works.
open Polynomial in
example : (!![X, 1; 0, X] : Matrix (Fin 2) (Fin 2) ℚ[X]) * !![X, 1; 1, 0] =
    !![X ^ 2 + 1, X; X, 0] := by
  simp only [norm_matmul]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp; polynomial

-- a chain of three that multiplies to a multiple of the identity
example : (!![3, 1, 4; 1, 5, 9; 2, 6, 5] : Matrix (Fin 3) (Fin 3) ℝ) *
    !![3, 5, 8; 9, 7, 9; 3, 2, 3] *
    !![-2, 16, -14; -25, -55, 65; 20, 26, -34] = (90 : ℝ) • 1 := by
  simp only [norm_matmul]
  simp [Matrix.one_fin_three]
