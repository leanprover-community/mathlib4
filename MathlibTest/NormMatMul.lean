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

-- a chain of four factors
example : (!![5, 3, 1, 8, 6;
      1, 9, 8, 7, 6;
      6, 6, 6, 6, 6;
      2, 3, 4, 5, 6;
      7, 9, 2, 4, 6] : Matrix (Fin 5) (Fin 5) ℝ) *
    !![9, 7, 5, 3, 1;
      5, 4, 3, 2, 1;
      1, 1, 1, 1, 1;
      6, 7, 8, 9, 1;
      2, 4, 6, 8, 1] *
    !![4, 2, 9, 7, 5;
      9, 8, 7, 6, 5;
      5, 5, 5, 5, 5;
      1, 2, 3, 4, 5;
      6, 8, 1, 3, 5] *
    !![8, 6, 4, 2, 9;
      4, 3, 2, 1, 9;
      9, 9, 9, 9, 9;
      5, 6, 7, 8, 9;
      1, 3, 5, 7, 9] =
    !![75725, 76551, 77377, 78203, 124029;
      74443, 75198, 75953, 76708, 122265;
      81378, 82134, 82890, 83646, 132894;
      53654, 54267, 54880, 55493, 88362;
      80956, 81642, 82328, 83014, 131634] := by
  simp only [norm_matmul]
