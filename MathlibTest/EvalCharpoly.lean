module

import Mathlib.Tactic.NormCharpoly
import Mathlib.Basic.Real.Basic

open Polynomial

example : Matrix.charpoly (R := ℚ) !![] = 1 := by
  eval_charpoly

example : Matrix.charpoly (R := ℚ) !![3] = X - 3 := by
  eval_charpoly

example : Matrix.charpoly (R := ℚ) !![1, 0; 0, 1] = X ^ 2 - 2 * X + 1 := by
  eval_charpoly

example : Matrix.charpoly (R := ℚ) !![1/2, 1; 1, 2] = X ^ 2 - C (5/2) * X := by
  eval_charpoly

example : Matrix.charpoly (R := ℚ) !![1 + 1, 6/4; -(2*2), 5] = X ^ 2 - 7 * X + 16 := by
  eval_charpoly

example : Matrix.charpoly (R := ℚ) !![1, 2; 3, 4] = Matrix.charpoly (R := ℚ) !![4, 3; 2, 1] := by
  simp only [norm_charpoly]

example : Matrix.charpoly (R := ℚ)
    !![0,  2, -2, 0,  0;
       0,  3,  0, 1, -1;
       2, -2,  3, 0,  0;
       0, -2, -1, 1,  0;
       0,  3,  0, 0,  3] =
    X ^ 5 - 10 * X ^ 4 + 45 * X ^ 3 - 108 * X ^ 2 + 144 * X - 84 := by
  eval_charpoly

example :
    Matrix.charpoly (R := ℚ)
      !![ 2, -1,  0,  0,  0,  0,  0,  0,  0;
         -1,  2, -1,  0,  0,  0,  0,  0,  0;
          0, -1,  2, -1,  0,  0,  0,  0,  0;
          0,  0, -1,  2, -1,  0,  0,  0,  0;
          0,  0,  0, -1,  2, -1,  0,  0,  0;
          0,  0,  0,  0, -1,  2, -1,  0, -1;
          0,  0,  0,  0,  0, -1,  2, -1,  0;
          0,  0,  0,  0,  0,  0, -1,  2,  0;
          0,  0,  0,  0,  0, -1,  0,  0,  2] =
      X ^ 9 - 18 * X ^ 8 + 136 * X ^ 7 - 560 * X ^ 6 + 1364 * X ^ 5 - 1992 * X ^ 4 + 1679 * X ^ 3 -
        730 * X ^ 2 + 120 * X := by
  eval_charpoly

example (A : Matrix (Fin 2) (Fin 2) ℚ) (hA : A = !![1, 2; 3, 4]) :
    A.charpoly = X ^ 2 - 5 * X - 2 := by
  rw [hA]
  eval_charpoly

example (a : ℚ) :
    Matrix.charpoly (R := ℚ) !![1, 0; 0, 1] + Matrix.charpoly (R := ℚ) !![a, 1; 1, a] =
      1 - X * 2 + X ^ 2 + Matrix.charpoly (R := ℚ) !![a, 1; 1, a] := by
  simp only [norm_charpoly]

/--
error: unsolved goals
⊢ -2 - X * 5 + X ^ 2 = X ^ 2 - 5 * X - 3
-/
#guard_msgs in
example : Matrix.charpoly (R := ℚ) !![1, 2; 3, 4] = X ^ 2 - 5 * X - 3 := by
  eval_charpoly

set_option trace.Tactic.evalCharpoly true

/--
error: `eval_charpoly` made no progress.
Additional information may be available using `set_option trace.Tactic.evalCharpoly true`.
---
trace: [Tactic.evalCharpoly] A is not a closed matrix literal
-/
#guard_msgs in
example (A : Matrix (Fin 2) (Fin 2) ℚ) : A.charpoly = X ^ 2 := by eval_charpoly

/--
error: `eval_charpoly` made no progress.
Additional information may be available using `set_option trace.Tactic.evalCharpoly true`.
---
trace: [Tactic.evalCharpoly] expected the element type to be ℚ
-/
#guard_msgs in
example : Matrix.charpoly (R := ℤ) !![1, 2; 3, 4] = X ^ 2 - 5 * X - 2 := by eval_charpoly

/--
error: `eval_charpoly` made no progress.
Additional information may be available using `set_option trace.Tactic.evalCharpoly true`.
---
trace: [Tactic.evalCharpoly] expected the element type to be ℚ
-/
#guard_msgs in
example : Matrix.charpoly (R := ℝ) !![1, 2; 3, 4] = X ^ 2 - 5 * X - 2 := by eval_charpoly
