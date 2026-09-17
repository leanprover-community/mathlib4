module

import Mathlib.Tactic.NormCharpoly
import Mathlib.Basic.Real.Basic

/-! # Tests for the `eval_charpoly` tactic -/

open Polynomial

/-! ## Basic evaluation -/

example : Matrix.charpoly (R := ℚ) !![] = 1 := by
  eval_charpoly

example : Matrix.charpoly (R := ℚ) !![3] = X - 3 := by
  eval_charpoly

example : Matrix.charpoly (R := ℚ) !![1, 0; 0, 1] = X ^ 2 - 2 * X + 1 := by
  eval_charpoly

-- no pivot at all
example : Matrix.charpoly (R := ℚ) !![0, 0; 0, 0] = X ^ 2 := by
  eval_charpoly

-- a nilpotent block
example : Matrix.charpoly (R := ℚ) !![0, 1; 0, 0] = X ^ 2 := by
  eval_charpoly

example : Matrix.charpoly (R := ℚ) !![1/2, 1; 1, 2] = X ^ 2 - C (5/2) * X := by
  eval_charpoly

-- negative non-integer entries
example : Matrix.charpoly (R := ℚ) !![-1/2, 1; 1, -1/2] = X ^ 2 + X - C (3/4) := by
  eval_charpoly

-- compound entries are evaluated by `norm_num`
example : Matrix.charpoly (R := ℚ) !![1 + 1, 6/4; -(2*2), 5] = X ^ 2 - 7 * X + 16 := by
  eval_charpoly

/-! ## Row and column swaps -/

-- a zero pivot at the first step forces a swap
example : Matrix.charpoly (R := ℚ) !![0, 0, 1; 1, 0, 0; 0, 1, 0] = X ^ 3 - 1 := by
  eval_charpoly

-- the pivot vanishes only after the first elimination step
example : Matrix.charpoly (R := ℚ) !![1, 2, 3; 1, 2, 4; 0, 0, 1] =
    X ^ 3 - 4 * X ^ 2 + 3 * X := by
  eval_charpoly

-- a zero below the diagonal in the first column
example : Matrix.charpoly (R := ℚ)
    !![0,  2, -2, 0,  0;
       0,  3,  0, 1, -1;
       2, -2,  3, 0,  0;
       0, -2, -1, 1,  0;
       0,  3,  0, 0,  3] =
    X ^ 5 - 10 * X ^ 4 + 45 * X ^ 3 - 108 * X ^ 2 + 144 * X - 84 := by
  eval_charpoly

/-! ## A larger matrix -/

-- the Cartan matrix of the affine-type E8 root system
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

/-! ## Rewrites and simplifications -/

-- both literals are rewritten
example : Matrix.charpoly (R := ℚ) !![1, 2; 3, 4] = Matrix.charpoly (R := ℚ) !![4, 3; 2, 1] := by
  simp only [norm_charpoly]

-- rewrite
example (A : Matrix (Fin 2) (Fin 2) ℚ) (hA : A = !![1, 2; 3, 4]) :
    A.charpoly = X ^ 2 - 5 * X - 2 := by
  rw [hA]
  eval_charpoly

-- a let-bound literal
example : Matrix.charpoly (R := ℚ) (let A := !![1, 2; 3, 4]; A) = X ^ 2 - 5 * X - 2 := by
  eval_charpoly

-- the result feeds a further computation
example : (Matrix.charpoly (R := ℚ) !![1, 2; 3, 4]).eval 1 = -6 := by
  simp only [norm_charpoly]; norm_num

-- a symbolic literal is skipped without an error while the closed one is rewritten
example (a : ℚ) :
    Matrix.charpoly (R := ℚ) !![1, 0; 0, 1] + Matrix.charpoly (R := ℚ) !![a, 1; 1, a] =
      1 - X * 2 + X ^ 2 + Matrix.charpoly (R := ℚ) !![a, 1; 1, a] := by
  simp only [norm_charpoly]

/-! ## Failure tests -/

-- the goal is left in the normal form of `ring_nf` when `ring1` cannot close it
/--
error: unsolved goals
⊢ -2 - X * 5 + X ^ 2 = X ^ 2 - 5 * X - 3
-/
#guard_msgs in
example : Matrix.charpoly (R := ℚ) !![1, 2; 3, 4] = X ^ 2 - 5 * X - 3 := by
  eval_charpoly

set_option trace.Tactic.evalCharpoly true

/-! ### No closed matrix literal in the goal -/

/--
error: `eval_charpoly` made no progress.
Additional information may be available using `set_option trace.Tactic.evalCharpoly true`.
---
trace: [Tactic.evalCharpoly] not a closed matrix literal
      A
-/
#guard_msgs in
example (A : Matrix (Fin 2) (Fin 2) ℚ) : A.charpoly = X ^ 2 := by eval_charpoly

/--
error: `eval_charpoly` made no progress.
Additional information may be available using `set_option trace.Tactic.evalCharpoly true`.
---
trace: [Tactic.evalCharpoly] not a closed matrix literal
      !![a, 1; 1, a]
-/
#guard_msgs in
example (a : ℚ) :
    Matrix.charpoly (R := ℚ) !![a, 1; 1, a] = X ^ 2 - C (2 * a) * X + C (a ^ 2 - 1) := by
  eval_charpoly

/-! ### Other element types -/

/--
error: `eval_charpoly` made no progress.
Additional information may be available using `set_option trace.Tactic.evalCharpoly true`.
---
trace: [Tactic.evalCharpoly] expected the element type to be ℚ, found ℤ
      !![1, 2; 3, 4]
-/
#guard_msgs in
example : Matrix.charpoly (R := ℤ) !![1, 2; 3, 4] = X ^ 2 - 5 * X - 2 := by eval_charpoly

/--
error: `eval_charpoly` made no progress.
Additional information may be available using `set_option trace.Tactic.evalCharpoly true`.
---
trace: [Tactic.evalCharpoly] expected the element type to be ℚ, found ℝ
      !![1, 2; 3, 4]
-/
#guard_msgs in
example : Matrix.charpoly (R := ℝ) !![1, 2; 3, 4] = X ^ 2 - 5 * X - 2 := by eval_charpoly
