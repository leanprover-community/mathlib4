module

public import Mathlib.Tactic.Echelon.Interface

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Cartan
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-! # Tests for the `eval_rank` tactic -/

/-! ## Basic evaluation over `ℤ` and `ℚ` -/

example : Matrix.rank (R := ℤ)
    !![1, 2, 3] = 1 := by
  eval_rank

example : Matrix.rank (R := ℤ)
    !![1;
       2;
       3] = 1 := by
  eval_rank

example : Matrix.rank (R := ℚ)
    !![] = 0 := by
  eval_rank

example : Matrix.rank (R := ℚ)
    !![0, 0;
       0, 0] = 0 := by
  eval_rank

example : Matrix.rank (R := ℚ)
    !![1, 2;
       2, 4] = 1 := by
  eval_rank

example : Matrix.rank (R := ℚ)
    !![1, 2, 3, 4;
       2, 4, 6, 8;
       1, 1, 1, 1;
       2, 3, 4, 5] = 2 := by
  eval_rank

example : Matrix.rank (R := ℚ)
    !![1, 2, 0, 1, 3;
       0, 1, 1, 2, 1;
       2, 4, 0, 2, 6;
       0, 0, 1, 0, 2;
       1, 3, 1, 3, 4] = 3 := by
  eval_rank

example : Matrix.rank (R := ℚ)
    !![1, 2, 3;
       4, 5, 6;
       7, 8, 10] = 3 := by
  eval_rank

example : Matrix.rank (R := ℚ)
    !![1, 0;
       0, 1;
       1, 1;
       2, 3] = 2 := by
  eval_rank

example : Matrix.rank (R := ℚ)
    !![1, 2, 3, 4;
       2, 4, 6, 8] = 1 := by
  eval_rank

example : Matrix.rank (R := ℚ)
    !![1/2, 1/3;
       1/5, 1/7] = 2 := by
  eval_rank

-- row 2 = (1/2) * row 1
example : Matrix.rank (R := ℚ)
    !![1/2, 1/3;
       1/4, 1/6] = 1 := by
  eval_rank

-- compound entries: 1/2 * 5/2 = 5/4, det ≠ 0
example : Matrix.rank (R := ℚ) !![1/2 * 5/2, 1; 1, 1] = 2 := by eval_rank

-- 1/2 * 4 = 2 collapses the rank
example : Matrix.rank (R := ℚ) !![1/2 * 4, 2; 1, 1] = 1 := by eval_rank

/-! ## Element-type coverage -/

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

example : Matrix.rank (R := ZMod 7) !![3, 5; 2, 4] = 2 := by eval_rank

-- det = -7 ≡ 0 (mod 7): full rank over ℚ, but rank 1 over ZMod 7
example : Matrix.rank (R := ZMod 7) !![2, 5; 3, 4] = 1 := by eval_rank

-- 2 * 4 ≡ 1 (mod 7), det ≡ 0
example : Matrix.rank (R := ZMod 7) !![2 * 4, 1; 1, 1] = 1 := by eval_rank

-- ℤ[i] with integer entries
example : Matrix.rank (R := GaussianInt) !![2, 5; 3, 4] = 2 := by eval_rank

/-! ## Unfolding and rewrites -/

-- rewrite
example (A : Matrix (Fin 1) (Fin 3) ℤ) (hA : A = !![1, 2, 3]) :
    A.rank = 1 := by
  rw [hA]
  eval_rank

-- rank of an existing definition, after unfolding it to a literal
example : Matrix.rank (R := ℤ) CartanMatrix.E₇ = 7 := by
  unfold CartanMatrix.E₇
  eval_rank

/-! ## Behavior inside `simp` -/

-- mixed element types in one goal: the ℤ literal is rewritten while the unsupported ℝ
-- literal is skipped, without an error; the ℝ rank is then evaluated by recognizing the
-- identity matrix
example :
    Matrix.rank (R := ℤ) !![1, 2; 2, 4] = Matrix.rank (R := ℝ) !![1, 0; 0, 1] - 1 := by
  simp only [norm_rank]
  rw [← Matrix.one_fin_two, Matrix.rank_one]
  simp

-- the same via `eval_rank`: partial progress is success — the no-progress diagnosis is
-- suppressed and the failure of the closing `omega` on the opaque ℝ rank is absorbed,
-- leaving the residual goal
example :
    Matrix.rank (R := ℤ) !![1, 2; 2, 4] = Matrix.rank (R := ℝ) !![1, 0; 0, 1] - 1 := by
  eval_rank
  rw [← Matrix.one_fin_two, Matrix.rank_one]
  simp

-- a literal with symbolic entries is not closed: it is skipped, not an error
example (a : ℚ) (h : Matrix.rank (R := ℚ) !![a, 1; 1, a] = 2) :
    Matrix.rank (R := ℚ) !![1, 0; 0, 1] = Matrix.rank (R := ℚ) !![a, 1; 1, a] := by
  simp only [norm_rank]
  omega

/-! ## A larger matrix -/

-- This 9x9 matrix has rank 8 and is the Cartan matrix of the affine-type E8 root system.
example :
    Matrix.rank (R := ℤ)
      !![ 2, -1,  0,  0,  0,  0,  0,  0,  0;
         -1,  2, -1,  0,  0,  0,  0,  0,  0;
          0, -1,  2, -1,  0,  0,  0,  0,  0;
          0,  0, -1,  2, -1,  0,  0,  0,  0;
          0,  0,  0, -1,  2, -1,  0,  0,  0;
          0,  0,  0,  0, -1,  2, -1,  0, -1;
          0,  0,  0,  0,  0, -1,  2, -1,  0;
          0,  0,  0,  0,  0,  0, -1,  2,  0;
          0,  0,  0,  0,  0, -1,  0,  0,  2] = 8 := by
  eval_rank

/-! ## Failure tests -/

-- only closed matrix literals are in scope: the commitment gate skips an abstract matrix,
-- and `eval_rank` reports that nothing was found
/-- error: eval_rank: no closed `Matrix.rank` literal found in the goal -/
#guard_msgs in
example (A : Matrix (Fin 2) (Fin 2) ℚ) : A.rank = 2 := by eval_rank

-- a literal with symbolic entries is likewise not closed; substitute or unfold the
-- variables before calling the tactic
/-- error: eval_rank: no closed `Matrix.rank` literal found in the goal -/
#guard_msgs in
example (a : ℚ) : Matrix.rank (R := ℚ) !![a, 1; 1, a] = 2 := by eval_rank

/-- error: expected the element type to be a commutative ring -/
#guard_msgs in
example : Matrix.rank (R := ℕ) !![1, 2; 3, 4] = 2 := by eval_rank

/-- error: expected the element type to be a domain -/
#guard_msgs in
example : Matrix.rank (R := ZMod 4) !![1, 2; 3, 4] = 2 := by eval_rank

/--
error: equality in the element type does not reduce in the kernel
  ℝ
-/
#guard_msgs in
example : Matrix.rank (R := ℝ) !![1, 2; 3, 4] = 2 := by eval_rank

open Polynomial in
/--
error: equality in the element type does not reduce in the kernel
  ℚ[X]
-/
#guard_msgs in
example : Matrix.rank (R := ℚ[X]) !![X, 1; 1, X] = 2 := by eval_rank

/--
error: division entries are supported only in characteristic zero
  2 / 3
-/
#guard_msgs in
example : Matrix.rank (R := ZMod 7) !![2/3, 0; 0, 1] = 2 := by eval_rank

/--
error: the entry does not evaluate to a rational numeral
  { re := 0, im := 1 }
-/
#guard_msgs in
example : Matrix.rank (R := GaussianInt) !![⟨0, 1⟩, 1; 1, ⟨0, 1⟩] = 2 := by eval_rank
