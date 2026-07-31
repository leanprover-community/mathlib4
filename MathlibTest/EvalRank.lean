module
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.Tactic.Echelon.Interface
public import Mathlib.LinearAlgebra.Matrix.Cartan

/-! # Tests for the `eval_rank` tactic -/

example (A : Matrix (Fin 1) (Fin 3) ℤ) (hA : A = !![1, 2, 3]) :
     A.rank = 1 := by
  rw [hA]
  eval_rank

/-
take existing definitions that will unfold to a literals
-/
example : Matrix.rank (R := ℤ) CartanMatrix.E₇ = 7 := by unfold CartanMatrix.E₇; eval_rank


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

-- more rows than columns, full column rank
example : Matrix.rank (R := ℚ)
    !![1, 0;
       0, 1;
       1, 1;
       2, 3] = 2 := by
  eval_rank

-- more columns than rows, row 2 = 2 * row 1
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

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

example : Matrix.rank (R := ZMod 7) !![3, 5; 2, 4] = 2 := by eval_rank

-- det = -7 ≡ 0 (mod 7): full rank over ℚ, but rank 1 over ZMod 7
example : Matrix.rank (R := ZMod 7) !![2, 5; 3, 4] = 1 := by eval_rank

-- division entries are refused in positive characteristic, where the fraction
-- reading `2 / 3 = (2 : ℚ)/3` is not faithful
/--
error: division entries are supported only in characteristic zero; write the entry as a numeral
  2 / 3
-/
#guard_msgs in
example : Matrix.rank (R := ZMod 7) !![2/3, 0; 0, 1] = 2 := by eval_rank

-- This 9x9 matrix has rank 8 and is the Cartan matrix of the
-- affine-type E8 root system.
public lemma test_Cartan_matrix :
    Matrix.rank (R := ℚ)
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

-- axiom-footprint regression guard: exactly the three standard axioms, no `sorryAx`
set_option linter.hashCommand false in
/-- info: 'test_Cartan_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms test_Cartan_matrix

/-! ## element-type coverage -/

set_option linter.hashCommand false

open Polynomial

-- ℤ[i] with integer entries
example : Matrix.rank (R := GaussianInt) !![2, 5; 3, 4] = 2 := by eval_rank

-- entries must still have a rational value: `i = ⟨0, 1⟩` has none
/--
error: the entry does not evaluate to a numeral
  { re := 0, im := 1 }
-/
#guard_msgs in
example : Matrix.rank (R := GaussianInt) !![⟨0, 1⟩, 1; 1, ⟨0, 1⟩] = 2 := by eval_rank

-- compound entries: 1/2 * 5/2 = 5/4, det ≠ 0
example : Matrix.rank (R := ℚ) !![1/2 * 5/2, 1; 1, 1] = 2 := by eval_rank

-- 1/2 * 4 = 2 collapses the rank
example : Matrix.rank (R := ℚ) !![1/2 * 4, 2; 1, 1] = 1 := by eval_rank

-- 2 * 4 ≡ 1 (mod 7), det ≡ 0
example : Matrix.rank (R := ZMod 7) !![2 * 4, 1; 1, 1] = 1 := by eval_rank

-- only closed matrix literals are in scope: the commitment gate skips an abstract matrix,
-- and `eval_rank` reports that nothing was found
/-- error: eval_rank: no closed `Matrix.rank` literal found in the goal -/
#guard_msgs in
example (A : Matrix (Fin 2) (Fin 2) ℚ) : A.rank = 2 := by eval_rank

-- graceful skip: `norm_rank` rewrites the closed literal and skips the abstract `rank`
-- term in the same goal instead of aborting the `simp` call
example (A : Matrix (Fin 2) (Fin 2) ℚ) (h : A.rank = 2) :
    Matrix.rank (R := ℚ) !![1, 0; 0, 1] = A.rank := by
  simp only [norm_rank]
  omega

/-- error: expected the element type to be a commutative ring -/
#guard_msgs in
example : Matrix.rank (R := ℕ) !![1, 2; 3, 4] = 2 := by eval_rank

/-- error: expected the element type to be a domain -/
#guard_msgs in
example : Matrix.rank (R := ZMod 4) !![1, 2; 3, 4] = 2 := by eval_rank

/--
error: cannot verify the rank certificate: equality in the element type does not reduce in
the kernel
  ℝ
-/
#guard_msgs in
example : Matrix.rank (R := ℝ) !![1, 2; 3, 4] = 2 := by eval_rank

/--
error: cannot verify the rank certificate: equality in the element type does not reduce in
the kernel
  ℚ[X]
-/
#guard_msgs in
example : Matrix.rank (R := ℚ[X]) !![1, 2; 2, 4] = 1 := by eval_rank

/--
error: cannot verify the rank certificate: equality in the element type does not reduce in the kernel
  ℚ[X]
-/
#guard_msgs in
example : Matrix.rank (R := ℚ[X]) !![X, 1; 1, X] = 2 := by eval_rank

-- in a larger simp set, an unsupported element type is skipped rather than aborting the
-- whole `simp` call (the skip is exactly why the argument goes unused)
set_option linter.unusedSimpArgs false in
example : Matrix.rank (R := ℝ) !![1, 0; 0, 1] = 2 ∨ True := by simp [norm_rank]
