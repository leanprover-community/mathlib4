module

import Mathlib.Tactic.NormRank

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Cartan
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatSqrt

/-! # Tests for the `eval_rank` tactic -/

/-! ## Basic evaluation over `ℤ` and `ℚ` -/

example : Matrix.rank (R := ℤ)
    !![1, 2, 3] = 1 := by
  eval_rank

example : Matrix.rank (R := ℤ)
    !![1 - 1, 2, 3] = 1 := by
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
    !![,,,] = 0 := by
  eval_rank

example : Matrix.rank (R := ℚ)
    !![;;;] = 0 := by
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
    !![1, 2, 0, 1, 3;
       0, 1, 1, 2, 1;
       2, 4, 0, 2, 6;
       0, 0, 1, 0, 2;
       1, 3, 1, 3, 4] = 3 := by
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

/-! ## Row swaps -/

-- a swap after an elimination step:
example : Matrix.rank (R := ℤ) !![1, 1, 1; 2, 2, 3; 3, 4, 5] = 3 := by eval_rank

-- consecutive swaps after elimination
example : Matrix.rank (R := ℤ)
    !![1, 1, 1, 1;
       2, 2, 2, 3;
       3, 4, 5, 6;
       4, 5, 7, 8] = 4 := by
  eval_rank

-- swap with fractional entries: the row scales follow the swapped order
example : Matrix.rank (R := ℚ) !![0, 1/2; 1/3, 1] = 2 := by eval_rank

/-! ## Element-type coverage: `ZMod p`, `ℤ√d` -/

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

example : Matrix.rank (R := ZMod 7) !![3, 5; 2, 4] = 2 := by eval_rank

-- det = -7 ≡ 0 (mod 7): full rank over ℚ, but rank 1 over ZMod 7
example : Matrix.rank (R := ZMod 7) !![2, 5; 3, 4] = 1 := by eval_rank

-- 2 * 4 ≡ 1 (mod 7), det ≡ 0
example : Matrix.rank (R := ZMod 7) !![2 * 4, 1; 1, 1] = 1 := by eval_rank

-- the pivot entry vanishes only modulo 7, forcing a swap through the mod test
example : Matrix.rank (R := ZMod 7) !![7, 1; 3, 5] = 2 := by eval_rank

-- ℤ[i] with integer entries
example : Matrix.rank (R := GaussianInt) !![2, 5; 3, 4] = 2 := by eval_rank

-- row 2 = i · row 1 over ℤ[i]
example : Matrix.rank (R := GaussianInt) !![1, ⟨0, 1⟩; ⟨0, 1⟩, -1] = 1 := by eval_rank

-- a zero pivot over ℤ[i] forces the swap in the `ℤ√d` model
example : Matrix.rank (R := GaussianInt) !![0, ⟨0, 1⟩; ⟨0, 1⟩, 1] = 2 := by eval_rank

-- handling Zsqrtd.sqrtd def without rewriting
example : Matrix.rank (R := GaussianInt) !![Zsqrtd.sqrtd, ⟨0, 1⟩] = 1 := by eval_rank

/-! ## Unfolding, rewrites, and simplifications -/

-- rewrite
example (A : Matrix (Fin 1) (Fin 3) ℤ) (hA : A = !![1, 2, 3]) :
    A.rank = 1 := by
  rw [hA]
  eval_rank

-- rank of an existing definition, after rewriting it to a literal
example : Matrix.rank (R := ℤ) (CartanMatrix.E 7) = 7 := by
  rw [CartanMatrix.E_seven_eq]
  eval_rank

section Binet

instance : Zsqrtd.Nonsquare 5 :=
  ⟨fun n h => by have := (Nat.exists_mul_self 5).mp ⟨n, h.symm⟩; norm_num at this⟩

-- mathlib states the `Nonsquare`-based instance for `ℕ`-coerced `d` only
instance : IsDomain (Zsqrtd 5) :=
  inferInstanceAs (IsDomain (Zsqrtd (5 : ℕ)))

local notation "Φ" => (⟨1, 1⟩ : Zsqrtd 5)
local notation "Ψ" => (⟨1, -1⟩ : Zsqrtd 5)

private theorem mul_def {d : ℤ} (x y x' y' : ℤ) :
    (⟨x, y⟩ * ⟨x', y'⟩ : Zsqrtd d) = ⟨x * x' + d * y * y', x * y' + y * x'⟩ := rfl

/- The first two columns are the powers `Φⁿ` and `Ψⁿ` of `Φ = 1 + √5 = 2φ` and
`Ψ = 1 - √5 = 2ψ`, the scaled golden ratio and its conjugate; the third is the Fibonacci
data `√5 * 2ⁿ * Fₙ`. Binet's formula gives that `Φⁿ - Ψⁿ = √5 * 2ⁿ * Fₙ`
(cf. `Real.coe_fib_eq`), so the rank is 2. -/
example : Matrix.rank (R := Zsqrtd 5)
    !![Φ, Ψ, ⟨0, 2^1 * Nat.fib 1⟩;
       Φ^2, Ψ^2, ⟨0, 2^2 * Nat.fib 2⟩;
       Φ^3, Ψ^3, ⟨0, 2^3 * Nat.fib 3⟩] = 2 := by
  norm_num [pow_succ, mul_def]
  eval_rank

end Binet


/-! ## Behavior inside `simp` -/

-- mixed element types in one goal: the ℤ literal is rewritten while the unsupported ℝ
-- literal is skipped, without an error; the ℝ rank is then evaluated by recognizing the
-- identity matrix
example :
    Matrix.rank (R := ℤ) !![1, 2; 2, 4] = Matrix.rank (R := ℝ) !![1, 0; 0, 1] - 1 := by
  simp only [norm_rank]
  simp [← Matrix.one_fin_two, Matrix.rank_one]

-- a similar example via `eval_rank`, plus testing that the tactic doesn't hard commit to
-- the first occurrence of Matrix.rank
example :
    Matrix.rank (R := ℝ) !![1, 0; 0, 1] = Matrix.rank (R := ℤ) !![1, 2; 2, 4] + 1 := by
  eval_rank
  simp [← Matrix.one_fin_two, Matrix.rank_one]

-- a literal with symbolic entries is skipped instead of reporting an error
example (a : ℚ) (h : Matrix.rank (R := ℚ) !![a, 1; 1, a] = 2) :
    Matrix.rank (R := ℚ) !![1, 0; 0, 1] = Matrix.rank (R := ℚ) !![a, 1; 1, a] := by
  simp only [norm_rank]
  lia

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

set_option trace.Tactic.evalRank true

/-! ### No closed matrix literal in the goal -/

/--
error: `eval_rank` made no progress.
Additional information may be available using `set_option trace.Tactic.evalRank true`.
---
trace: [Tactic.evalRank] not a closed matrix literal
      A
-/
#guard_msgs in
example (A : Matrix (Fin 2) (Fin 2) ℚ) : A.rank = 2 := by eval_rank

/--
error: `eval_rank` made no progress.
Additional information may be available using `set_option trace.Tactic.evalRank true`.
---
trace: [Tactic.evalRank] not a closed matrix literal
      !![a, 1; 1, a]
-/
#guard_msgs in
example (a : ℚ) : Matrix.rank (R := ℚ) !![a, 1; 1, a] = 2 := by eval_rank

/-! ### Out of scope for the Bareiss method -/

/--
error: `eval_rank` made no progress.
Additional information may be available using `set_option trace.Tactic.evalRank true`.
---
trace: [Tactic.evalRank] expected the element type to be a commutative ring
      !![1, 2; 3, 4]
-/
#guard_msgs in
example : Matrix.rank (R := ℕ) !![1, 2; 3, 4] = 2 := by eval_rank

/--
error: `eval_rank` made no progress.
Additional information may be available using `set_option trace.Tactic.evalRank true`.
---
trace: [Tactic.evalRank] expected the element type to be a domain
      !![1, 2; 3, 4]
-/
#guard_msgs in
example : Matrix.rank (R := ZMod 4) !![1, 2; 3, 4] = 2 := by eval_rank

/-! ### Possible extensions

Rejected today; extensions of the tactic could support these inputs. -/

-- Requires a more general cert checker that works for rational literals in types like ℝ
/--
error: `eval_rank` made no progress.
Additional information may be available using `set_option trace.Tactic.evalRank true`.
---
trace: [Tactic.evalRank] equality in the element type does not reduce in the kernel
      ℝ
      !![1, 2; 3, 4]
-/
#guard_msgs in
example : Matrix.rank (R := ℝ) !![1, 2; 3, 4] = 2 := by eval_rank

-- Requires computable polynomial ops in the kernel
open Polynomial in
/--
error: `eval_rank` made no progress.
Additional information may be available using `set_option trace.Tactic.evalRank true`.
---
trace: [Tactic.evalRank] equality in the element type does not reduce in the kernel
      ℚ[X]
      !![X, 1; 1, X]
-/
#guard_msgs in
example : Matrix.rank (R := ℚ[X]) !![X, 1; 1, X] = 2 := by eval_rank

-- Requires an extension to compute the modulo inverse and handle the syntax parsing
/--
error: `eval_rank` made no progress.
Additional information may be available using `set_option trace.Tactic.evalRank true`.
---
trace: [Tactic.evalRank] the following entry cannot be simplified to a numeral
      2 / 3
-/
#guard_msgs in
example : Matrix.rank (R := ZMod 7) !![2/3, 0; 0, 1] = 2 := by eval_rank

-- under bare `simp` the same failure is reported without the trace hint
/--
error: `simp` made no progress
---
trace: [Tactic.evalRank] the following entry cannot be simplified to a numeral
      2 / 3
-/
#guard_msgs in
example : Matrix.rank (R := ZMod 7) !![2/3, 0; 0, 1] = 2 := by
  simp only [norm_rank]
