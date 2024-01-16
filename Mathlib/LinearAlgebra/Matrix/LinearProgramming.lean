/-
Copyright (c) 2024 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!

# Linear programming

We define linear programs over a `LinearOrderedField K` in the standard matrix form.

## Main definitions

 * `StandardLP` defines a linear program in the standard form $ \max cᵀx, A x ≤ b, x ≥ 0 $.
 * `StandardLP.IsSolution` tells if given vector is a solution satisfying given standard LP.
 * `StandardLP.IsFeasible` tells if given standard LP has any solution.
 * `StandardLP.Reaches` tells if given value can be obtained as a cost of any solution of given
    standard LP.
 * `StandardLP.dual` defines a dual problem to given standard LP.

## Main results

* `StandardLP.weakDuality`: The weak duality theorem (`cᵀx` such that `A x ≤ b` and `x ≥ 0` is
   always less or equal to `bᵀy` such that `Aᵀ y ≥ c` and `y ≥ 0`).

-/

open Matrix

/-- Linear program in the standard form. -/
structure StandardLP (m n K : Type) [Fintype m] [Fintype n] [LinearOrderedField K] where
  /-- Matrix of coefficients -/
  A : Matrix m n K
  /-- Right-hand side -/
  b : m → K
  /-- Objective function coefficients -/
  c : n → K

variable {m n K : Type} [Fintype m] [Fintype n] [LinearOrderedField K]

/-- Vector `x` is a solution to linear program `P` iff all entries of `x` are nonnegative and its
multiplication by matrix `A` from the left yields a vector whose all entries are less or equal to
corresponding entries of the vector `b`. -/
def StandardLP.IsSolution (P : StandardLP m n K) (x : n → K) : Prop :=
  P.A.mulVec x ≤ P.b ∧ 0 ≤ x

/-- Linear program `P` is feasible iff there is a vector `x` that is a solution to `P`. -/
def StandardLP.IsFeasible (P : StandardLP m n K) : Prop :=
  ∃ x : n → K, P.IsSolution x

/-- Linear program `P` reaches objective value `v` iff there is a solution `x` such that,
when its entries are elementwise multiplied by the costs (given by the vector `c`) and summed up,
the result is the value `v`. -/
def StandardLP.Reaches (P : StandardLP m n K) (v : K) : Prop :=
  ∃ x : n → K, P.IsSolution x ∧ P.c ⬝ᵥ x = v

/-- Dual linear program to given linear program `P` in the standard form.
The matrix gets transposed and its values flip signs.
The original cost function gets flipped signs as well and becomes the new righ-hand side vector.
The original righ-hand side vector becomes the new vector of objective function coefficients. -/
def StandardLP.dual (P : StandardLP m n K) : StandardLP n m K :=
  ⟨-P.Aᵀ, -P.c, P.b⟩

/-- Objective values reached by linear program `P` are all less or equal to all objective values
reached by the dual of `P`. -/
theorem StandardLP.weakDuality {P : StandardLP m n K}
    {v : K} (hP : P.Reaches v) {w : K} (hD : P.dual.Reaches w) :
    v ≤ w := by
  obtain ⟨x, ⟨hxb, h0x⟩, rfl⟩ := hP
  obtain ⟨y, ⟨hyc, h0y⟩, rfl⟩ := hD
  dsimp only [StandardLP.dual] at hyc ⊢
  have hxyb : P.A.mulVec x ⬝ᵥ y ≤ P.b ⬝ᵥ y
  · exact dotProduct_le_dotProduct_of_nonneg_right hxb h0y
  have hcxy : P.c ⬝ᵥ x ≤ P.Aᵀ.mulVec y ⬝ᵥ x
  · rw [← neg_le_neg_iff, ← neg_dotProduct, ← neg_dotProduct, ← neg_mulVec]
    exact dotProduct_le_dotProduct_of_nonneg_right hyc h0x
  rw [dotProduct_comm (P.Aᵀ.mulVec y), dotProduct_mulVec, vecMul_transpose] at hcxy
  exact hcxy.trans hxyb

set_option linter.unusedVariables false in
proof_wanted StandardLP.strongDuality {P : StandardLP m n K}
    (hP : P.IsFeasible) (hD : P.dual.IsFeasible) :
    ∃ v : K, P.Reaches v ∧ P.dual.Reaches v
