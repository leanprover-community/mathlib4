/-
Copyright (c) 2024 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!

# Linear programming

TODO

## Main definitions

 * `StandardLP` defines a linear program in the standard form $ \max cᵀx, A x ≤ b, x ≥ 0 $.
 * `StandardLP.IsSolution` tells if given vector is a solution satisfying given standard LP.

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

def StandardLP.IsSolution (P : StandardLP m n K) (x : n → K) : Prop :=
  P.A.mulVec x ≤ P.b ∧ 0 ≤ x

def StandardLP.IsFeasible (P : StandardLP m n K) : Prop :=
  ∃ x : n → K, P.IsSolution x

def StandardLP.Reaches (P : StandardLP m n K) (v : K) : Prop :=
  ∃ x : n → K, P.IsSolution x ∧ P.c ⬝ᵥ x = v

def StandardLP.dual (P : StandardLP m n K) : StandardLP n m K :=
  ⟨-P.Aᵀ, -P.c, P.b⟩

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
