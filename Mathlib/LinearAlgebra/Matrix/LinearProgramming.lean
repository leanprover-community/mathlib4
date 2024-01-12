import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!

# Linear programming

TODO

## Main definitions

 * `StandardLP` defines a linear program in the standard form.
 * `StandardLP.Admits` tells if given vector is an admissible solution to given standard LP.

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

def StandardLP.Admits (P : StandardLP m n K) (x : n → K) : Prop :=
  P.A.mulVec x ≤ P.b ∧ 0 ≤ x

def StandardLP.Reaches (P : StandardLP m n K) (v : K) : Prop :=
  ∃ x : n → K, P.Admits x ∧ P.c ⬝ᵥ x = v

def StandardLP.Minimum (P : StandardLP m n K) (v : K) : Prop :=
  IsLeast P.Reaches v

def StandardLP.Maximum (P : StandardLP m n K) (v : K) : Prop :=
  IsGreatest P.Reaches v

def StandardLP.dual (P : StandardLP m n K) : StandardLP n m K :=
  ⟨-P.Aᵀ, -P.c, P.b⟩

example (a b c : ℤ) (hab : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by
  exact Int.mul_le_mul_of_nonneg_right hab hc

theorem StandardLP.weakDuality (P : StandardLP m n K) {v : K} (hP : P.Reaches v)
    {w : K} (hD : P.dual.Reaches w) : v ≤ w := by
  obtain ⟨x, ⟨hxb, h0x⟩, rfl⟩ := hP
  obtain ⟨y, ⟨hyc, h0y⟩, rfl⟩ := hD
  dsimp only [StandardLP.dual] at hyc ⊢
  have hxyb : P.A.mulVec x ⬝ᵥ y ≤ P.b ⬝ᵥ y
  · exact Matrix.dotProduct_le_dotProduct_of_nonneg_right hxb h0y
  have hcxy : P.c ⬝ᵥ x ≤ P.Aᵀ.mulVec y ⬝ᵥ x
  · rw [← neg_le_neg_iff, ← neg_dotProduct, ← neg_dotProduct, ← Matrix.neg_mulVec]
    exact Matrix.dotProduct_le_dotProduct_of_nonneg_right hyc h0x
  have middle : P.Aᵀ.mulVec y ⬝ᵥ x = P.A.mulVec x ⬝ᵥ y
  · sorry
  exact (hcxy.trans_eq middle).trans hxyb
