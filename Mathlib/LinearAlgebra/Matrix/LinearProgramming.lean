/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Data.Matrix.Basic

/-! # Linear programming

TODO

## Main definitions

 * `CanonicalLP` defines a linear program in the canonical form.
 * `CanonicalLP.Admits` tells if given vector is an admissible solution to given LP.

-/

open Matrix

/-- Linear program in the canonical form. -/
structure CanonicalLP (m n α : Type _) [Fintype m] [Fintype n] [LinearOrderedField α] where
  A : Matrix m n ℚ /-- matrix of coefficients -/
  b : m → ℚ        /-- right-hand side -/
  c : n → ℚ

variable {m n α : Type _} [Fintype m] [Fintype n] [LinearOrderedField α]

def CanonicalLP.Admits (P : CanonicalLP m n α) (x : n → ℚ) : Prop :=
  P.A.mulVec x = P.b ∧ 0 ≤ x

def CanonicalLP.HasMinAt (P : CanonicalLP m n α) (x : n → ℚ) : Prop :=
  P.Admits x ∧ (∀ y, P.Admits y → P.c ⬝ᵥ x ≤ P.c ⬝ᵥ y)

def CanonicalLP.HasMin (P : CanonicalLP m n α) : Prop :=
  ∃ x : n → ℚ, P.HasMinAt x

def CanonicalLP.Minimum (P : CanonicalLP m n α) (d : ℚ) : Prop :=
  ∃ x : n → ℚ, P.HasMinAt x ∧ d = P.c ⬝ᵥ x
-- Or should it be `CanonicalLP.Minimum (P) : Option ℚ` instead?
