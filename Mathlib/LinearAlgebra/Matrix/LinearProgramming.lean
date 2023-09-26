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
structure CanonicalLP where
  {m n : ℕ}                    /-- size -/
  A : Matrix (Fin m) (Fin n) ℚ /-- matrix of coefficients -/
  b : (Fin m) → ℚ              /-- right-hand side -/
  c : (Fin n) → ℚ              /-- weights -/

def CanonicalLP.Admits (P : CanonicalLP) (x : (Fin P.n) → ℚ) : Prop :=
  P.A.mulVec x = P.b ∧ 0 ≤ x

def CanonicalLP.HasMinAt (P : CanonicalLP) (x : (Fin P.n) → ℚ) : Prop :=
  P.Admits x ∧ (∀ y, P.Admits y → P.c ⬝ᵥ x ≤ P.c ⬝ᵥ y)

def CanonicalLP.HasMin (P : CanonicalLP) : Prop :=
  ∃ x : (Fin P.n) → ℚ, P.HasMinAt x

def CanonicalLP.Minimum (P : CanonicalLP) (d : ℚ) : Prop :=
  ∃ x : (Fin P.n) → ℚ, P.HasMinAt x ∧ d = P.c ⬝ᵥ x
-- Or should it be `CanonicalLP.Minimum (P : CanonicalLP) : Option ℚ` instead?

example : (CanonicalLP.mk ![![1, 2, 0], ![1, -1, 4]] ![5, 3] 0).Admits ![1, 2, 1] := by
  constructor
  · ext i : 1
    match i with
    | 0 =>
      rfl
    | 1 =>
      rfl
  · simp [LE.le]
