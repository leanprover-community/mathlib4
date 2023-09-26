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
  A : Matrix m n α /- matrix of coefficients -/
  b : m → α        /- right-hand side -/
  c : n → α        /- coefficients -/

variable {m n α : Type _} [Fintype m] [Fintype n] [LinearOrderedField α]

def CanonicalLP.Admits (P : CanonicalLP m n α) (x : n → α) : Prop :=
  P.A.mulVec x = P.b ∧ 0 ≤ x

def CanonicalLP.HasMinAt (P : CanonicalLP m n α) (x : n → α) : Prop :=
  P.Admits x ∧ (∀ y, P.Admits y → P.c ⬝ᵥ x ≤ P.c ⬝ᵥ y)

def CanonicalLP.HasMin (P : CanonicalLP m n α) : Prop :=
  ∃ x : n → α, P.HasMinAt x

def CanonicalLP.Minimum (P : CanonicalLP m n α) (d : α) : Prop :=
  ∃ x : n → α, P.HasMinAt x ∧ d = P.c ⬝ᵥ x
-- Or should it be `CanonicalLP.Minimum (P) : Option α` instead?

example : (@CanonicalLP.mk (Fin 2) (Fin 3) ℚ _ _ _
      ![![1, 2, 0], ![1, -1, 4]] ![5, 3] 0
    ).Admits ![1, 2, 1] := by
  constructor
  · ext i : 1
    match i with
    | 0 =>
      rfl
    | 1 =>
      rfl
  · simp [LE.le]
