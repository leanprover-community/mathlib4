/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-! # Linear programming

TODO

## Main definitions

 * `CanonicalLP` defines a linear program in the canonical form.
 * `CanonicalLP.Admits` tells if given vector is an admissible solution to given canonical LP.
 * `StandardLP` defines a linear program in the standard form.
 * `StandardLP.Permits` tells if given vector is an admissible solution to given standard LP.

-/

section canonical

open Matrix

/-- Linear program in the canonical form. -/
structure CanonicalLP (m n K : Type _) [Fintype m] [Fintype n] [LinearOrderedField K] where
  /-- (possibly not a) matrix of coefficients -/
  A : (n → K) →ₗ[K] (m → K)
  /-- Right-hand side -/
  b : m → K              
  /-- Objective function coefficients -/  
  c : n → K                

variable {m n K : Type _} [Fintype m] [Fintype n] [LinearOrderedField K]

def CanonicalLP.Admits (P : CanonicalLP m n K) (x : n → K) : Prop :=
  P.A x = P.b ∧ 0 ≤ x

def CanonicalLP.HasMinAt (P : CanonicalLP m n K) (x : n → K) : Prop :=
  P.Admits x ∧ (∀ y, P.Admits y → P.c ⬝ᵥ x ≤ P.c ⬝ᵥ y)

def CanonicalLP.HasMin (P : CanonicalLP m n K) : Prop :=
  ∃ x : n → K, P.HasMinAt x

def CanonicalLP.Minimum (P : CanonicalLP m n K) (d : K) : Prop :=
  ∃ x : n → K, P.HasMinAt x ∧ d = P.c ⬝ᵥ x
-- Or should it be `CanonicalLP.Minimum (P) : Option K` instead?
-- Or `CanonicalLP.Minimum (P) : P.HasMin → K` something?

example : (@CanonicalLP.mk (Fin 2) (Fin 3) ℚ _ _ _
      (Matrix.toLin' !![1, 2, 0; 1, -1, 4]) ![5, 3] 0
    ).Admits ![1, 2, 1] := by
  constructor
  · ext i : 1
    match i with
    | 0 =>
      rfl
    | 1 =>
      rfl
  · simp [LE.le]

end canonical


/-- Linear program in the standard form. -/
structure StandardLP (K V : Type) [LinearOrderedField K] [AddCommGroup V] [Module K V] where
  constr : Finset (AffineMap K V K)
  obj : AffineMap K V K

def StandardLP.Permits {K V : Type} [LinearOrderedField K] [AddCommGroup V] [Module K V]
    (P : StandardLP K V) (x : V) : Prop :=
  ∀ c ∈ P.constr, 0 ≤ c x


/-- Linear program in a more versatile form. -/
structure SomeLP (K V : Type) [LinearOrderedField K] [AddCommGroup V] [Module K V] where
  eq : Finset (AffineMap K V K)
  le : Finset (AffineMap K V K)
  obj : AffineMap K V K

def SomeLP.Solutions {K V : Type} [LinearOrderedField K] [AddCommGroup V] [Module K V]
    (P : SomeLP K V) : Set V :=
  { x : V | (∀ e ∈ P.eq, e x = 0) ∧ (∀ i ∈ P.le, 0 ≤ i x) }
