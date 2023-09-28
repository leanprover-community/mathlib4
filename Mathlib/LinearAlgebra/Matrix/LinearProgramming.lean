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
  /-- Matrix of coefficients -/
  A : Matrix m n K
  /-- Right-hand side -/
  b : m → K
  /-- Objective function coefficients -/
  c : n → K

variable {m n K : Type _} [Fintype m] [Fintype n] [LinearOrderedField K]

def CanonicalLP.Admits (P : CanonicalLP m n K) (x : n → K) : Prop :=
  P.A.mulVec x = P.b ∧ 0 ≤ x

def CanonicalLP.HasMinAt (P : CanonicalLP m n K) (x : n → K) : Prop :=
  P.Admits x ∧ (∀ y, P.Admits y → P.c ⬝ᵥ x ≤ P.c ⬝ᵥ y)

def CanonicalLP.HasMin (P : CanonicalLP m n K) : Prop :=
  ∃ x : n → K, P.HasMinAt x

def CanonicalLP.Minimum (P : CanonicalLP m n K) (d : K) : Prop :=
  ∃ x : n → K, P.HasMinAt x ∧ d = P.c ⬝ᵥ x
-- Or should it be `CanonicalLP.Minimum (P) : Option K` instead?
-- Or `CanonicalLP.Minimum (P) : P.HasMin → K` something?

example : (@CanonicalLP.mk (Fin 2) (Fin 3) ℚ _ _ _ !![1, 2, 0; 1, -1, 4] ![5, 3] 0
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
  /-- Inequality constraints -/
  constr : Finset (AffineMap K V K)
  /-- The objective function -/
  objective : AffineMap K V K

def StandardLP.Permits {K V : Type} [LinearOrderedField K] [AddCommGroup V] [Module K V]
    (P : StandardLP K V) (x : V) : Prop :=
  ∀ c ∈ P.constr, 0 ≤ c x


/-- Linear program in a more versatile form. -/
structure SomeLP (K : Type*) {V : Type*} (P : Type*)
    [LinearOrderedField K] [AddCommGroup V] [Module K V] [AddTorsor V P] where
  /-- Equality constraints -/
  eq : List (P →ᵃ[K] K)
  /-- Inequality constraints -/
  le : List (P →ᵃ[K] K)
  /-- The objective function -/
  obj : P →ᵃ[K] K

def SomeLP.Solutions {K V P : Type*}
    [LinearOrderedField K] [AddCommGroup V] [Module K V] [AddTorsor V P]
    (lp : SomeLP K P) : Set P :=
  { x : P | (∀ e ∈ lp.eq, e x = 0) ∧ (∀ i ∈ lp.le, 0 ≤ i x) }

/-- Convert equality constraints to inequality constraints -/
def SomeLP.removeEQs {K V P : Type*}
    [LinearOrderedField K] [AddCommGroup V] [Module K V] [AddTorsor V P]
    (lp : SomeLP K P) : SomeLP K P where
  eq := []
  le := lp.le ++ lp.eq ++ lp.eq.map Neg.neg
  obj := lp.obj
