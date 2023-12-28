/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ComplexShape
import Mathlib.Algebra.GroupPower.NegOnePow

/-! Signs in constructions on homological complexes

In this file, we shall introduce various typeclasses which will allow
the construction of the total complex of a bicomplex and of the
the monoidal category structure on categories of homological complexes (TODO).

The most important definition is that of `TotalComplexShape c₁ c₂ c₁₂` given
three complex shapes `c₁`, `c₂`, `c₁₂`: it allows the definition of a total
complex functor `HomologicalComplex₂ C c₁ c₂ ⥤ HomologicalComplex C c₁₂` (at least
when suitable coproducts exists).

We shall construct an instance of `TotalComplexShape c c c` when `c : ComplexShape I`
and `I` is an additive monoid equipped with a group homomorphism `ε : I → ℤˣ`
satisfying certain properties (TODO).

-/

variable {I₁ I₂ I₁₂ : Type*}
  (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c₁₂ : ComplexShape I₁₂)

/-- A total complex shape for three complexes shapes `c₁`, `c₂`, `c₁₂` on three types
`I₁`, `I₂` and `I₁₂` consists of the data and properties that will allow the construction
of a total complex functor `HomologicalComplex₂ C c₁ c₂ ⥤ HomologicalComplex C c₁₂` which
sends `K` to a complex which in degree `i₁₂ : I₁₂` consists of the coproduct
of the `(K.X i₁).X i₂` such that `π ⟨i₁, i₂⟩ = i₁₂`. -/
class TotalComplexShape  where
  /-- a map -/
  π : I₁ × I₂ → I₁₂
  /-- the sign of the horizontal differential in the total complex -/
  ε₁ : I₁ × I₂ → ℤˣ
  /-- the sign of the vertical differential in the total complex -/
  ε₂ : I₁ × I₂ → ℤˣ
  rel₁ {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) : c₁₂.Rel (π ⟨i₁, i₂⟩) (π ⟨i₁', i₂⟩)
  rel₂ (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') : c₁₂.Rel (π ⟨i₁, i₂⟩) (π ⟨i₁, i₂'⟩)
  ε₂ε₁ {i₁ i₁' : I₁} {i₂ i₂' : I₂} (h₁ : c₁.Rel i₁ i₁') (h₂ : c₂.Rel i₂ i₂') :
    ε₂ ⟨i₁, i₂⟩ * ε₁ ⟨i₁, i₂'⟩ = - ε₁ ⟨i₁, i₂⟩ * ε₂ ⟨i₁', i₂⟩

namespace ComplexShape

variable [TotalComplexShape c₁ c₂ c₁₂]

/-- The map `I₁ × I₂ → I₁₂` on indices given by `TotalComplexShape c₁ c₂ c₁₂`. -/
abbrev π (i : I₁ × I₂) : I₁₂ := TotalComplexShape.π c₁ c₂ c₁₂ i

/-- The sign of the horizontal differential in the total complex. -/
abbrev ε₁ (i : I₁ × I₂) : ℤˣ := TotalComplexShape.ε₁ c₁ c₂ c₁₂ i

/-- The sign of the vertical differential in the total complex. -/
abbrev ε₂ (i : I₁ × I₂) : ℤˣ := TotalComplexShape.ε₂ c₁ c₂ c₁₂ i

variable {c₁}

lemma rel_π₁ {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) :
    c₁₂.Rel (π c₁ c₂ c₁₂ ⟨i₁, i₂⟩) (π c₁ c₂ c₁₂ ⟨i₁', i₂⟩) :=
  TotalComplexShape.rel₁ h i₂

lemma next_π₁ {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) :
    c₁₂.next (π c₁ c₂ c₁₂ ⟨i₁, i₂⟩) = π c₁ c₂ c₁₂ ⟨i₁', i₂⟩ :=
  c₁₂.next_eq' (rel_π₁ c₂ c₁₂ h i₂)

variable (c₁) {c₂}

lemma rel_π₂ (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') :
    c₁₂.Rel (π c₁ c₂ c₁₂ ⟨i₁, i₂⟩) (π c₁ c₂ c₁₂ ⟨i₁, i₂'⟩) :=
  TotalComplexShape.rel₂ i₁ h

lemma next_π₂ (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') :
    c₁₂.next (π c₁ c₂ c₁₂ ⟨i₁, i₂⟩) = π c₁ c₂ c₁₂ ⟨i₁, i₂'⟩ :=
  c₁₂.next_eq' (rel_π₂ c₁ c₁₂ i₁ h)

variable {c₁}

lemma ε₂ε₁ {i₁ i₁' : I₁} {i₂ i₂' : I₂} (h₁ : c₁.Rel i₁ i₁') (h₂ : c₂.Rel i₂ i₂') :
    ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ * ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂'⟩ =
      - ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ * ε₂ c₁ c₂ c₁₂ ⟨i₁', i₂⟩ :=
  TotalComplexShape.ε₂ε₁ h₁ h₂

end ComplexShape
