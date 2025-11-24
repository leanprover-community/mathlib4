/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import Mathlib.CategoryTheory.Sites.Hypercover.Zero

/-!
# Locality conditions on object properties

In this file we define locality conditions on object properties in a category. Let `K` be a
precoverage in a category `C` and `P` be an object property that is closed under isomorphisms.

We say that

- `P` is local if for every `X : C`, `P` holds for `X` if and only if it holds for `Uᵢ` for a
  `K`-cover `{Uᵢ}` of `X`.

## Implementation details

The covers appearing in the definitions have index type in the morphism universe of `C`.
-/

@[expose] public section

universe v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C]

/-- An object property is local if it holds for `X` if and only if it holds for all `Uᵢ` where
`{Uᵢ}` is a `K`-cover of `X`. -/
class IsLocal (P : ObjectProperty C) (K : Precoverage C) extends IsClosedUnderIsomorphisms P where
  component {X : C} (𝒰 : Precoverage.ZeroHypercover.{v} K X) (i : 𝒰.I₀) : P X → P (𝒰.X i)
  of_zeroHypercover {X : C} (𝒰 : Precoverage.ZeroHypercover.{v} K X) (h : ∀ i, P (𝒰.X i)) : P X

variable {P : ObjectProperty C} {K L : Precoverage C}

namespace IsLocal

lemma of_le [IsLocal P L] (hle : K ≤ L) : IsLocal P K where
  component 𝒰 i h := component (𝒰.weaken hle) i h
  of_zeroHypercover 𝒰 := of_zeroHypercover (𝒰.weaken hle)

instance top : IsLocal (⊤ : ObjectProperty C) K where
  component := by simp
  of_zeroHypercover := by simp

variable [IsLocal P K] {X : C} (𝒰 : Precoverage.ZeroHypercover.{v} K X)

instance inf (P Q : ObjectProperty C) [IsLocal P K] [IsLocal Q K] :
    IsLocal (P ⊓ Q) K where
  component _ i h := ⟨component _ i h.1, component _ i h.2⟩
  of_zeroHypercover _ h :=
    ⟨of_zeroHypercover _ fun i ↦ (h i).1, of_zeroHypercover _ fun i ↦ (h i).2⟩

end IsLocal

lemma of_zeroHypercover [P.IsLocal K] {X : C} (𝒰 : K.ZeroHypercover X)
    [Precoverage.ZeroHypercover.Small.{v} 𝒰] (h : ∀ i, P (𝒰.X i)) : P X :=
  IsLocal.of_zeroHypercover 𝒰.restrictIndexOfSmall fun _ ↦ h _

lemma iff_of_zeroHypercover [P.IsLocal K] {X : C} (𝒰 : Precoverage.ZeroHypercover.{v} K X) :
    P X ↔ ∀ i, P (𝒰.X i) :=
  ⟨fun h _ ↦ IsLocal.component _ _ h, fun h ↦ of_zeroHypercover 𝒰 h⟩

end CategoryTheory.ObjectProperty
