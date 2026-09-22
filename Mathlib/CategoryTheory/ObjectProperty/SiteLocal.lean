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

public section

universe v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C]

/-- An object property is local if it holds for `X` if and only if it holds for all `Uᵢ` where
`{Uᵢ}` is a `K`-cover of `X`. -/
class IsLocal (P : ObjectProperty C) (K : Precoverage C) extends IsClosedUnderIsomorphisms P where
  component {X : C} {R : Presieve X} (hR : R ∈ K X) {Y : C} (f : Y ⟶ X) (hf : R f) : P X → P Y
  of_presieve {X : C} {R : Presieve X} (hR : R ∈ K X) (H : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, R f → P Y) : P X

export IsLocal (of_presieve)

variable {P : ObjectProperty C} {K L : Precoverage C}

lemma iff_of_presieve [P.IsLocal K] {X : C} {R : Presieve X} (hR : R ∈ K X) :
    P X ↔ ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, R f → P Y :=
  ⟨fun h _ _ hf ↦ IsLocal.component hR _ hf h, fun h ↦ of_presieve hR h⟩

namespace IsLocal

lemma mk_of_zeroHypercover [P.IsClosedUnderIsomorphisms]
    (H : ∀ ⦃X : C⦄ (𝒰 : Precoverage.ZeroHypercover.{max u v} K X),
      P X ↔ ∀ i, P (𝒰.X i)) :
    P.IsLocal K where
  component {X R} hR Y f hf hX := by
    rw [CategoryTheory.Precoverage.mem_iff_exists_zeroHypercover] at hR
    obtain ⟨𝒰, rfl⟩ := hR
    rw [H 𝒰] at hX
    obtain ⟨i⟩ := hf
    exact hX i
  of_presieve {X R} hR h := by
    rw [CategoryTheory.Precoverage.mem_iff_exists_zeroHypercover] at hR
    obtain ⟨𝒰, rfl⟩ := hR
    rw [H 𝒰]
    intro i
    exact h ⟨i⟩

lemma of_le [IsLocal P L] (hle : K ≤ L) : IsLocal P K where
  component hR _ f hf hX := component (hle _ hR) f hf hX
  of_presieve hR H := of_presieve (hle _ hR) H

instance top : IsLocal (⊤ : ObjectProperty C) K where
  component := by simp
  of_presieve := by simp

instance inf (P Q : ObjectProperty C) [IsLocal P K] [IsLocal Q K] :
    IsLocal (P ⊓ Q) K where
  component hR _ _ hf h := ⟨component hR _ hf h.1, component hR _ hf h.2⟩
  of_presieve hR h := ⟨of_presieve hR fun _ _ hf ↦ (h hf).1, of_presieve hR fun _ _ hf ↦ (h hf).2⟩

end IsLocal

lemma of_zeroHypercover [P.IsLocal K] {X : C} (𝒰 : K.ZeroHypercover X) (h : ∀ i, P (𝒰.X i)) : P X :=
  P.of_presieve 𝒰.mem₀ fun _ f ⟨i⟩ ↦ h i

lemma iff_of_zeroHypercover [P.IsLocal K] {X : C} (𝒰 : K.ZeroHypercover X) :
    P X ↔ ∀ i, P (𝒰.X i) :=
  ⟨fun h i ↦ IsLocal.component 𝒰.mem₀ _ ⟨i⟩ h, fun h ↦ of_zeroHypercover 𝒰 h⟩

end CategoryTheory.ObjectProperty
