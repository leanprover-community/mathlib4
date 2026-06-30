/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Presentable.Dense
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Pure subobjects

-/

@[expose] public section

universe w

namespace CategoryTheory

variable {C : Type*} [Category* C]

class IsCardinalPure (κ : Cardinal.{w}) [Fact κ.IsRegular]
    {X Y : C} (f : X ⟶ Y) : Prop where
  exists_of_commSq {X' Y' : C} {t : X' ⟶ Y'} {l : X' ⟶ X} {r : Y' ⟶ Y}
    [IsCardinalPresentable X' κ] [IsCardinalPresentable Y' κ]
    (sq : CommSq t l r f) : ∃ (ρ : Y' ⟶ X), t ≫ ρ = l

variable (κ : Cardinal.{w}) [Fact κ.IsRegular]

variable (C) in
abbrev isCardinalPure : MorphismProperty C := fun _ _ f ↦ IsCardinalPure κ f

instance {X Y : C} (f : X ⟶ Y) [IsSplitMono f] : IsCardinalPure κ f where
  exists_of_commSq {X' Y' t l r _ _} sq :=
    ⟨r ≫ retraction f, by simp [sq.w_assoc]⟩

instance {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsCardinalPure κ f] [IsCardinalPure κ g] :
    IsCardinalPure κ (f ≫ g) where
  exists_of_commSq {X' Y' t l r _ _} sq := by
    obtain ⟨ρ, hρ⟩ := IsCardinalPure.exists_of_commSq κ
      (show CommSq t (l ≫ f) r g from ⟨by simpa using sq.w⟩)
    exact IsCardinalPure.exists_of_commSq κ (CommSq.mk hρ)

instance : (isCardinalPure C κ).IsMultiplicative where
  id_mem _ := inferInstance
  comp_mem _ _ _ _ := inferInstance

lemma IsCardinalPure.of_postcomp
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsCardinalPure κ (f ≫ g)] :
    IsCardinalPure κ f where
  exists_of_commSq {X' Y' t l r _ _} sq :=
    exists_of_commSq κ (show CommSq t l (r ≫ g) (f ≫ g) from ⟨by simp [sq.w_assoc]⟩)

instance : (isCardinalPure C κ).HasOfPostcompProperty (⊤ : MorphismProperty C) where
  of_postcomp f g _ _ := IsCardinalPure.of_postcomp κ f g

end CategoryTheory
