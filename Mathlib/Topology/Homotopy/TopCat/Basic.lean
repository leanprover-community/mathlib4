/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Topology.Category.TopCat.Monoidal
public import Mathlib.Topology.Homotopy.Basic

/-!
# Homotopies between morphisms in `TopCat`

In this file, we define the type `TopCat.Homotopy` of homotopies
between two morphisms in the category `TopCat`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace TopCat

variable {X Y Z : TopCat.{u}}

/-- A homotopy between morphisms in `TopCat` is a homotopy between
the corresponding continuous maps. -/
abbrev Homotopy (f g : X ⟶ Y) := ContinuousMap.Homotopy f.hom g.hom

namespace Homotopy

variable {f₀ f₁ f₂ : X ⟶ Y} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂)

/-- The morphism `X ⊗ I ⟶ Y` that is part of a homotopy between two morphisms in `TopCat`. -/
def h (H : Homotopy f₀ f₁) : X ⊗ I ⟶ Y :=
  (β_ _ _).hom ≫ ofHom (H.toContinuousMap.comp (ContinuousMap.prodMap I.homeomorph (.id _)))

-- simps generates the wrong apply lemma
@[simp]
theorem h_hom_apply (p : ↑(X ⊗ I)) : F.h p = F (I.homeomorph p.2, p.1) := rfl

@[reassoc (attr := simp)]
lemma ι₀_h : ι₀ ≫ F.h = f₀ := by
  ext x
  exact F.map_zero_left x

@[reassoc (attr := simp)]
lemma ι₁_h : ι₁ ≫ F.h = f₁ := by
  ext x
  exact F.map_one_left x

/-- The identity homotopy of a morphism `f : X ⟶ Y` in `TopCat`. -/
@[simps!]
abbrev refl (f : X ⟶ Y) := ContinuousMap.Homotopy.refl f.hom

@[simp]
lemma h_refl : h (refl f₀) = fst _ _ ≫ f₀ := rfl

/-- The reverse of a homotopy `F` in `TopCat`. -/
@[simps!]
abbrev symm := ContinuousMap.Homotopy.symm F

@[simp]
lemma h_symm : h F.symm = (X ◁ I.symm) ≫ F.h := rfl

/-- The compositions of homotopies in `TopCat`. -/
noncomputable abbrev trans := ContinuousMap.Homotopy.trans F G

/-- The homotopy between compositions of morphisms in `TopCat`. -/
@[simps!]
abbrev comp {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z} (G : Homotopy g₀ g₁) (F : Homotopy f₀ f₁) :
    Homotopy (f₀ ≫ g₀) (f₁ ≫ g₁) := ContinuousMap.Homotopy.comp G F

@[simp]
lemma h_comp {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z} (G : Homotopy g₀ g₁) (F : Homotopy f₀ f₁) :
    (G.comp F).h = X ◁ lift (𝟙 I) (𝟙 I) ≫ (α_ _ _ _).inv ≫ F.h ▷ _ ≫ G.h := by
  ext
  simp

end Homotopy

end TopCat
