/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Enriched.Basic

/-!
# Simplicial categories

A simplicial category is a category `C` that is enriched over the
category of simplicial sets in such a way that morphisms in
`C` identify to the `0`-simplices of the enriched hom.

## TODO

* construct a simplicial category structure on simplicial objects, so
that it applies in particular to simplicial sets
* obtain the adjunction property `(K ⊗ X ⟶ Y) ≃ (K ⟶ sHom X Y)` when `K`, `X`, and `Y`
are simplicial sets
* develop the notion of "simplicial tensor" `K ⊗ₛ X : C` with `K : SSet` and `X : C`
an object in a simplicial category `C`
* define the notion of path between `0`-simplices of simplicial sets
* deduce the notion of homotopy between morphisms in a simplicial category
* obtain that homotopies in simplicial categories can be interpreted as given
by morphisms `Δ[1] ⊗ X ⟶ Y`.

## References
* [Daniel G. Quillen, *Homotopical algebra*, II §1][quillen-1967]

-/

universe v u

open CategoryTheory Category Simplicial MonoidalCategory

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- A simplicial category is a category `C` that is enriched over the
category of simplicial sets in such a way that morphisms in
`C` identify to the `0`-simplices of the enriched hom. -/
class SimplicialCategory extends EnrichedCategory SSet.{v} C where
  /-- morphisms identify to `0`-simplices of the enriched hom -/
  homEquiv (K L : C) : (K ⟶ L) ≃ (𝟙_ SSet.{v} ⟶ EnrichedCategory.Hom K L)
  homEquiv_id (K : C) : homEquiv K K (𝟙 K) = eId SSet K := by aesop_cat
  homEquiv_comp {K L M : C} (f : K ⟶ L) (g : L ⟶ M) :
    homEquiv K M (f ≫ g) = (λ_ _).inv ≫ (homEquiv K L f ⊗ homEquiv L M g) ≫
      eComp SSet K L M := by aesop_cat

namespace SimplicialCategory

variable [SimplicialCategory C]

variable {C}

/-- Abbreviation for the enriched hom of a simplicial category. -/
abbrev sHom (K L : C) : SSet.{v} := EnrichedCategory.Hom K L

/-- Abbreviation for the enriched composition in a simplicial category. -/
abbrev sHomComp (K L M : C) : sHom K L ⊗ sHom L M ⟶ sHom K M := eComp SSet K L M

/-- The bijection `(K ⟶ L) ≃ sHom K L _[0]` for all objects `K` and `L`
in a simplicial category. -/
def homEquiv' (K L : C) : (K ⟶ L) ≃ sHom K L _[0] :=
  (homEquiv K L).trans (sHom K L).unitHomEquiv

/-- The morphism `sHom K' L ⟶ sHom K L` induced by a morphism `K ⟶ K'`. -/
noncomputable def sHomWhiskerRight {K K' : C} (f : K ⟶ K') (L : C) :
    sHom K' L ⟶ sHom K L :=
  (λ_ _).inv ≫ homEquiv K K' f ▷ _ ≫ sHomComp K K' L

@[simp]
lemma sHomWhiskerRight_id (K L : C) : sHomWhiskerRight (𝟙 K) L = 𝟙 _ := by
  simp [sHomWhiskerRight, homEquiv_id]

@[simp, reassoc]
lemma sHomWhiskerRight_comp {K K' K'' : C} (f : K ⟶ K') (f' : K' ⟶ K'') (L : C) :
    sHomWhiskerRight (f ≫ f') L = sHomWhiskerRight f' L ≫ sHomWhiskerRight f L := by
  dsimp [sHomWhiskerRight]
  simp only [assoc, homEquiv_comp, comp_whiskerRight, leftUnitor_inv_whiskerRight, ← e_assoc']
  rfl

/-- The morphism `sHom K L ⟶ sHom K L'` induced by a morphism `L ⟶ L'`. -/
noncomputable def sHomWhiskerLeft (K : C) {L L' : C} (g : L ⟶ L') :
    sHom K L ⟶ sHom K L' :=
  (ρ_ _).inv ≫ _ ◁ homEquiv L L' g ≫ sHomComp K L L'

@[simp]
lemma sHomWhiskerLeft_id (K L : C) : sHomWhiskerLeft K (𝟙 L) = 𝟙 _ := by
  simp [sHomWhiskerLeft, homEquiv_id]

@[simp, reassoc]
lemma sHomWhiskerLeft_comp (K : C) {L L' L'' : C} (g : L ⟶ L') (g' : L' ⟶ L'') :
    sHomWhiskerLeft K (g ≫ g') = sHomWhiskerLeft K g ≫ sHomWhiskerLeft K g' := by
  dsimp [sHomWhiskerLeft]
  simp only [homEquiv_comp, MonoidalCategory.whiskerLeft_comp, assoc, ← e_assoc]
  rfl

@[reassoc]
lemma sHom_whisker_exchange {K K' L L' : C} (f : K ⟶ K') (g : L ⟶ L') :
    sHomWhiskerLeft K' g ≫ sHomWhiskerRight f L' =
      sHomWhiskerRight f L ≫ sHomWhiskerLeft K g :=
  ((ρ_ _).inv ≫ _ ◁ homEquiv L L' g ≫ (λ_ _).inv ≫ homEquiv K K' f ▷ _) ≫=
    (e_assoc SSet.{v} K K' L L').symm

attribute [local simp] sHom_whisker_exchange

variable (C) in
/-- The bifunctor `Cᵒᵖ ⥤ C ⥤ SSet.{v}` which sends `K : Cᵒᵖ` and `L : C` to `sHom K.unop L`. -/
@[simps]
noncomputable def sHomFunctor : Cᵒᵖ ⥤ C ⥤ SSet.{v} where
  obj K :=
    { obj := fun L => sHom K.unop L
      map := fun φ => sHomWhiskerLeft K.unop φ }
  map φ :=
    { app := fun L => sHomWhiskerRight φ.unop L }

end SimplicialCategory

end CategoryTheory
