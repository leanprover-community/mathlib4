/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes

/-!
# Simplicial categories

A simplicial category is a category `C` that is enriched over the
category of simplicial sets, in such a way that morphisms in
`C` identify to the `0`-simplices of the enriched hom.

TODO: add reference to the original source by Quillen, Homotopical algebra

-/

universe v u

open CategoryTheory Category Simplicial MonoidalCategory

namespace SimplexCategory

def const' (Δ Δ' : SimplexCategory) (x : Fin (Δ'.len + 1)) : Δ ⟶ Δ' :=
  SimplexCategory.Hom.mk ⟨fun _ => x, by tauto⟩

@[simp]
lemma const'_eq_id : const' [0] [0] 0 = 𝟙 _ := by aesop

end SimplexCategory

namespace SSet

structure Path (X : SSet.{v}) (x y : X _[0]) where
  p : X _[1]
  p₀ : X.δ 1 p = x
  p₁ : X.δ 1 p = x

instance : ChosenFiniteProducts SSet.{v} where
  terminal := FunctorToTypes.functorEmptyLimitCone _
  product := FunctorToTypes.binaryProductLimitCone

def unitHomEquiv (K : SSet.{v}) : (𝟙_ _ ⟶ K) ≃ K _[0] where
  toFun φ := φ.app _ PUnit.unit
  invFun x :=
    { app := fun Δ _ => K.map (SimplexCategory.const' Δ.unop [0] 0).op x
      naturality := fun Δ Δ' f => by
        ext ⟨⟩
        dsimp
        rw [← FunctorToTypes.map_comp_apply]
        rfl }
  left_inv φ := by
    ext Δ ⟨⟩
    dsimp
    erw [← FunctorToTypes.naturality]
    rfl
  right_inv x := by
    dsimp
    rw [SimplexCategory.const'_eq_id]
    erw [FunctorToTypes.map_id_apply]

@[simp]
lemma leftUnitor_hom_apply (K : SSet.{v}) {Δ : SimplexCategoryᵒᵖ} (x : (𝟙_ _ ⊗ K).obj Δ) :
  (λ_ K).hom.app Δ x = x.2 := rfl

@[simp]
lemma leftUnitor_inv_apply (K : SSet.{v}) {Δ : SimplexCategoryᵒᵖ} (x : K.obj Δ) :
  (λ_ K).inv.app Δ x = ⟨PUnit.unit, x⟩ := rfl

@[simp]
lemma rightUnitor_hom_apply (K : SSet.{v}) {Δ : SimplexCategoryᵒᵖ} (x : (K ⊗ 𝟙_ _).obj Δ) :
  (ρ_ K).hom.app Δ x = x.1 := rfl

@[simp]
lemma rightUnitor_inv_apply (K : SSet.{v}) {Δ : SimplexCategoryᵒᵖ} (x : K.obj Δ) :
  (ρ_ K).inv.app Δ x = ⟨x, PUnit.unit⟩ := rfl

@[simp]
lemma whiskerLeft_apply (K : SSet.{v}) {L L' : SSet.{v}} (g : L ⟶ L')
    {Δ : SimplexCategoryᵒᵖ} (x : (K ⊗ L).obj Δ) :
    (K ◁ g).app Δ x = ⟨x.1, g.app Δ x.2⟩ := rfl

@[simp]
lemma whiskerRight_apply {K K' : SSet.{v}} (f : K ⟶ K') (L : SSet.{v})
    {Δ : SimplexCategoryᵒᵖ} (x : (K ⊗ L).obj Δ) :
    (f ▷ L).app Δ x = ⟨f.app Δ x.1, x.2⟩ := rfl

@[simp]
lemma associator_hom_apply (K L M : SSet.{v}) {Δ : SimplexCategoryᵒᵖ} (x : ((K ⊗ L) ⊗ M).obj Δ) :
  (α_ K L M).hom.app Δ x = ⟨x.1.1, x.1.2, x.2⟩ := rfl

@[simp]
lemma associator_inv_apply (K L M : SSet.{v}) {Δ : SimplexCategoryᵒᵖ} (x : (K ⊗ L ⊗ M).obj Δ) :
  (α_ K L M).inv.app Δ x = ⟨⟨x.1, x.2.1⟩, x.2.2⟩ := rfl

end SSet

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

section

/-- A (pre)simplicial category is a category `C` that is enriched in the category
of simplicial sets in such a way that the `0`-simplicies of this simplicial hom
identifies to morphisms in `C`. -/
class SimplicialCategory where
  enrichedCategory : EnrichedCategory SSet.{v} C := by infer_instance
  homEquiv (K L : C) : (K ⟶ L) ≃ (𝟙_ SSet.{v} ⟶ EnrichedCategory.Hom K L)
  homEquiv_id (K : C) : homEquiv K K (𝟙 K) = eId SSet K := by aesop_cat
  homEquiv_comp {K L M : C} (f : K ⟶ L) (g : L ⟶ M) :
    homEquiv K M (f ≫ g) = (λ_ _).inv ≫ (homEquiv K L f ⊗ homEquiv L M g) ≫
      eComp SSet K L M := by aesop_cat

end

namespace SimplicialCategory

attribute [instance] enrichedCategory

variable [SimplicialCategory C]

variable {C}

abbrev sHom (K L : C) : SSet.{v} := EnrichedCategory.Hom K L

def homEquiv' (K L : C) : (K ⟶ L) ≃ sHom K L _[0] :=
  (homEquiv K L).trans (sHom K L).unitHomEquiv

noncomputable def sHomMap₁ {K K' : C} (f : K ⟶ K') (L : C) :
    sHom K' L ⟶ sHom K L :=
  (λ_ _).inv ≫ homEquiv K K' f ▷ _ ≫ eComp SSet K K' L

@[simp]
lemma sHomMap₁_id (K L : C) :
    sHomMap₁ (𝟙 K) L = 𝟙 _ := by
  simp [sHomMap₁, homEquiv_id]

@[simp, reassoc]
lemma sHomMap₁_comp {K K' K'' : C} (f : K ⟶ K') (f' : K' ⟶ K'') (L : C) :
    sHomMap₁ (f ≫ f') L = sHomMap₁ f' L ≫ sHomMap₁ f L := by
  dsimp [sHomMap₁]
  simp only [assoc, homEquiv_comp, comp_whiskerRight, leftUnitor_inv_whiskerRight, ← e_assoc']
  rfl

noncomputable def sHomMap₂ (K : C) {L L' : C} (g : L ⟶ L') :
    sHom K L ⟶ sHom K L' :=
  (ρ_ _).inv ≫ _ ◁ homEquiv L L' g ≫ eComp SSet K L L'

@[simp]
lemma sHomMap₂_id (K L : C) :
    sHomMap₂ K (𝟙 L) = 𝟙 _ := by
  simp [sHomMap₂, homEquiv_id]

@[simp, reassoc]
lemma sHomMap₂_comp (K : C) {L L' L'' : C} (g : L ⟶ L') (g' : L' ⟶ L'') :
    sHomMap₂ K (g ≫ g') = sHomMap₂ K g ≫ sHomMap₂ K g' := by
  dsimp [sHomMap₂]
  simp only [homEquiv_comp, MonoidalCategory.whiskerLeft_comp, assoc, ← e_assoc]
  rfl

@[reassoc]
lemma sHomMap₂_sHomMap₁ {K K' L L' : C} (f : K ⟶ K') (g : L ⟶ L') :
    sHomMap₂ K' g ≫ sHomMap₁ f L' = sHomMap₁ f L ≫ sHomMap₂ K g :=
  ((ρ_ _).inv ≫ _ ◁ homEquiv L L' g ≫ (λ_ _).inv ≫ homEquiv K K' f ▷ _) ≫=
    (e_assoc SSet.{v} K K' L L').symm

attribute [local simp] sHomMap₂_sHomMap₁

@[simps]
noncomputable def sHomFunctor : Cᵒᵖ ⥤ C ⥤ SSet.{v} where
  obj K :=
    { obj := fun L => sHom K.unop L
      map := fun φ => sHomMap₂ K.unop φ }
  map φ :=
    { app := fun L => sHomMap₁ φ.unop L }

abbrev Homotopy {K L : C} (f g : K ⟶ L) :=
  (sHom K L).Path (homEquiv' K L f) (homEquiv' K L g)

-- TODO: develop API for the "adjoint functors"
-- especially, introduce a *data valued* class containing the data
-- of a representative of `A ⊗ K` for `A : SSet.{v}` and `K : C`, so
-- it can be chosen to be definitionnaly the constructed product in case `K : SSet.{v}`

end SimplicialCategory

end CategoryTheory
