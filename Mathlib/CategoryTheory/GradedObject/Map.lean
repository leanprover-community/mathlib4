import Mathlib.CategoryTheory.GradedObject

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C]

namespace GradedObject

variable {I J : Type*} (X Y Z : GradedObject I C) (φ : X ⟶ Y) (ψ : Y ⟶ Z) (p : I → J)

abbrev HasMap : Prop := ∀ (j : J), HasCoproduct (fun (i : (p ⁻¹' {j})) => X i)

variable [X.HasMap p] [Y.HasMap p] [Z.HasMap p]

noncomputable def mapObj : GradedObject J C := fun j => ∐ (fun (i : (p ⁻¹' {j})) => X i)

variable {X Y}

noncomputable def mapMap : X.mapObj p ⟶ Y.mapObj p := fun _ => Limits.Sigma.map (fun i => φ i)

lemma congr_mapMap (φ₁ φ₂ : X ⟶ Y) (h : φ₁ = φ₂) : mapMap φ₁ p = mapMap φ₂ p := by
  subst h
  rfl

variable (X)

@[simp]
lemma mapMap_id : mapMap (𝟙 X) p = 𝟙 _ := by
  ext j
  apply Limits.Sigma.map_id

variable {X Z}

@[simp]
lemma mapMap_comp : mapMap (φ ≫ ψ) p = mapMap φ p ≫ mapMap ψ p := by
  ext j
  symm
  dsimp [mapMap]
  apply Limits.Sigma.map_comp_map

variable (C)

abbrev HasMapFunctor := ∀ (j : J), HasColimitsOfShape (Discrete (p ⁻¹' {j})) C

noncomputable def map [HasMapFunctor C p] : GradedObject I C ⥤ GradedObject J C where
  obj X := X.mapObj p
  map φ := mapMap φ p

end GradedObject

end CategoryTheory
