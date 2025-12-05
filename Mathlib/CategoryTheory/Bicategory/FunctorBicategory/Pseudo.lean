/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo
public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Oplax
public import Mathlib.CategoryTheory.Bicategory.Product

/-!
# The bicategory of pseudofunctors

Given bicategories `B` and `C`, we define a bicategory structure on `Pseudofunctor B C` whose
* objects are pseudofunctors,
* 1-morphisms are strong natural transformations, and
* 2-morphisms are modifications.

We scope this instance to the `CategoryTheory.Pseudofunctor.StrongTrans` namespace to avoid
potential future conflicts with other bicategory instances on `Pseudofunctor B C`.
-/

@[expose] public section

namespace CategoryTheory.Pseudofunctor

open Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace StrongTrans

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

variable {F G H I : B ⥤ᵖ C}

/-- Left whiskering of a strong natural transformation between pseudofunctors
and a modification. -/
abbrev whiskerLeft (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι) : η ≫ θ ⟶ η ≫ ι where
  as := {
    app a := η.app a ◁ Γ.as.app a
    naturality {a b} f := by
      dsimp
      rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc]
      simp }

/-- Right whiskering of an strong natural transformation between pseudofunctors
and a modification. -/
abbrev whiskerRight {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H) : η ≫ ι ⟶ θ ≫ ι where
  as := {
    app a := Γ.as.app a ▷ ι.app a
    naturality {a b} f := by
      dsimp
      simp_rw [Category.assoc, ← associator_inv_naturality_left, whisker_exchange_assoc]
      simp }

/-- Associator for the vertical composition of strong natural transformations
between pseudofunctors. -/
abbrev associator (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I) : (η ≫ θ) ≫ ι ≅ η ≫ θ ≫ ι :=
  isoMk (fun a => α_ (η.app a) (θ.app a) (ι.app a))

/-- Left unitor for the vertical composition of strong natural transformations
between pseudofunctors. -/
abbrev leftUnitor (η : F ⟶ G) : 𝟙 F ≫ η ≅ η :=
  isoMk (fun a => λ_ (η.app a))

/-- Right unitor for the vertical composition of strong natural transformations
between pseudofunctors. -/
abbrev rightUnitor (η : F ⟶ G) : η ≫ 𝟙 G ≅ η :=
  isoMk (fun a => ρ_ (η.app a))

variable (B C)

/-- A bicategory structure on pseudofunctors, with strong transformations as 1-morphisms.

Note that this instance is scoped to the `Pseudofunctor.StrongTrans` namespace. -/
@[simps! whiskerLeft_as_app whiskerRight_as_app associator_hom_as_app associator_inv_as_app
rightUnitor_hom_as_app rightUnitor_inv_as_app leftUnitor_hom_as_app leftUnitor_inv_as_app]
scoped instance bicategory : Bicategory (Pseudofunctor B C) where
  whiskerLeft {F G H} η _ _ Γ := StrongTrans.whiskerLeft η Γ
  whiskerRight {F G H} _ _ Γ η := StrongTrans.whiskerRight Γ η
  associator {F G H} I := StrongTrans.associator
  leftUnitor {F G} := StrongTrans.leftUnitor
  rightUnitor {F G} := StrongTrans.rightUnitor
  whisker_exchange {a b c f g h i} η θ := by ext; exact whisker_exchange _ _

end StrongTrans

open StrongTrans

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] (C : Type u₂) [Bicategory.{w₂, v₂} C]

/-- Object-wise evaluation as a strict pseudofunctor from `B ⥤ᵖ C` to `C`. -/
@[simps!] -- remove eqToIso simps...!
def eval (b : B) : StrictPseudofunctor (B ⥤ᵖ C) C := .mk' {
  obj P := P.obj b
  map θ := θ.app b
  map₂ Γ := Γ.as.app b }

/-- The evaluation pseudofunctor, sending `X : B` and `F : B ⥤ᵖ C` to `F.obj X`. It is
pseudofunctorial in both `X` and `F`. -/
@[simps!]
def evaluation : B ⥤ᵖ (B ⥤ᵖ C) ⥤ᵖ C where
  obj b := (eval C b).toPseudofunctor
  map f := {
    app P := P.map f
    naturality θ := (θ.naturality f).symm }
  map₂ η :=
    { as :=
      { app P := P.map₂ η
        naturality θ := by simp [map₂_whiskerRight_app] }}
  mapId b := isoMk (fun P ↦ P.mapId b) (fun θ ↦ by simp [naturality_id_inv])
  mapComp f g := isoMk (fun P ↦ P.mapComp f g) (fun θ ↦ by simp [naturality_comp_inv])

/-- The evaluation pseudofunctor, sending `X : B` and `F : B ⥤ᵖ C` to `F.obj X`. It is
pseudofunctorial in both `X` and `F`. -/
@[simps!]
def evaluationUncurried : B × (B ⥤ᵖ C) ⥤ᵖ C where
  obj X := X.2.obj X.1
  map {X Y} f := f.2.app X.1 ≫ Y.2.map f.1
  map₂ {X Y f g} η := η.2.as.app X.1 ▷ Y.2.map f.1 ≫ (g.2.app X.1 ◁ Y.2.map₂ η.1)
  map₂_comp {X Y f g h} η θ := by simp [← whisker_exchange_assoc]
      -- TODO: add toProd
  mapId X := λ_ (X.2.map (𝟙 X : (X.1 ⟶ X.1) × (X.2 ⟶ X.2)).1) ≪≫ X.2.mapId X.1
  mapComp {X Y Z} f g := by
    apply whiskerLeftIso _ (Z.2.mapComp f.1 g.1) ≪≫ _
    dsimp -- TODO: fix
    apply (α_ _ _ _) ≪≫ _
    sorry
  map₂_whisker_left := sorry
  map₂_whisker_right := sorry
  map₂_associator := sorry
  map₂_left_unitor := sorry
  map₂_right_unitor := sorry
  --(StrictPseudofunctor.prodPseudofunctor B (B ⥤ᵖ C)).comp (evaluation C).toStrictPseudofunctor


end CategoryTheory.Pseudofunctor
