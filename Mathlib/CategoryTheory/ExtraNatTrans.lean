/-
Copyright (c) 2024 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
import Mathlib.CategoryTheory.Functor.Trifunctor
import Mathlib.CategoryTheory.Functor.Hom

/-!
# Extranatural transformations

Defines extranatural transformations between functors
with a variable of mixed variance.

An extranatural transformation `α : ExtraNatTrans F G` between two functors
`F : A ⥤ B ⥤ Bᵒᵖ ⥤ D`, `G : A ⥤ C ⥤ Cᵒᵖ ⥤ D` consists of morphisms
`α.app X Y Z : F.obj X Y Y ⟶ G.obj X Z Z`, and three naturality squares:
* In the `A`-variable we have usual naturality,
`α.naturality₁ f Y Z : F.map₃ f (𝟙 Y) (𝟙 Y) ≫ α.app X' Y Z = α.app X Y Z ≫ G.map₃ f (𝟙 Z) (𝟙 Z)`,
where `f : X ⟶ X'`.
* In the `B`-variable we have extranaturality,
`α.naturality₂ X g Z : F.map₃ (𝟙 X) (𝟙 Y) g ≫ α.app X Y Z = F.map₃ (𝟙 X) g (𝟙 Y') ≫ α.app X Y' Z`,
where `g : Y ⟶ Y'`.
* In the `C`-variable we have extranaturality,
`α.naturality₃ X Y h : α.app X Y Z ≫ G.map₃ (𝟙 X) h (𝟙 Z) = α.app X Y Z' ≫ G.map₃ (𝟙 X) (𝟙 Z') h`,
where `h : Z ⟶ Z'`.

-/

namespace CategoryTheory

-- declare the `v`'s first; see note [CategoryTheory universes].
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
         {C : Type u₃} [Category.{v₃} C] {D : Type u₄} [Category.{v₄} D]

open Opposite

/-- `ExtraNatTrans F G` represents a transformation between functors `F` and `G`
which is ordinary-natural in the first variable and extranatural in the other two.

The field `app` provides the components of the natural transformation.

Naturality is expressed by `α.naturality₁`, `α.naturality₂`, and `α.naturality₃`.
-/
@[ext, pp_dot]
structure ExtraNatTrans (F : A ⥤ B ⥤ Bᵒᵖ ⥤ D) (G : A ⥤ C ⥤ Cᵒᵖ ⥤ D) :
    Type max u₁ u₂ u₃ v₄ where
  /-- The component of an extranatural transformation. -/
  app : ∀ X Y Z, F.obj₃ X Y (op Y) ⟶ G.obj₃ X Z (op Z)
  /-- The naturality square. -/
  naturality₁ : ∀ ⦃X X'⦄ (f : X ⟶ X') Y Z,
    F.map₃ f (𝟙 Y) (𝟙 (op Y)) ≫ app X' Y Z = app X Y Z ≫ G.map₃ f (𝟙 Z) (𝟙 (op Z)) :=
    by aesop_cat
  /-- The extranaturality cowedge. -/
  naturality₂ : ∀ X ⦃Y Y'⦄ (g : Y ⟶ Y') Z,
    F.map₃ (𝟙 X) (𝟙 Y) (op g) ≫ app X Y Z = F.map₃ (𝟙 X) g (𝟙 (op Y')) ≫ app X Y' Z :=
    by aesop_cat
  /-- The extranaturality wedge. -/
  naturality₃ : ∀ X Y ⦃Z Z'⦄ (h : Z ⟶ Z'),
    app X Y Z ≫ G.map₃ (𝟙 X) h (𝟙 (op Z)) = app X Y Z' ≫ G.map₃ (𝟙 X) (𝟙 Z') (op h) :=
    by aesop_cat

attribute [reassoc (attr := simp)]
  ExtraNatTrans.naturality₁ ExtraNatTrans.naturality₂  ExtraNatTrans.naturality₃

namespace ExtraNatTrans

variable {F : A ⥤ B ⥤ Bᵒᵖ ⥤ D} {G : A ⥤ C ⥤ Cᵒᵖ ⥤ D}

theorem congr_app {α β : ExtraNatTrans F G} (h : α = β) (X : A) (Y : B) (Z : C) :
    α.app X Y Z = β.app X Y Z := by aesop_cat

attribute [pp_dot] ExtraNatTrans.app

@[simps!]
def fixMixedVar (F : A ⥤ B ⥤ Bᵒᵖ ⥤ C) (b : B) : A ⥤ C :=
  (F.flip.obj b).flip.obj (op b)

lemma fixMixedVar_curry₃ (F : A × B × Bᵒᵖ ⥤ C) (b : B) :
    fixMixedVar (curry₃.obj F) b = (Prod.sectl A (b, op b)) ⋙ F := rfl

lemma fixMixedVar_obj_eq_obj₃ (F : A ⥤ B ⥤ Bᵒᵖ ⥤ C) (b : B) (a : A) :
    (fixMixedVar F b).obj a = F.obj₃ a b (op b) := rfl

lemma fixMixedVar_map_eq_map₃ (F : A ⥤ B ⥤ Bᵒᵖ ⥤ C) (b : B) {a₁ a₂ : A}
    (f : a₁ ⟶ a₂) : (fixMixedVar F b).map f = F.map₃ f (𝟙 _) (𝟙 _) :=
  (F.map₃_id₂_id₃ f _ _).symm

private
lemma fixMixedVar_eq_comp_uncurry₃ (F : A ⥤ B ⥤ Bᵒᵖ ⥤ C) (b : B) :
    fixMixedVar F b = (Prod.sectl A (b, op b)) ⋙ uncurry₃.obj F :=
  Functor.hext (fun _ => rfl) $ fun _ _ _ => heq_of_eq
    $ Eq.trans (fixMixedVar_map_eq_map₃ F b _)
    $ Eq.symm $ uncurry₃_obj_map_apply_eq_uncurry₃_map₃_apply _ _

def fixMixedVar_iso_comp_uncurry₃ (F : A ⥤ B ⥤ Bᵒᵖ ⥤ C) (b : B) :
    fixMixedVar F b ≅ (Prod.sectl A (b, op b)) ⋙ uncurry₃.obj F :=
  eqToIso (fixMixedVar_eq_comp_uncurry₃ F b)

lemma fixMixedVar_iso_comp_uncurry₃_app (F : A ⥤ B ⥤ Bᵒᵖ ⥤ C) (b : B)
    (a : A) : (fixMixedVar_iso_comp_uncurry₃ F b).app a = Iso.refl _ :=
  eqToIso_app _ _

@[pp_dot]
def natTransComponent (α : ExtraNatTrans F G) (Y : B) (Z : C) :
    NatTrans (fixMixedVar F Y) (fixMixedVar G Z) where
  app X := α.app X Y Z
  naturality _ _ f :=
    Eq.trans (congrArg (. ≫ _) (fixMixedVar_map_eq_map₃ F Y f))
    $ Eq.trans (α.naturality₁ f Y Z)
    $ congrArg (_ ≫ .) (fixMixedVar_map_eq_map₃ G Z f).symm

end ExtraNatTrans

-- We refrain from implementing composition until mathlib has multicategories

end CategoryTheory
