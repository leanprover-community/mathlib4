/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Strong

/-!
# The Grothendieck construction

Given a category `𝒮` and any pseudofunctor `F` from `𝒮ᵒᵖ` to `Cat`, we associate to it a category
`∫ F`, equipped with a functor `∫ F ⥤ 𝒮`.

The category `∫ F` is defined as follows:
* Objects: pairs `(S, a)` where `S` is an object of the base category and `a` is an object of the
  category `F(S)`.
* Morphisms: morphisms `(R, b) ⟶ (S, a)` are defined as pairs `(f, h)` where `f : R ⟶ S` is a
  morphism in `𝒮` and `h : b ⟶ F(f)(a)`

The projection functor `∫ F ⥤ 𝒮` is then given by projecting to the first factors, i.e.
* On objects, it sends `(S, a)` to `S`
* On morphisms, it sends `(f, h)` to `f`

## TODO
1. Implement functoriality for the Grothendieck construction.
2. Obtain the results in `CategoryTheory.Grothendieck` as a specialization of these results.

## References
[Vistoli2008] "Notes on Grothendieck Topologies, Fibered Categories and Descent Theory" by
Angelo Vistoli

-/

namespace CategoryTheory

universe w v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Functor Category Opposite Discrete Bicategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}}

/-- The type of objects in the fibered category associated to a presheaf valued in types. -/
@[ext]
structure Pseudofunctor.Grothendieck (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}) where
  /-- The underlying object in the base category. -/
  base : 𝒮
  /-- The object in the fiber of the base object. -/
  fiber : F.obj ⟨op base⟩

namespace Pseudofunctor.Grothendieck

/-- Notation for the Grothendieck category associated to a pseudofunctor `F`. -/
scoped prefix:75 "∫ " => Pseudofunctor.Grothendieck

@[simps]
instance categoryStruct : CategoryStruct (∫ F) where
  Hom X Y := (f : X.1 ⟶ Y.1) × (X.2 ⟶ (F.map f.op.toLoc).obj Y.2)
  id X := ⟨𝟙 X.1, (F.mapId ⟨op X.1⟩).inv.app X.2⟩
  comp {_ _ Z} f g := ⟨f.1 ≫ g.1, f.2 ≫ (F.map f.1.op.toLoc).map g.2 ≫
    (F.mapComp g.1.op.toLoc f.1.op.toLoc).inv.app Z.2⟩

section

variable {a b : ∫ F} (f : a ⟶ b)

@[ext]
lemma hom_ext (g : a ⟶ b) (hfg₁ : f.1 = g.1) (hfg₂ : f.2 = g.2 ≫ eqToHom (hfg₁ ▸ rfl)) :
    f = g := by
  apply Sigma.ext hfg₁
  rw [← conj_eqToHom_iff_heq _ _ rfl (hfg₁ ▸ rfl)]
  simp only [hfg₂, eqToHom_refl, id_comp]

lemma hom_ext_iff (g : a ⟶ b) : f = g ↔ ∃ (hfg : f.1 = g.1), f.2 = g.2 ≫ eqToHom (hfg ▸ rfl) where
  mp hfg := ⟨by rw [hfg], by simp [hfg]⟩
  mpr := fun ⟨hfg₁, hfg₂⟩ => hom_ext f g hfg₁ hfg₂

protected lemma id_comp : 𝟙 a ≫ f = f := by
  ext
  · simp
  · simp [F.mapComp_id_right_inv f.1.op.toLoc, ← (F.mapId ⟨op a.1⟩).inv.naturality_assoc f.2]

protected lemma comp_id : f ≫ 𝟙 b = f := by
  ext
  · simp
  simp [F.mapComp_id_left_inv, ← Cat.whiskerRight_app, ← Cat.comp_app]

end

protected lemma assoc {a b c d : ∫ F} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (f ≫ g) ≫ h = f ≫ g ≫ h := by
  ext
  · simp
  dsimp
  slice_lhs 3 5 =>
    rw [← (F.mapComp g.1.op.toLoc f.1.op.toLoc).inv.naturality_assoc h.2]
    -- lemmas should make this unecessary
    -- can make unecessary w/ better comp lemmas (where non whiskering is isolated)
    rw [← Cat.whiskerLeft_app, ← Cat.comp_app]
    rw [F.mapComp_assoc_right_inv h.1.op.toLoc g.1.op.toLoc f.1.op.toLoc]
  simp

/-- The category structure on `∫ F`. -/
instance category : Category (∫ F) where
  toCategoryStruct := Pseudofunctor.Grothendieck.categoryStruct
  id_comp := Pseudofunctor.Grothendieck.id_comp
  comp_id := Pseudofunctor.Grothendieck.comp_id
  assoc := Pseudofunctor.Grothendieck.assoc

/-- The projection `∫ F ⥤ 𝒮` given by projecting both objects and homs to the first
factor. -/
@[simps]
def forget (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}) : ∫ F ⥤ 𝒮 where
  obj := fun X => X.1
  map := fun f => f.1

section

-- TODO: different universe?
variable {G : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}}
  {H : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}}

/-- The Grothendieck construction is functorial: a strong natural transformation `α : F ⟶ G`
induces a functor `Grothendieck.map : ∫ F ⥤ ∫ G`.
-/
@[simps!]
def map (α : F ⟶ G) : ∫ F ⥤ ∫ G where
  obj a := {
    base := a.base
    fiber := (α.app ⟨op a.base⟩).obj a.fiber }
  -- TODO: give names to structure for `f`
  map {a b} f := {
    fst := f.1
    -- Now: f : a.fiber ⟶ (F.map f.1.op.toLoc).obj b.fiber
    -- thus image of f through α.app.map should be a morphism from
    -- α.app.obj a.fiber = obj (..).fiber to α.app.obj ((F.map f.1.op.toLoc).obj b.fiber)
    -- Thus, need to commute this last thing. This is done using α.naturality somehow
    -- this is PROBABLY correct...
    snd := (α.app ⟨op a.base⟩).map f.2 ≫ (α.naturality f.1.op.toLoc).hom.app b.fiber
  }
  map_id a := by
    ext
    · simp
    dsimp
    rw [comp_id]

    sorry -- this should follow from variation of naturality_id (after taking inverses)
  map_comp {a b c} f g := by
    ext
    · simp
    dsimp
    sorry -- something something naturality_comp

-- maybe some API here...!

theorem map_comp_forget (α : F ⟶ G) : map α ⋙ forget G = forget F := rfl

/-- The underlying homomorphism of `mapIdIso`. This is done so that `mapIdIso` compiles. -/
abbrev mapIdIso_hom : map (𝟙 F) ⟶ 𝟭 (∫ F) := { app := fun a ↦ eqToHom (by aesop_cat) }

-- TODO: give hom_ext higher precedence as an ext lemma?
abbrev mapIdIso_inv : 𝟭 (∫ F) ⟶ map (𝟙 F) := { app := fun a ↦ eqToHom (by aesop_cat) }

/-- TODO -/
-- TODO: explicit arg
def mapIdIso : map (𝟙 F) ≅ 𝟭 (∫ F) where
  hom := mapIdIso_hom
  inv := mapIdIso_inv
  hom_inv_id := by
    dsimp
    ext
    · simp
    simp [F.mapComp_id_left_inv, ← Cat.whiskerRight_app, ← Cat.comp_app]
  inv_hom_id := by
    dsimp
    ext
    · simp
    simp [F.mapComp_id_left_inv, ← Cat.whiskerRight_app, ← Cat.comp_app]

abbrev mapCompIso_hom (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) ⟶ map α ⋙ map β where
  app := fun a ↦ eqToHom (by aesop_cat)

abbrev mapCompIso_inv (α : F ⟶ G) (β : G ⟶ H) : map α ⋙ map β ⟶ map (α ≫ β) where
  app := fun a ↦ eqToHom (by aesop_cat)

def mapCompIso (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) ≅ map α ⋙ map β where
  hom := mapCompIso_hom α β
  inv := mapCompIso_inv α β
  hom_inv_id := by
    dsimp
    ext
    · simp
    simp [H.mapComp_id_left_inv, ← Cat.whiskerRight_app, ← Cat.comp_app]
  inv_hom_id := by
    dsimp
    ext
    · simp
    simp [H.mapComp_id_left_inv, ← Cat.whiskerRight_app, ← Cat.comp_app]

-- TODO: mapComp_eq and mapId_eq?


end

end Pseudofunctor.Grothendieck

end CategoryTheory
