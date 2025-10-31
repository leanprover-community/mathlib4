/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# The Grothendieck and CoGrothendieck constructions

## The Grothendieck construction

Given a category `𝒮` and any pseudofunctor `F` from `𝒮` to `Cat`, we associate to it a category
`∫ F`, defined as follows:
* Objects: pairs `(S, a)` where `S` is an object of the base category and `a` is an object of the
  category `F(S)`.
* Morphisms: morphisms `(R, b) ⟶ (S, a)` are defined as pairs `(f, h)` where `f : R ⟶ S` is a
  morphism in `𝒮` and `h : F(f)(a) ⟶ b`

The category `∫ F` is equipped with a projection functor `∫ F ⥤ 𝒮`,
given by projecting to the first factors, i.e.
* On objects, it sends `(S, a)` to `S`
* On morphisms, it sends `(f, h)` to `f`

## The CoGrothendieck construction

Given a category `𝒮` and any pseudofunctor `F` from `𝒮ᵒᵖ` to `Cat`, we associate to it a category
`∫ᶜ F` (TODO: promote `CategoryStruct` to `Category` instance), defined as follows:
* Objects: pairs `(S, a)` where `S` is an object of the base category and `a` is an object of the
  category `F(S)`.
* Morphisms: morphisms `(R, b) ⟶ (S, a)` are defined as pairs `(f, h)` where `f : R ⟶ S` is a
  morphism in `𝒮` and `h : b ⟶ F(f)(a)`

The category `∫ᶜ F` is equipped with a functor `∫ᶜ F ⥤ 𝒮` (TODO: define this functor),
given by projecting to the first factors, i.e.
* On objects, it sends `(S, a)` to `S`
* On morphisms, it sends `(f, h)` to `f`

## Naming conventions

The name `Grothendieck` is reserved for the construction on covariant pseudofunctors from `𝒮` to
`Cat`, whereas the word `CoGrothendieck` is used for the contravariant construction.
This is consistent with the convention for the Grothendieck construction on 1-functors
`CategoryTheory.Grothendieck`.

## Future work / TODO

1. Once the bicategory of pseudofunctors has been defined, show that this construction forms a
pseudofunctor from `Pseudofunctor (LocallyDiscrete 𝒮) Catᵒᵖ` to `Cat`.
2. Deduce the results in `CategoryTheory.Grothendieck` as a specialization of
   `Pseudofunctor.Grothendieck`.
3. Dualize all `CoGrothendieck` results to `Grothendieck`.

## References
[Vistoli2008] "Notes on Grothendieck Topologies, Fibered Categories and Descent Theory" by
Angelo Vistoli

-/

namespace CategoryTheory.Pseudofunctor

universe w v₁ v₂ v₃ u₁ u₂ u₃

open Functor Category Opposite Discrete Bicategory StrongTrans

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

/-- The type of objects in the fibered category associated to a pseudofunctor from a
1-category to Cat. -/
@[ext]
structure Grothendieck (F : Pseudofunctor (LocallyDiscrete 𝒮) Cat.{v₂, u₂}) where
  /-- The underlying object in the base category. -/
  base : 𝒮
  /-- The object in the fiber of the base object. -/
  fiber : F.obj ⟨base⟩

namespace Grothendieck

variable {F : Pseudofunctor (LocallyDiscrete 𝒮) Cat.{v₂, u₂}}

/-- Notation for the Grothendieck category associated to a pseudofunctor `F`. -/
scoped prefix:75 "∫ " => Grothendieck

/-- A morphism in the Grothendieck construction `∫ F` between two points `X Y : ∫ F` consists of
a morphism in the base category `base : X.base ⟶ Y.base` and
a morphism in a fiber `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`. -/
structure Hom (X Y : ∫ F) where
  /-- The morphism between base objects. -/
  base : X.base ⟶ Y.base
  /-- The morphism in the fiber over the domain. -/
  fiber : (F.map base.toLoc).obj X.fiber ⟶ Y.fiber

@[simps! id_base id_fiber comp_base comp_fiber]
instance categoryStruct : CategoryStruct (∫ F) where
  Hom X Y := Hom X Y
  id X := {
    base := 𝟙 X.base
    fiber := (F.mapId ⟨X.base⟩).hom.app X.fiber }
  comp {X _ _} f g := {
    base := f.base ≫ g.base
    fiber := (F.mapComp f.base.toLoc g.base.toLoc).hom.app X.fiber ≫
      (F.map g.base.toLoc).map f.fiber ≫ g.fiber }

instance (X : ∫ F) : Inhabited (Hom X X) :=
  ⟨𝟙 X⟩

end Grothendieck

/-- The type of objects in the fibered category associated to a contravariant
pseudofunctor from a 1-category to Cat. -/
@[ext]
structure CoGrothendieck (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}) where
  /-- The underlying object in the base category. -/
  base : 𝒮
  /-- The object in the fiber of the base object. -/
  fiber : F.obj ⟨op base⟩

namespace CoGrothendieck

variable {F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}}

/-- Notation for the CoGrothendieck category associated to a pseudofunctor `F`. -/
scoped prefix:75 "∫ᶜ " => CoGrothendieck

/-- A morphism in the CoGrothendieck construction `∫ᶜ F` between two points `X Y : ∫ᶜ F` consists of
a morphism in the base category `base : X.base ⟶ Y.base` and
a morphism in a fiber `f.fiber : X.fiber ⟶ (F.map base.op.toLoc).obj Y.fiber`. -/
structure Hom (X Y : ∫ᶜ F) where
  /-- The morphism between base objects. -/
  base : X.base ⟶ Y.base
  /-- The morphism in the fiber over the domain. -/
  fiber : X.fiber ⟶ (F.map base.op.toLoc).obj Y.fiber

@[simps! id_base id_fiber comp_base comp_fiber]
instance categoryStruct : CategoryStruct (∫ᶜ F) where
  Hom X Y := Hom X Y
  id X := {
    base := 𝟙 X.base
    fiber := (F.mapId ⟨op X.base⟩).inv.app X.fiber }
  comp {_ _ Z} f g := {
    base := f.base ≫ g.base
    fiber := f.fiber ≫ (F.map f.base.op.toLoc).map g.fiber ≫
      (F.mapComp g.base.op.toLoc f.base.op.toLoc).inv.app Z.fiber }

section

variable {a b : ∫ᶜ F}

@[ext (iff := false)]
lemma Hom.ext (f g : a ⟶ b) (hfg₁ : f.base = g.base)
    (hfg₂ : f.fiber = g.fiber ≫ eqToHom (hfg₁ ▸ rfl)) : f = g := by
  cases f; cases g
  congr
  dsimp at hfg₁
  rw [← conj_eqToHom_iff_heq _ _ rfl (hfg₁ ▸ rfl)]
  simpa only [eqToHom_refl, id_comp] using hfg₂

lemma Hom.ext_iff (f g : a ⟶ b) :
    f = g ↔ ∃ (hfg : f.base = g.base), f.fiber = g.fiber ≫ eqToHom (hfg ▸ rfl) where
  mp hfg := ⟨by rw [hfg], by simp [hfg]⟩
  mpr := fun ⟨hfg₁, hfg₂⟩ => Hom.ext f g hfg₁ hfg₂

lemma Hom.congr {a b : ∫ᶜ F} {f g : a ⟶ b} (h : f = g) :
    f.fiber = g.fiber ≫ eqToHom (h ▸ rfl) := by
  simp [h]

end

attribute [local simp] PrelaxFunctor.map₂_eqToHom in
/-- The category structure on `∫ᶜ F`. -/
instance category : Category (∫ᶜ F) where
  toCategoryStruct := Pseudofunctor.CoGrothendieck.categoryStruct
  id_comp {a b} f := by
    ext
    · simp
    · simp [F.mapComp_id_right_inv_app, Strict.rightUnitor_eqToIso, ← NatTrans.naturality_assoc]
  comp_id {a b} f := by
    ext
    · simp
    · simp [F.mapComp_id_left_inv_app, ← Functor.map_comp_assoc, Strict.leftUnitor_eqToIso]
  assoc f g h := by
    ext
    · simp
    · simp [← NatTrans.naturality_assoc, F.mapComp_assoc_right_inv_app, Strict.associator_eqToIso]

variable (F)

/-- The projection `∫ᶜ F ⥤ 𝒮` given by projecting both objects and homs to the first
factor. -/
@[simps]
def forget (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}) : ∫ᶜ F ⥤ 𝒮 where
  obj X := X.base
  map f := f.base

section

attribute [local simp]
  Strict.leftUnitor_eqToIso Strict.rightUnitor_eqToIso Strict.associator_eqToIso

variable {F} {G : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}}
  {H : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}}

/-- The CoGrothendieck construction is functorial: a strong natural transformation `α : F ⟶ G`
induces a functor `CoGrothendieck.map : ∫ᶜ F ⥤ ∫ᶜ G`. -/
@[simps!]
def map (α : F ⟶ G) : ∫ᶜ F ⥤ ∫ᶜ G where
  obj a := {
    base := a.base
    fiber := (α.app ⟨op a.base⟩).obj a.fiber }
  map {a b} f := {
    base := f.1
    fiber := (α.app ⟨op a.base⟩).map f.2 ≫ (α.naturality f.1.op.toLoc).hom.app b.fiber }
  map_id a := by
    ext1
    · dsimp
    · simp [StrongTrans.naturality_id_hom_app, ← Functor.map_comp_assoc]
  map_comp {a b c} f g := by
    ext
    · dsimp
    · dsimp
      simp only [StrongTrans.naturality_comp_hom_app, map_comp, assoc, comp_id]
      slice_lhs 2 4 => simp only [← Functor.map_comp, Iso.inv_hom_id_app, Cat.comp_obj, comp_id]
      simp [← Functor.comp_map]

@[simp]
lemma map_id_map {x y : ∫ᶜ F} (f : x ⟶ y) : (map (𝟙 F)).map f = f := by
  ext <;> simp

@[simp]
theorem map_comp_forget (α : F ⟶ G) : map α ⋙ forget G = forget F := rfl

section

variable (F)

/-- The natural isomorphism witnessing the pseudo-unity constraint of `CoGrothendieck.map`. -/
def mapIdIso : map (𝟙 F) ≅ 𝟭 (∫ᶜ F) :=
  NatIso.ofComponents (fun _ ↦ eqToIso (by cat_disch))

lemma map_id_eq : map (𝟙 F) = 𝟭 (∫ᶜ F) :=
  Functor.ext_of_iso (mapIdIso F) (fun x ↦ by simp [map]) (fun x ↦ by simp [mapIdIso])

end

/-- The natural isomorphism witnessing the pseudo-functoriality of `CoGrothendieck.map`. -/
def mapCompIso (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) ≅ map α ⋙ map β :=
  NatIso.ofComponents (fun _ ↦ eqToIso (by cat_disch)) (fun f ↦ by
    dsimp
    simp only [comp_id, id_comp]
    ext <;> simp)

lemma map_comp_eq (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) = map α ⋙ map β :=
  Functor.ext_of_iso (mapCompIso α β) (fun _ ↦ by simp [map]) (fun _ ↦ by simp [mapCompIso])

end

end Pseudofunctor.CoGrothendieck

end CategoryTheory
