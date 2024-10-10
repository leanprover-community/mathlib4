/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

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

/-- A morphism in the Grothendieck category `F : C ⥤ Cat` consists of
`base : X.base ⟶ Y.base` and `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`.
-/
structure Hom (X Y : ∫ F) where
  /-- The morphism between base objects. -/
  base : X.base ⟶ Y.base
  /-- The morphism in the fiber over the domain. -/
  fiber : X.fiber ⟶ (F.map base.op.toLoc).obj Y.fiber

@[simps!]
instance categoryStruct : CategoryStruct (∫ F) where
  Hom X Y := Hom X Y
  id X := {
    base := 𝟙 X.base
    fiber := (F.mapId ⟨op X.base⟩).inv.app X.fiber}
  comp {_ _ Z} f g := {
    base := f.base ≫ g.base
    fiber := f.fiber ≫ (F.map f.base.op.toLoc).map g.fiber ≫
      (F.mapComp g.base.op.toLoc f.base.op.toLoc).inv.app Z.fiber }

section

variable {a b : ∫ F}

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

lemma Hom.congr {a b : ∫ F} {f g : a ⟶ b} (h : f = g) :
    f.fiber = g.fiber ≫ eqToHom (h ▸ rfl) := by
  simp [h]

end

/-- The category structure on `∫ F`. -/
instance category : Category (∫ F) where
  toCategoryStruct := Pseudofunctor.Grothendieck.categoryStruct
  id_comp {a b} f := by
    ext
    · simp
    · simp [F.mapComp_id_right_inv_app, Strict.rightUnitor_eqToIso,
        ← (F.mapId ⟨op a.1⟩).inv.naturality_assoc f.fiber]
  comp_id {a b} f := by
    ext
    · simp
    · simp [F.mapComp_id_left_inv_app, ← Functor.map_comp_assoc, Strict.leftUnitor_eqToIso]
  assoc f g h := by
    ext
    · simp
    · dsimp
      slice_lhs 3 4 => rw [← (F.mapComp g.base.op.toLoc f.base.op.toLoc).inv.naturality h.fiber]
      simp [F.mapComp_assoc_right_inv_app, Strict.associator_eqToIso]


/-- The projection `∫ F ⥤ 𝒮` given by projecting both objects and homs to the first
factor. -/
@[simps]
def forget (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}) : ∫ F ⥤ 𝒮 where
  obj := fun X => X.base
  map := fun f => f.base

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
  map {a b} f := {
    base := f.1
    fiber := (α.app ⟨op a.base⟩).map f.2 ≫ (α.naturality f.1.op.toLoc).hom.app b.fiber }
  map_id a := by
    ext1
    · dsimp
    -- todo: app version
    simp [StrongPseudoNatTrans.naturality_id_hom_app, ← Functor.map_comp_assoc]
  map_comp {a b c} f g := by
    ext
    · dsimp
    dsimp
    rw [StrongPseudoNatTrans.naturality_comp_hom_app]
    simp only [map_comp, toOplax_toPrelaxFunctor, Cat.comp_obj, Strict.associator_eqToIso,
      eqToIso_refl, Iso.refl_hom, Cat.id_app, Iso.refl_inv, id_comp, assoc, comp_id]
    slice_lhs 2 4 => simp only [← Functor.map_comp, Iso.inv_hom_id_app, Cat.comp_obj, comp_id]
    slice_lhs 2 3 => rw [← Functor.comp_map, NatTrans.naturality]
    simp

-- maybe some API here...!

theorem map_comp_forget (α : F ⟶ G) : map α ⋙ forget G = forget F := rfl

/-- The underlying homomorphism of `m4apIdIso`. This is done so that `mapIdIso` compiles. -/
abbrev mapIdIso_hom : map (𝟙 F) ⟶ 𝟭 (∫ F) where
  app a := eqToHom (by aesop_cat)

abbrev mapIdIso_inv : 𝟭 (∫ F) ⟶ map (𝟙 F) where
  app a := eqToHom (by aesop_cat)

/-- TODO -/
-- TODO: explicit arg
def mapIdIso : map (𝟙 F) ≅ 𝟭 (∫ F) where
  hom := mapIdIso_hom
  inv := mapIdIso_inv
  hom_inv_id := by
    dsimp
    ext
    · simp
    simp [F.mapComp_id_left_inv_app, ← Functor.map_comp_assoc]
  inv_hom_id := by
    dsimp
    ext
    · simp
    simp [F.mapComp_id_left_inv_app, ← Functor.map_comp_assoc]

lemma map_id_eq : map (𝟙 F) = 𝟭 (∫ F) :=
  Functor.ext_of_iso (mapIdIso) (fun x ↦ by simp [map]) (fun x ↦ by simp [mapIdIso])

abbrev mapCompIso_hom (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) ⟶ map α ⋙ map β where
  app a := eqToHom (by aesop_cat)

abbrev mapCompIso_inv (α : F ⟶ G) (β : G ⟶ H) : map α ⋙ map β ⟶ map (α ≫ β) where
  app a := eqToHom (by aesop_cat)

def mapCompIso (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) ≅ map α ⋙ map β where
  hom := mapCompIso_hom α β
  inv := mapCompIso_inv α β
  hom_inv_id := by
    dsimp
    ext
    · simp
    simp [H.mapComp_id_left_inv_app, ← Functor.map_comp_assoc]
  inv_hom_id := by
    dsimp
    ext
    · simp
    simp [H.mapComp_id_left_inv_app, ← Functor.map_comp_assoc]

lemma map_comp_eq (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) = map α ⋙ map β := by
  apply Functor.ext_of_iso (mapCompIso α β)
  · intro x
    simp [mapCompIso]
  · intro x
    simp [map]

/-
TODO BEFORE PR:
1. refactor strong nat trans
3. PR ordinary grothendieck construction
-/


end

end Pseudofunctor.Grothendieck

end CategoryTheory
