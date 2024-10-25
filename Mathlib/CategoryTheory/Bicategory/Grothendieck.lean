/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
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
    fiber := (F.mapId ⟨op X.base⟩).inv.app X.fiber }
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

/-- The projection `∫ F ⥤ 𝒮` given by projecting both objects and homs to the first
factor. -/
@[simps]
def forget : ∫ F ⥤ 𝒮 where
  obj X := X.base
  map f := f.base

variable {F}
variable {G : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}}
variable (α : F ⟶ G)

/-- A (strong oplax) natural transformation of pseudofunctor induces a functor between the
Grothendieck constructions. -/
@[simps]
def map (α : F ⟶ G) : ∫ F ⥤ ∫ G where
  obj X :=
  { base := X.base
    fiber := (α.app ⟨op X.base⟩).obj X.fiber }
  map {X Y} f :=
  { base := f.base
    fiber := (α.app ⟨op X.base⟩).map f.fiber ≫ (α.naturality f.base.op.toLoc).hom.app Y.fiber }
  map_id X := by
    ext
    · simp
    · simp only [toOplax_toPrelaxFunctor, categoryStruct_Hom, categoryStruct_id_base, op_id,
        Quiver.Hom.id_toLoc, categoryStruct_id_fiber, eqToHom_refl, comp_id]
      rw [← NatIso.app_inv, ← Functor.mapIso_inv, Iso.inv_comp_eq]
      symm
      rw [← NatIso.app_inv, Iso.comp_inv_eq]
      simp only [mapIso_hom, Iso.app_hom]
      haveI := congr_arg (·.app X.fiber) (α.naturality_id ⟨op X.base⟩)
      simp only [toOplax_toPrelaxFunctor, Cat.comp_obj, Cat.id_obj, toOplax_mapId, Cat.comp_app,
        Cat.whiskerLeft_app, Cat.whiskerRight_app, NatTrans.naturality_assoc, NatTrans.naturality,
        Cat.comp_map, Cat.id_map] at this
      rw [this]
      simp [F.mapComp_id_right_inv_app, ← Functor.map_comp_assoc, Strict.leftUnitor_eqToIso,
        Strict.rightUnitor_eqToIso]
  map_comp {X Y Z} f g := by
    ext
    · simp
    · simp only [toOplax_toPrelaxFunctor, categoryStruct_Hom, categoryStruct_comp_base, op_comp,
        Quiver.Hom.comp_toLoc, categoryStruct_comp_fiber, map_comp, assoc, eqToHom_refl, comp_id]
      congr 1
      haveI := congr_arg (·.app Z.fiber) (α.naturality_comp g.base.op.toLoc f.base.op.toLoc)
      simp only [toOplax_toPrelaxFunctor, Cat.comp_obj, toOplax_mapComp, Cat.comp_app,
        Cat.whiskerLeft_app, Cat.whiskerRight_app] at this
      conv_rhs => rw [← NatIso.app_inv]
      symm
      slice_lhs 1 3 => rfl
      rw [Iso.comp_inv_eq]
      simp only [Iso.app_hom, assoc]
      rw [this]
      simp only [Strict.associator_eqToIso, eqToIso_refl, Iso.refl_hom, Cat.id_app, Cat.comp_obj,
        Iso.refl_inv, comp_id, id_comp]
      simp only [Category.assoc, ← Functor.map_comp, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
        Cat.comp_obj, comp_id]
      haveI := (α.naturality f.base.op.toLoc).hom.naturality g.fiber
      simp only [toOplax_toPrelaxFunctor, Cat.comp_obj, Cat.comp_map] at this
      rw [reassoc_of%(this)]
      simp

variable {α}

@[simp]
lemma map_obj (X : ∫ F) : (map α).obj X = ⟨X.base, (α.app ⟨op X.base⟩).obj X.fiber⟩ := rfl

@[simp]
lemma map_map (X Y : ∫ F) (f : X ⟶ Y) : (map α).map f =
    ⟨f.base, (α.app ⟨op X.base⟩).map f.fiber ≫ (α.naturality f.base.op.toLoc).hom.app Y.fiber⟩ :=
  rfl

/-- The functor `Pseudofunctor.Grothendieck.map α` lies over `C` -/
lemma map_comp_forget (α : F ⟶ G) :
    map α ⋙ forget G = forget F := rfl

/-- Making the equality of functors into an isomorphism. Note: we should avoid equality of functors
if possible, and we should prefer `mapCompIso` to `map_comp_eq` whenever we can. -/
def mapCompForgetIso (α : F ⟶ G) :
    map α ⋙ forget G ≅ forget F := Iso.refl _

/-- The natural transformation induced by the identity is the identity. -/
theorem map_id_eq : map (𝟙 F) = 𝟭 (∫ F) := by
  fapply Functor.ext
  · intro X; rfl
  · intro X Y f
    ext
    · simp
    · dsimp
      simp [F.mapComp_id_left_inv, F.mapComp_id_right_inv, Strict.leftUnitor_eqToIso,
        Strict.rightUnitor_eqToIso]
      simp only [← Functor.map_comp_assoc, ← NatTrans.naturality_assoc]
      simp only [Cat.id_obj, Cat.id_map, id_comp, eqToHom_naturality_assoc, Iso.inv_hom_id_app,
        comp_id, assoc]
      slice_rhs 3 5 => equals (F.map _).map ((F.mapId _).hom.app _) =>
        symm
        rw [conj_eqToHom_iff_heq']
        congr
        simp
      rw [← NatIso.app_inv, ← Functor.map_comp]
      simp

/-- Making the equality of functors into an isomorphism. Note: we should avoid equality of functors
if possible, and we should prefer `mapCompIso` to `map_comp_eq` whenever we can. -/
def mapIdIso : map (𝟙 F) ≅ 𝟭 (∫ F) := eqToIso map_id_eq

variable (α)

variable {H : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}}
set_option maxHeartbeats 225000 in -- We need this for the second-to last simp to work.
/-- The construction `map` strictly commutes with functor composition. -/
theorem map_comp_eq (β : G ⟶ H) : map (α ≫ β) = map α ⋙ map β := by
  fapply Functor.ext
  · intro x
    rfl
  · intro X Y f
    ext
    · simp
    · dsimp
      simp only [Strict.associator_eqToIso, eqToIso_refl, Iso.refl_inv, Cat.id_app, Cat.comp_obj,
        Iso.refl_hom, comp_id, id_comp, map_comp, assoc, H.mapComp_id_left_inv,
        Strict.leftUnitor_eqToIso, eqToIso.inv, PrelaxFunctor.map₂_eqToHom, eqToHom_naturality,
        Cat.comp_app, Cat.eqToHom_app, Cat.whiskerRight_app, Cat.id_obj, H.mapComp_id_right_inv,
        Strict.rightUnitor_eqToIso, Cat.whiskerLeft_app, eqToHom_trans_assoc]
      rw [eqToHom_map]
      slice_rhs 6 8 => equals (H.map (𝟙 ⟨op X.base⟩)).map <| (H.map f.base.op.toLoc).map <|
        (H.mapId ⟨op Y.base⟩).hom.app _ =>
        symm
        rw [conj_eqToHom_iff_heq']
        congr 1 <;> simp only [Cat.id_obj, id_comp]
        congr
        simp
      simp only [← Cat.whiskerLeft_app, ← Cat.whiskerRight_app, ← Cat.whiskerLeft_app,
        ← NatTrans.comp_app_assoc, ← NatTrans.comp_app, ← Functor.comp_map]
      slice_rhs 1 2 => erw [← NatTrans.naturality]
      simp only [← Cat.whiskerLeft_app, ← Cat.whiskerRight_app, ← Cat.whiskerLeft_app,
        ← NatTrans.comp_app_assoc, ← NatTrans.comp_app, ← Functor.comp_map]
      simp only [Functor.comp_map, toOplax_toPrelaxFunctor, NatTrans.comp_app, Cat.comp_obj,
        Cat.whiskerRight_app, Cat.whiskerLeft_app, Cat.id_obj, Cat.comp_map, Cat.id_map,
        whisker_assoc, Strict.associator_eqToIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv, id_comp,
        Bicategory.whiskerLeft_comp, assoc, comp_whiskerRight, Cat.id_app, map_id,
        NatTrans.naturality, NatTrans.naturality_assoc, Iso.inv_hom_id_app_assoc]
      congr
      rw [← NatIso.app_inv, ← Functor.map_comp]
      simp

/-- Making the equality of functors into an isomorphism. Note: we should avoid equality of functors
if possible, and we should prefer `mapCompIso` to `map_comp_eq` whenever we can. -/
def mapCompIso (β : G ⟶ H) : map (α ≫ β) ≅ map α ⋙ map β := eqToIso (map_comp_eq α β)

end Pseudofunctor.Grothendieck

end CategoryTheory
