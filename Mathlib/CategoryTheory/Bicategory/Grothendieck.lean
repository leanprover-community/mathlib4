/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.FiberedCategory.Fibered

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

instance isPreFibered : IsPreFibered (forget F) := by
  constructor; intro a b f
  use ⟨b, (F.map f.op.toLoc).obj a.fiber⟩, ⟨f, 𝟙 _⟩
  refine {universal_property := ?_, cond := ?_}
  · apply IsHomLiftAux.map (p := forget F) (a := ⟨b, (F.map f.op.toLoc).obj a.fiber⟩)
      ⟨ f, 𝟙 ((F.map f.op.toLoc).obj a.fiber) ⟩
  · intro a' g hfg
    let eq := IsHomLift.domain_eq (forget F) f g
    refine ⟨⟨eqToHom <| eq, g.fiber ≫ ?_⟩, ?_⟩
    · have : g.base = eqToHom eq ≫ f := by simpa using IsHomLift.fac' (forget F) f g
      exact ((eqToIso (congrArg (fun u ↦ F.map u.op.toLoc) this)).app a.fiber).hom ≫
       ((F.mapComp f.op.toLoc _).app _).hom
    · simp; constructor
      · constructor
        · apply IsHomLift.of_fac' <;> simpa using eq
        · apply Hom.ext <;> simpa using (IsHomLift.fac' (forget F) f g).symm
      · rintro H K rfl
        apply Hom.ext
        · simp only [categoryStruct_comp_base, op_comp, Quiver.Hom.comp_toLoc,
          categoryStruct_comp_fiber, forget_obj, forget_map, eqToHom_refl, id_eq, eq_mpr_eq_cast,
          map_id, id_comp, assoc]
          conv_lhs => rw [← Category.comp_id H.fiber]
          congr!
          have : H.base.op.toLoc = (eqToHom eq).op.toLoc := by
            congr!
            simpa using IsHomLift.fac' (forget F) (𝟙 b) H
          simp [F.mapComp_congr rfl this]
        · simpa using IsHomLift.fac' (forget F) (𝟙 b) H

end Pseudofunctor.Grothendieck

end CategoryTheory
