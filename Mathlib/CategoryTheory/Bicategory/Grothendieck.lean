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

variable {a : ∫ F} {b : 𝒮} (f : b ⟶ (forget F).obj a)

/-- The domain of the cartesian lift of `f`. -/
@[simps]
def domainCartesianLift : ∫ F :=
  ⟨b, (F.map f.op.toLoc).obj a.fiber⟩

/-- The cartesian lift of `f`. -/
@[simps]
def cartesianLift : domainCartesianLift F f ⟶ a :=
  ⟨f, 𝟙 _⟩

lemma isHomLift_cartesianLift :
    IsHomLift (forget F) f (cartesianLift F f) :=
  ⟨IsHomLiftAux.map (p := forget F) (a := domainCartesianLift F f) ⟨f, 𝟙 _⟩⟩

/-- Given some lift `g` of `f`, the canonical map from the domain of `g` to the domain of
the cartesian lift of `f`. -/
def homCartesianLift {a' : ∫ F} (g : a' ⟶ a) [(forget F).IsHomLift f g] :
    a' ⟶ domainCartesianLift F f where
  base := eqToHom <| IsHomLift.domain_eq (forget F) f g
  fiber :=
    have : g.base = eqToHom _ ≫ f := by simpa using IsHomLift.fac' (forget F) f g
    g.fiber ≫ ((eqToIso (congrArg (fun u ↦ F.map u.op.toLoc) this)).app a.fiber).hom ≫
      ((F.mapComp f.op.toLoc _).app _).hom

lemma isHomLift_homCartesianLift {a' : ∫ F} (g : a' ⟶ a) [(forget F).IsHomLift f g] :
    (forget F).IsHomLift (𝟙 b) (homCartesianLift F f g) := by
  apply IsHomLift.of_fac'
  · simp; rfl
  · apply IsHomLift.domain_eq (forget F) f g
  · rfl

/-- The preFibered structure on `∫ F`, using the forgetful functor `forget F`. -/
instance isPreFibered : IsPreFibered (forget F) := by
  refine ⟨fun {a b} f ↦ ⟨domainCartesianLift F f, cartesianLift F f, ?_⟩⟩
  refine {cond := (isHomLift_cartesianLift F f).cond, universal_property := ?_}
  intro a' g hfg
  refine ⟨homCartesianLift F f g, ?_⟩
  simp only [categoryStruct_Hom, and_imp, homCartesianLift, cartesianLift]
  refine ⟨⟨isHomLift_homCartesianLift _ _ _, ?_⟩, ?_⟩
  · exact Hom.ext _ _ (by simpa using (IsHomLift.fac' (forget F) f g).symm) (by simp)
  · rintro H K rfl
    apply Hom.ext
    · have := by simpa using IsHomLift.fac' (forget F) (𝟙 b) H
      simp [F.mapComp_congr rfl (congrArg (fun u ↦ u.op.toLoc) this)]
    · simpa using IsHomLift.fac' (forget F) (𝟙 b) H

end Pseudofunctor.Grothendieck

end CategoryTheory
