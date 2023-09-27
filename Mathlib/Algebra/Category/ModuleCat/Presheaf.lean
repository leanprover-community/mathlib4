/-
Copyright (c) 2023 Scott Morrison All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.Ring.Basic

/-!
# Presheaves of modules over a presheaf of rings.

We give a hands-on description of a presheaf of modules over a fixed presheaf of rings,
as a presheaf of abelian groups with additional data.

## Future work

* Compare this to the definition as a presheaf of pairs `(R, M)` with specified first part.
* Compare this to the definition as a module object of the presheaf of rings
  thought of as a monoid object.
* (Pre)sheaves of modules over a given sheaf of rings are an abelian category.
* Presheaves of modules over a presheaf of commutative rings form a monoidal category.
* Pushforward and pullback.
-/

universe v₁ u₁ u

open CategoryTheory LinearMap Opposite

variable {C : Type u₁} [Category.{v₁} C]

set_option autoImplicit true in
/-- A presheaf of modules over a given presheaf of rings,
described as a presheaf of abelian groups, and the extra data of the action at each object,
and a condition relating functoriality and scalar multiplication. -/
structure PresheafOfModules (R : Cᵒᵖ ⥤ RingCat.{u}) where
  presheaf : Cᵒᵖ ⥤ AddCommGroupCat.{v}
  module : ∀ X : Cᵒᵖ, Module (R.obj X) (presheaf.obj X)
  map_smul : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : R.obj X) (x : presheaf.obj X),
    presheaf.map f (r • x) = R.map f r • presheaf.map f x

namespace PresheafOfModules

variable {R : Cᵒᵖ ⥤ RingCat.{u}}

attribute [instance] PresheafOfModules.module

/-- The bundled module over an object `X`. -/
def obj (P : PresheafOfModules R) (X : Cᵒᵖ) : ModuleCat (R.obj X) :=
  ModuleCat.of _ (P.presheaf.obj X)

/--
If `P` is a presheaf of modules over a presheaf of rings `R`, both over some category `C`,
and `f : X ⟶ Y` is a morphism in `Cᵒᵖ`, we construct the `R.map f`-semilinear map
from the `R.obj X`-module `P.presheaf.obj X` to the `R.obj Y`-module `P.presheaf.obj Y`.
 -/
def map (P : PresheafOfModules R) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    P.obj X →ₛₗ[R.map f] P.obj Y :=
  { toAddHom := (P.presheaf.map f).toAddHom,
    map_smul' := P.map_smul f, }

@[simp]
theorem map_apply (P : PresheafOfModules R) {X Y : Cᵒᵖ} (f : X ⟶ Y) (x) :
    P.map f x = (P.presheaf.map f) x :=
  rfl

instance (X : Cᵒᵖ) : RingHomId (R.map (𝟙 X)) where
  eq_id := R.map_id X

instance {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    RingHomCompTriple (R.map f) (R.map g) (R.map (f ≫ g)) where
  comp_eq := (R.map_comp f g).symm

@[simp]
theorem map_id (P : PresheafOfModules R) (X : Cᵒᵖ) :
    P.map (𝟙 X) = LinearMap.id' := by
  ext
  simp

@[simp]
theorem map_comp (P : PresheafOfModules R) {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    P.map (f ≫ g) = (P.map g).comp (P.map f) := by
  ext
  simp

/-- A morphism of presheaves of modules. -/
structure Hom (P Q : PresheafOfModules R) where
  hom : P.presheaf ⟶ Q.presheaf
  map_smul : ∀ (X : Cᵒᵖ) (r : R.obj X) (x : P.presheaf.obj X), hom.app X (r • x) = r • hom.app X x

namespace Hom

/-- The identity morphism on a presheaf of modules. -/
def id (P : PresheafOfModules R) : Hom P P where
  hom := 𝟙 _
  map_smul _ _ _ := rfl

/-- Composition of morphisms of presheaves of modules. -/
def comp {P Q R : PresheafOfModules R} (f : Hom P Q) (g : Hom Q R) : Hom P R where
  hom := f.hom ≫ g.hom
  map_smul _ _ _ := by simp [Hom.map_smul]

end Hom

instance : Category (PresheafOfModules R) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g

namespace Hom

variable {P Q T : PresheafOfModules R}

/--
The `(X : Cᵒᵖ)`-component of morphism between presheaves of modules
over a presheaf of rings `R`, as an `R.obj X`-linear map. -/
def app (f : Hom P Q) (X : Cᵒᵖ) : P.obj X →ₗ[R.obj X] Q.obj X :=
  { toAddHom := (f.hom.app X).toAddHom
    map_smul' := f.map_smul X }

@[simp]
lemma comp_app (f : P ⟶ Q) (g : Q ⟶ T) (X : Cᵒᵖ) :
    (f ≫ g).app X = (g.app X).comp (f.app X) := rfl

@[ext]
theorem ext {f g : P ⟶ Q} (w : ∀ X, f.app X = g.app X) : f = g := by
  cases f; cases g;
  congr
  ext X x
  exact LinearMap.congr_fun (w X) x

instance : Zero (P ⟶ Q) := ⟨mk 0 (by
  intros
  simp only [Limits.zero_app, AddMonoidHom.zero_apply, smul_zero])⟩

variable (P Q)

@[simp]
lemma zero_app (X : Cᵒᵖ) : (0 : P ⟶ Q).app X = 0 := rfl

variable {P Q}

instance : Add (P ⟶ Q) := ⟨fun f g => mk (f.hom + g.hom) (by
  intros
  simp only [NatTrans.app_add, AddCommGroupCat.hom_add_apply, map_smul, smul_add])⟩

@[simp]
lemma add_app (f g : P ⟶ Q) (X : Cᵒᵖ) : (f + g).app X = f.app X + g.app X := rfl

instance : Sub (P ⟶ Q) := ⟨fun f g => mk (f.hom - g.hom) (by
  intros
  rw [NatTrans.app_sub, AddMonoidHom.sub_apply, AddMonoidHom.sub_apply,
    smul_sub, map_smul, map_smul])⟩

@[simp]
lemma sub_app (f g : P ⟶ Q) (X : Cᵒᵖ) : (f - g).app X = f.app X - g.app X := rfl

instance : Neg (P ⟶ Q) := ⟨fun f => mk (-f.hom) (by
  intros
  rw [NatTrans.app_neg, AddMonoidHom.neg_apply, AddMonoidHom.neg_apply,
    map_smul, smul_neg])⟩

@[simp]
lemma neg_app (f : P ⟶ Q) (X : Cᵒᵖ): (-f).app X = -f.app X := rfl

instance : AddCommGroup (P ⟶ Q) where
  add_assoc := by intros; ext1; simp only [add_app, add_assoc]
  zero_add := by intros; ext1; simp only [add_app, zero_app, zero_add]
  add_left_neg := by intros; ext1; simp only [add_app, neg_app, add_left_neg, zero_app]
  add_zero := by intros; ext1; simp only [add_app, zero_app, add_zero]
  add_comm := by intros; ext1; simp only [add_app]; apply add_comm
  sub_eq_add_neg := by intros; ext1; simp only [add_app, sub_app, neg_app, sub_eq_add_neg]

instance : Preadditive (PresheafOfModules R) where
  add_comp := by intros; ext1; simp only [comp_app, add_app, comp_add]
  comp_add := by intros; ext1; simp only [comp_app, add_app, add_comp]

end Hom

variable (R)

/-- The functor from presheaves of modules over a specified presheaf of rings,
to presheaves of abelian groups.
-/
@[simps obj]
def toPresheaf : PresheafOfModules R ⥤ (Cᵒᵖ ⥤ AddCommGroupCat) where
  obj P := P.presheaf
  map f := f.hom

variable {R}

@[simp]
lemma toPresheaf_map_app {P Q : PresheafOfModules R}
    (f : P ⟶ Q) (X : Cᵒᵖ) :
    ((toPresheaf R).map f).app X = (f.app X).toAddMonoidHom := rfl

instance : (toPresheaf R).Additive where

instance : Faithful (toPresheaf R) where
  map_injective {P Q} f g h := by
    ext X x
    have eq := congr_app h X
    simp only [toPresheaf_obj, toPresheaf_map_app] at eq
    simp only [← toAddMonoidHom_coe, eq]

end PresheafOfModules
