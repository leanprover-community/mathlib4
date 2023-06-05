/-
Copyright (c) 2023 Scott Morrison All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.Ring.Basic

open CategoryTheory

-- TODO: move these definitions to the linear algebra library.
-- They belong in `Mathlib.Algebra.Ring.CompTypeclasses`.

class RingHomId {R : Type _} [Semiring R] (σ : R →+* R) : Prop where
  eq_id : σ = RingHom.id R

instance {R : Type _} [Semiring R] : RingHomId (RingHom.id R) where
  eq_id := rfl

/-- A generalisation of `LinearMap.id` that constructs the identity function
as a `σ`-semilinear map for any ring homomorphism `σ` which we know is the identity. -/
@[simps]
def LinearMap.id' {R : Type _} [Semiring R]
    {M : Type _} [AddCommMonoid M] [Module R M]
    {σ : R →+* R} [RingHomId σ] : M →ₛₗ[σ] M where
  toFun x := x
  map_add' x y := rfl
  map_smul' r x := by
    have := (RingHomId.eq_id : σ = _)
    subst this
    rfl

open LinearMap

open Opposite

variable {C : Type u₁} [Category.{v₁} C] {R : Type u₂} [Category.{v₂} R]

/-- A presheaf of modules over a given presheaf of rings,
described as a presheaf of abelian groups, and the extra data of the action at each object,
and a condition relating functoriality and scalar multiplication. -/
structure PresheafOfModules (F : Cᵒᵖ ⥤ RingCat.{u}) where
  presheaf : Cᵒᵖ ⥤ AddCommGroupCat.{v}
  module : ∀ X : Cᵒᵖ, Module (F.obj X) (presheaf.obj X)
  map_smul : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : F.obj X) (x : presheaf.obj X),
    presheaf.map f (r • x) = F.map f r • presheaf.map f x

namespace PresheafOfModules

variable {F : Cᵒᵖ ⥤ RingCat.{u}}

attribute [instance] PresheafOfModules.module

/-- The bundled module over an object `X`. -/
def obj (P : PresheafOfModules F) (X : Cᵒᵖ) : ModuleCat (F.obj X) :=
  ModuleCat.of _ (P.presheaf.obj X)

/--
If `P` is a presheaf of modules over a presheaf of rings `F`, both over some category `C`,
and `f : X ⟶ Y` is a morphism in `Cᵒᵖ`, we construct the `F.map f`-semilinear map
from the `F.obj X`-module `P.presheaf.obj X` to the `F.obj Y`-module `P.presheaf.obj Y`.
 -/
def map (P : PresheafOfModules F) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    P.obj X →ₛₗ[F.map f] P.obj Y :=
  { toAddHom := (P.presheaf.map f).toAddHom,
    map_smul' := P.map_smul f, }

@[simp]
theorem map_apply (P : PresheafOfModules F) {X Y : Cᵒᵖ} (f : X ⟶ Y) (x) :
    P.map f x = (P.presheaf.map f) x :=
  rfl

instance (X : Cᵒᵖ) : RingHomId (F.map (𝟙 X)) where
  eq_id := F.map_id X

instance {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    RingHomCompTriple (F.map f) (F.map g) (F.map (f ≫ g)) where
  comp_eq := (F.map_comp f g).symm

@[simp]
theorem map_id (P : PresheafOfModules F) (X : Cᵒᵖ) :
    P.map (𝟙 X) = LinearMap.id' := by
  ext
  simp

@[simp]
theorem map_comp (P : PresheafOfModules F) {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    P.map (f ≫ g) = (P.map g).comp (P.map f) := by
  ext
  simp

/-- A morphism of presheaves of modules. -/
structure Hom (P Q : PresheafOfModules F) where
  hom : P.presheaf ⟶ Q.presheaf
  map_smul : ∀ (X : Cᵒᵖ) (r : F.obj X) (x : P.presheaf.obj X), hom.app X (r • x) = r • hom.app X x

namespace Hom

/-- The identity morphism on a presheaf of modules. -/
def id (P : PresheafOfModules F) : Hom P P where
  hom := 𝟙 _
  map_smul _ _ _ := rfl

/-- Composition of morphisms of presheaves of modules. -/
def comp {P Q R : PresheafOfModules F} (f : Hom P Q) (g : Hom Q R) : Hom P R where
  hom := f.hom ≫ g.hom
  map_smul _ _ _ := by simp [Hom.map_smul]

end Hom

instance : Category (PresheafOfModules F) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g

variable {P Q : PresheafOfModules F}

/--
The `(X : Cᵒᵖ)`-component of morphism between presheaves of modules
over a presheaf of rings `F`, as an `F.obj X`-linear map. -/
def Hom.app (f : Hom P Q) (X : Cᵒᵖ) : P.obj X →ₗ[F.obj X] Q.obj X :=
  { toAddHom := (f.hom.app X).toAddHom
    map_smul' := f.map_smul X }

@[ext]
theorem Hom.ext {f g : P ⟶ Q} (w : ∀ X, f.app X = g.app X) : f = g := by
  cases f; cases g;
  congr
  ext X x
  exact LinearMap.congr_fun (w X) x

/-- The functor from presheaves of modules over a specified presheaf of rings,
to presheaves of abelian groups.
-/
def toPresheaf : PresheafOfModules F ⥤ (Cᵒᵖ ⥤ AddCommGroupCat) where
  obj P := P.presheaf
  map f := f.hom

end PresheafOfModules
