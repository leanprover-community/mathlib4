/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebraic_geometry.sheafed_space
! leanprover-community/mathlib commit f384f5d1a4e39f36817b8d22afff7b52af8121d1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicGeometry.PresheafedSpace.HasColimits
import Mathbin.Topology.Sheaves.Functors

/-!
# Sheafed spaces

Introduces the category of topological spaces equipped with a sheaf (taking values in an
arbitrary target category `C`.)

We further describe how to apply functors and natural transformations to the values of the
presheaves.
-/


universe v u

open CategoryTheory

open TopCat

open TopologicalSpace

open Opposite

open CategoryTheory.Limits

open CategoryTheory.Category CategoryTheory.Functor

variable (C : Type u) [Category.{v} C]

attribute [local tidy] tactic.op_induction'

namespace AlgebraicGeometry

/-- A `SheafedSpace C` is a topological space equipped with a sheaf of `C`s. -/
structure SheafedSpace extends PresheafedSpace.{v} C where
  IsSheaf : presheaf.IsSheaf
#align algebraic_geometry.SheafedSpace AlgebraicGeometry.SheafedSpace

variable {C}

namespace SheafedSpace

instance coeCarrier : Coe (SheafedSpace C) TopCat where coe X := X.carrier
#align algebraic_geometry.SheafedSpace.coe_carrier AlgebraicGeometry.SheafedSpace.coeCarrier

/-- Extract the `sheaf C (X : Top)` from a `SheafedSpace C`. -/
def sheaf (X : SheafedSpace C) : Sheaf C (X : TopCat.{v}) :=
  ⟨X.Presheaf, X.IsSheaf⟩
#align algebraic_geometry.SheafedSpace.sheaf AlgebraicGeometry.SheafedSpace.sheaf

@[simp]
theorem as_coe (X : SheafedSpace.{v} C) : X.carrier = (X : TopCat.{v}) :=
  rfl
#align algebraic_geometry.SheafedSpace.as_coe AlgebraicGeometry.SheafedSpace.as_coe

@[simp]
theorem mk_coe (carrier) (presheaf) (h) :
    (({     carrier
            Presheaf
            IsSheaf := h } : SheafedSpace.{v} C) : TopCat.{v}) = carrier :=
  rfl
#align algebraic_geometry.SheafedSpace.mk_coe AlgebraicGeometry.SheafedSpace.mk_coe

instance (X : SheafedSpace.{v} C) : TopologicalSpace X :=
  X.carrier.str

/-- The trivial `unit` valued sheaf on any topological space. -/
def unit (X : TopCat) : SheafedSpace (discrete Unit) :=
  { @PresheafedSpace.const (discrete Unit) _ X ⟨⟨⟩⟩ with IsSheaf := Presheaf.isSheaf_unit _ }
#align algebraic_geometry.SheafedSpace.unit AlgebraicGeometry.SheafedSpace.unit

instance : Inhabited (SheafedSpace (discrete Unit)) :=
  ⟨unit (TopCat.of PEmpty)⟩

instance : Category (SheafedSpace C) :=
  show Category (InducedCategory (PresheafedSpace.{v} C) SheafedSpace.toPresheafedSpace) by
    infer_instance

/-- Forgetting the sheaf condition is a functor from `SheafedSpace C` to `PresheafedSpace C`. -/
def forgetToPresheafedSpace : SheafedSpace.{v} C ⥤ PresheafedSpace.{v} C :=
  inducedFunctor _ deriving Full, Faithful
#align algebraic_geometry.SheafedSpace.forget_to_PresheafedSpace AlgebraicGeometry.SheafedSpace.forgetToPresheafedSpace

instance is_presheafedSpace_iso {X Y : SheafedSpace.{v} C} (f : X ⟶ Y) [IsIso f] :
    @IsIso (PresheafedSpace C) _ _ _ f :=
  SheafedSpace.forgetToPresheafedSpace.map_isIso f
#align algebraic_geometry.SheafedSpace.is_PresheafedSpace_iso AlgebraicGeometry.SheafedSpace.is_presheafedSpace_iso

variable {C}

section

attribute [local simp] id comp

@[simp]
theorem id_base (X : SheafedSpace C) : (𝟙 X : X ⟶ X).base = 𝟙 (X : TopCat.{v}) :=
  rfl
#align algebraic_geometry.SheafedSpace.id_base AlgebraicGeometry.SheafedSpace.id_base

theorem id_c (X : SheafedSpace C) :
    (𝟙 X : X ⟶ X).c = eqToHom (Presheaf.Pushforward.id_eq X.Presheaf).symm :=
  rfl
#align algebraic_geometry.SheafedSpace.id_c AlgebraicGeometry.SheafedSpace.id_c

@[simp]
theorem id_c_app (X : SheafedSpace C) (U) :
    (𝟙 X : X ⟶ X).c.app U =
      eqToHom
        (by
          induction U using Opposite.rec'
          cases U
          rfl) :=
  by
  induction U using Opposite.rec'
  cases U
  simp only [id_c]
  dsimp
  simp
#align algebraic_geometry.SheafedSpace.id_c_app AlgebraicGeometry.SheafedSpace.id_c_app

@[simp]
theorem comp_base {X Y Z : SheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl
#align algebraic_geometry.SheafedSpace.comp_base AlgebraicGeometry.SheafedSpace.comp_base

@[simp]
theorem comp_c_app {X Y Z : SheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
    (α ≫ β).c.app U = β.c.app U ≫ α.c.app (op ((Opens.map β.base).obj (unop U))) :=
  rfl
#align algebraic_geometry.SheafedSpace.comp_c_app AlgebraicGeometry.SheafedSpace.comp_c_app

theorem comp_c_app' {X Y Z : SheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
    (α ≫ β).c.app (op U) = β.c.app (op U) ≫ α.c.app (op ((Opens.map β.base).obj U)) :=
  rfl
#align algebraic_geometry.SheafedSpace.comp_c_app' AlgebraicGeometry.SheafedSpace.comp_c_app'

theorem congr_app {X Y : SheafedSpace C} {α β : X ⟶ Y} (h : α = β) (U) :
    α.c.app U = β.c.app U ≫ X.Presheaf.map (eqToHom (by subst h)) :=
  PresheafedSpace.congr_app h U
#align algebraic_geometry.SheafedSpace.congr_app AlgebraicGeometry.SheafedSpace.congr_app

variable (C)

/-- The forgetful functor from `SheafedSpace` to `Top`. -/
def forget : SheafedSpace C ⥤ TopCat
    where
  obj X := (X : TopCat.{v})
  map X Y f := f.base
#align algebraic_geometry.SheafedSpace.forget AlgebraicGeometry.SheafedSpace.forget

end

open TopCat.Presheaf

/-- The restriction of a sheafed space along an open embedding into the space.
-/
def restrict {U : TopCat} (X : SheafedSpace C) {f : U ⟶ (X : TopCat.{v})} (h : OpenEmbedding f) :
    SheafedSpace C :=
  { X.toPresheafedSpace.restrict h with IsSheaf := isSheaf_of_openEmbedding h X.IsSheaf }
#align algebraic_geometry.SheafedSpace.restrict AlgebraicGeometry.SheafedSpace.restrict

/-- The restriction of a sheafed space `X` to the top subspace is isomorphic to `X` itself.
-/
def restrictTopIso (X : SheafedSpace C) : X.restrict (Opens.openEmbedding ⊤) ≅ X :=
  forgetToPresheafedSpace.preimageIso X.toPresheafedSpace.restrictTopIso
#align algebraic_geometry.SheafedSpace.restrict_top_iso AlgebraicGeometry.SheafedSpace.restrictTopIso

/-- The global sections, notated Gamma.
-/
def Γ : (SheafedSpace C)ᵒᵖ ⥤ C :=
  forgetToPresheafedSpace.op ⋙ PresheafedSpace.Γ
#align algebraic_geometry.SheafedSpace.Γ AlgebraicGeometry.SheafedSpace.Γ

theorem Γ_def : (Γ : _ ⥤ C) = forgetToPresheafedSpace.op ⋙ PresheafedSpace.Γ :=
  rfl
#align algebraic_geometry.SheafedSpace.Γ_def AlgebraicGeometry.SheafedSpace.Γ_def

@[simp]
theorem Γ_obj (X : (SheafedSpace C)ᵒᵖ) : Γ.obj X = (unop X).Presheaf.obj (op ⊤) :=
  rfl
#align algebraic_geometry.SheafedSpace.Γ_obj AlgebraicGeometry.SheafedSpace.Γ_obj

theorem Γ_obj_op (X : SheafedSpace C) : Γ.obj (op X) = X.Presheaf.obj (op ⊤) :=
  rfl
#align algebraic_geometry.SheafedSpace.Γ_obj_op AlgebraicGeometry.SheafedSpace.Γ_obj_op

@[simp]
theorem Γ_map {X Y : (SheafedSpace C)ᵒᵖ} (f : X ⟶ Y) : Γ.map f = f.unop.c.app (op ⊤) :=
  rfl
#align algebraic_geometry.SheafedSpace.Γ_map AlgebraicGeometry.SheafedSpace.Γ_map

theorem Γ_map_op {X Y : SheafedSpace C} (f : X ⟶ Y) : Γ.map f.op = f.c.app (op ⊤) :=
  rfl
#align algebraic_geometry.SheafedSpace.Γ_map_op AlgebraicGeometry.SheafedSpace.Γ_map_op

noncomputable instance [HasLimits C] :
    CreatesColimits (forgetToPresheafedSpace : SheafedSpace C ⥤ _) :=
  ⟨fun J hJ =>
    ⟨fun K =>
      creates_colimit_of_fully_faithful_of_iso
        ⟨(PresheafedSpace.colimit_cocone (K ⋙ forget_to_PresheafedSpace)).pt,
          limit_is_sheaf _ fun j => sheaf.pushforward_sheaf_of_sheaf _ (K.obj (unop j)).2⟩
        (colimit.iso_colimit_cocone ⟨_, PresheafedSpace.colimit_cocone_is_colimit _⟩).symm⟩⟩

instance [HasLimits C] : HasColimits (SheafedSpace C) :=
  has_colimits_of_has_colimits_creates_colimits forgetToPresheafedSpace

noncomputable instance [HasLimits C] : PreservesColimits (forget C) :=
  Limits.compPreservesColimits forgetToPresheafedSpace (PresheafedSpace.forget C)

end SheafedSpace

end AlgebraicGeometry

