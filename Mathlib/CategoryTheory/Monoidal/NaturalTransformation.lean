/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.FullSubcategory

#align_import category_theory.monoidal.natural_transformation from "leanprover-community/mathlib"@"d047eb4671130d5998b185e49a0443a0d2e9b191"

/-!
# Monoidal natural transformations

Natural transformations between (lax) monoidal functors must satisfy
an additional compatibility relation with the tensorators:
`F.μ X Y ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ G.μ X Y`.

(Lax) monoidal functors between a fixed pair of monoidal categories
themselves form a category.
-/

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory.Category

open CategoryTheory.Functor

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [MonoidalCategory.{v₂} D]

/-- A monoidal natural transformation is a natural transformation between (lax) monoidal functors
additionally satisfying:
`F.μ X Y ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ G.μ X Y`
-/
@[ext]
structure MonoidalNatTrans (F G : LaxMonoidalFunctor C D) extends
  NatTrans F.toFunctor G.toFunctor where
  /-- The unit condition for a monoidal natural transformation. -/
  unit : F.ε ≫ app (𝟙_ C) = G.ε := by aesop_cat
  /-- The tensor condition for a monoidal natural transformation. -/
  tensor : ∀ X Y, F.μ _ _ ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ G.μ _ _ := by aesop_cat
#align category_theory.monoidal_nat_trans CategoryTheory.MonoidalNatTrans

-- Porting note: `reassoc (attr := simp)` seems to add a `simp`
-- attribute to the original lemma as well.
attribute [reassoc (attr := simp)] MonoidalNatTrans.tensor
attribute [reassoc (attr := simp)] MonoidalNatTrans.unit

initialize_simps_projections MonoidalNatTrans (+toNatTrans, -app)

#align category_theory.monoidal_nat_trans.unit CategoryTheory.MonoidalNatTrans.unit
#align category_theory.monoidal_nat_trans.unit_assoc CategoryTheory.MonoidalNatTrans.unit_assoc
#align category_theory.monoidal_nat_trans.tensor CategoryTheory.MonoidalNatTrans.tensor
#align category_theory.monoidal_nat_trans.tensor_assoc CategoryTheory.MonoidalNatTrans.tensor_assoc

namespace MonoidalNatTrans

/-- The identity monoidal natural transformation. -/
@[simps!]
def id (F : LaxMonoidalFunctor C D) : MonoidalNatTrans F F :=
  { 𝟙 F.toFunctor with }
#align category_theory.monoidal_nat_trans.id CategoryTheory.MonoidalNatTrans.id

instance (F : LaxMonoidalFunctor C D) : Inhabited (MonoidalNatTrans F F) :=
  ⟨id F⟩

/-- Vertical composition of monoidal natural transformations. -/
@[simps!]
def vcomp {F G H : LaxMonoidalFunctor C D} (α : MonoidalNatTrans F G) (β : MonoidalNatTrans G H) :
    MonoidalNatTrans F H :=
  { NatTrans.vcomp α.toNatTrans β.toNatTrans with }
#align category_theory.monoidal_nat_trans.vcomp CategoryTheory.MonoidalNatTrans.vcomp

instance categoryLaxMonoidalFunctor : Category (LaxMonoidalFunctor C D) where
  Hom := MonoidalNatTrans
  id := id
  comp α β := vcomp α β
#align category_theory.monoidal_nat_trans.category_lax_monoidal_functor CategoryTheory.MonoidalNatTrans.categoryLaxMonoidalFunctor

@[simp]
theorem comp_toNatTrans_lax {F G H : LaxMonoidalFunctor C D} {α : F ⟶ G} {β : G ⟶ H} :
    (α ≫ β).toNatTrans = @CategoryStruct.comp (C ⥤ D) _ _ _ _ α.toNatTrans β.toNatTrans :=
  rfl
#align category_theory.monoidal_nat_trans.comp_to_nat_trans_lax CategoryTheory.MonoidalNatTrans.comp_toNatTrans_lax

instance categoryMonoidalFunctor : Category (MonoidalFunctor C D) :=
  InducedCategory.category MonoidalFunctor.toLaxMonoidalFunctor
#align category_theory.monoidal_nat_trans.category_monoidal_functor CategoryTheory.MonoidalNatTrans.categoryMonoidalFunctor

-- Porting note: added, as `MonoidalNatTrans.ext` does not apply to morphisms.
@[ext]
lemma ext' {F G : LaxMonoidalFunctor C D} {α β : F ⟶ G} (w : ∀ X : C, α.app X = β.app X) : α = β :=
  MonoidalNatTrans.ext _ _ (funext w)

@[simp]
theorem comp_toNatTrans {F G H : MonoidalFunctor C D} {α : F ⟶ G} {β : G ⟶ H} :
    (α ≫ β).toNatTrans = @CategoryStruct.comp (C ⥤ D) _ _ _ _ α.toNatTrans β.toNatTrans :=
  rfl
#align category_theory.monoidal_nat_trans.comp_to_nat_trans CategoryTheory.MonoidalNatTrans.comp_toNatTrans

variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory.{v₃} E]

/-- Horizontal composition of monoidal natural transformations. -/
@[simps]
def hcomp {F G : LaxMonoidalFunctor C D} {H K : LaxMonoidalFunctor D E} (α : MonoidalNatTrans F G)
    (β : MonoidalNatTrans H K) : MonoidalNatTrans (F ⊗⋙ H) (G ⊗⋙ K) :=
  { NatTrans.hcomp α.toNatTrans β.toNatTrans with
    unit := by
      dsimp; simp
      conv_lhs => rw [← K.toFunctor.map_comp, α.unit]
    tensor := fun X Y => by
      dsimp; simp
      conv_lhs => rw [← K.toFunctor.map_comp, α.tensor, K.toFunctor.map_comp] }
#align category_theory.monoidal_nat_trans.hcomp CategoryTheory.MonoidalNatTrans.hcomp

section

attribute [local simp] NatTrans.naturality MonoidalNatTrans.unit MonoidalNatTrans.tensor

/-- The cartesian product of two monoidal natural transformations is monoidal. -/
@[simps]
def prod {F G : LaxMonoidalFunctor C D} {H K : LaxMonoidalFunctor C E} (α : MonoidalNatTrans F G)
    (β : MonoidalNatTrans H K) : MonoidalNatTrans (F.prod' H) (G.prod' K) where
  app X := (α.app X, β.app X)
#align category_theory.monoidal_nat_trans.prod CategoryTheory.MonoidalNatTrans.prod

end

end MonoidalNatTrans

namespace MonoidalNatIso

variable {F G : LaxMonoidalFunctor C D}

/-- Construct a monoidal natural isomorphism from object level isomorphisms,
and the monoidal naturality in the forward direction. -/
def ofComponents (app : ∀ X : C, F.obj X ≅ G.obj X)
    (naturality' : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (app Y).hom = (app X).hom ≫ G.map f)
    (unit' : F.ε ≫ (app (𝟙_ C)).hom = G.ε)
    (tensor' : ∀ X Y, F.μ X Y ≫ (app (X ⊗ Y)).hom = ((app X).hom ⊗ (app Y).hom) ≫ G.μ X Y) :
    F ≅ G where
  hom := { app := fun X => (app X).hom }
  inv := {
    (NatIso.ofComponents app @naturality').inv with
    app := fun X => (app X).inv
    unit := by
      dsimp
      rw [← unit', assoc, Iso.hom_inv_id, comp_id]
    tensor := fun X Y => by
      dsimp
      rw [Iso.comp_inv_eq, assoc, tensor', ← tensor_comp_assoc,
        Iso.inv_hom_id, Iso.inv_hom_id, tensor_id, id_comp] }
#align category_theory.monoidal_nat_iso.of_components CategoryTheory.MonoidalNatIso.ofComponents

@[simp]
theorem ofComponents.hom_app (app : ∀ X : C, F.obj X ≅ G.obj X) (naturality) (unit) (tensor) (X) :
    (ofComponents app naturality unit tensor).hom.app X = (app X).hom :=
  rfl
#align category_theory.monoidal_nat_iso.of_components.hom_app CategoryTheory.MonoidalNatIso.ofComponents.hom_app

@[simp]
theorem ofComponents.inv_app (app : ∀ X : C, F.obj X ≅ G.obj X) (naturality) (unit) (tensor) (X) :
    (ofComponents app naturality unit tensor).inv.app X = (app X).inv := by simp [ofComponents]
#align category_theory.monoidal_nat_iso.of_components.inv_app CategoryTheory.MonoidalNatIso.ofComponents.inv_app

instance isIso_of_isIso_app (α : F ⟶ G) [∀ X : C, IsIso (α.app X)] : IsIso α :=
  ⟨(IsIso.of_iso
        (ofComponents (fun X => asIso (α.app X)) (fun f => α.toNatTrans.naturality f) α.unit
          α.tensor)).1⟩
#align category_theory.monoidal_nat_iso.is_iso_of_is_iso_app CategoryTheory.MonoidalNatIso.isIso_of_isIso_app

end MonoidalNatIso

noncomputable section

/-- The unit of a monoidal equivalence can be upgraded to a monoidal natural transformation. -/
@[simps! toNatTrans] -- Porting note: have to manually specify the toNatTrans projection
def monoidalUnit (F : MonoidalFunctor C D) [IsEquivalence F.toFunctor] :
    LaxMonoidalFunctor.id C ⟶ F.toLaxMonoidalFunctor ⊗⋙ (monoidalInverse F).toLaxMonoidalFunctor :=
  let e := F.toFunctor.asEquivalence
  { toNatTrans := e.unit
    tensor := fun X Y => by
      -- This proof is not pretty; golfing welcome!
      dsimp
      simp only [Adjunction.homEquiv_unit, Adjunction.homEquiv_naturality_right,
        id_comp, assoc]
      simp only [← Functor.map_comp, assoc]
      erw [e.counit_app_functor, e.counit_app_functor,
        F.toLaxMonoidalFunctor.μ_natural, IsIso.inv_hom_id_assoc]
      simp only [CategoryTheory.IsEquivalence.inv_fun_map]
      slice_rhs 2 3 => erw [Iso.hom_inv_id_app]
      dsimp
      simp only [CategoryTheory.Category.id_comp]
      slice_rhs 1 2 =>
        rw [← tensor_comp, Iso.hom_inv_id_app, Iso.hom_inv_id_app]
        dsimp
        rw [tensor_id]
      simp }
#align category_theory.monoidal_unit CategoryTheory.monoidalUnit

instance (F : MonoidalFunctor C D) [IsEquivalence F.toFunctor] : IsIso (monoidalUnit F) :=
  haveI : ∀ X : C, IsIso ((monoidalUnit F).toNatTrans.app X) := by
    dsimp; infer_instance
  MonoidalNatIso.isIso_of_isIso_app _

/-- The counit of a monoidal equivalence can be upgraded to a monoidal natural transformation. -/
@[simps! toNatTrans] -- Porting note: have to manually specify the toNatTrans projection
def monoidalCounit (F : MonoidalFunctor C D) [IsEquivalence F.toFunctor] :
    (monoidalInverse F).toLaxMonoidalFunctor ⊗⋙ F.toLaxMonoidalFunctor ⟶ LaxMonoidalFunctor.id D :=
  let e := F.toFunctor.asEquivalence
  { toNatTrans := e.counit
    unit := by
      dsimp
      simp only [comp_id, assoc, Functor.map_inv, Functor.map_comp,
        NatIso.inv_inv_app, IsIso.inv_comp, IsEquivalence.fun_inv_map, Adjunction.homEquiv_unit]
      erw [e.counit_app_functor, ← e.functor.map_comp_assoc, Iso.hom_inv_id_app]
      dsimp; simp
    tensor := fun X Y => by
      dsimp
      simp only [Adjunction.homEquiv_unit, Adjunction.homEquiv_naturality_right, assoc,
        comp_id, Functor.map_comp]
      simp only [IsEquivalence.fun_inv_map]
      erw [e.counit_app_functor]
      simp only [assoc]
      erw [← e.functor.map_comp_assoc]
      simp only [CategoryTheory.Iso.inv_hom_id_app, CategoryTheory.Iso.inv_hom_id_app_assoc]
      erw [Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
      simp only [id_comp, CategoryTheory.Iso.inv_hom_id_app,
        CategoryTheory.IsIso.hom_inv_id_assoc]
      erw [comp_id] }
#align category_theory.monoidal_counit CategoryTheory.monoidalCounit

instance (F : MonoidalFunctor C D) [IsEquivalence F.toFunctor] : IsIso (monoidalCounit F) :=
  haveI : ∀ X : D, IsIso ((monoidalCounit F).toNatTrans.app X) :=
    by dsimp; infer_instance
  MonoidalNatIso.isIso_of_isIso_app _

end

end CategoryTheory
