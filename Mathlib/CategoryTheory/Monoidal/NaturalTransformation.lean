/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Functor.FullyFaithful

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

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
         {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]
         {E : Type u₃} [Category.{v₃} E] [MonoidalCategory.{v₃} E]

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

end MonoidalNatTrans

variable (C D)

instance LaxMonoidalFunctor.categoryLaxMonoidalFunctor :
    Category (LaxMonoidalFunctor C D) where
  Hom := MonoidalNatTrans
  id := MonoidalNatTrans.id
  comp α β := MonoidalNatTrans.vcomp α β
#align category_theory.monoidal_nat_trans.category_lax_monoidal_functor CategoryTheory.LaxMonoidalFunctor.categoryLaxMonoidalFunctor

instance MonoidalFunctor.categoryMonoidalFunctor : Category (MonoidalFunctor C D) :=
  InducedCategory.category MonoidalFunctor.toLaxMonoidalFunctor
#align category_theory.monoidal_nat_trans.category_monoidal_functor CategoryTheory.MonoidalFunctor.categoryMonoidalFunctor

def MonoidalFunctor.forget : MonoidalFunctor C D ⥤ LaxMonoidalFunctor C D :=
  inducedFunctor _

instance : Faithful (MonoidalFunctor.forget C D) :=
  inferInstanceAs (Faithful (inducedFunctor _))

instance : Full (MonoidalFunctor.forget C D) :=
  inferInstanceAs (Full (inducedFunctor _))

/-- The isomorphism witnessing that the lax monoidal functor underlying the
identity strong monoidal functor is the lax monoidal identity functor. -/
@[simps!]
def MonoidalFunctor.forget_id_iso_id :
    (MonoidalFunctor.forget C C).obj (.id C) ≅ LaxMonoidalFunctor.id C := Iso.refl _

variable {C D}

/-- The isomorphism witnessing that the lax monoidal functor underlying the
composition of strong monoidal functor is the composition of the
underlying lax monoidal functors. -/
@[simps!]
def MonoidalFunctor.forget_comp_iso_comp (F : MonoidalFunctor C D)
    (G : MonoidalFunctor D E) :
    (MonoidalFunctor.forget C E).obj (F ⊗⋙ G) ≅
      (MonoidalFunctor.forget C D).obj F ⊗⋙ (MonoidalFunctor.forget D E).obj G :=
  Iso.refl _

namespace MonoidalNatTrans

@[simp]
theorem comp_toNatTrans_lax {F G H : LaxMonoidalFunctor C D} {α : F ⟶ G} {β : G ⟶ H} :
    (α ≫ β).toNatTrans = @CategoryStruct.comp (C ⥤ D) _ _ _ _ α.toNatTrans β.toNatTrans :=
  rfl
#align category_theory.monoidal_nat_trans.comp_to_nat_trans_lax CategoryTheory.MonoidalNatTrans.comp_toNatTrans_lax

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

section

/-- The unit of a monoidal adjunction can be upgraded to a monoidal natural transformation. -/
@[simps toNatTrans]
def Adjunction.monoidalUnit (F : MonoidalFunctor C D) [IsLeftAdjoint F.toFunctor] :
    LaxMonoidalFunctor.id C ⟶ F.toLaxMonoidalFunctor ⊗⋙ monoidalAdjoint F where
  toNatTrans := IsLeftAdjoint.adj.unit
  unit := (IsLeftAdjoint.adj.homEquiv _ _).symm.injective <| by
    simp [F.εIso.eq_inv_comp, ← tensor_comp_assoc]
  tensor X Y := (IsLeftAdjoint.adj.homEquiv _ _).symm.injective <| by
    simp [(F.μIso X Y).eq_inv_comp, ← tensor_comp_assoc]

/-- The unit of a monoidal equivalence can be upgraded to a monoidal natural transformation. -/
@[simps!] -- Porting note: have to manually specify the toNatTrans projection
def Equivalence.monoidalUnitIso (F : MonoidalFunctor C D) [IsEquivalence F.toFunctor] :
    MonoidalFunctor.id C ≅ F ⊗⋙ monoidalInverse F :=
  let η := Adjunction.monoidalUnit F
  (isoEquivOfFullyFaithful (MonoidalFunctor.forget _ _)).symm <|
    MonoidalNatIso.ofComponents (fun X => IsEquivalence.unitIso.app X)
      (fun f => η.naturality f) η.unit η.tensor

/-- The counit of a monoidal adjunction can be upgraded to a monoidal natural transformation. -/
@[simps toNatTrans]
def Adjunction.monoidalCounit (F : MonoidalFunctor C D) [IsLeftAdjoint F.toFunctor] :
    monoidalAdjoint F ⊗⋙ F.toLaxMonoidalFunctor ⟶ LaxMonoidalFunctor.id D where
  toNatTrans := IsLeftAdjoint.adj.counit

/-- The counit of a monoidal equivalence can be upgraded to a monoidal natural transformation. -/
@[simps!] -- Porting note: have to manually specify the toNatTrans projection
def Equivalence.monoidalCounitIso (F : MonoidalFunctor C D) [IsEquivalence F.toFunctor] :
    monoidalInverse F ⊗⋙ F ≅ MonoidalFunctor.id D :=
  let η := Adjunction.monoidalCounit F
  (isoEquivOfFullyFaithful (MonoidalFunctor.forget _ _)).symm <|
    MonoidalNatIso.ofComponents (fun X => IsEquivalence.counitIso.app X)
      (fun f => η.naturality f) η.unit η.tensor

end

end CategoryTheory
