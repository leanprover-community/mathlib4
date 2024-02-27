/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Brendan Murphy
-/
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Functor.FullyFaithful

#align_import category_theory.monoidal.natural_transformation from "leanprover-community/mathlib"@"d047eb4671130d5998b185e49a0443a0d2e9b191"

/-!
# Monoidal natural transformations

Natural transformations between lax monoidal functors must satisfy
an additional compatibility relation with the tensorators:
`F.μ X Y ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ G.μ X Y`.

There is a dual condition for colax monoidal functors, and a hexagonal
condition for transformations `F ⋙ H → G ⋙ K` when `F, G` are lax and `H, K` colax.

((Co)lax) monoidal functors between a fixed pair of monoidal categories
themselves form a category.
There is a double category with objects monoidal category and lax/colax
functors as the vertical/horizontal 1-cells, with `MonoidalSquare`s as 2-cells.

References: Adjoint for double categories, Grandis and Pare
-/

open CategoryTheory

universe v₀ v₁ v₂ v₃ u₀ u₁ u₂ u₃

open CategoryTheory.Category

open CategoryTheory.Functor

namespace CategoryTheory

open MonoidalCategory

variable {B : Type u₀} [Category.{v₀} B] [MonoidalCategory.{v₀} B]
         {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
         {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]
         {E : Type u₃} [Category.{v₃} E] [MonoidalCategory.{v₃} E]

/-- A lax monoidal natural transformation is a natural transformation between
lax monoidal functors additionally satisfying:
`F.μ X Y ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ G.μ X Y`
-/
@[ext]
structure LaxMonoidalNatTrans (F G : LaxMonoidalFunctor C D) extends
  NatTrans F.toFunctor G.toFunctor where
  /-- The unit condition for a lax monoidal natural transformation. -/
  unit : F.η ≫ app (𝟙_ C) = G.η := by aesop_cat
  /-- The tensor condition for a lax monoidal natural transformation. -/
  tensor : ∀ X Y, F.μ _ _ ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ G.μ _ _ := by aesop_cat
#align category_theory.monoidal_nat_trans CategoryTheory.LaxMonoidalNatTrans

/-- A colax monoidal natural transformation is a natural transformation between
colax monoidal functors additionally satisfying:
`F.δ X Y ≫ (app X ⊗ app Y) = app (X ⊗ Y) ≫ G.δ X Y`
-/
@[ext]
structure ColaxMonoidalNatTrans (F G : ColaxMonoidalFunctor C D) extends
  NatTrans F.toFunctor G.toFunctor where
  /-- The counit condition for a colax monoidal natural transformation. -/
  counit : app (𝟙_ C) ≫ G.ε = F.ε  := by aesop_cat
  /-- The cotensor condition for a colax monoidal natural transformation. -/
  cotensor : ∀ X Y, F.δ X Y ≫ (app X ⊗ app Y) = app (X ⊗ Y) ≫ G.δ X Y := by aesop_cat

/-- A monoidal natural transformation is a natural transformation between
monoidal functors which is both lax and colax; equivalently it is either lax or colax. -/
@[ext]
structure MonoidalNatTrans (F G : MonoidalFunctor C D) extends
  LaxMonoidalNatTrans F.toLaxMonoidalFunctor G.toLaxMonoidalFunctor,
  ColaxMonoidalNatTrans F.toColaxMonoidalFunctor G.toColaxMonoidalFunctor

/-- A monoidal square is a natural transformation between compositions of lax
and colax monoidal functors, satisfying a hexagonal coherence condition about
the (co)tensorators and a trapezoidal coherence condition about the (co)units.
The argument order is chosen to be consistent with `CommSq`. -/
@[ext]
class MonoidalSquare (F : LaxMonoidalFunctor B C) (G : ColaxMonoidalFunctor B D)
    (H : ColaxMonoidalFunctor C E) (K : LaxMonoidalFunctor D E)
    extends NatTrans (F.toFunctor ⋙ H.toFunctor) (G.toFunctor ⋙ K.toFunctor) where
  trapezoid : H.map F.η ≫ app (𝟙_ B) ≫ K.map G.ε = H.ε ≫ K.η := by aesop_cat
  hexagon : ∀ X Y : B,
      H.map (F.μ X Y) ≫ app (X ⊗ Y) ≫ K.map (G.δ X Y) =
        H.δ (F.obj X) (F.obj Y) ≫ (app X ⊗ app Y) ≫ K.μ (G.obj X) (G.obj Y) :=
    by aesop_cat

attribute [reassoc (attr := simp)] LaxMonoidalNatTrans.tensor
attribute [reassoc (attr := simp)] LaxMonoidalNatTrans.unit
attribute [reassoc (attr := simp)] ColaxMonoidalNatTrans.cotensor
attribute [reassoc (attr := simp)] ColaxMonoidalNatTrans.counit
attribute [reassoc (attr := simp)] MonoidalSquare.hexagon
attribute [reassoc (attr := simp)] MonoidalSquare.trapezoid

initialize_simps_projections LaxMonoidalNatTrans (+toNatTrans, -app)
initialize_simps_projections ColaxMonoidalNatTrans (+toNatTrans, -app)
initialize_simps_projections MonoidalNatTrans (+toNatTrans, -app)

#align category_theory.monoidal_nat_trans.unit CategoryTheory.LaxMonoidalNatTrans.unit
#align category_theory.monoidal_nat_trans.unit_assoc CategoryTheory.LaxMonoidalNatTrans.unit_assoc
#align category_theory.monoidal_nat_trans.tensor CategoryTheory.LaxMonoidalNatTrans.tensor
#align category_theory.monoidal_nat_trans.tensor_assoc CategoryTheory.LaxMonoidalNatTrans.tensor_assoc

namespace LaxMonoidalNatTrans

@[simps apply_toNatTrans symm_apply_toNatTrans]
def equivHGlobularSquare (F G : LaxMonoidalFunctor C D) :
    LaxMonoidalNatTrans F G ≃ MonoidalSquare F (.id C) (.id D) G where
  toFun α := { (F.rightUnitor.hom ≫ α.toNatTrans ≫ G.leftUnitor.hom) with }
  invFun σ := { (F.rightUnitor.inv ≫ σ.toNatTrans ≫ G.leftUnitor.inv) with
                unit := by simpa using σ.trapezoid
                tensor := by simpa using σ.hexagon }
  left_inv α := by aesop_cat
  right_inv σ := by aesop_cat

/-- The identity lax monoidal natural transformation. -/
@[simps!]
def id (F : LaxMonoidalFunctor C D) : LaxMonoidalNatTrans F F :=
  { 𝟙 F.toFunctor with }
#align category_theory.monoidal_nat_trans.id CategoryTheory.LaxMonoidalNatTrans.id

instance (F : LaxMonoidalFunctor C D) : Inhabited (LaxMonoidalNatTrans F F) :=
  ⟨id F⟩

/-- Vertical composition of lax monoidal natural transformations. -/
@[simps!]
def vcomp {F G H : LaxMonoidalFunctor C D} (α : LaxMonoidalNatTrans F G) (β : LaxMonoidalNatTrans G H) :
    LaxMonoidalNatTrans F H :=
  { NatTrans.vcomp α.toNatTrans β.toNatTrans with }
#align category_theory.monoidal_nat_trans.vcomp CategoryTheory.LaxMonoidalNatTrans.vcomp

end LaxMonoidalNatTrans

variable (C D)

instance LaxMonoidalFunctor.categoryLaxMonoidalFunctor :
    Category (LaxMonoidalFunctor C D) where
  Hom := LaxMonoidalNatTrans
  id := LaxMonoidalNatTrans.id
  comp α β := LaxMonoidalNatTrans.vcomp α β
#align category_theory.monoidal_nat_trans.category_lax_monoidal_functor CategoryTheory.LaxMonoidalFunctor.categoryLaxMonoidalFunctor

instance MonoidalFunctor.categoryMonoidalFunctor : Category (MonoidalFunctor C D) :=
  InducedCategory.category MonoidalFunctor.toLaxMonoidalFunctor
#align category_theory.monoidal_nat_trans.category_monoidal_functor CategoryTheory.MonoidalFunctor.categoryMonoidalFunctor

/-- The functor which takes the underlying lax monoidal functor of a
strong monoidal functor. -/
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

namespace LaxMonoidalNatTrans

@[simp]
theorem comp_toNatTrans_lax {F G H : LaxMonoidalFunctor C D} {α : F ⟶ G} {β : G ⟶ H} :
    (α ≫ β).toNatTrans = @CategoryStruct.comp (C ⥤ D) _ _ _ _ α.toNatTrans β.toNatTrans :=
  rfl
#align category_theory.monoidal_nat_trans.comp_to_nat_trans_lax CategoryTheory.LaxMonoidalNatTrans.comp_toNatTrans_lax

-- Porting note: added, as `LaxMonoidalNatTrans.ext` does not apply to morphisms.
@[ext]
lemma ext' {F G : LaxMonoidalFunctor C D} {α β : F ⟶ G} (w : ∀ X : C, α.app X = β.app X) : α = β :=
  LaxMonoidalNatTrans.ext _ _ (funext w)

@[simp]
theorem comp_toNatTrans {F G H : MonoidalFunctor C D} {α : F ⟶ G} {β : G ⟶ H} :
    (α ≫ β).toNatTrans = @CategoryStruct.comp (C ⥤ D) _ _ _ _ α.toNatTrans β.toNatTrans :=
  rfl
#align category_theory.monoidal_nat_trans.comp_to_nat_trans CategoryTheory.LaxMonoidalNatTrans.comp_toNatTrans

variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory.{v₃} E]

/-- Horizontal composition of monoidal natural transformations. -/
@[simps]
def hcomp {F G : LaxMonoidalFunctor C D} {H K : LaxMonoidalFunctor D E} (α : LaxMonoidalNatTrans F G)
    (β : LaxMonoidalNatTrans H K) : LaxMonoidalNatTrans (F ⊗⋙ H) (G ⊗⋙ K) :=
  { NatTrans.hcomp α.toNatTrans β.toNatTrans with
    unit := by
      dsimp; simp
      conv_lhs => rw [← K.toFunctor.map_comp, α.unit]
    tensor := fun X Y => by
      dsimp; simp
      conv_lhs => rw [← K.toFunctor.map_comp, α.tensor, K.toFunctor.map_comp] }
#align category_theory.monoidal_nat_trans.hcomp CategoryTheory.LaxMonoidalNatTrans.hcomp

/-- The cartesian product of two monoidal natural transformations is monoidal. -/
@[simps]
def prod {F G : LaxMonoidalFunctor C D} {H K : LaxMonoidalFunctor C E} (α : LaxMonoidalNatTrans F G)
    (β : LaxMonoidalNatTrans H K) : LaxMonoidalNatTrans (F.prod' H) (G.prod' K) where
  app X := (α.app X, β.app X)
#align category_theory.monoidal_nat_trans.prod CategoryTheory.LaxMonoidalNatTrans.prod

end LaxMonoidalNatTrans

namespace MonoidalNatIso

variable {F G : LaxMonoidalFunctor C D}

/-- Construct a monoidal natural isomorphism from object level isomorphisms,
and the monoidal naturality in the forward direction. -/
def ofComponents (app : ∀ X : C, F.obj X ≅ G.obj X)
    (naturality' : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (app Y).hom = (app X).hom ≫ G.map f)
    (unit' : F.η ≫ (app (𝟙_ C)).hom = G.η)
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
def Adjunction.monoidalUnit (F : MonoidalFunctor C D) [IsLeftAdjoint F.toFunctor] :
    LaxMonoidalFunctor.id C ⟶ F.toLaxMonoidalFunctor ⊗⋙ F.rightAdjoint where
  toNatTrans := (ofLeftAdjoint F.toFunctor).unit
  unit := by simp [← (rightAdjoint F.toFunctor).map_comp, -map_comp]
  tensor X Y := ((ofLeftAdjoint F.toFunctor).homEquiv _ _).symm.injective <| by
    -- we shouldn't need to do this! maybe related to the diamond inheritance issue?
    have H := @ColaxMonoidalFunctor.δ_natural_assoc _ _ _ _ _ _
      F.toColaxMonoidalFunctor
    dsimp at H
    simp [← tensor_comp_assoc, H]

/-- The unit of a monoidal equivalence can be upgraded to a monoidal natural transformation. -/
@[simps!] -- Porting note: have to manually specify the toNatTrans projection
def Equivalence.monoidalUnitIso (F : MonoidalFunctor C D) [IsEquivalence F.toFunctor] :
    MonoidalFunctor.id C ≅ F ⊗⋙ F.monoidalInverse :=
  let η := Adjunction.monoidalUnit F
  (isoEquivOfFullyFaithful (MonoidalFunctor.forget _ _)).symm <|
    MonoidalNatIso.ofComponents (fun X => IsEquivalence.unitIso.app X)
      (fun f => η.naturality f) η.unit η.tensor

/-- The counit of a monoidal adjunction can be upgraded to a monoidal natural transformation. -/
@[simps toNatTrans]
def Adjunction.monoidalCounit (F : MonoidalFunctor C D) [IsLeftAdjoint F.toFunctor] :
    F.rightAdjoint ⊗⋙ F.toLaxMonoidalFunctor ⟶ LaxMonoidalFunctor.id D where
  toNatTrans := (ofLeftAdjoint F.toFunctor).counit

/-- The counit of a monoidal equivalence can be upgraded to a monoidal natural transformation. -/
@[simps!] -- Porting note: have to manually specify the toNatTrans projection
def Equivalence.monoidalCounitIso (F : MonoidalFunctor C D) [IsEquivalence F.toFunctor] :
    F.monoidalInverse ⊗⋙ F ≅ MonoidalFunctor.id D :=
  let η := Adjunction.monoidalCounit F
  (isoEquivOfFullyFaithful (MonoidalFunctor.forget _ _)).symm <|
    MonoidalNatIso.ofComponents (fun X => IsEquivalence.counitIso.app X)
      (fun f => η.naturality f) η.unit η.tensor

end

end CategoryTheory
