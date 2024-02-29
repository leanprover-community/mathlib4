/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Brendan Murphy
-/
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.CatSquares

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

universe v₀ v₁ v₂ v₃ v₄ v₅ u₀ u₁ u₂ u₃ u₄ u₅

open CategoryTheory.Category

open CategoryTheory.Functor

namespace CategoryTheory

open MonoidalCategory

variable {B : Type u₀} [Category.{v₀} B] [MonoidalCategory.{v₀} B]
         {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
         {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]
         {E : Type u₃} [Category.{v₃} E] [MonoidalCategory.{v₃} E]
         {M : Type u₄} [Category.{v₄} M] [MonoidalCategory.{v₄} M]
         {N : Type u₅} [Category.{v₅} N] [MonoidalCategory.{v₅} N]

/-- A lax monoidal natural transformation is a natural transformation between
lax monoidal functors additionally satisfying:
`F.μ X Y ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ G.μ X Y`
-/
@[ext]
structure LaxMonoidalNatTrans (F G : C ⥤⊗ℓ D) extends
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
structure ColaxMonoidalNatTrans (F G : C ⥤⊗c D) extends
  NatTrans F.toFunctor G.toFunctor where
  /-- The counit condition for a colax monoidal natural transformation. -/
  counit : app (𝟙_ C) ≫ G.ε = F.ε  := by aesop_cat
  /-- The cotensor condition for a colax monoidal natural transformation. -/
  cotensor : ∀ X Y, F.δ X Y ≫ (app X ⊗ app Y) = app (X ⊗ Y) ≫ G.δ X Y := by aesop_cat

/-- A monoidal natural transformation is a natural transformation between
monoidal functors which is both lax and colax; equivalently it is either lax or colax. -/
@[ext]
structure MonoidalNatTrans (F G : C ⥤⊗s D) extends
  LaxMonoidalNatTrans F.toLaxMonoidalFunctor G.toLaxMonoidalFunctor,
  ColaxMonoidalNatTrans F.toColaxMonoidalFunctor G.toColaxMonoidalFunctor

/-- A monoidal square is a natural transformation between compositions of lax
and colax monoidal functors, satisfying a hexagonal coherence condition about
the (co)tensorators and a trapezoidal coherence condition about the (co)units.
The argument order is chosen to be consistent with `CommSq`. -/
@[ext]
structure MonoidalSq (F : B ⥤⊗ℓ C) (G : B ⥤⊗c D) (H : C ⥤⊗c E) (K : D ⥤⊗ℓ E)
    extends CatColaxSq F.toFunctor G.toFunctor H.toFunctor K.toFunctor where
  trapezoid' : H.map F.η ≫ constraint.app (𝟙_ B) ≫ K.map G.ε = H.ε ≫ K.η :=
    by aesop_cat
  hexagon' : ∀ X Y : B,
      H.map (F.μ X Y) ≫ constraint.app (X ⊗ Y) ≫ K.map (G.δ X Y) =
        H.δ (F.obj X) (F.obj Y) ≫ (constraint.app X ⊗ constraint.app Y) ≫
          K.μ (G.obj X) (G.obj Y) :=
    by aesop_cat

attribute [reassoc (attr := simp)] LaxMonoidalNatTrans.tensor
attribute [reassoc (attr := simp)] LaxMonoidalNatTrans.unit
attribute [reassoc (attr := simp)] ColaxMonoidalNatTrans.cotensor
attribute [reassoc (attr := simp)] ColaxMonoidalNatTrans.counit

initialize_simps_projections LaxMonoidalNatTrans (+toNatTrans, -app)
initialize_simps_projections ColaxMonoidalNatTrans (+toNatTrans, -app)
initialize_simps_projections MonoidalNatTrans (+toNatTrans, -app)
initialize_simps_projections MonoidalSq (+constraint, -constraint_app)

#align category_theory.monoidal_nat_trans.unit CategoryTheory.LaxMonoidalNatTrans.unit
#align category_theory.monoidal_nat_trans.unit_assoc CategoryTheory.LaxMonoidalNatTrans.unit_assoc
#align category_theory.monoidal_nat_trans.tensor CategoryTheory.LaxMonoidalNatTrans.tensor
#align category_theory.monoidal_nat_trans.tensor_assoc CategoryTheory.LaxMonoidalNatTrans.tensor_assoc

namespace MonoidalSq

variable {F : B ⥤⊗ℓ C} {G : B ⥤⊗c D} {H : C ⥤⊗c E} {K : D ⥤⊗ℓ E}

@[reassoc (attr := simp)]
lemma trapezoid (s : MonoidalSq F G H K) :
    H.map F.η ≫ s.app (𝟙_ B) ≫ K.map G.ε = H.ε ≫ K.η :=
  s.trapezoid'

@[reassoc (attr := simp)]
lemma hexagon_components (s : MonoidalSq F G H K) (X Y : B) :
    H.map (F.μ X Y) ≫ s.app (X ⊗ Y) ≫ K.map (G.δ X Y) =
      H.δ (F.obj X) (F.obj Y) ≫ (s.app X ⊗ s.app Y) ≫ K.μ (G.obj X) (G.obj Y) :=
  s.hexagon' X Y

@[reassoc (attr := simp)]
lemma hexagon (s : MonoidalSq F G H K) :
    (whiskerRight F.μNatTrans H.toFunctor) ≫
      (Functor.associator _ _ _).hom ≫ (whiskerLeft (tensor B) s.constraint) ≫
        (Functor.associator _ _ _).inv ≫ (whiskerRight G.δNatTrans K.toFunctor) =
    (Functor.associator _ _ _).hom ≫
      whiskerLeft (F.toFunctor.prod F.toFunctor) H.δNatTrans ≫
        (Functor.associator _ _ _).inv ≫
          whiskerRight (Functor.prodCompIso _ _ _ _).inv (tensor E) ≫
            whiskerRight (.prod s.constraint s.constraint) (tensor E) ≫
              whiskerRight (Functor.prodCompIso _ _ _ _).hom (tensor E) ≫
                (Functor.associator _ _ _).hom ≫
                  whiskerLeft (.prod G.toFunctor G.toFunctor) K.μNatTrans ≫
                    (Functor.associator _ _ _).inv := by
  aesop_cat

def mkOfNatTransHexagon
    (sq : CatColaxSq F.toFunctor G.toFunctor H.toFunctor K.toFunctor)
    (trapezoid : H.map F.η ≫ sq.app (𝟙_ B) ≫ K.map G.ε = H.ε ≫ K.η :=
      by aesop_cat)
    (hexagon :
      (whiskerRight F.μNatTrans H.toFunctor) ≫
        (Functor.associator _ _ _).hom ≫ (whiskerLeft (tensor B) sq.constraint) ≫
          (Functor.associator _ _ _).inv ≫ (whiskerRight G.δNatTrans K.toFunctor) =
      (Functor.associator _ _ _).hom ≫
        whiskerLeft (F.toFunctor.prod F.toFunctor) H.δNatTrans ≫
          (Functor.associator _ _ _).inv ≫
            whiskerRight (Functor.prodCompIso _ _ _ _).inv (tensor E) ≫
              whiskerRight (.prod sq.constraint sq.constraint) (tensor E) ≫
                whiskerRight (Functor.prodCompIso _ _ _ _).hom (tensor E) ≫
                  (Functor.associator _ _ _).hom ≫
                    whiskerLeft (.prod G.toFunctor G.toFunctor) K.μNatTrans ≫
                      (Functor.associator _ _ _).inv := by aesop_cat) :
    MonoidalSq F G H K where
  __ := sq
  trapezoid' := trapezoid
  hexagon' X Y := by simpa using congrArg (NatTrans.app . (X, Y)) hexagon

end MonoidalSq

section comparison

open Quiver.Hom (op_inj unop_inj)

attribute [local ext] unop_inj in
@[simps!]
def LaxMonoidalNatTrans.op {F G : C ⥤⊗ℓ D} (α : LaxMonoidalNatTrans F G) :
    ColaxMonoidalNatTrans G.op F.op where
  toNatTrans := .op α.toNatTrans

@[simps!]
def LaxMonoidalNatTrans.unop {F G : Cᵒᵖ ⥤⊗ℓ Dᵒᵖ} (α : LaxMonoidalNatTrans F G) :
    ColaxMonoidalNatTrans G.unop F.unop where
  toNatTrans := .unop α.toNatTrans
  counit := op_inj <| by simp
  cotensor X Y := op_inj <| by simp

attribute [local ext] unop_inj in
@[simps!]
def ColaxMonoidalNatTrans.op {F G : C ⥤⊗c D} (α : ColaxMonoidalNatTrans F G) :
    LaxMonoidalNatTrans G.op F.op where
  toNatTrans := .op α.toNatTrans

@[simps!]
def ColaxMonoidalNatTrans.unop {F G : Cᵒᵖ ⥤⊗c Dᵒᵖ} (α : ColaxMonoidalNatTrans F G) :
    LaxMonoidalNatTrans G.unop F.unop where
  toNatTrans := .unop α.toNatTrans
  unit := op_inj <| by simp
  tensor X Y := op_inj <| by simp

end comparison

namespace LaxMonoidalNatTrans

@[simps]
def equivHGlobularSquare (F G : C ⥤⊗ℓ D) :
    LaxMonoidalNatTrans F G ≃ MonoidalSq F (.id C) (.id D) G where
  toFun α := { constraint := F.rightUnitor.hom ≫ α.toNatTrans ≫ G.leftUnitor.hom }
  invFun σ := { F.rightUnitor.inv ≫ σ.constraint ≫ G.leftUnitor.inv with
                unit := by simpa using σ.trapezoid
                tensor := by simpa using σ.hexagon_components }
  left_inv α := by aesop_cat
  right_inv σ := by aesop_cat

/-- The identity lax monoidal natural transformation. -/
@[simps!]
def id (F : C ⥤⊗ℓ D) : LaxMonoidalNatTrans F F :=
  { 𝟙 F.toFunctor with }
#align category_theory.monoidal_nat_trans.id CategoryTheory.LaxMonoidalNatTrans.id

instance (F : C ⥤⊗ℓ D) : Inhabited (LaxMonoidalNatTrans F F) :=
  ⟨id F⟩

/-- Vertical composition of lax monoidal natural transformations. -/
@[simps!]
def vcomp {F G H : C ⥤⊗ℓ D} (α : LaxMonoidalNatTrans F G)
    (β : LaxMonoidalNatTrans G H) : LaxMonoidalNatTrans F H :=
  { NatTrans.vcomp α.toNatTrans β.toNatTrans with }
#align category_theory.monoidal_nat_trans.vcomp CategoryTheory.LaxMonoidalNatTrans.vcomp

end LaxMonoidalNatTrans

variable (C D)

@[simps! comp_toNatTrans id_toNatTrans]
instance LaxMonoidalFunctor.category : Category (C ⥤⊗ℓ D) where
  Hom := LaxMonoidalNatTrans
  id := .id
  comp α β := .vcomp α β
#align category_theory.monoidal_nat_trans.category_lax_monoidal_functor CategoryTheory.LaxMonoidalFunctor.category
#align category_theory.monoidal_nat_trans.comp_to_nat_trans_lax CategoryTheory.LaxMonoidalFunctor.category_comp_toNatTrans

variable {C D}

namespace LaxMonoidalNatTrans

-- Porting note: added, as `LaxMonoidalNatTrans.ext` does not apply to morphisms.
@[ext]
lemma ext' {F G : C ⥤⊗ℓ D} {α β : F ⟶ G} (w : ∀ X : C, α.app X = β.app X) : α = β :=
  LaxMonoidalNatTrans.ext _ _ (funext w)

/-- Horizontal composition of lax monoidal natural transformations. -/
@[simps]
def hcomp {F G : C ⥤⊗ℓ D} {H K : D ⥤⊗ℓ E} (α : LaxMonoidalNatTrans F G)
    (β : LaxMonoidalNatTrans H K) : LaxMonoidalNatTrans (F ⊗⋙ H) (G ⊗⋙ K) :=
  { NatTrans.hcomp α.toNatTrans β.toNatTrans with
    unit := by simp [← K.toFunctor.map_comp, -map_comp]
    tensor := by simp [← K.toFunctor.map_comp, -map_comp] }
#align category_theory.monoidal_nat_trans.hcomp CategoryTheory.LaxMonoidalNatTrans.hcomp

/-- The cartesian product of two lax monoidal natural transformations is monoidal. -/
@[simps]
def prod {F G : C ⥤⊗ℓ D} {H K : C ⥤⊗ℓ E} (α : LaxMonoidalNatTrans F G)
    (β : LaxMonoidalNatTrans H K) : LaxMonoidalNatTrans (F.prod' H) (G.prod' K) where
  app X := (α.app X, β.app X)
#align category_theory.monoidal_nat_trans.prod CategoryTheory.LaxMonoidalNatTrans.prod

end LaxMonoidalNatTrans

namespace LaxMonoidalNatIso

variable {F G : C ⥤⊗ℓ D}

/-- Construct a lax monoidal natural isomorphism from object level isomorphisms,
and the monoidal naturality in the forward direction. -/
@[simps hom_app inv_app]
def ofComponents (app : ∀ X : C, F.obj X ≅ G.obj X)
    (naturality' : ∀ {X Y : C} (f : X ⟶ Y),
      F.map f ≫ (app Y).hom = (app X).hom ≫ G.map f := by aesop_cat)
    (unit' : F.η ≫ (app (𝟙_ C)).hom = G.η  := by aesop_cat)
    (tensor' : ∀ X Y,
      F.μ X Y ≫ (app (X ⊗ Y)).hom =
        ((app X).hom ⊗ (app Y).hom) ≫ G.μ X Y := by aesop_cat) : F ≅ G where
  hom := { app := fun X => (app X).hom }
  inv := {
    (NatIso.ofComponents app @naturality').inv with
    app := fun X => (app X).inv
    unit := by
      dsimp
      rw [← unit', assoc, Iso.hom_inv_id, comp_id]
    tensor := fun X Y => tensor' X Y |> .mk |> .vert_inv
      (g := app X ⊗ app Y) (h := app (X ⊗ Y)) |> CommSq.w }
#align category_theory.monoidal_nat_iso.of_components CategoryTheory.LaxMonoidalNatIso.ofComponents
#align category_theory.monoidal_nat_iso.of_components.hom_app CategoryTheory.LaxMonoidalNatIso.ofComponents_hom_app
#align category_theory.monoidal_nat_iso.of_components.inv_app CategoryTheory.LaxMonoidalNatIso.ofComponents_inv_app

instance isIso_of_isIso_app (α : F ⟶ G) [∀ X : C, IsIso (α.app X)] : IsIso α :=
  ⟨(IsIso.of_iso
        (ofComponents (fun X => asIso (α.app X)) (fun f => α.toNatTrans.naturality f) α.unit
          α.tensor)).1⟩
#align category_theory.monoidal_nat_iso.is_iso_of_is_iso_app CategoryTheory.LaxMonoidalNatIso.isIso_of_isIso_app

/-- Construct a lax monoidal natural isomorphism from a natural isomorphism of
underlying functors and coherence of the forward direction. -/
@[simps! hom_app inv_app]
def ofNatIso (α : F.toFunctor ≅ G.toFunctor)
    (unit' : F.η ≫ (α.app (𝟙_ C)).hom = G.η := by aesop_cat)
    (tensor' : ∀ X Y,
      F.μ X Y ≫ (α.app (X ⊗ Y)).hom =
        ((α.app X).hom ⊗ (α.app Y).hom) ≫ G.μ X Y := by aesop_cat) : F ≅ G :=
  ofComponents α.app

end LaxMonoidalNatIso

namespace LaxMonoidalFunctor

/- The left unitor for functors, upgraded to a lax natural transformation. -/
@[simps! hom_app inv_app]
def leftUnitor (F : C ⥤⊗ℓ D) : .id C ⊗⋙ F ≅ F :=
  LaxMonoidalNatIso.ofNatIso F.toFunctor.leftUnitor

/- The right unitor for functors, upgraded to a lax natural transformation. -/
@[simps! hom_app inv_app]
def rightUnitor (F : C ⥤⊗ℓ D) : F ⊗⋙ .id D ≅ F :=
  LaxMonoidalNatIso.ofNatIso F.toFunctor.rightUnitor

/- The associator for functors, upgraded to a lax natural transformation. -/
@[simps! hom_app inv_app]
def associator (F : B ⥤⊗ℓ C) (G : C ⥤⊗ℓ D) (H : D ⥤⊗ℓ E) :
    (F ⊗⋙ G) ⊗⋙ H ≅ F ⊗⋙ (G ⊗⋙ H) :=
  LaxMonoidalNatIso.ofNatIso (Functor.associator _ _ _)

end LaxMonoidalFunctor

namespace ColaxMonoidalNatTrans

@[simps]
def equivVGlobularSquare (F G : C ⥤⊗c D) :
    ColaxMonoidalNatTrans F G ≃ MonoidalSq (.id C) G F (.id D) where
  toFun α := { constraint := F.leftUnitor.hom ≫ α.toNatTrans ≫ G.rightUnitor.inv }
  invFun σ := { F.leftUnitor.inv ≫ σ.constraint ≫ G.rightUnitor.hom with
                counit := by simpa using σ.trapezoid
                cotensor := fun X Y => by simpa using (σ.hexagon_components X Y).symm }
  left_inv α := by aesop_cat
  right_inv σ := by aesop_cat

/-- The identity colax monoidal natural transformation. -/
@[simps!]
def id (F : C ⥤⊗c D) : ColaxMonoidalNatTrans F F :=
  LaxMonoidalNatTrans.unop (.id F.op)

instance (F : C ⥤⊗c D) : Inhabited (ColaxMonoidalNatTrans F F) := ⟨id F⟩

/-- Vertical composition of colax monoidal natural transformations. -/
@[simps!]
def vcomp {F G H : C ⥤⊗c D} (α : ColaxMonoidalNatTrans F G)
    (β : ColaxMonoidalNatTrans G H) : ColaxMonoidalNatTrans F H :=
  LaxMonoidalNatTrans.unop (.vcomp β.op α.op)

end ColaxMonoidalNatTrans

variable (C D)

@[simps! comp_toNatTrans id_toNatTrans]
instance ColaxMonoidalFunctor.category : Category (C ⥤⊗c D) where
  Hom := ColaxMonoidalNatTrans
  id := .id
  comp α β := .vcomp α β

variable {C D}

namespace ColaxMonoidalNatTrans

@[ext]
lemma ext' {F G : C ⥤⊗c D} {α β : F ⟶ G} (w : ∀ X : C, α.app X = β.app X) : α = β :=
  ColaxMonoidalNatTrans.ext _ _ (funext w)

/-- Horizontal composition of colax monoidal natural transformations. -/
@[simps!]
def hcomp {F G : C ⥤⊗c D} {H K : D ⥤⊗c E} (α : ColaxMonoidalNatTrans F G)
    (β : ColaxMonoidalNatTrans H K) : ColaxMonoidalNatTrans (F ⊗⋙ H) (G ⊗⋙ K) :=
  { NatTrans.hcomp α.toNatTrans β.toNatTrans with
    counit := by simp [← K.toFunctor.map_comp_assoc, ← β.naturality_assoc,
                  -map_comp, -NatTrans.naturality, -NatTrans.naturality_assoc]
    cotensor := by simp [← K.δ_natural, ← K.map_comp_assoc,
                  -map_comp, -ColaxMonoidalFunctor.δ_natural] }
  -- (α.op.hcomp β.op).unop gives bad defeqs

/-- The cartesian product of two colax monoidal natural transformations is monoidal. -/
@[simps]
def prod {F G : C ⥤⊗c D} {H K : C ⥤⊗c E} (α : ColaxMonoidalNatTrans F G)
    (β : ColaxMonoidalNatTrans H K) :
    ColaxMonoidalNatTrans (F.prod' H) (G.prod' K) where
  app X := (α.app X, β.app X)

end ColaxMonoidalNatTrans

section comparison

open Quiver.Hom (op_inj unop_inj)

@[simps!]
def LaxMonoidalNatIso.op {F G : C ⥤⊗ℓ D} (α : F ≅ G) : G.op ≅ F.op where
  hom := LaxMonoidalNatTrans.op α.hom
  inv := LaxMonoidalNatTrans.op α.inv
  hom_inv_id := ColaxMonoidalNatTrans.ext' fun X => unop_inj <|
    show (α.inv ≫ α.hom).toNatTrans.app _ = _ by simp
  inv_hom_id := ColaxMonoidalNatTrans.ext' fun X => unop_inj <|
    show (α.hom ≫ α.inv).toNatTrans.app _ = _ by simp

@[simps!]
def LaxMonoidalNatIso.unop {F G : C ⥤⊗c D} (α : F.op ≅ G.op) : G ≅ F where
  hom := LaxMonoidalNatTrans.unop α.hom
  inv := LaxMonoidalNatTrans.unop α.inv
  hom_inv_id := ColaxMonoidalNatTrans.ext' fun X => op_inj <|
    show (α.inv ≫ α.hom).toNatTrans.app _ = _ by simp
  inv_hom_id := ColaxMonoidalNatTrans.ext' fun X => op_inj <|
    show (α.hom ≫ α.inv).toNatTrans.app _ = _ by simp

@[simps!]
def ColaxMonoidalNatIso.op {F G : C ⥤⊗c D} (α : F ≅ G) : G.op ≅ F.op where
  hom := ColaxMonoidalNatTrans.op α.hom
  inv := ColaxMonoidalNatTrans.op α.inv
  hom_inv_id := LaxMonoidalNatTrans.ext' fun X => unop_inj <|
    show (α.inv ≫ α.hom).toNatTrans.app _ = _ by simp
  inv_hom_id := LaxMonoidalNatTrans.ext' fun X => unop_inj <|
    show (α.hom ≫ α.inv).toNatTrans.app _ = _ by simp

@[simps!]
def ColaxMonoidalNatIso.unop {F G : C ⥤⊗ℓ D} (α : F.op ≅ G.op) : G ≅ F where
  hom := ColaxMonoidalNatTrans.unop α.hom
  inv := ColaxMonoidalNatTrans.unop α.inv
  hom_inv_id := LaxMonoidalNatTrans.ext' fun X => op_inj <|
    show (α.inv ≫ α.hom).toNatTrans.app _ = _ by simp
  inv_hom_id := LaxMonoidalNatTrans.ext' fun X => op_inj <|
    show (α.hom ≫ α.inv).toNatTrans.app _ = _ by simp

end comparison

namespace ColaxMonoidalNatIso

variable {F G : C ⥤⊗c D}

/-- Construct a colax monoidal natural isomorphism from object level isomorphisms,
and the monoidal naturality in the forward direction. -/
@[simps! hom_app inv_app]
def ofComponents (app : ∀ X : C, F.obj X ≅ G.obj X)
    (naturality' : ∀ {X Y : C} (f : X ⟶ Y),
      F.map f ≫ (app Y).hom = (app X).hom ≫ G.map f := by aesop_cat)
    (counit' : (app (𝟙_ C)).hom ≫ G.ε = F.ε := by aesop_cat)
    (cotensor' : ∀ X Y,
      F.δ X Y ≫ ((app X).hom ⊗ (app Y).hom) =
        (app (X ⊗ Y)).hom ≫ G.δ X Y := by aesop_cat) : F ≅ G :=
  LaxMonoidalNatIso.unop <| LaxMonoidalNatIso.ofComponents (fun X => (app X.unop).op)
    (fun f => Quiver.Hom.unop_inj <| Eq.symm <| naturality' f.unop)
    (Quiver.Hom.unop_inj counit')
    (fun X Y => Quiver.Hom.unop_inj (cotensor' X.unop Y.unop).symm)

instance isIso_of_isIso_app (α : F ⟶ G) [∀ X : C, IsIso (α.app X)] : IsIso α :=
  ⟨(IsIso.of_iso
        (ofComponents (fun X => asIso (α.app X)) (fun f => α.toNatTrans.naturality f) α.counit
          α.cotensor)).1⟩

/-- Construct a colax monoidal natural isomorphism from a natural isomorphism
of underlying functors and coherence of the forward direction. -/
@[simps! hom_app inv_app]
def ofNatIso (α : F.toFunctor ≅ G.toFunctor)
    (counit' : (α.app (𝟙_ C)).hom ≫ G.ε = F.ε := by aesop_cat)
    (cotensor' : ∀ X Y,
      F.δ X Y ≫ ((α.app X).hom ⊗ (α.app Y).hom) =
        (α.app (X ⊗ Y)).hom ≫ G.δ X Y := by aesop_cat) : F ≅ G :=
  ofComponents α.app

end ColaxMonoidalNatIso

namespace ColaxMonoidalFunctor

/- The left unitor for functors, upgraded to a colax natural transformation. -/
@[simps! hom_app inv_app]
def leftUnitor (F : C ⥤⊗c D) : .id C ⊗⋙ F ≅ F :=
  ColaxMonoidalNatIso.ofNatIso F.toFunctor.leftUnitor

/- The right unitor for functors, upgraded to a colax natural transformation. -/
@[simps! hom_app inv_app]
def rightUnitor (F : C ⥤⊗c D) : F ⊗⋙ .id D ≅ F :=
  ColaxMonoidalNatIso.ofNatIso F.toFunctor.rightUnitor

/- The associator for functors, upgraded to a colax natural transformation. -/
@[simps! hom_app inv_app]
def associator (F : B ⥤⊗c C) (G : C ⥤⊗c D) (H : D ⥤⊗c E) :
    (F ⊗⋙ G) ⊗⋙ H ≅ F ⊗⋙ (G ⊗⋙ H) :=
  ColaxMonoidalNatIso.ofNatIso (Functor.associator _ _ _)

end ColaxMonoidalFunctor

namespace MonoidalNatTrans

def mkOfLax {F G : C ⥤⊗s D}
    (α : LaxMonoidalNatTrans F.toLaxMonoidalFunctor G.toLaxMonoidalFunctor) :
    MonoidalNatTrans F G where
  counit := (cancel_epi F.η).mp <| by simp
  cotensor := fun X Y => (cancel_epi (F.μ X Y)).mp <| by simp
  __ := α

@[simp] lemma mkOfLax_toNatTrans {F G : C ⥤⊗s D}
    (α : LaxMonoidalNatTrans F.toLaxMonoidalFunctor G.toLaxMonoidalFunctor) :
    (mkOfLax α).toNatTrans = α.toNatTrans := rfl

@[simps]
def mkOfColax {F G : C ⥤⊗s D}
    (α : ColaxMonoidalNatTrans F.toColaxMonoidalFunctor G.toColaxMonoidalFunctor) :
    MonoidalNatTrans F G where
  unit := (cancel_mono G.ε).mp <| by
    have := α.counit; dsimp at this; simp [this]
  tensor := fun X Y => (cancel_mono (G.δ X Y)).mp <| by
    have := α.cotensor X Y; dsimp at this; simp [← this]
  __ := α

/-- The identity monoidal natural transformation. -/
@[simps!]
def id (F : C ⥤⊗s D) : MonoidalNatTrans F F where
  __ := LaxMonoidalNatTrans.id F.toLaxMonoidalFunctor
  __ := ColaxMonoidalNatTrans.id F.toColaxMonoidalFunctor

instance (F : C ⥤⊗s D) : Inhabited (MonoidalNatTrans F F) := ⟨id F⟩

/-- Vertical composition of monoidal natural transformations. -/
@[simps!]
def vcomp {F G H : C ⥤⊗s D} (α : MonoidalNatTrans F G)
    (β : MonoidalNatTrans G H) : MonoidalNatTrans F H where
  __ := α.toLaxMonoidalNatTrans.vcomp β.toLaxMonoidalNatTrans
  __ := α.toColaxMonoidalNatTrans.vcomp β.toColaxMonoidalNatTrans

end MonoidalNatTrans

variable (C D)

@[simps! comp_toNatTrans id_toNatTrans]
instance MonoidalFunctor.category : Category (C ⥤⊗s D) where
  Hom := MonoidalNatTrans
  id := .id
  comp α β := .vcomp α β
#align category_theory.monoidal_nat_trans.category_monoidal_functor CategoryTheory.MonoidalFunctor.category

variable {C D}

namespace MonoidalNatTrans

@[ext]
lemma ext' {F G : C ⥤⊗s D} {α β : F ⟶ G} (w : ∀ X : C, α.app X = β.app X) : α = β :=
  MonoidalNatTrans.ext _ _ (funext w)

/-- Horizontal composition of monoidal natural transformations. -/
@[simps!]
def hcomp {F G : C ⥤⊗s D} {H K : D ⥤⊗s E} (α : MonoidalNatTrans F G)
    (β : MonoidalNatTrans H K) : MonoidalNatTrans (F ⊗⋙ H) (G ⊗⋙ K) where
  __ := α.toLaxMonoidalNatTrans.hcomp β.toLaxMonoidalNatTrans
  __ := α.toColaxMonoidalNatTrans.hcomp β.toColaxMonoidalNatTrans

/-- The cartesian product of two monoidal natural transformations is monoidal. -/
@[simps!]
def prod {F G : C ⥤⊗s D} {H K : C ⥤⊗s E} (α : MonoidalNatTrans F G)
    (β : MonoidalNatTrans H K) :
    MonoidalNatTrans (F.prod' H) (G.prod' K) where
  __ := α.toLaxMonoidalNatTrans.prod β.toLaxMonoidalNatTrans
  __ := α.toColaxMonoidalNatTrans.prod β.toColaxMonoidalNatTrans

end MonoidalNatTrans

namespace MonoidalNatIso

variable {F G : C ⥤⊗s D}

/-- Construct a monoidal natural isomorphism from object level isomorphisms,
and lax monoidal naturality in the forward direction. -/
@[simps! hom_app inv_app]
def ofLaxComponents (app : ∀ X : C, F.obj X ≅ G.obj X)
    (naturality' : ∀ {X Y : C} (f : X ⟶ Y),
      F.map f ≫ (app Y).hom = (app X).hom ≫ G.map f := by aesop_cat)
    (unit' : F.η ≫ (app (𝟙_ C)).hom = G.η := by aesop_cat)
    (tensor' : ∀ X Y,
      F.μ X Y ≫ (app (X ⊗ Y)).hom =
        ((app X).hom ⊗ (app Y).hom) ≫ G.μ X Y := by aesop_cat) : F ≅ G where
  hom := .mkOfLax <| Iso.hom <|
    LaxMonoidalNatIso.ofComponents app naturality' unit' tensor'
  inv := .mkOfLax <| Iso.inv <|
    LaxMonoidalNatIso.ofComponents app naturality' unit' tensor'

/-- Construct a monoidal natural isomorphism from object level isomorphisms,
and colax monoidal naturality in the forward direction. -/
@[simps! hom_app inv_app]
def ofColaxComponents (app : ∀ X : C, F.obj X ≅ G.obj X)
    (naturality' : ∀ {X Y : C} (f : X ⟶ Y),
      F.map f ≫ (app Y).hom = (app X).hom ≫ G.map f := by aesop_cat)
    (counit' : (app (𝟙_ C)).hom ≫ G.ε = F.ε := by aesop_cat)
    (cotensor' : ∀ X Y,
      F.δ X Y ≫ ((app X).hom ⊗ (app Y).hom) =
        (app (X ⊗ Y)).hom ≫ G.δ X Y := by aesop_cat) : F ≅ G where
  hom := .mkOfColax <| Iso.hom <|
    ColaxMonoidalNatIso.ofComponents app naturality' counit' cotensor'
  inv := .mkOfColax <| Iso.inv <|
    ColaxMonoidalNatIso.ofComponents app naturality' counit' cotensor'

instance isIso_of_isIso_app (α : F ⟶ G) [∀ X : C, IsIso (α.app X)] : IsIso α :=
  ⟨(IsIso.of_iso
        (ofLaxComponents (fun X => asIso (α.app X)) (fun f => α.toNatTrans.naturality f) α.unit
          α.tensor)).1⟩

/-- Construct a monoidal natural isomorphism from a natural isomorphism
of underlying functors and lax coherence of the forward direction. -/
@[simps! hom_app inv_app]
def ofNatIsoLax (α : F.toFunctor ≅ G.toFunctor)
    (unit' : F.η ≫ (α.app (𝟙_ C)).hom = G.η := by aesop_cat)
    (tensor' : ∀ X Y,
      F.μ X Y ≫ (α.app (X ⊗ Y)).hom =
        ((α.app X).hom ⊗ (α.app Y).hom) ≫ G.μ X Y := by aesop_cat) : F ≅ G :=
  ofLaxComponents α.app

/-- Construct a monoidal natural isomorphism from a natural isomorphism
of underlying functors and colax coherence of the forward direction. -/
@[simps! hom_app inv_app]
def ofNatIsoColax (α : F.toFunctor ≅ G.toFunctor)
    (counit' : (α.app (𝟙_ C)).hom ≫ G.ε = F.ε := by aesop_cat)
    (cotensor' : ∀ X Y,
      F.δ X Y ≫ ((α.app X).hom ⊗ (α.app Y).hom) =
        (α.app (X ⊗ Y)).hom ≫ G.δ X Y := by aesop_cat) : F ≅ G :=
  ofColaxComponents α.app (fun f => α.hom.naturality f)

end MonoidalNatIso

namespace MonoidalFunctor

/- The left unitor for functors, upgraded to a monoidal natural transformation. -/
@[simps! hom_app inv_app]
def leftUnitor (F : C ⥤⊗s D) : .id C ⊗⋙ F ≅ F :=
  MonoidalNatIso.ofNatIsoLax F.toFunctor.leftUnitor

/- The right unitor for functors, upgraded to a monoidal natural transformation. -/
@[simps! hom_app inv_app]
def rightUnitor (F : C ⥤⊗s D) : F ⊗⋙ .id D ≅ F :=
  MonoidalNatIso.ofNatIsoLax F.toFunctor.rightUnitor

/- The associator for functors, upgraded to a monoidal natural transformation. -/
@[simps! hom_app inv_app]
def associator (F : B ⥤⊗s C) (G : C ⥤⊗s D) (H : D ⥤⊗s E) :
    (F ⊗⋙ G) ⊗⋙ H ≅ F ⊗⋙ (G ⊗⋙ H) :=
  MonoidalNatIso.ofNatIsoLax (Functor.associator _ _ _)

end MonoidalFunctor

variable (C D)

/-- The functor which takes the underlying lax monoidal functor of a
strong monoidal functor. -/
@[simps]
def MonoidalFunctor.toLax : (C ⥤⊗s D) ⥤ (C ⥤⊗ℓ D) where
  obj F := F.toLaxMonoidalFunctor
  map α := α.toLaxMonoidalNatTrans

instance : Faithful (MonoidalFunctor.toLax C D) where

@[simps]
instance : Full (MonoidalFunctor.toLax C D) where
  preimage f := MonoidalNatTrans.mkOfLax f

/-- The isomorphism witnessing that the lax monoidal functor underlying the
identity strong monoidal functor is the lax monoidal identity functor. -/
@[simps!]
def MonoidalFunctor.toLax_id_iso_id :
    (MonoidalFunctor.toLax C C).obj (.id C) ≅ LaxMonoidalFunctor.id C := Iso.refl _

/-- The functor which takes the underlying colax monoidal functor of a
strong monoidal functor. -/
@[simps obj map]
def MonoidalFunctor.toColax : (C ⥤⊗s D) ⥤ (C ⥤⊗c D) where
  obj F := F.toColaxMonoidalFunctor
  map α := α.toColaxMonoidalNatTrans

instance : Faithful (MonoidalFunctor.toColax C D) where
  map_injective h := by ext X; exact congrArg (fun t => t.toNatTrans.app X) h

@[simps]
instance : Full (MonoidalFunctor.toColax C D) where
  preimage f := MonoidalNatTrans.mkOfColax f

/-- The isomorphism witnessing that the colax monoidal functor underlying the
identity strong monoidal functor is the colax monoidal identity functor. -/
@[simps!]
def MonoidalFunctor.toColax_id_iso_id :
    (MonoidalFunctor.toColax C C).obj (.id C) ≅ ColaxMonoidalFunctor.id C := Iso.refl _

variable {C D}

/-- The isomorphism witnessing that the lax monoidal functor underlying the
composition of strong monoidal functor is the composition of the
underlying lax monoidal functors. -/
@[simps!]
def MonoidalFunctor.toLax_comp_iso_comp (F : C ⥤⊗s D) (G : D ⥤⊗s E) :
    (MonoidalFunctor.toLax C E).obj (F ⊗⋙ G) ≅
      (MonoidalFunctor.toLax C D).obj F ⊗⋙ (MonoidalFunctor.toLax D E).obj G :=
  Iso.refl _

/-- The isomorphism witnessing that the colax monoidal functor underlying the
composition of strong monoidal functor is the composition of the
underlying colax monoidal functors. -/
@[simps!]
def MonoidalFunctor.toColax_comp_iso_comp (F : C ⥤⊗s D)
    (G : MonoidalFunctor D E) :
    (MonoidalFunctor.toColax C E).obj (F ⊗⋙ G) ≅
      (MonoidalFunctor.toColax C D).obj F ⊗⋙ (MonoidalFunctor.toColax D E).obj G :=
  Iso.refl _

namespace MonoidalSq

@[simps! constraint]
def vcomp {F : B ⥤⊗ℓ C} {G : B ⥤⊗c D} {H : C ⥤⊗c E} {K : D ⥤⊗ℓ E}
    {I : D ⥤⊗c M} {J : E ⥤⊗c N} {L : M ⥤⊗ℓ N}
    (α : MonoidalSq F G H K) (β : MonoidalSq K I J L) :
    MonoidalSq F (G ⊗⋙ I) (H ⊗⋙ J) L where
  trapezoid' := by
    dsimp
    simp_rw [comp_id, id_comp, map_comp, assoc, ← β.naturality_assoc,
            ← J.map_comp_assoc, trapezoid, J.map_comp_assoc, trapezoid]
  hexagon' := fun X Y => by
    dsimp
    simp only [comp_id, id_comp, map_comp, assoc, tensor_comp]
    simp_rw [← β.naturality_assoc, ← J.map_comp_assoc, α.hexagon_components,
            J.map_comp_assoc, β.hexagon_components]
    erw [J.δ_natural_assoc]
  __ := α.toCatColaxSq.vComp β.toCatColaxSq

@[simps! constraint]
def hcomp {F : B ⥤⊗ℓ C} {G : B ⥤⊗c D} {H : C ⥤⊗c E} {K : D ⥤⊗ℓ E}
    {I : C ⥤⊗ℓ M} {J : M ⥤⊗c N} {L : E ⥤⊗ℓ N}
    (α : MonoidalSq F G H K) (β : MonoidalSq I H J L) :
    MonoidalSq (F ⊗⋙ I) G J (K ⊗⋙ L) where
  trapezoid' := by
    dsimp
    simp only [map_comp, comp_id, id_comp, assoc]
    rw [β.naturality_assoc, ← L.map_comp, ← L.map_comp, trapezoid,
        L.map_comp, trapezoid_assoc]
  hexagon' := fun X Y => by
    dsimp
    simp only [map_comp, comp_id, id_comp, assoc, tensor_comp,
              LaxMonoidalFunctor.μ_natural_assoc]
    simp_rw [β.naturality_assoc, ← L.map_comp, hexagon_components,
            L.map_comp, hexagon_components_assoc]
  __ := α.toCatColaxSq.hComp β.toCatColaxSq

end MonoidalSq

end CategoryTheory
