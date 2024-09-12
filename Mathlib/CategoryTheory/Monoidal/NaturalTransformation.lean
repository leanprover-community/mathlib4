/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.FullSubcategory

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
section

open SemigroupalCategory

variable {C : Type u₁} [Category.{v₁} C] [SemigroupalCategory.{v₁} C] {D : Type u₂}
  [Category.{v₂} D] [SemigroupalCategory.{v₂} D]

/-- A semigroupal natural transformation is a natural transformation between (lax) semigroupal functors
additionally satisfying:
`F.μ X Y ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ G.μ X Y`
-/
@[ext]
structure SemigroupalNatTrans (F G : LaxSemigroupalFunctor C D) extends
  NatTrans F.toFunctor G.toFunctor where
  /-- The tensor condition for a semigroupal natural transformation. -/
  tensor : ∀ X Y, F.μ _ _ ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ G.μ _ _ := by aesop_cat

-- Porting note: `reassoc (attr := simp)` seems to add a `simp`
-- attribute to the original lemma as well.
attribute [reassoc (attr := simp)] SemigroupalNatTrans.tensor

initialize_simps_projections SemigroupalNatTrans (+toNatTrans, -app)

namespace SemigroupalNatTrans

/-- The identity semigroupal natural transformation. -/
@[simps!]
def id (F : LaxSemigroupalFunctor C D) : SemigroupalNatTrans F F :=
  { 𝟙 F.toFunctor with }

instance (F : LaxSemigroupalFunctor C D) : Inhabited (SemigroupalNatTrans F F) :=
  ⟨id F⟩

/-- Vertical composition of semigroupal natural transformations. -/
@[simps!]
def vcomp {F G H : LaxSemigroupalFunctor C D}
    (α : SemigroupalNatTrans F G) (β : SemigroupalNatTrans G H) :
    SemigroupalNatTrans F H :=
  { NatTrans.vcomp α.toNatTrans β.toNatTrans with }

instance categoryLaxSemigroupalFunctor : Category (LaxSemigroupalFunctor C D) where
  Hom := SemigroupalNatTrans
  id := id
  comp α β := vcomp α β

@[simp]
theorem comp_toNatTrans_lax {F G H : LaxSemigroupalFunctor C D} {α : F ⟶ G} {β : G ⟶ H} :
    (α ≫ β).toNatTrans = @CategoryStruct.comp (C ⥤ D) _ _ _ _ α.toNatTrans β.toNatTrans :=
  rfl

instance categorySemigroupalFunctor : Category (SemigroupalFunctor C D) :=
  InducedCategory.category SemigroupalFunctor.toLaxSemigroupalFunctor

-- Porting note: added, as `SemigroupalNatTrans.ext` does not apply to morphisms.
@[ext]
lemma ext' {F G : LaxSemigroupalFunctor C D} {α β : F ⟶ G}
    (w : ∀ X : C, α.app X = β.app X) : α = β :=
  SemigroupalNatTrans.ext (funext w)

@[simp]
theorem comp_toNatTrans {F G H : SemigroupalFunctor C D} {α : F ⟶ G} {β : G ⟶ H} :
    (α ≫ β).toNatTrans = @CategoryStruct.comp (C ⥤ D) _ _ _ _ α.toNatTrans β.toNatTrans :=
  rfl

variable {E : Type u₃} [Category.{v₃} E] [SemigroupalCategory.{v₃} E]

/-- Horizontal composition of semigroupal natural transformations. -/
@[simps]
def hcomp {F G : LaxSemigroupalFunctor C D}
    {H K : LaxSemigroupalFunctor D E} (α : SemigroupalNatTrans F G)
    (β : SemigroupalNatTrans H K) : SemigroupalNatTrans (F ⊗⋙ H) (G ⊗⋙ K) :=
  { NatTrans.hcomp α.toNatTrans β.toNatTrans with
    tensor := fun X Y => by
      dsimp; simp
      conv_lhs => rw [← K.toFunctor.map_comp, α.tensor, K.toFunctor.map_comp] }

section

attribute [local simp] NatTrans.naturality SemigroupalNatTrans.tensor

/-- The cartesian product of two semigroupal natural transformations is semigroupal. -/
@[simps]
def prod {F G : LaxSemigroupalFunctor C D} {H K : LaxSemigroupalFunctor C E}
    (α : SemigroupalNatTrans F G) (β : SemigroupalNatTrans H K) :
    SemigroupalNatTrans (F.prod' H) (G.prod' K) where
  app X := (α.app X, β.app X)

end

end SemigroupalNatTrans

namespace SemigroupalNatIso

variable {F G : LaxSemigroupalFunctor C D}

/-- Construct a semigroupal natural isomorphism from object level isomorphisms,
and the semigroupal naturality in the forward direction. -/
def ofComponents (app : ∀ X : C, F.obj X ≅ G.obj X)
    (naturality' :
      ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (app Y).hom = (app X).hom ≫ G.map f := by aesop_cat)
    (tensor' :
      ∀ X Y, F.μ X Y ≫ (app (X ⊗ Y)).hom = ((app X).hom ⊗ (app Y).hom) ≫ G.μ X Y := by aesop_cat) :
    F ≅ G where
  hom := { app := fun X => (app X).hom }
  inv := {
    (NatIso.ofComponents app @naturality').inv with
    app := fun X => (app X).inv
    tensor := fun X Y => by
      dsimp
      rw [Iso.comp_inv_eq, assoc, tensor', ← tensor_comp_assoc,
        Iso.inv_hom_id, Iso.inv_hom_id, tensor_id, id_comp] }

@[simp]
theorem ofComponents.hom_app (app : ∀ X : C, F.obj X ≅ G.obj X) (naturality) (tensor) (X) :
    (ofComponents app naturality tensor).hom.app X = (app X).hom :=
  rfl

@[simp]
theorem ofComponents.inv_app (app : ∀ X : C, F.obj X ≅ G.obj X) (naturality) (tensor) (X) :
    (ofComponents app naturality tensor).inv.app X = (app X).inv := by simp [ofComponents]

instance isIso_of_isIso_app (α : F ⟶ G) [∀ X : C, IsIso (α.app X)] : IsIso α :=
  (ofComponents (fun X => asIso (α.app X)) (fun f => α.toNatTrans.naturality f) α.tensor).isIso_hom

end SemigroupalNatIso

variable (F : SemigroupalFunctor C D) {G : D ⥤ C} (h : F.toFunctor ⊣ G)

/-- The unit of a adjunction can be upgraded to a semigroupal natural transformation. -/
def semigroupalUnit  :
    LaxSemigroupalFunctor.id C ⟶ F.toLaxSemigroupalFunctor ⊗⋙ (semigroupalAdjoint F h) where
  toNatTrans := h.unit
  tensor X Y := by
    dsimp
    simp only [id_comp, comp_id, assoc, Adjunction.homEquiv_unit,
      ← h.unit_naturality_assoc, ← Functor.map_comp,
      F.map_tensor, IsIso.hom_inv_id_assoc, ← tensor_comp_assoc,
      Adjunction.left_triangle_components, tensorHom_id, id_whiskerRight,
      IsIso.inv_hom_id, map_id]

/-- The unit of a adjunction can be upgraded to a semigroupal natural transformation. -/
@[simps]
def semigroupalCounit :
    (semigroupalAdjoint F h) ⊗⋙ F.toLaxSemigroupalFunctor ⟶ LaxSemigroupalFunctor.id D where
  toNatTrans := h.counit
  tensor X Y := by
    have eq := h.counit_naturality (F.μ (G.obj X) (G.obj Y)) =≫ inv (F.μ _ _)
    simp only [assoc, IsIso.hom_inv_id, comp_id] at eq
    dsimp
    simp only [Adjunction.homEquiv_unit, comp_id, assoc,
      map_comp, map_inv, h.counit_naturality, ← eq,
      h.left_triangle_components_assoc,
      IsIso.inv_hom_id_assoc, IsIso.hom_inv_id_assoc]

instance [F.IsEquivalence] : IsIso (semigroupalUnit F h) := by
  dsimp [semigroupalUnit]
  infer_instance

instance [F.IsEquivalence] : IsIso (semigroupalCounit F h) := by
  dsimp [semigroupalCounit]
  infer_instance

end
open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [MonoidalCategory.{v₂} D]

/-- A monoidal natural transformation is a natural transformation between (lax) monoidal functors
additionally satisfying:
`F.μ X Y ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ G.μ X Y`
-/
@[ext]
structure MonoidalNatTrans (F G : LaxMonoidalFunctor C D) extends
    SemigroupalNatTrans F.1 G.1 where
  /-- The unit condition for a monoidal natural transformation. -/
  unit : F.ε ≫ app (𝟙_ C) = G.ε := by aesop_cat

-- Porting note: `reassoc (attr := simp)` seems to add a `simp`
-- attribute to the original lemma as well.
attribute [reassoc (attr := simp)] MonoidalNatTrans.unit

initialize_simps_projections MonoidalNatTrans (+toNatTrans, -app)

namespace MonoidalNatTrans

/-- The identity monoidal natural transformation. -/
@[simps!]
def id (F : LaxMonoidalFunctor C D) : MonoidalNatTrans F F :=
  { 𝟙 F.toFunctor with }

instance (F : LaxMonoidalFunctor C D) : Inhabited (MonoidalNatTrans F F) :=
  ⟨id F⟩

/-- Vertical composition of monoidal natural transformations. -/
@[simps!]
def vcomp {F G H : LaxMonoidalFunctor C D} (α : MonoidalNatTrans F G) (β : MonoidalNatTrans G H) :
    MonoidalNatTrans F H :=
  { NatTrans.vcomp α.toNatTrans β.toNatTrans with }

instance categoryLaxMonoidalFunctor : Category (LaxMonoidalFunctor C D) where
  Hom := MonoidalNatTrans
  id := id
  comp α β := vcomp α β

@[simp]
theorem comp_toNatTrans_lax {F G H : LaxMonoidalFunctor C D} {α : F ⟶ G} {β : G ⟶ H} :
    (α ≫ β).toNatTrans = @CategoryStruct.comp (C ⥤ D) _ _ _ _ α.toNatTrans β.toNatTrans :=
  rfl

instance categoryMonoidalFunctor : Category (MonoidalFunctor C D) :=
  InducedCategory.category MonoidalFunctor.toLaxMonoidalFunctor

-- Porting note: added, as `MonoidalNatTrans.ext` does not apply to morphisms.
@[ext]
lemma ext' {F G : LaxMonoidalFunctor C D} {α β : F ⟶ G} (w : ∀ X : C, α.app X = β.app X) : α = β :=
  MonoidalNatTrans.ext (funext w)

@[simp]
theorem comp_toNatTrans {F G H : MonoidalFunctor C D} {α : F ⟶ G} {β : G ⟶ H} :
    (α ≫ β).toNatTrans = @CategoryStruct.comp (C ⥤ D) _ _ _ _ α.toNatTrans β.toNatTrans :=
  rfl

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

section

attribute [local simp] NatTrans.naturality MonoidalNatTrans.unit

/-- The cartesian product of two monoidal natural transformations is monoidal. -/
@[simps]
def prod {F G : LaxMonoidalFunctor C D} {H K : LaxMonoidalFunctor C E} (α : MonoidalNatTrans F G)
    (β : MonoidalNatTrans H K) : MonoidalNatTrans (F.prod' H) (G.prod' K) where
  app X := (α.app X, β.app X)

end

end MonoidalNatTrans

namespace MonoidalNatIso

variable {F G : LaxMonoidalFunctor C D}

open SemigroupalCategory

/-- Construct a monoidal natural isomorphism from object level isomorphisms,
and the monoidal naturality in the forward direction. -/
def ofComponents (app : ∀ X : C, F.obj X ≅ G.obj X)
    (naturality' :
      ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (app Y).hom = (app X).hom ≫ G.map f := by aesop_cat)
    (unit' : F.ε ≫ (app (𝟙_ C)).hom = G.ε := by aesop_cat)
    (tensor' :
      ∀ X Y, F.μ X Y ≫ (app (X ⊗ Y)).hom = ((app X).hom ⊗ (app Y).hom) ≫ G.μ X Y := by aesop_cat) :
    F ≅ G where
  hom := { app := fun X => (app X).hom }
  inv := {
    (NatIso.ofComponents app @naturality').inv,
    (SemigroupalNatIso.ofComponents app naturality' tensor').inv with
    app := fun X => (app X).inv
    unit := by
      dsimp
      rw [← unit', assoc, Iso.hom_inv_id, comp_id] }

@[simp]
theorem ofComponents.hom_app (app : ∀ X : C, F.obj X ≅ G.obj X) (naturality) (unit) (tensor) (X) :
    (ofComponents app naturality unit tensor).hom.app X = (app X).hom :=
  rfl

@[simp]
theorem ofComponents.inv_app (app : ∀ X : C, F.obj X ≅ G.obj X) (naturality) (unit) (tensor) (X) :
    (ofComponents app naturality unit tensor).inv.app X = (app X).inv := by simp [ofComponents]

instance isIso_of_isIso_app (α : F ⟶ G) [∀ X : C, IsIso (α.app X)] : IsIso α :=
  (ofComponents (fun X => asIso (α.app X)) (fun f => α.toNatTrans.naturality f)
    α.unit α.tensor).isIso_hom

end MonoidalNatIso

variable (F : MonoidalFunctor C D) {G : D ⥤ C} (h : F.toFunctor ⊣ G)

/-- The unit of a adjunction can be upgraded to a monoidal natural transformation. -/
def monoidalUnit  :
    LaxMonoidalFunctor.id C ⟶ F.toLaxMonoidalFunctor ⊗⋙ (monoidalAdjoint F h) where
  toSemigroupalNatTrans := semigroupalUnit F.toSemigroupalFunctor h

/-- The unit of a adjunction can be upgraded to a monoidal natural transformation. -/
@[simps]
def monoidalCounit :
    (monoidalAdjoint F h) ⊗⋙ F.toLaxMonoidalFunctor ⟶ LaxMonoidalFunctor.id D :=
{ semigroupalCounit F.toSemigroupalFunctor h with
  toNatTrans := h.counit
  unit := by
    have eq := h.counit.naturality F.ε
    dsimp at eq ⊢
    rw [map_inv, map_comp, assoc, assoc, map_inv, ← cancel_mono F.ε, assoc, assoc, assoc, ← eq,
      IsIso.inv_hom_id_assoc, Adjunction.left_triangle_components, comp_id, id_comp] }

instance [F.IsEquivalence] : IsIso (monoidalUnit F h) := by
  dsimp [monoidalUnit, semigroupalUnit]
  infer_instance

instance [F.IsEquivalence] : IsIso (monoidalCounit F h) := by
  dsimp [monoidalCounit, semigroupalCounit]
  infer_instance

end CategoryTheory
