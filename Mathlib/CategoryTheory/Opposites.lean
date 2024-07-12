/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison
-/
import Mathlib.CategoryTheory.Equivalence

#align_import category_theory.opposites from "leanprover-community/mathlib"@"dde670c9a3f503647fd5bfdf1037bad526d3397a"

/-!
# Opposite categories

We provide a category instance on `Cᵒᵖ`.
The morphisms `X ⟶ Y` are defined to be the morphisms `unop Y ⟶ unop X` in `C`.

Here `Cᵒᵖ` is an irreducible typeclass synonym for `C`
(it is the same one used in the algebra library).

We also provide various mechanisms for constructing opposite morphisms, functors,
and natural transformations.

Unfortunately, because we do not have a definitional equality `op (op X) = X`,
there are quite a few variations that are needed in practice.
-/

universe v₁ v₂ u₁ u₂

-- morphism levels before object levels. See note [CategoryTheory universes].
open Opposite

variable {C : Type u₁}

section Quiver

variable [Quiver.{v₁} C]

theorem Quiver.Hom.op_inj {X Y : C} :
    Function.Injective (Quiver.Hom.op : (X ⟶ Y) → (Opposite.op Y ⟶ Opposite.op X)) := fun _ _ H =>
  congr_arg Quiver.Hom.unop H
#align quiver.hom.op_inj Quiver.Hom.op_inj

theorem Quiver.Hom.unop_inj {X Y : Cᵒᵖ} :
    Function.Injective (Quiver.Hom.unop : (X ⟶ Y) → (Opposite.unop Y ⟶ Opposite.unop X)) :=
  fun _ _ H => congr_arg Quiver.Hom.op H
#align quiver.hom.unop_inj Quiver.Hom.unop_inj

@[simp]
theorem Quiver.Hom.unop_op {X Y : C} (f : X ⟶ Y) : f.op.unop = f :=
  rfl
#align quiver.hom.unop_op Quiver.Hom.unop_op

@[simp]
theorem Quiver.Hom.unop_op' {X Y : Cᵒᵖ} {x} :
    @Quiver.Hom.unop C _ X Y no_index (Opposite.op (unop := x)) = x := rfl

@[simp]
theorem Quiver.Hom.op_unop {X Y : Cᵒᵖ} (f : X ⟶ Y) : f.unop.op = f :=
  rfl
#align quiver.hom.op_unop Quiver.Hom.op_unop

@[simp] theorem Quiver.Hom.unop_mk {X Y : Cᵒᵖ} (f : X ⟶ Y) : Quiver.Hom.unop {unop := f} = f := rfl

end Quiver

namespace CategoryTheory

variable [Category.{v₁} C]

/-- The opposite category.

See <https://stacks.math.columbia.edu/tag/001M>.
-/
instance Category.opposite : Category.{v₁} Cᵒᵖ where
  comp f g := (g.unop ≫ f.unop).op
  id X := (𝟙 (unop X)).op
#align category_theory.category.opposite CategoryTheory.Category.opposite

@[simp, reassoc]
theorem op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g).op = g.op ≫ f.op :=
  rfl
#align category_theory.op_comp CategoryTheory.op_comp

@[simp]
theorem op_id {X : C} : (𝟙 X).op = 𝟙 (op X) :=
  rfl
#align category_theory.op_id CategoryTheory.op_id

@[simp, reassoc]
theorem unop_comp {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g).unop = g.unop ≫ f.unop :=
  rfl
#align category_theory.unop_comp CategoryTheory.unop_comp

@[simp]
theorem unop_id {X : Cᵒᵖ} : (𝟙 X).unop = 𝟙 (unop X) :=
  rfl
#align category_theory.unop_id CategoryTheory.unop_id

@[simp]
theorem unop_id_op {X : C} : (𝟙 (op X)).unop = 𝟙 X :=
  rfl
#align category_theory.unop_id_op CategoryTheory.unop_id_op

@[simp]
theorem op_id_unop {X : Cᵒᵖ} : (𝟙 (unop X)).op = 𝟙 X :=
  rfl
#align category_theory.op_id_unop CategoryTheory.op_id_unop

section

variable (C)

/-- The functor from the double-opposite of a category to the underlying category. -/
@[simps]
def unopUnop : Cᵒᵖᵒᵖ ⥤ C where
  obj X := unop (unop X)
  map f := f.unop.unop
#align category_theory.op_op CategoryTheory.unopUnop

/-- The functor from a category to its double-opposite.  -/
@[simps]
def opOp : C ⥤ Cᵒᵖᵒᵖ where
  obj X := op (op X)
  map f := f.op.op
#align category_theory.unop_unop CategoryTheory.opOp

/-- The double opposite category is equivalent to the original. -/
@[simps]
def opOpEquivalence : Cᵒᵖᵒᵖ ≌ C where
  functor := unopUnop C
  inverse := opOp C
  unitIso := Iso.refl (𝟭 Cᵒᵖᵒᵖ)
  counitIso := Iso.refl (opOp C ⋙ unopUnop C)
#align category_theory.op_op_equivalence CategoryTheory.opOpEquivalence

end

/-- If `f` is an isomorphism, so is `f.op` -/
instance isIso_op {X Y : C} (f : X ⟶ Y) [IsIso f] : IsIso f.op :=
  ⟨⟨(inv f).op, ⟨Quiver.Hom.unop_inj (by aesop_cat), Quiver.Hom.unop_inj (by aesop_cat)⟩⟩⟩
#align category_theory.is_iso_op CategoryTheory.isIso_op

/-- If `f.op` is an isomorphism `f` must be too.
(This cannot be an instance as it would immediately loop!)
-/
theorem isIso_of_op {X Y : C} (f : X ⟶ Y) [IsIso f.op] : IsIso f :=
  ⟨⟨(inv f.op).unop, ⟨Quiver.Hom.op_inj (by simp), Quiver.Hom.op_inj (by simp)⟩⟩⟩
#align category_theory.is_iso_of_op CategoryTheory.isIso_of_op

theorem isIso_op_iff {X Y : C} (f : X ⟶ Y) : IsIso f.op ↔ IsIso f :=
  ⟨fun _ => isIso_of_op _, fun _ => inferInstance⟩
#align category_theory.is_iso_op_iff CategoryTheory.isIso_op_iff

theorem isIso_unop_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) : IsIso f.unop ↔ IsIso f := by
  rw [← isIso_op_iff f.unop, Quiver.Hom.op_unop]
#align category_theory.is_iso_unop_iff CategoryTheory.isIso_unop_iff

instance isIso_unop {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso f] : IsIso f.unop :=
  (isIso_unop_iff _).2 inferInstance
#align category_theory.is_iso_unop CategoryTheory.isIso_unop

@[simp]
theorem op_inv {X Y : C} (f : X ⟶ Y) [IsIso f] : (inv f).op = inv f.op := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← op_comp, IsIso.inv_hom_id, op_id]
#align category_theory.op_inv CategoryTheory.op_inv

@[simp]
theorem unop_inv {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso f] : (inv f).unop = inv f.unop := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← unop_comp, IsIso.inv_hom_id, unop_id]
#align category_theory.unop_inv CategoryTheory.unop_inv

namespace Functor

section

variable {D : Type u₂} [Category.{v₂} D]

/-- The opposite of a functor, i.e. considering a functor `F : C ⥤ D` as a functor `Cᵒᵖ ⥤ Dᵒᵖ`.
In informal mathematics no distinction is made between these. -/
@[simps]
protected def op (F : C ⥤ D) : Cᵒᵖ ⥤ Dᵒᵖ where
  obj X := op (F.obj (unop X))
  map f := (F.map f.unop).op
#align category_theory.functor.op CategoryTheory.Functor.op

/-- Given a functor `F : Cᵒᵖ ⥤ Dᵒᵖ` we can take the "unopposite" functor `F : C ⥤ D`.
In informal mathematics no distinction is made between these.
-/
@[simps]
protected def unop (F : Cᵒᵖ ⥤ Dᵒᵖ) : C ⥤ D where
  obj X := unop (F.obj (op X))
  map f := (F.map f.op).unop
#align category_theory.functor.unop CategoryTheory.Functor.unop

/-- The isomorphism between `F.op.unop` and `F`. -/
@[simps!]
def opUnopIso (F : C ⥤ D) : F.op.unop ≅ F :=
  NatIso.ofComponents fun X => Iso.refl _
#align category_theory.functor.op_unop_iso CategoryTheory.Functor.opUnopIso

/-- The isomorphism between `F.unop.op` and `F`. -/
@[simps!]
def unopOpIso (F : Cᵒᵖ ⥤ Dᵒᵖ) : F.unop.op ≅ F :=
  NatIso.ofComponents fun X => Iso.refl _
#align category_theory.functor.unop_op_iso CategoryTheory.Functor.unopOpIso

variable (C D)

/-- Taking the opposite of a functor is functorial.
-/
@[simps]
def opHom : (C ⥤ D)ᵒᵖ ⥤ Cᵒᵖ ⥤ Dᵒᵖ where
  obj F := (unop F).op
  map α :=
    { app := fun X => (α.unop.app (unop X)).op
      naturality := fun X Y f => Quiver.Hom.unop_inj (α.unop.naturality f.unop).symm }
#align category_theory.functor.op_hom CategoryTheory.Functor.opHom

/-- Take the "unopposite" of a functor is functorial.
-/
@[simps]
def opInv : (Cᵒᵖ ⥤ Dᵒᵖ) ⥤ (C ⥤ D)ᵒᵖ where
  obj F := op F.unop
  map α :=
    Quiver.Hom.op
      { app := fun X => (α.app (op X)).unop
        naturality := fun X Y f => Quiver.Hom.op_inj <| (α.naturality f.op).symm }
#align category_theory.functor.op_inv CategoryTheory.Functor.opInv

variable {C D}

/--
Another variant of the opposite of functor, turning a functor `C ⥤ Dᵒᵖ` into a functor `Cᵒᵖ ⥤ D`.
In informal mathematics no distinction is made.
-/
@[simps]
protected def leftOp (F : C ⥤ Dᵒᵖ) : Cᵒᵖ ⥤ D where
  obj X := unop (F.obj (unop X))
  map f := (F.map f.unop).unop
#align category_theory.functor.left_op CategoryTheory.Functor.leftOp

/--
Another variant of the opposite of functor, turning a functor `Cᵒᵖ ⥤ D` into a functor `C ⥤ Dᵒᵖ`.
In informal mathematics no distinction is made.
-/
@[simps]
protected def rightOp (F : Cᵒᵖ ⥤ D) : C ⥤ Dᵒᵖ where
  obj X := op (F.obj (op X))
  map f := (F.map f.op).op
#align category_theory.functor.right_op CategoryTheory.Functor.rightOp

lemma rightOp_map_unop {F : Cᵒᵖ ⥤ D} {X Y} (f : X ⟶ Y) :
    (F.rightOp.map f).unop = F.map f.op := rfl

instance {F : C ⥤ D} [Full F] : Full F.op where
  map_surjective f := ⟨(F.preimage f.unop).op, by simp⟩

instance {F : C ⥤ D} [Faithful F] : Faithful F.op where
  map_injective h := Quiver.Hom.unop_inj <| by simpa using map_injective F (Quiver.Hom.op_inj h)

/-- If F is faithful then the right_op of F is also faithful. -/
instance rightOp_faithful {F : Cᵒᵖ ⥤ D} [Faithful F] : Faithful F.rightOp where
  map_injective h := Quiver.Hom.op_inj (map_injective F (Quiver.Hom.op_inj h))
#align category_theory.functor.right_op_faithful CategoryTheory.Functor.rightOp_faithful

/-- If F is faithful then the left_op of F is also faithful. -/
instance leftOp_faithful {F : C ⥤ Dᵒᵖ} [Faithful F] : Faithful F.leftOp where
  map_injective h := Quiver.Hom.unop_inj (map_injective F (Quiver.Hom.unop_inj h))
#align category_theory.functor.left_op_faithful CategoryTheory.Functor.leftOp_faithful

instance rightOp_full {F : Cᵒᵖ ⥤ D} [Full F] : Full F.rightOp where
  map_surjective f := ⟨(F.preimage f.unop).unop, by simp⟩

instance leftOp_full {F : C ⥤ Dᵒᵖ} [Full F] : Full F.leftOp where
  map_surjective f := ⟨(F.preimage f.op).op, by simp⟩


/-- The isomorphism between `F.leftOp.rightOp` and `F`. -/
@[simps!]
def leftOpRightOpIso (F : C ⥤ Dᵒᵖ) : F.leftOp.rightOp ≅ F :=
  NatIso.ofComponents fun X => Iso.refl _
#align category_theory.functor.left_op_right_op_iso CategoryTheory.Functor.leftOpRightOpIso

/-- The isomorphism between `F.rightOp.leftOp` and `F`. -/
@[simps!]
def rightOpLeftOpIso (F : Cᵒᵖ ⥤ D) : F.rightOp.leftOp ≅ F :=
  NatIso.ofComponents fun X => Iso.refl _
#align category_theory.functor.right_op_left_op_iso CategoryTheory.Functor.rightOpLeftOpIso

/-- Whenever possible, it is advisable to use the isomorphism `rightOpLeftOpIso`
instead of this equality of functors. -/
theorem rightOp_leftOp_eq (F : Cᵒᵖ ⥤ D) : F.rightOp.leftOp = F := by
  cases F
  rfl
#align category_theory.functor.right_op_left_op_eq CategoryTheory.Functor.rightOp_leftOp_eq

end

end Functor

namespace NatTrans

variable {D : Type u₂} [Category.{v₂} D]

section

variable {F G : C ⥤ D}

/-- The opposite of a natural transformation. -/
@[simps]
protected def op (α : F ⟶ G) : G.op ⟶ F.op where
  app X := (α.app (unop X)).op
  naturality X Y f := Quiver.Hom.unop_inj (by simp)
#align category_theory.nat_trans.op CategoryTheory.NatTrans.op

@[simp]
theorem op_id (F : C ⥤ D) : NatTrans.op (𝟙 F) = 𝟙 F.op :=
  rfl
#align category_theory.nat_trans.op_id CategoryTheory.NatTrans.op_id

/-- The "unopposite" of a natural transformation. -/
@[simps]
protected def unop {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ⟶ G) : G.unop ⟶ F.unop where
  app X := (α.app (op X)).unop
  naturality X Y f := Quiver.Hom.op_inj (by simp)
#align category_theory.nat_trans.unop CategoryTheory.NatTrans.unop

@[simp]
theorem unop_id (F : Cᵒᵖ ⥤ Dᵒᵖ) : NatTrans.unop (𝟙 F) = 𝟙 F.unop :=
  rfl
#align category_theory.nat_trans.unop_id CategoryTheory.NatTrans.unop_id

/-- Given a natural transformation `α : F.op ⟶ G.op`,
we can take the "unopposite" of each component obtaining a natural transformation `G ⟶ F`.
-/
@[simps]
protected def removeOp (α : F.op ⟶ G.op) : G ⟶ F where
  app X := (α.app (op X)).unop
  naturality X Y f :=
    Quiver.Hom.op_inj <| by simpa only [Functor.op_map] using (α.naturality f.op).symm
#align category_theory.nat_trans.remove_op CategoryTheory.NatTrans.removeOp

@[simp]
theorem removeOp_id (F : C ⥤ D) : NatTrans.removeOp (𝟙 F.op) = 𝟙 F :=
  rfl
#align category_theory.nat_trans.remove_op_id CategoryTheory.NatTrans.removeOp_id

/-- Given a natural transformation `α : F.unop ⟶ G.unop`, we can take the opposite of each
component obtaining a natural transformation `G ⟶ F`. -/
@[simps]
protected def removeUnop {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F.unop ⟶ G.unop) : G ⟶ F where
  app X := (α.app (unop X)).op
  naturality X Y f :=
    Quiver.Hom.unop_inj <| by simpa only [Functor.unop_map] using (α.naturality f.unop).symm
#align category_theory.nat_trans.remove_unop CategoryTheory.NatTrans.removeUnop

@[simp]
theorem removeUnop_id (F : Cᵒᵖ ⥤ Dᵒᵖ) : NatTrans.removeUnop (𝟙 F.unop) = 𝟙 F :=
  rfl
#align category_theory.nat_trans.remove_unop_id CategoryTheory.NatTrans.removeUnop_id

end

section

variable {F G H : C ⥤ Dᵒᵖ}

/-- Given a natural transformation `α : F ⟶ G`, for `F G : C ⥤ Dᵒᵖ`,
taking `unop` of each component gives a natural transformation `G.leftOp ⟶ F.leftOp`.
-/
@[simps]
protected def leftOp (α : F ⟶ G) : G.leftOp ⟶ F.leftOp where
  app X := (α.app (unop X)).unop
  naturality X Y f := Quiver.Hom.op_inj (by simp)
#align category_theory.nat_trans.left_op CategoryTheory.NatTrans.leftOp

@[simp]
theorem leftOp_id : NatTrans.leftOp (𝟙 F : F ⟶ F) = 𝟙 F.leftOp :=
  rfl
#align category_theory.nat_trans.left_op_id CategoryTheory.NatTrans.leftOp_id

@[simp]
theorem leftOp_comp (α : F ⟶ G) (β : G ⟶ H) : NatTrans.leftOp (α ≫ β) =
    NatTrans.leftOp β ≫ NatTrans.leftOp α :=
  rfl
#align category_theory.nat_trans.left_op_comp CategoryTheory.NatTrans.leftOp_comp

/-- Given a natural transformation `α : F.leftOp ⟶ G.leftOp`, for `F G : C ⥤ Dᵒᵖ`,
taking `op` of each component gives a natural transformation `G ⟶ F`.
-/
@[simps]
protected def removeLeftOp (α : F.leftOp ⟶ G.leftOp) : G ⟶ F where
  app X := (α.app (op X)).op
  naturality X Y f :=
    Quiver.Hom.unop_inj <| by simpa only [Functor.leftOp_map] using (α.naturality f.op).symm
#align category_theory.nat_trans.remove_left_op CategoryTheory.NatTrans.removeLeftOp

@[simp]
theorem removeLeftOp_id : NatTrans.removeLeftOp (𝟙 F.leftOp) = 𝟙 F :=
  rfl
#align category_theory.nat_trans.remove_left_op_id CategoryTheory.NatTrans.removeLeftOp_id

end

section

variable {F G H : Cᵒᵖ ⥤ D}

/-- Given a natural transformation `α : F ⟶ G`, for `F G : Cᵒᵖ ⥤ D`,
taking `op` of each component gives a natural transformation `G.rightOp ⟶ F.rightOp`.
-/
@[simps]
protected def rightOp (α : F ⟶ G) : G.rightOp ⟶ F.rightOp where
  app X := (α.app _).op
  naturality X Y f := Quiver.Hom.unop_inj (by simp)
#align category_theory.nat_trans.right_op CategoryTheory.NatTrans.rightOp

@[simp]
theorem rightOp_id : NatTrans.rightOp (𝟙 F : F ⟶ F) = 𝟙 F.rightOp :=
  rfl
#align category_theory.nat_trans.right_op_id CategoryTheory.NatTrans.rightOp_id

@[simp]
theorem rightOp_comp (α : F ⟶ G) (β : G ⟶ H) : NatTrans.rightOp (α ≫ β) =
    NatTrans.rightOp β ≫ NatTrans.rightOp α :=
  rfl
#align category_theory.nat_trans.right_op_comp CategoryTheory.NatTrans.rightOp_comp

/-- Given a natural transformation `α : F.rightOp ⟶ G.rightOp`, for `F G : Cᵒᵖ ⥤ D`,
taking `unop` of each component gives a natural transformation `G ⟶ F`.
-/
@[simps]
protected def removeRightOp (α : F.rightOp ⟶ G.rightOp) : G ⟶ F where
  app X := (α.app X.unop).unop
  naturality X Y f :=
    Quiver.Hom.op_inj <| by simpa only [Functor.rightOp_map] using (α.naturality f.unop).symm
#align category_theory.nat_trans.remove_right_op CategoryTheory.NatTrans.removeRightOp

@[simp]
theorem removeRightOp_id : NatTrans.removeRightOp (𝟙 F.rightOp) = 𝟙 F :=
  rfl
#align category_theory.nat_trans.remove_right_op_id CategoryTheory.NatTrans.removeRightOp_id

end

end NatTrans

namespace Iso

variable {X Y : C}

/-- The opposite isomorphism.
-/
@[simps]
protected def op (α : X ≅ Y) : op Y ≅ op X where
  hom := α.hom.op
  inv := α.inv.op
  hom_inv_id := Quiver.Hom.unop_inj α.inv_hom_id
  inv_hom_id := Quiver.Hom.unop_inj α.hom_inv_id
#align category_theory.iso.op CategoryTheory.Iso.op

/-- The isomorphism obtained from an isomorphism in the opposite category. -/
@[simps]
def unop {X Y : Cᵒᵖ} (f : X ≅ Y) : Y.unop ≅ X.unop where
  hom := f.hom.unop
  inv := f.inv.unop
  hom_inv_id := by simp only [← unop_comp, f.inv_hom_id, unop_id]
  inv_hom_id := by simp only [← unop_comp, f.hom_inv_id, unop_id]
#align category_theory.iso.unop CategoryTheory.Iso.unop

@[simp]
theorem unop_op {X Y : Cᵒᵖ} (f : X ≅ Y) : f.unop.op = f := by (ext; rfl)
#align category_theory.iso.unop_op CategoryTheory.Iso.unop_op

@[simp]
theorem op_unop {X Y : C} (f : X ≅ Y) : f.op.unop = f := by (ext; rfl)
#align category_theory.iso.op_unop CategoryTheory.Iso.op_unop

section

variable {D : Type*} [Category D] {F G : C ⥤ Dᵒᵖ} (e : F ≅ G) (X : C)

@[reassoc (attr := simp)]
lemma unop_hom_inv_id_app : (e.hom.app X).unop ≫ (e.inv.app X).unop = 𝟙 _ := by
  rw [← unop_comp, inv_hom_id_app, unop_id]

@[reassoc (attr := simp)]
lemma unop_inv_hom_id_app : (e.inv.app X).unop ≫ (e.hom.app X).unop = 𝟙 _ := by
  rw [← unop_comp, hom_inv_id_app, unop_id]

end

end Iso

namespace NatIso

variable {D : Type u₂} [Category.{v₂} D]
variable {F G : C ⥤ D}

/-- The natural isomorphism between opposite functors `G.op ≅ F.op` induced by a natural
isomorphism between the original functors `F ≅ G`. -/
@[simps]
protected def op (α : F ≅ G) : G.op ≅ F.op where
  hom := NatTrans.op α.hom
  inv := NatTrans.op α.inv
  hom_inv_id := by ext; dsimp; rw [← op_comp]; rw [α.inv_hom_id_app]; rfl
  inv_hom_id := by ext; dsimp; rw [← op_comp]; rw [α.hom_inv_id_app]; rfl
#align category_theory.nat_iso.op CategoryTheory.NatIso.op

/-- The natural isomorphism between functors `G ≅ F` induced by a natural isomorphism
between the opposite functors `F.op ≅ G.op`. -/
@[simps]
protected def removeOp (α : F.op ≅ G.op) : G ≅ F where
  hom := NatTrans.removeOp α.hom
  inv := NatTrans.removeOp α.inv
#align category_theory.nat_iso.remove_op CategoryTheory.NatIso.removeOp

/-- The natural isomorphism between functors `G.unop ≅ F.unop` induced by a natural isomorphism
between the original functors `F ≅ G`. -/
@[simps]
protected def unop {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ≅ G) : G.unop ≅ F.unop where
  hom := NatTrans.unop α.hom
  inv := NatTrans.unop α.inv
#align category_theory.nat_iso.unop CategoryTheory.NatIso.unop

end NatIso

namespace Equivalence

variable {D : Type u₂} [Category.{v₂} D]

/-- An equivalence between categories gives an equivalence between the opposite categories.
-/
@[simps]
def op (e : C ≌ D) : Cᵒᵖ ≌ Dᵒᵖ where
  functor := e.functor.op
  inverse := e.inverse.op
  unitIso := (NatIso.op e.unitIso).symm
  counitIso := (NatIso.op e.counitIso).symm
  functor_unitIso_comp X := by
    apply Quiver.Hom.unop_inj
    dsimp
    simp
#align category_theory.equivalence.op CategoryTheory.Equivalence.op

/-- An equivalence between opposite categories gives an equivalence between the original categories.
-/
@[simps]
def unop (e : Cᵒᵖ ≌ Dᵒᵖ) : C ≌ D where
  functor := e.functor.unop
  inverse := e.inverse.unop
  unitIso := (NatIso.unop e.unitIso).symm
  counitIso := (NatIso.unop e.counitIso).symm
  functor_unitIso_comp X := by
    apply Quiver.Hom.op_inj
    dsimp
    simp
#align category_theory.equivalence.unop CategoryTheory.Equivalence.unop

end Equivalence

/-- The equivalence between arrows of the form `A ⟶ B` and `B.unop ⟶ A.unop`. Useful for building
adjunctions.
Note that this (definitionally) gives variants
```
def opEquiv' (A : C) (B : Cᵒᵖ) : (Opposite.op A ⟶ B) ≃ (B.unop ⟶ A) :=
  opEquiv _ _

def opEquiv'' (A : Cᵒᵖ) (B : C) : (A ⟶ Opposite.op B) ≃ (B ⟶ A.unop) :=
  opEquiv _ _

def opEquiv''' (A B : C) : (Opposite.op A ⟶ Opposite.op B) ≃ (B ⟶ A) :=
  opEquiv _ _
```
-/
@[simps]
def opEquiv (A B : Cᵒᵖ) : (A ⟶ B) ≃ (B.unop ⟶ A.unop) where
  toFun f := f.unop
  invFun g := g.op
  left_inv _ := rfl
  right_inv _ := rfl
#align category_theory.op_equiv CategoryTheory.opEquiv

instance subsingleton_of_unop (A B : Cᵒᵖ) [Subsingleton (unop B ⟶ unop A)] : Subsingleton (A ⟶ B) :=
  (opEquiv A B).subsingleton
#align category_theory.subsingleton_of_unop CategoryTheory.subsingleton_of_unop

instance decidableEqOfUnop (A B : Cᵒᵖ) [DecidableEq (unop B ⟶ unop A)] : DecidableEq (A ⟶ B) :=
  (opEquiv A B).decidableEq
#align category_theory.decidable_eq_of_unop CategoryTheory.decidableEqOfUnop

/-- The equivalence between isomorphisms of the form `A ≅ B` and `B.unop ≅ A.unop`.

Note this is definitionally the same as the other three variants:
* `(Opposite.op A ≅ B) ≃ (B.unop ≅ A)`
* `(A ≅ Opposite.op B) ≃ (B ≅ A.unop)`
* `(Opposite.op A ≅ Opposite.op B) ≃ (B ≅ A)`
-/
@[simps]
def isoOpEquiv (A B : Cᵒᵖ) : (A ≅ B) ≃ (B.unop ≅ A.unop) where
  toFun f := f.unop
  invFun g := g.op
  left_inv _ := by
    ext
    rfl
  right_inv _ := by
    ext
    rfl
#align category_theory.iso_op_equiv CategoryTheory.isoOpEquiv

namespace Functor

variable (C)
variable (D : Type u₂) [Category.{v₂} D]

/-- The equivalence of functor categories induced by `op` and `unop`.
-/
@[simps]
def opUnopEquiv : (C ⥤ D)ᵒᵖ ≌ Cᵒᵖ ⥤ Dᵒᵖ where
  functor := opHom _ _
  inverse := opInv _ _
  unitIso :=
    NatIso.ofComponents (fun F => F.unop.opUnopIso.op)
      (by
        intro F G f
        dsimp [opUnopIso]
        rw [show f = f.unop.op by simp, ← op_comp, ← op_comp]
        congr 1
        aesop_cat)
  counitIso := NatIso.ofComponents fun F => F.unopOpIso
#align category_theory.functor.op_unop_equiv CategoryTheory.Functor.opUnopEquiv

/-- The equivalence of functor categories induced by `leftOp` and `rightOp`.
-/
@[simps!]
def leftOpRightOpEquiv : (Cᵒᵖ ⥤ D)ᵒᵖ ≌ C ⥤ Dᵒᵖ where
  functor :=
    { obj := fun F => F.unop.rightOp
      map := fun η => NatTrans.rightOp η.unop }
  inverse :=
    { obj := fun F => op F.leftOp
      map := fun η => η.leftOp.op }
  unitIso :=
    NatIso.ofComponents (fun F => F.unop.rightOpLeftOpIso.op)
      (by
        intro F G η
        dsimp
        rw [show η = η.unop.op by simp, ← op_comp, ← op_comp]
        congr 1
        aesop_cat)
  counitIso := NatIso.ofComponents fun F => F.leftOpRightOpIso
#align category_theory.functor.left_op_right_op_equiv CategoryTheory.Functor.leftOpRightOpEquiv

instance {F : C ⥤ D} [EssSurj F] : EssSurj F.op where
  mem_essImage X := ⟨op _, ⟨(F.objObjPreimageIso X.unop).op.symm⟩⟩

instance {F : Cᵒᵖ ⥤ D} [EssSurj F] : EssSurj F.rightOp where
  mem_essImage X := ⟨_, ⟨(F.objObjPreimageIso X.unop).op.symm⟩⟩

instance {F : C ⥤ Dᵒᵖ} [EssSurj F] : EssSurj F.leftOp where
  mem_essImage X := ⟨op _, ⟨(F.objObjPreimageIso (op X)).unop.symm⟩⟩

instance {F : C ⥤ D} [IsEquivalence F] : IsEquivalence F.op where

instance {F : Cᵒᵖ ⥤ D} [IsEquivalence F] : IsEquivalence F.rightOp where

instance {F : C ⥤ Dᵒᵖ} [IsEquivalence F] : IsEquivalence F.leftOp where

end Functor

end CategoryTheory
