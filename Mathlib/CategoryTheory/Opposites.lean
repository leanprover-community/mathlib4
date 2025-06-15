/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Kim Morrison
-/
import Mathlib.CategoryTheory.Equivalence

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

theorem Quiver.Hom.unop_inj {X Y : Cᵒᵖ} :
    Function.Injective (Quiver.Hom.unop : (X ⟶ Y) → (Opposite.unop Y ⟶ Opposite.unop X)) :=
  fun _ _ H => congr_arg Quiver.Hom.op H

@[simp]
theorem Quiver.Hom.unop_op {X Y : C} (f : X ⟶ Y) : f.op.unop = f :=
  rfl

@[simp]
theorem Quiver.Hom.unop_op' {X Y : Cᵒᵖ} {x} :
    @Quiver.Hom.unop C _ X Y no_index (Opposite.op (unop := x)) = x := rfl

@[simp]
theorem Quiver.Hom.op_unop {X Y : Cᵒᵖ} (f : X ⟶ Y) : f.unop.op = f :=
  rfl

@[simp] theorem Quiver.Hom.unop_mk {X Y : Cᵒᵖ} (f : X ⟶ Y) : Quiver.Hom.unop {unop := f} = f := rfl

end Quiver

namespace CategoryTheory

section

variable [CategoryStruct.{v₁} C]

/-- The opposite `CategoryStruct`. -/
instance CategoryStruct.opposite : CategoryStruct.{v₁} Cᵒᵖ where
  comp f g := (g.unop ≫ f.unop).op
  id X := (𝟙 (unop X)).op

@[simp, reassoc]
theorem op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g).op = g.op ≫ f.op :=
  rfl

@[simp]
theorem op_id {X : C} : (𝟙 X).op = 𝟙 (op X) :=
  rfl

@[simp, reassoc]
theorem unop_comp {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g).unop = g.unop ≫ f.unop :=
  rfl

@[simp]
theorem unop_id {X : Cᵒᵖ} : (𝟙 X).unop = 𝟙 (unop X) :=
  rfl

@[simp]
theorem unop_id_op {X : C} : (𝟙 (op X)).unop = 𝟙 X :=
  rfl

@[simp]
theorem op_id_unop {X : Cᵒᵖ} : (𝟙 (unop X)).op = 𝟙 X :=
  rfl

end

variable [Category.{v₁} C]

/-- The opposite category. -/
@[stacks 001M]
instance Category.opposite : Category.{v₁} Cᵒᵖ where
  toCategoryStruct := CategoryStruct.opposite
  id_comp f := congrArg op <| Category.comp_id _
  comp_id f := congrArg op <| Category.id_comp _
  assoc f g h := congrArg op <| by simp

section

variable (C)

/-- The functor from the double-opposite of a category to the underlying category. -/
@[simps]
def unopUnop : Cᵒᵖᵒᵖ ⥤ C where
  obj X := unop (unop X)
  map f := f.unop.unop

/-- The functor from a category to its double-opposite. -/
@[simps]
def opOp : C ⥤ Cᵒᵖᵒᵖ where
  obj X := op (op X)
  map f := f.op.op

/-- The double opposite category is equivalent to the original. -/
@[simps]
def opOpEquivalence : Cᵒᵖᵒᵖ ≌ C where
  functor := unopUnop C
  inverse := opOp C
  unitIso := Iso.refl (𝟭 Cᵒᵖᵒᵖ)
  counitIso := Iso.refl (opOp C ⋙ unopUnop C)

instance : (opOp C).IsEquivalence :=
  (opOpEquivalence C).isEquivalence_inverse

instance : (unopUnop C).IsEquivalence :=
  (opOpEquivalence C).isEquivalence_functor

end

/-- If `f` is an isomorphism, so is `f.op` -/
instance isIso_op {X Y : C} (f : X ⟶ Y) [IsIso f] : IsIso f.op :=
  ⟨⟨(inv f).op, ⟨Quiver.Hom.unop_inj (by simp), Quiver.Hom.unop_inj (by simp)⟩⟩⟩

/-- If `f.op` is an isomorphism `f` must be too.
(This cannot be an instance as it would immediately loop!)
-/
theorem isIso_of_op {X Y : C} (f : X ⟶ Y) [IsIso f.op] : IsIso f :=
  ⟨⟨(inv f.op).unop, ⟨Quiver.Hom.op_inj (by simp), Quiver.Hom.op_inj (by simp)⟩⟩⟩

theorem isIso_op_iff {X Y : C} (f : X ⟶ Y) : IsIso f.op ↔ IsIso f :=
  ⟨fun _ => isIso_of_op _, fun _ => inferInstance⟩

theorem isIso_unop_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) : IsIso f.unop ↔ IsIso f := by
  rw [← isIso_op_iff f.unop, Quiver.Hom.op_unop]

instance isIso_unop {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso f] : IsIso f.unop :=
  (isIso_unop_iff _).2 inferInstance

@[simp]
theorem op_inv {X Y : C} (f : X ⟶ Y) [IsIso f] : (inv f).op = inv f.op := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← op_comp, IsIso.inv_hom_id, op_id]

@[simp]
theorem unop_inv {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso f] : (inv f).unop = inv f.unop := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← unop_comp, IsIso.inv_hom_id, unop_id]

namespace Functor

section

variable {D : Type u₂} [Category.{v₂} D]

/-- The opposite of a functor, i.e. considering a functor `F : C ⥤ D` as a functor `Cᵒᵖ ⥤ Dᵒᵖ`.
In informal mathematics no distinction is made between these. -/
@[simps]
protected def op (F : C ⥤ D) : Cᵒᵖ ⥤ Dᵒᵖ where
  obj X := op (F.obj (unop X))
  map f := (F.map f.unop).op

/-- Given a functor `F : Cᵒᵖ ⥤ Dᵒᵖ` we can take the "unopposite" functor `F : C ⥤ D`.
In informal mathematics no distinction is made between these.
-/
@[simps]
protected def unop (F : Cᵒᵖ ⥤ Dᵒᵖ) : C ⥤ D where
  obj X := unop (F.obj (op X))
  map f := (F.map f.op).unop

/-- The isomorphism between `F.op.unop` and `F`. -/
@[simps!]
def opUnopIso (F : C ⥤ D) : F.op.unop ≅ F :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- The isomorphism between `F.unop.op` and `F`. -/
@[simps!]
def unopOpIso (F : Cᵒᵖ ⥤ Dᵒᵖ) : F.unop.op ≅ F :=
  NatIso.ofComponents fun _ => Iso.refl _

variable (C D)

/-- Taking the opposite of a functor is functorial.
-/
@[simps]
def opHom : (C ⥤ D)ᵒᵖ ⥤ Cᵒᵖ ⥤ Dᵒᵖ where
  obj F := (unop F).op
  map α :=
    { app := fun X => (α.unop.app (unop X)).op
      naturality := fun _ _ f => Quiver.Hom.unop_inj (α.unop.naturality f.unop).symm }

/-- Take the "unopposite" of a functor is functorial.
-/
@[simps]
def opInv : (Cᵒᵖ ⥤ Dᵒᵖ) ⥤ (C ⥤ D)ᵒᵖ where
  obj F := op F.unop
  map α :=
    Quiver.Hom.op
      { app := fun X => (α.app (op X)).unop
        naturality := fun _ _ f => Quiver.Hom.op_inj <| (α.naturality f.op).symm }

variable {C D}

section Compositions

variable {E : Type*} [Category E]

/-- Compatibility of `Functor.op` with respect to functor composition. -/
@[simps!]
def opComp (F : C ⥤ D) (G : D ⥤ E) : (F ⋙ G).op ≅ F.op ⋙ G.op := Iso.refl _

/-- Compatibility of `Functor.unop` with respect to functor composition. -/
@[simps!]
def unopComp (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : Dᵒᵖ ⥤ Eᵒᵖ) : (F ⋙ G).unop ≅ F.unop ⋙ G.unop := Iso.refl _

variable (C) in
/-- `Functor.op` transforms identity functors to identity functors. -/
@[simps!]
def opId : (𝟭 C).op ≅ 𝟭 (Cᵒᵖ) := Iso.refl _

variable (C) in
/-- `Functor.unop` transforms identity functors to identity functors. -/
@[simps!]
def unopId : (𝟭 Cᵒᵖ).unop ≅ 𝟭 C := Iso.refl _

end Compositions

/--
Another variant of the opposite of functor, turning a functor `C ⥤ Dᵒᵖ` into a functor `Cᵒᵖ ⥤ D`.
In informal mathematics no distinction is made.
-/
@[simps]
protected def leftOp (F : C ⥤ Dᵒᵖ) : Cᵒᵖ ⥤ D where
  obj X := unop (F.obj (unop X))
  map f := (F.map f.unop).unop

/--
Another variant of the opposite of functor, turning a functor `Cᵒᵖ ⥤ D` into a functor `C ⥤ Dᵒᵖ`.
In informal mathematics no distinction is made.
-/
@[simps]
protected def rightOp (F : Cᵒᵖ ⥤ D) : C ⥤ Dᵒᵖ where
  obj X := op (F.obj (op X))
  map f := (F.map f.op).op

lemma rightOp_map_unop {F : Cᵒᵖ ⥤ D} {X Y} (f : X ⟶ Y) :
    (F.rightOp.map f).unop = F.map f.op := rfl

instance {F : C ⥤ D} [Full F] : Full F.op where
  map_surjective f := ⟨(F.preimage f.unop).op, by simp⟩

instance {F : C ⥤ D} [Faithful F] : Faithful F.op where
  map_injective h := Quiver.Hom.unop_inj <| by simpa using map_injective F (Quiver.Hom.op_inj h)

/-- The opposite of a fully faithful functor is fully faithful. -/
protected def FullyFaithful.op {F : C ⥤ D} (hF : F.FullyFaithful) : F.op.FullyFaithful where
  preimage {X Y} f := .op <| hF.preimage f.unop

/-- If F is faithful then the right_op of F is also faithful. -/
instance rightOp_faithful {F : Cᵒᵖ ⥤ D} [Faithful F] : Faithful F.rightOp where
  map_injective h := Quiver.Hom.op_inj (map_injective F (Quiver.Hom.op_inj h))

/-- If F is faithful then the left_op of F is also faithful. -/
instance leftOp_faithful {F : C ⥤ Dᵒᵖ} [Faithful F] : Faithful F.leftOp where
  map_injective h := Quiver.Hom.unop_inj (map_injective F (Quiver.Hom.unop_inj h))

instance rightOp_full {F : Cᵒᵖ ⥤ D} [Full F] : Full F.rightOp where
  map_surjective f := ⟨(F.preimage f.unop).unop, by simp⟩

instance leftOp_full {F : C ⥤ Dᵒᵖ} [Full F] : Full F.leftOp where
  map_surjective f := ⟨(F.preimage f.op).op, by simp⟩

/-- The opposite of a fully faithful functor is fully faithful. -/
protected def FullyFaithful.leftOp {F : C ⥤ Dᵒᵖ} (hF : F.FullyFaithful) :
    F.leftOp.FullyFaithful where
  preimage {X Y} f := .op <| hF.preimage f.op

/-- The opposite of a fully faithful functor is fully faithful. -/
protected def FullyFaithful.rightOp {F : Cᵒᵖ ⥤ D} (hF : F.FullyFaithful) :
    F.rightOp.FullyFaithful where
  preimage {X Y} f := .unop <| hF.preimage f.unop

/-- Compatibility of `Functor.rightOp` with respect to functor composition. -/
@[simps!]
def rightOpComp {E : Type*} [Category E] (F : Cᵒᵖ ⥤ D) (G : D ⥤ E) :
    (F ⋙ G).rightOp ≅ F.rightOp ⋙ G.op :=
  Iso.refl _

/-- Compatibility of `Functor.leftOp` with respect to functor composition. -/
@[simps!]
def leftOpComp {E : Type*} [Category E] (F : C ⥤ D) (G : D ⥤ Eᵒᵖ) :
    (F ⋙ G).leftOp ≅ F.op ⋙ G.leftOp :=
  Iso.refl _

section
variable (C)

/-- `Functor.rightOp` sends identity functors to the canonical isomorphism `opOp`. -/
@[simps!]
def rightOpId : (𝟭 Cᵒᵖ).rightOp ≅ opOp C := Iso.refl _

/-- `Functor.leftOp` sends identity functors to the canonical isomorphism `unopUnop`. -/
@[simps!]
def leftOpId : (𝟭 Cᵒᵖ).leftOp ≅ unopUnop C := Iso.refl _

end

/-- The isomorphism between `F.leftOp.rightOp` and `F`. -/
@[simps!]
def leftOpRightOpIso (F : C ⥤ Dᵒᵖ) : F.leftOp.rightOp ≅ F :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- The isomorphism between `F.rightOp.leftOp` and `F`. -/
@[simps!]
def rightOpLeftOpIso (F : Cᵒᵖ ⥤ D) : F.rightOp.leftOp ≅ F :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- Whenever possible, it is advisable to use the isomorphism `rightOpLeftOpIso`
instead of this equality of functors. -/
theorem rightOp_leftOp_eq (F : Cᵒᵖ ⥤ D) : F.rightOp.leftOp = F := by
  cases F
  rfl

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

@[simp]
theorem op_id (F : C ⥤ D) : NatTrans.op (𝟙 F) = 𝟙 F.op :=
  rfl

@[simp, reassoc]
theorem op_comp {H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) :
    NatTrans.op (α ≫ β) = NatTrans.op β ≫ NatTrans.op α :=
  rfl

@[reassoc]
lemma op_whiskerRight {E : Type*} [Category E] {H : D ⥤ E} (α : F ⟶ G) :
    NatTrans.op (whiskerRight α H) =
    (Functor.opComp _ _).hom ≫ whiskerRight (NatTrans.op α) H.op ≫ (Functor.opComp _ _).inv := by
  aesop_cat

@[reassoc]
lemma op_whiskerLeft {E : Type*} [Category E] {H : E ⥤ C} (α : F ⟶ G) :
    NatTrans.op (whiskerLeft H α) =
    (Functor.opComp _ _).hom ≫ whiskerLeft H.op (NatTrans.op α) ≫ (Functor.opComp _ _).inv := by
  aesop_cat

/-- The "unopposite" of a natural transformation. -/
@[simps]
protected def unop {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ⟶ G) : G.unop ⟶ F.unop where
  app X := (α.app (op X)).unop
  naturality X Y f := Quiver.Hom.op_inj (by simp)

@[simp]
theorem unop_id (F : Cᵒᵖ ⥤ Dᵒᵖ) : NatTrans.unop (𝟙 F) = 𝟙 F.unop :=
  rfl

@[simp, reassoc]
theorem unop_comp {F G H : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ⟶ G) (β : G ⟶ H) :
    NatTrans.unop (α ≫ β) = NatTrans.unop β ≫ NatTrans.unop α :=
  rfl

@[reassoc]
lemma unop_whiskerRight {F G : Cᵒᵖ ⥤ Dᵒᵖ} {E : Type*} [Category E] {H : Dᵒᵖ ⥤ Eᵒᵖ} (α : F ⟶ G) :
    NatTrans.unop (whiskerRight α H) =
    (Functor.unopComp _ _).hom ≫ whiskerRight (NatTrans.unop α) H.unop ≫
      (Functor.unopComp _ _).inv := by
  aesop_cat

@[reassoc]
lemma unop_whiskerLeft {F G : Cᵒᵖ ⥤ Dᵒᵖ} {E : Type*} [Category E] {H : Eᵒᵖ ⥤ Cᵒᵖ} (α : F ⟶ G) :
    NatTrans.unop (whiskerLeft H α) =
    (Functor.unopComp _ _).hom ≫ whiskerLeft H.unop (NatTrans.unop α) ≫
      (Functor.unopComp _ _).inv := by
  aesop_cat

/-- Given a natural transformation `α : F.op ⟶ G.op`,
we can take the "unopposite" of each component obtaining a natural transformation `G ⟶ F`.
-/
@[simps]
protected def removeOp (α : F.op ⟶ G.op) : G ⟶ F where
  app X := (α.app (op X)).unop
  naturality X Y f :=
    Quiver.Hom.op_inj <| by simpa only [Functor.op_map] using (α.naturality f.op).symm

@[simp]
theorem removeOp_id (F : C ⥤ D) : NatTrans.removeOp (𝟙 F.op) = 𝟙 F :=
  rfl

/-- Given a natural transformation `α : F.unop ⟶ G.unop`, we can take the opposite of each
component obtaining a natural transformation `G ⟶ F`. -/
@[simps]
protected def removeUnop {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F.unop ⟶ G.unop) : G ⟶ F where
  app X := (α.app (unop X)).op
  naturality X Y f :=
    Quiver.Hom.unop_inj <| by simpa only [Functor.unop_map] using (α.naturality f.unop).symm

@[simp]
theorem removeUnop_id (F : Cᵒᵖ ⥤ Dᵒᵖ) : NatTrans.removeUnop (𝟙 F.unop) = 𝟙 F :=
  rfl

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

@[simp]
theorem leftOp_id : NatTrans.leftOp (𝟙 F : F ⟶ F) = 𝟙 F.leftOp :=
  rfl

@[simp]
theorem leftOp_comp (α : F ⟶ G) (β : G ⟶ H) : NatTrans.leftOp (α ≫ β) =
    NatTrans.leftOp β ≫ NatTrans.leftOp α :=
  rfl

@[reassoc]
lemma leftOpWhiskerRight {E : Type*} [Category E] {H : E ⥤ C} (α : F ⟶ G) :
    (whiskerLeft H α).leftOp = (Functor.leftOpComp H G).hom ≫ whiskerLeft _ α.leftOp ≫
      (Functor.leftOpComp H F).inv := by
  aesop_cat

/-- Given a natural transformation `α : F.leftOp ⟶ G.leftOp`, for `F G : C ⥤ Dᵒᵖ`,
taking `op` of each component gives a natural transformation `G ⟶ F`.
-/
@[simps]
protected def removeLeftOp (α : F.leftOp ⟶ G.leftOp) : G ⟶ F where
  app X := (α.app (op X)).op
  naturality X Y f :=
    Quiver.Hom.unop_inj <| by simpa only [Functor.leftOp_map] using (α.naturality f.op).symm

@[simp]
theorem removeLeftOp_id : NatTrans.removeLeftOp (𝟙 F.leftOp) = 𝟙 F :=
  rfl

end

section

variable {F G H : Cᵒᵖ ⥤ D}

/-- Given a natural transformation `α : F ⟶ G`, for `F G : Cᵒᵖ ⥤ D`,
taking `op` of each component gives a natural transformation `G.rightOp ⟶ F.rightOp`.
-/
@[simps]
protected def rightOp (α : F ⟶ G) : G.rightOp ⟶ F.rightOp where
  app _ := (α.app _).op
  naturality X Y f := Quiver.Hom.unop_inj (by simp)

@[simp]
theorem rightOp_id : NatTrans.rightOp (𝟙 F : F ⟶ F) = 𝟙 F.rightOp :=
  rfl

@[simp]
theorem rightOp_comp (α : F ⟶ G) (β : G ⟶ H) : NatTrans.rightOp (α ≫ β) =
    NatTrans.rightOp β ≫ NatTrans.rightOp α :=
  rfl

@[reassoc]
lemma rightOpWhiskerRight {E : Type*} [Category E] {H : D ⥤ E} (α : F ⟶ G) :
    (whiskerRight α H).rightOp = (Functor.rightOpComp G H).hom ≫ whiskerRight α.rightOp H.op ≫
      (Functor.rightOpComp F H).inv := by
  aesop_cat

/-- Given a natural transformation `α : F.rightOp ⟶ G.rightOp`, for `F G : Cᵒᵖ ⥤ D`,
taking `unop` of each component gives a natural transformation `G ⟶ F`.
-/
@[simps]
protected def removeRightOp (α : F.rightOp ⟶ G.rightOp) : G ⟶ F where
  app X := (α.app X.unop).unop
  naturality X Y f :=
    Quiver.Hom.op_inj <| by simpa only [Functor.rightOp_map] using (α.naturality f.unop).symm

@[simp]
theorem removeRightOp_id : NatTrans.removeRightOp (𝟙 F.rightOp) = 𝟙 F :=
  rfl

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

/-- The isomorphism obtained from an isomorphism in the opposite category. -/
@[simps]
def unop {X Y : Cᵒᵖ} (f : X ≅ Y) : Y.unop ≅ X.unop where
  hom := f.hom.unop
  inv := f.inv.unop
  hom_inv_id := by simp only [← unop_comp, f.inv_hom_id, unop_id]
  inv_hom_id := by simp only [← unop_comp, f.hom_inv_id, unop_id]

@[simp]
theorem unop_op {X Y : Cᵒᵖ} (f : X ≅ Y) : f.unop.op = f := by (ext; rfl)

@[simp]
theorem op_unop {X Y : C} (f : X ≅ Y) : f.op.unop = f := by (ext; rfl)

variable (X) in
@[simp]
theorem op_refl : Iso.op (Iso.refl X) = Iso.refl (op X) := rfl

@[simp]
theorem op_trans {Z : C} (α : X ≅ Y) (β : Y ≅ Z) :
    Iso.op (α ≪≫ β) = Iso.op β ≪≫ Iso.op α :=
  rfl

@[simp]
theorem op_symm (α : X ≅ Y) : Iso.op α.symm = (Iso.op α).symm := rfl

@[simp]
theorem unop_refl (X : Cᵒᵖ) : Iso.unop (Iso.refl X) = Iso.refl X.unop := rfl

@[simp]
theorem unop_trans {X Y Z : Cᵒᵖ} (α : X ≅ Y) (β : Y ≅ Z) :
    Iso.unop (α ≪≫ β) = Iso.unop β ≪≫ Iso.unop α :=
  rfl

@[simp]
theorem unop_symm {X Y : Cᵒᵖ} (α : X ≅ Y) : Iso.unop α.symm = (Iso.unop α).symm := rfl

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

@[simp]
theorem op_refl : NatIso.op (Iso.refl F) = Iso.refl F.op := rfl

@[simp]
theorem op_trans {H : C ⥤ D} (α : F ≅ G) (β : G ≅ H) :
    NatIso.op (α ≪≫ β) = NatIso.op β ≪≫ NatIso.op α :=
  rfl

@[simp]
theorem op_symm (α : F ≅ G) : NatIso.op α.symm = (NatIso.op α).symm := rfl

/-- The natural isomorphism between functors `G ≅ F` induced by a natural isomorphism
between the opposite functors `F.op ≅ G.op`. -/
@[simps]
protected def removeOp (α : F.op ≅ G.op) : G ≅ F where
  hom := NatTrans.removeOp α.hom
  inv := NatTrans.removeOp α.inv

/-- The natural isomorphism between functors `G.unop ≅ F.unop` induced by a natural isomorphism
between the original functors `F ≅ G`. -/
@[simps]
protected def unop {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ≅ G) : G.unop ≅ F.unop where
  hom := NatTrans.unop α.hom
  inv := NatTrans.unop α.inv

@[simp]
theorem unop_refl (F : Cᵒᵖ ⥤ Dᵒᵖ) : NatIso.unop (Iso.refl F) = Iso.refl F.unop := rfl

@[simp]
theorem unop_trans {F G H : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ≅ G) (β : G ≅ H) :
    NatIso.unop (α ≪≫ β) = NatIso.unop β ≪≫ NatIso.unop α :=
  rfl

@[simp]
theorem unop_symm {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ≅ G) : NatIso.unop α.symm = (NatIso.unop α).symm := rfl

lemma op_isoWhiskerRight {E : Type*} [Category E] {H : D ⥤ E} (α : F ≅ G) :
    NatIso.op (isoWhiskerRight α H) =
    (Functor.opComp _ _) ≪≫ isoWhiskerRight (NatIso.op α) H.op ≪≫ (Functor.opComp _ _).symm := by
  aesop_cat

lemma op_isoWhiskerLeft {E : Type*} [Category E] {H : E ⥤ C} (α : F ≅ G) :
    NatIso.op (isoWhiskerLeft H α) =
    (Functor.opComp _ _) ≪≫ isoWhiskerLeft H.op (NatIso.op α) ≪≫ (Functor.opComp _ _).symm := by
  aesop_cat

lemma unop_whiskerRight {F G : Cᵒᵖ ⥤ Dᵒᵖ} {E : Type*} [Category E] {H : Dᵒᵖ ⥤ Eᵒᵖ} (α : F ≅ G) :
    NatIso.unop (isoWhiskerRight α H) =
    (Functor.unopComp _ _) ≪≫ isoWhiskerRight (NatIso.unop α) H.unop ≪≫
      (Functor.unopComp _ _).symm := by
  aesop_cat

lemma unop_whiskerLeft {F G : Cᵒᵖ ⥤ Dᵒᵖ} {E : Type*} [Category E] {H : Eᵒᵖ ⥤ Cᵒᵖ} (α : F ≅ G) :
    NatIso.unop (isoWhiskerLeft H α) =
    (Functor.unopComp _ _) ≪≫ isoWhiskerLeft H.unop (NatIso.unop α) ≪≫
      (Functor.unopComp _ _).symm := by
  aesop_cat

lemma op_leftUnitor :
    NatIso.op F.leftUnitor =
    F.op.leftUnitor.symm ≪≫
      isoWhiskerRight (Functor.opId C).symm F.op ≪≫
      (Functor.opComp _ _).symm := by
  aesop_cat

lemma op_rightUnitor :
    NatIso.op F.rightUnitor =
    F.op.rightUnitor.symm ≪≫
      isoWhiskerLeft F.op (Functor.opId D).symm ≪≫
      (Functor.opComp _ _).symm := by
  aesop_cat

lemma op_associator {E E': Type*} [Category E] [Category E'] {F : C ⥤ D} {G : D ⥤ E} {H : E ⥤ E'} :
    NatIso.op (Functor.associator F G H) =
      Functor.opComp _ _ ≪≫ isoWhiskerLeft F.op (Functor.opComp _ _) ≪≫
        (Functor.associator F.op G.op H.op).symm ≪≫
        isoWhiskerRight (Functor.opComp _ _).symm H.op ≪≫ (Functor.opComp _ _).symm := by
  aesop_cat

lemma unop_leftUnitor {F : Cᵒᵖ ⥤ Dᵒᵖ} :
    NatIso.unop F.leftUnitor =
    F.unop.leftUnitor.symm ≪≫
      isoWhiskerRight (Functor.unopId C).symm F.unop ≪≫
      (Functor.unopComp _ _).symm := by
  aesop_cat

lemma unop_rightUnitor {F : Cᵒᵖ ⥤ Dᵒᵖ} :
    NatIso.unop F.rightUnitor =
    F.unop.rightUnitor.symm ≪≫
      isoWhiskerLeft F.unop (Functor.unopId D).symm ≪≫
      (Functor.unopComp _ _).symm := by
  aesop_cat

lemma unop_associator {E E': Type*} [Category E] [Category E']
    {F : Cᵒᵖ ⥤ Dᵒᵖ} {G : Dᵒᵖ ⥤ Eᵒᵖ} {H : Eᵒᵖ ⥤ E'ᵒᵖ} :
    NatIso.unop (Functor.associator F G H) =
      Functor.unopComp _ _ ≪≫ isoWhiskerLeft F.unop (Functor.unopComp _ _) ≪≫
        (Functor.associator F.unop G.unop H.unop).symm ≪≫
        isoWhiskerRight (Functor.unopComp _ _).symm H.unop ≪≫ (Functor.unopComp _ _).symm := by
  aesop_cat

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
    simp

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
    simp

/-- An equivalence between `C` and `Dᵒᵖ` gives an equivalence between `Cᵒᵖ` and `D`. -/
@[simps!] def leftOp (e : C ≌ Dᵒᵖ) : Cᵒᵖ ≌ D := e.op.trans (opOpEquivalence D)

/-- An equivalence between `Cᵒᵖ` and `D` gives an equivalence between `C` and `Dᵒᵖ`. -/
@[simps!] def rightOp (e : Cᵒᵖ ≌ D) : C ≌ Dᵒᵖ := (opOpEquivalence C).symm.trans e.op

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

instance subsingleton_of_unop (A B : Cᵒᵖ) [Subsingleton (unop B ⟶ unop A)] : Subsingleton (A ⟶ B) :=
  (opEquiv A B).subsingleton

instance decidableEqOfUnop (A B : Cᵒᵖ) [DecidableEq (unop B ⟶ unop A)] : DecidableEq (A ⟶ B) :=
  (opEquiv A B).decidableEq

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
