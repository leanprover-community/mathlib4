/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Creates

universe v₁ v₁' v₂ v₂' u₁ u₁' u₂ u₂'

namespace CategoryTheory

class IsOpposite (C : Type u₁) [Category.{v₁} C] (C' : Type u₁') [Category.{v₁'} C'] where
  equivOpposite : C' ≌ Cᵒᵖ

def equivOpposite (C : Type u₁) [Category.{v₁} C] (C' : Type u₁') [Category.{v₁'} C']
    [IsOpposite C C'] : C' ≌ Cᵒᵖ :=
  IsOpposite.equivOpposite

instance {C : Type u₁} [Category.{v₁} C] : IsOpposite C Cᵒᵖ where
  equivOpposite := Equivalence.refl

instance {C : Type u₁} [Category.{v₁} C] : IsOpposite Cᵒᵖ C where
  equivOpposite := (opOpEquivalence C).symm

section

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₁'} [Category.{v₁'} C']
variable [IsOpposite C C']

variable (C') in
def opTo (X : C) : C' := (equivOpposite C C').inverse.obj (Opposite.op X)

variable (C) in
def unopTo (X : C') : C := ((equivOpposite C C').functor.obj X).unop

def unopToOpTo (X : C) : unopTo C (opTo C' X) ≅ X :=
  ((equivOpposite C C').counitIso.symm.app (Opposite.op X)).unop

def opToUnopTo (X : C') : opTo C' (unopTo C X) ≅ X :=
  (equivOpposite C C').unitIso.symm.app X

end

end CategoryTheory

namespace Quiver.Hom

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₁'} [Category.{v₁'} C']
variable [IsOpposite C C']

variable (C') in
def opTo {X Y : C} (f : X ⟶ Y) : opTo C' Y ⟶ opTo C' X :=
  (equivOpposite C C').inverse.map f.op

variable (C) in
def unopTo {X Y : C'} (f : X ⟶ Y) : unopTo C Y ⟶ unopTo C X :=
  ((equivOpposite C C').functor.map f).unop

variable (C') in
theorem opTo_inj {X Y : C} : Function.Injective (opTo C' : (X ⟶ Y) → _) :=
  fun _ _ hfg => Quiver.Hom.op_inj <| (equivOpposite C C').inverse.map_injective hfg

variable (C) in
theorem unopTo_inj {X Y : C'} : Function.Injective (unopTo C : (X ⟶ Y) → _) :=
  fun _ _ hfg => (equivOpposite C C').functor.map_injective <| Quiver.Hom.unop_inj hfg

end Quiver.Hom

namespace CategoryTheory

section

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₁'} [Category.{v₁'} C']
variable {D : Type u₂} [Category.{v₂} D] {D' : Type u₂'} [Category.{v₂'} D']
variable [IsOpposite C C'] [IsOpposite D D']

variable (C' D') in
def Functor.opTo (F : C ⥤ D) : C' ⥤ D' :=
  (equivOpposite C C').functor ⋙ F.op ⋙ (equivOpposite D D').inverse

def opToFunctor : (C ⥤ D)ᵒᵖ ⥤ C' ⥤ D' where
  obj F := F.unop.opTo C' D'
  map {F G} η := whiskerLeft _ (whiskerRight (NatTrans.op η.unop) _)
  map_id := by aesop_cat
  map_comp := by aesop_cat

variable (C C' D') in
def Functor.opToConst (X : D) :
    ((Functor.const C).obj X).opTo C' D' ≅ (Functor.const C').obj (CategoryTheory.opTo D' X) :=
  NatIso.ofComponents (fun X => Iso.refl _) (by intros; simp [Functor.opTo])

variable (C D) in
def Functor.unopTo (F' : C' ⥤ D') : C ⥤ D :=
  ((equivOpposite C C').inverse ⋙ F' ⋙ (equivOpposite D D').functor).unop

variable (C C' D) in
def Functor.unopToConst (X : D') :
    ((Functor.const C').obj X).unopTo C D ≅ (Functor.const C).obj (CategoryTheory.unopTo D X) :=
  NatIso.ofComponents (fun X => Iso.refl _) (by intros; simp [Functor.unopTo])

class IsOppositeFunctor (F : C ⥤ D) (F' : C' ⥤ D') where
  isoOp : F' ≅ F.opTo C' D'

def Functor.isoOpTo (F' : C' ⥤ D') (F : C ⥤ D) [IsOppositeFunctor F F'] :
    F' ≅ F.opTo C' D' :=
  IsOppositeFunctor.isoOp

def Functor.isoUnopTo (F : C ⥤ D) (F' : C' ⥤ D') [IsOppositeFunctor F F'] :
    F ≅ F'.unopTo C D :=
  NatIso.ofComponents (fun X => by
    dsimp [unopTo]
    sorry) _

instance (F : C ⥤ D) : IsOppositeFunctor F F.op where
  isoOp := Iso.refl _

instance (F : Cᵒᵖ ⥤ D) : IsOppositeFunctor F F.rightOp where
  isoOp := Iso.refl _

instance (F : C ⥤ Dᵒᵖ) : IsOppositeFunctor F F.leftOp where
  isoOp := Iso.refl _

instance (F : Cᵒᵖ ⥤ Dᵒᵖ) : IsOppositeFunctor F F.unop where
  isoOp := Iso.refl _

instance (F : C ⥤ D) : IsOppositeFunctor F.op F where
  isoOp := Iso.refl _

instance (F : Cᵒᵖ ⥤ D) : IsOppositeFunctor F.rightOp F where
  isoOp := Iso.refl _

instance (F : C ⥤ Dᵒᵖ) : IsOppositeFunctor F.leftOp F where
  isoOp := Iso.refl _

instance (F : Cᵒᵖ ⥤ Dᵒᵖ) : IsOppositeFunctor F.unop F where
  isoOp := Iso.refl _

end

namespace NatTrans

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₁'} [Category.{v₁'} C']
variable {D : Type u₂} [Category.{v₂} D] {D' : Type u₂'} [Category.{v₂'} D']
variable [IsOpposite C C'] [IsOpposite D D']
variable {F : C ⥤ D} {F' : C' ⥤ D'} [IsOppositeFunctor F F']
variable {G : C ⥤ D} {G' : C' ⥤ D'} [IsOppositeFunctor G G']

variable (C' D') in
def opTo (α : F ⟶ G) : G.opTo C' D' ⟶ F.opTo C' D' :=
  whiskerLeft _ (whiskerRight (NatTrans.op α) _)

variable (C D) in
def unopTo (α : F' ⟶ G') : G'.unopTo C D ⟶ F'.unopTo C D :=
  NatTrans.unop <| whiskerLeft _ (whiskerRight α _)

def opToFunctor (α : F ⟶ G) : G' ⟶ F' :=
  (G'.isoOpTo G).hom ≫ NatTrans.opTo C' D' α ≫ (F'.isoOpTo F).inv

end NatTrans

namespace Limits

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₁'} [Category.{v₁'} C']
variable {D : Type u₂} [Category.{v₂} D] {D' : Type u₂'} [Category.{v₂'} D']
variable [IsOpposite C C'] [IsOpposite D D']


variable {F : C ⥤ D} {F' : C' ⥤ D'} [IsOppositeFunctor F F']

def Cone.opOfIsOppositeFunctor (c : Cone F) : Cocone F' where
  pt := opTo D' c.pt
  ι := (F'.isoOpTo F).hom ≫ NatTrans.opTo C' D' c.π ≫ (Functor.opToConst C C' D' _).hom

def Cocone.unopOfIsOppositeFunctor (c : Cocone F') : Cone F where
  pt := unopTo D c.pt
  π := (Functor.unopToConst _ _ _ _).inv ≫ NatTrans.unopTo C D c.ι ≫ (F'.isoOpTo F).inv

def Cone.op' (c : Cone F) : Cocone F.op :=
  c.opOfIsOppositeFunctor

-- Don't use this
def Cone.opIsoOp' (c : Cone F) : c.op ≅ c.op' :=
  Cocones.ext (Iso.refl _) (by
    intro j
    dsimp [op', opOfIsOppositeFunctor, NatTrans.opTo, Functor.opToConst]
    simp
    erw [Category.id_comp]
    rfl)

end Limits

end CategoryTheory
