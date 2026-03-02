/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Order.Antisymmetrization
public import Mathlib.Order.Category.Preord
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Category of partial orders

This defines `PartOrd`, the category of partial orders with monotone maps.
-/

@[expose] public section

open CategoryTheory

universe u

/-- The category of partial orders. -/
structure PartOrd where
  /-- Construct a bundled `PartOrd` from the underlying type and typeclass. -/
  of ::
  /-- The underlying partially ordered type. -/
  (carrier : Type*)
  [str : PartialOrder carrier]

attribute [instance] PartOrd.str

initialize_simps_projections PartOrd (carrier → coe, -str)

namespace PartOrd

instance : CoeSort PartOrd (Type _) :=
  ⟨PartOrd.carrier⟩

attribute [coe] PartOrd.carrier

set_option backward.privateInPublic true in
/-- The type of morphisms in `PartOrd R`. -/
@[ext]
structure Hom (X Y : PartOrd.{u}) where
  private mk ::
  /-- The underlying `OrderHom`. -/
  hom' : X →o Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : Category PartOrd.{u} where
  Hom X Y := Hom X Y
  id _ := ⟨OrderHom.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : ConcreteCategory PartOrd (· →o ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `PartOrd` back into a `OrderHom`. -/
abbrev Hom.hom {X Y : PartOrd.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := PartOrd) f

/-- Typecheck a `OrderHom` as a morphism in `PartOrd`. -/
abbrev ofHom {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X →o Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := PartOrd) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (X Y : PartOrd.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

-- This is not `simp` to avoid rewriting in types of terms.
theorem coe_of (X : Type u) [PartialOrder X] : (PartOrd.of X : Type u) = X := rfl

@[simp]
lemma hom_id {X : PartOrd} : (𝟙 X : X ⟶ X).hom = OrderHom.id := rfl

@[simp]
lemma hom_comp {X Y Z : PartOrd} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

@[simp]
lemma ofHom_id {X : Type u} [PartialOrder X] : ofHom OrderHom.id = 𝟙 (of X) := rfl

@[simp]
lemma ofHom_comp {X Y Z : Type u} [PartialOrder X] [PartialOrder Y] [PartialOrder Z]
    (f : X →o Y) (g : Y →o Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X →o Y) (x : X) :
    (ofHom f) x = f x := rfl

instance hasForgetToPreord : HasForget₂ PartOrd Preord where
  forget₂.obj X := .of X
  forget₂.map f := Preord.ofHom f.hom

/-- Constructs an equivalence between partial orders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : PartOrd.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm

/-- `OrderDual` as a functor. -/
@[simps map]
def dual : PartOrd ⥤ PartOrd where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.dual

/-- The equivalence between `PartOrd` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : PartOrd ≌ PartOrd where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X

end PartOrd

theorem partOrd_dual_comp_forget_to_preord :
    PartOrd.dual ⋙ forget₂ PartOrd Preord =
      forget₂ PartOrd Preord ⋙ Preord.dual :=
  rfl

/-- `Antisymmetrization` as a functor. It is the free functor. -/
def preordToPartOrd : Preord.{u} ⥤ PartOrd where
  obj X := .of (Antisymmetrization X (· ≤ ·))
  map f := PartOrd.ofHom f.hom.antisymmetrization
  map_id X := by
    ext x
    exact Quotient.inductionOn' x fun x => Quotient.map'_mk'' _ (fun a b => id) _
  map_comp f g := by
    ext x
    exact Quotient.inductionOn' x fun x => OrderHom.antisymmetrization_apply_mk _ _

/-- `preordToPartOrd` is left adjoint to the forgetful functor, meaning it is the free
functor from `Preord` to `PartOrd`. -/
def preordToPartOrdForgetAdjunction :
    preordToPartOrd.{u} ⊣ forget₂ PartOrd Preord :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ :=
        { toFun f := Preord.ofHom
            ⟨f ∘ toAntisymmetrization (· ≤ ·), f.hom.mono.comp toAntisymmetrization_mono⟩
          invFun f := PartOrd.ofHom
            ⟨fun a => Quotient.liftOn' a f (fun _ _ h => (AntisymmRel.image h f.hom.mono).eq),
              fun a b => Quotient.inductionOn₂' a b fun _ _ h => f.hom.mono h⟩
          left_inv _ := ConcreteCategory.hom_ext _ _ fun x => by
            exact Quotient.inductionOn' x fun _ => rfl }
      homEquiv_naturality_left_symm _ _ := ConcreteCategory.hom_ext _ _ fun x => by
        exact Quotient.inductionOn' x fun _ => rfl }

-- The `simpNF` linter would complain as `Functor.comp_obj`, `Preord.dual_obj` both apply to LHS
-- of `preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd_hom_app_coe`
/-- `PreordToPartOrd` and `OrderDual` commute. -/
@[simps! -isSimp hom_app_hom_coe inv_app_hom_coe]
def preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd :
    preordToPartOrd.{u} ⋙ PartOrd.dual ≅ Preord.dual ⋙ preordToPartOrd :=
  NatIso.ofComponents (fun _ => PartOrd.Iso.mk <| OrderIso.dualAntisymmetrization _)
    (fun _ => ConcreteCategory.hom_ext _ _ fun x => by exact Quotient.inductionOn' x fun _ => rfl)

-- `simp`-normal form for `preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd_inv_app_hom_coe`
@[simp]
lemma preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd_inv_app_hom_coe' (X)
    (a : preordToPartOrd.obj (Preord.dual.obj X)) :
    (PartOrd.Hom.hom
        (X := preordToPartOrd.obj (Preord.dual.obj X))
        (Y := PartOrd.dual.obj (preordToPartOrd.obj X))
        (preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd.inv.app X)) a =
      (OrderIso.dualAntisymmetrization ↑X).symm a :=
  rfl
