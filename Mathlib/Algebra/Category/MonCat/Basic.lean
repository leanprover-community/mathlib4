/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.category.Mon.basic
! leanprover-community/mathlib commit 0caf3701139ef2e69c215717665361cda205a90b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.Algebra.PUnitInstances
import Mathlib.CategoryTheory.Functor.ReflectsIso

/-!
# Category instances for monoid, add_monoid, comm_monoid, and add_comm_monoid.

We introduce the bundled categories:
* `MonCat`
* `AddMonCat`
* `CommMonCat`
* `AddCommMonCat`
along with the relevant forgetful functors between them.
-/


universe u v

open CategoryTheory

/-- The category of monoids and monoid morphisms. -/
@[to_additive AddMonCat]
def MonCat : Type (u + 1) :=
  Bundled Monoid
set_option linter.uppercaseLean3 false in
#align Mon MonCat
set_option linter.uppercaseLean3 false in
#align AddMon AddMonCat

/-- The category of additive monoids and monoid morphisms. -/
add_decl_doc AddMonCat

namespace MonCat

/-- `MonoidHom` doesn't actually assume associativity. This alias is needed to make the category
theory machinery work. -/
@[to_additive]
abbrev AssocMonoidHom (M N : Type _) [Monoid M] [Monoid N] :=
  MonoidHom M N
set_option linter.uppercaseLean3 false in
#align Mon.assoc_monoid_hom MonCat.AssocMonoidHom
set_option linter.uppercaseLean3 false in
#align AddMon.assoc_add_monoid_hom AddMonCat.AssocAddMonoidHom

/-- `AddMonoidHom` doesn't actually assume associativity. This alias is needed to make
the category theory machinery work. -/
add_decl_doc AddMonCat.AssocAddMonoidHom

@[to_additive]
instance bundledHom : BundledHom AssocMonoidHom where
  toFun  {X Y} _ _ f := ⇑f
  id _ := MonoidHom.id _
  comp _ _ _ := MonoidHom.comp
set_option linter.uppercaseLean3 false in
#align Mon.bundled_hom MonCat.bundledHom
set_option linter.uppercaseLean3 false in
#align AddMon.bundled_hom AddMonCat.bundledHom

instance largeCategory : LargeCategory MonCat := by
  dsimp only [MonCat]
  infer_instance

instance concreteCategory : ConcreteCategory MonCat :=
  BundledHom.concreteCategory _

attribute [to_additive] MonCat.largeCategory MonCat.concreteCategory

@[to_additive]
instance : CoeSort MonCat (Type _) := by
  dsimp only [MonCat]
  infer_instance

/-- Construct a bundled `MonCat` from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [Monoid M] : MonCat :=
  Bundled.of M
set_option linter.uppercaseLean3 false in
#align Mon.of MonCat.of
set_option linter.uppercaseLean3 false in
#align AddMon.of AddMonCat.of

/-- Construct a bundled `MonCat` from the underlying type and typeclass. -/
add_decl_doc AddMonCat.of

/-- Typecheck a `MonoidHom` as a morphism in `MonCat`. -/
@[to_additive]
def ofHom {X Y : Type u} [Monoid X] [Monoid Y] (f : X →* Y) : of X ⟶ of Y :=
  f
set_option linter.uppercaseLean3 false in
#align Mon.of_hom MonCat.ofHom
set_option linter.uppercaseLean3 false in
#align AddMon.of_hom AddMonCat.ofHom

/-- Typecheck a `AddMonoidHom` as a morphism in `AddMonCat`. -/
add_decl_doc AddMonCat.ofHom

-- porting note: this instance was not necessary in mathlib
@[to_additive]
instance {X Y : MonCat} : CoeFun (X ⟶ Y) fun _ => X → Y :=
  ConcreteCategory.hasCoeToFun

-- porting note: in mathlib the LHS was `(⇑ofHom f) x`; the coercion was unfolded
-- to make the simp lemma work
@[to_additive (attr := simp) _root_.AddMonCat.ofHom_apply]
lemma ofHom_apply {X Y : Type u} [Monoid X] [Monoid Y] (f : X →* Y) (x : X) :
  ((forget MonCat).map (MonCat.ofHom f)) x = f x := rfl
set_option linter.uppercaseLean3 false in
#align Mon.of_hom_apply MonCat.ofHom_apply

@[to_additive]
instance : Inhabited MonCat :=
  -- The default instance for `Monoid PUnit` is derived via `CommRing` which breaks to_additive
  ⟨@of PUnit (@DivInvMonoid.toMonoid _ (@Group.toDivInvMonoid _
    (@CommGroup.toGroup _ PUnit.commGroup)))⟩

@[to_additive]
instance (M : MonCat) : Monoid M :=
  M.str

@[to_additive (attr := simp)]
theorem coe_of (R : Type u) [Monoid R] : (MonCat.of R : Type u) = R :=
  rfl
set_option linter.uppercaseLean3 false in
#align Mon.coe_of MonCat.coe_of
set_option linter.uppercaseLean3 false in
#align AddMon.coe_of AddMonCat.coe_of

@[to_additive]
instance {G : Type _} [Group G] : Group (MonCat.of G) := by assumption

-- porting note: this was added to ease the port
/-- the morphism in `MonCat` associated to a `MonoidHom` -/
@[to_additive (attr := simp)]
def Hom.mk {X Y : MonCat} (f : X →* Y) : X ⟶ Y := f

/-- the morphism in `AddMonCat` associated to a `AddMonoidHom` -/
add_decl_doc AddMonCat.Hom.mk

-- porting note: this lemma was added to make automation work in `MonCat.forget_reflects_isos`
@[to_additive (attr := simp)]
lemma Hom.map_mul {X Y : MonCat} (f : X ⟶ Y) (x y : X) :
  ((forget MonCat).map f) (x * y) =
    f x * f y := by
  apply MonoidHom.map_mul (show MonoidHom X Y from f)

-- porting note: added as a complement to `Hom.map_mul`
@[to_additive (attr := simp)]
lemma Hom.map_one {X Y : MonCat} (f : X ⟶ Y) :
  ((forget MonCat).map f) (1 : X) = (1 : Y) := by
  apply MonoidHom.map_one (show MonoidHom X Y from f)

end MonCat

/-- The category of commutative monoids and monoid morphisms. -/
@[to_additive AddCommMonCat]
def CommMonCat : Type (u + 1) :=
  Bundled CommMonoid
set_option linter.uppercaseLean3 false in
#align CommMon CommMonCat
set_option linter.uppercaseLean3 false in
#align AddCommMon AddCommMonCat

/-- The category of additive commutative monoids and monoid morphisms. -/
add_decl_doc AddCommMonCat

namespace CommMonCat

@[to_additive]
instance : BundledHom.ParentProjection @CommMonoid.toMonoid := ⟨⟩

instance largeCategory : LargeCategory CommMonCat := by
  dsimp only [CommMonCat]
  infer_instance

instance concreteCategory : ConcreteCategory CommMonCat := by
  dsimp only [CommMonCat]
  infer_instance

attribute [to_additive] CommMonCat.largeCategory CommMonCat.concreteCategory

@[to_additive]
instance : CoeSort CommMonCat (Type _) := by
  dsimp only [CommMonCat]
  infer_instance

/-- Construct a bundled `CommMonCat` from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [CommMonoid M] : CommMonCat :=
  Bundled.of M
set_option linter.uppercaseLean3 false in
#align CommMon.of CommMonCat.of
set_option linter.uppercaseLean3 false in
#align AddCommMon.of AddCommMonCat.of

/-- Construct a bundled `AddCommMon` from the underlying type and typeclass. -/
add_decl_doc AddCommMonCat.of

@[to_additive]
instance : Inhabited CommMonCat :=
  -- The default instance for `CommMonoid PUnit` is derived via `CommRing` which breaks to_additive
  ⟨@of PUnit (@CommGroup.toCommMonoid _ PUnit.commGroup)⟩

@[to_additive]
instance (M : CommMonCat) : CommMonoid M :=
  M.str

@[to_additive (attr := simp)]
theorem coe_of (R : Type u) [CommMonoid R] : (CommMonCat.of R : Type u) = R :=
  rfl
set_option linter.uppercaseLean3 false in
#align CommMon.coe_of CommMonCat.coe_of
set_option linter.uppercaseLean3 false in
#align AddCommMon.coe_of AddCommMonCat.coe_of

@[to_additive hasForgetToAddMonCat]
instance hasForgetToMonCat : HasForget₂ CommMonCat MonCat :=
  BundledHom.forget₂ _ _
set_option linter.uppercaseLean3 false in
#align CommMon.has_forget_to_Mon CommMonCat.hasForgetToMonCat
set_option linter.uppercaseLean3 false in
#align AddCommMon.has_forget_to_AddMon AddCommMonCat.hasForgetToAddMonCat

@[to_additive]
instance : Coe CommMonCat.{u} MonCat.{u} where coe := (forget₂ CommMonCat MonCat).obj

-- porting note: this instance was not necessary in mathlib
@[to_additive]
instance {X Y : CommMonCat} : CoeFun (X ⟶ Y) fun _ => X → Y :=
  ConcreteCategory.hasCoeToFun

-- porting note: this was added to make automation work
/-- Typecheck a `MonoidHom` as a morphism in `CommMonCat`. -/
@[to_additive]
def ofHom {X Y : Type u} [CommMonoid X] [CommMonoid Y] (f : X →* Y) : of X ⟶ of Y :=
  f

/-- Typecheck a `AddMonoidHom` as a morphism in `AddCommMonCat`. -/
add_decl_doc AddCommMonCat.ofHom

-- porting note: this was added to make automation work in `MulEquiv.toCommMonCatIso`
@[to_additive (attr := simp) _root_.AddCommMonCat.ofHom_apply]
lemma ofHom_apply {X Y : Type u} [CommMonoid X] [CommMonoid Y] (f : X →* Y) (x : X) :
  ((forget CommMonCat).map (CommMonCat.ofHom f)) x = f x := rfl

-- porting note: this was added to make the following examples work
/-- the morphism in `CommMonCat` associated to a `MonoidHom` -/
@[to_additive (attr := simp)]
def Hom.mk {X Y : CommMonCat} (f : X →* Y) : X ⟶ Y := f

/-- the morphism in `AddCommMonCat` associated to a `AddMonoidHom` -/
add_decl_doc AddCommMonCat.Hom.mk

-- porting note: this lemma was added to make automation work in `CommMonCat.forget_reflects_isos`
@[to_additive (attr := simp)]
lemma Hom.map_mul {X Y : CommMonCat} (f : X ⟶ Y) (x y : X) :
  ((forget CommMonCat).map f) (x * y) = f x * f y := by
  apply MonoidHom.map_mul (show MonoidHom X Y from f)

-- porting note: added as a complement to `Hom.map_mul`
@[to_additive (attr := simp)]
lemma Hom.map_one {X Y : CommMonCat} (f : X ⟶ Y) :
  ((forget CommMonCat).map f) (1 : X) = (1 : Y) := by
  apply MonoidHom.map_one (show MonoidHom X Y from f)

end CommMonCat

-- We verify that the coercions of morphisms to functions work correctly:
example {R S : MonCat} (f : R ⟶ S) : ↑R → ↑S := f

example {R S : CommMonCat} (f : R ⟶ S) : ↑R → ↑S := f

-- We verify that when constructing a morphism in `CommMonCat`,
-- when we construct the `toFun` field, the types are presented as `↥R`,
-- rather than `R.α` or (as we used to have) `↥(bundled.map comm_monoid.to_monoid R)`.
example (R : CommMonCat.{u}) : R ⟶ R :=
  -- porting note: the constructor `CommMonCat.Hom.mk` was added to make this example work
  CommMonCat.Hom.mk
    { toFun := fun x => by
        match_target (R : Type u)
        -- porting note: is there an equivalent of `match_hyp` in Lean4?
        --match_hyp x : (R : Type u)
        exact x * x
      map_one' := by simp
      map_mul' := fun x y => by
        dsimp
        rw [mul_assoc x y (x * y), ← mul_assoc y x y, mul_comm y x, mul_assoc, mul_assoc] }

variable {X Y : Type u}

attribute [local ext] ConcreteCategory.hom_ext

section

variable [Monoid X] [Monoid Y]

/-- Build an isomorphism in the category `MonCat` from a `MulEquiv` between `Monoid`s. -/
@[to_additive (attr := simps) AddEquiv.toAddMonCatIso
      "Build an isomorphism in the category `AddMonCat` from\nan `AddEquiv` between `AddMonoid`s."]
def MulEquiv.toMonCatIso (e : X ≃* Y) : MonCat.of X ≅ MonCat.of Y where
  hom := MonCat.ofHom e.toMonoidHom
  inv := MonCat.ofHom e.symm.toMonoidHom
set_option linter.uppercaseLean3 false in
#align mul_equiv.to_Mon_iso MulEquiv.toMonCatIso
set_option linter.uppercaseLean3 false in
#align add_equiv.to_AddMon_iso AddEquiv.toAddMonCatIso

end

section

variable [CommMonoid X] [CommMonoid Y]

/-- Build an isomorphism in the category `CommMonCat` from a `MulEquiv` between `CommMonoid`s. -/
@[to_additive (attr := simps) AddEquiv.toAddCommMonCatIso]
def MulEquiv.toCommMonCatIso (e : X ≃* Y) : CommMonCat.of X ≅ CommMonCat.of Y where
  hom := CommMonCat.ofHom e.toMonoidHom
  inv := CommMonCat.ofHom e.symm.toMonoidHom
set_option linter.uppercaseLean3 false in
#align mul_equiv.to_CommMon_iso MulEquiv.toCommMonCatIso
set_option linter.uppercaseLean3 false in
#align add_equiv.to_AddCommMon_iso AddEquiv.toAddCommMonCatIso

/-- Build an isomorphism in the category `AddCommMonCat`
from an `AddEquiv` between `AddCommMonoid`s. -/
add_decl_doc AddEquiv.toAddCommMonCatIso

end

namespace CategoryTheory.Iso

/-- Build a `MulEquiv` from an isomorphism in the category `MonCat`. -/
@[to_additive addMonCatIsoToAddEquiv
      "Build an `AddEquiv` from an isomorphism in the category\n`AddMonCat`."]
def monCatIsoToMulEquiv {X Y : MonCat} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom i.inv i.hom_inv_id i.inv_hom_id
set_option linter.uppercaseLean3 false in
#align category_theory.iso.Mon_iso_to_mul_equiv CategoryTheory.Iso.monCatIsoToMulEquiv
set_option linter.uppercaseLean3 false in
#align category_theory.iso.AddMon_iso_to_add_equiv CategoryTheory.Iso.addMonCatIsoToAddEquiv

/-- Build a `MulEquiv` from an isomorphism in the category `CommMonCat`. -/
@[to_additive "Build an `AddEquiv` from an isomorphism in the category\n`AddCommMonCat`."]
def commMonCatIsoToMulEquiv {X Y : CommMonCat} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom i.inv i.hom_inv_id i.inv_hom_id
set_option linter.uppercaseLean3 false in
#align category_theory.iso.CommMon_iso_to_mul_equiv CategoryTheory.Iso.commMonCatIsoToMulEquiv
set_option linter.uppercaseLean3 false in
#align category_theory.iso.CommMon_iso_to_add_equiv CategoryTheory.Iso.commMonCatIsoToAddEquiv

end CategoryTheory.Iso

/-- multiplicative equivalences between `Monoid`s are the same as (isomorphic to) isomorphisms
in `MonCat` -/
@[to_additive addEquivIsoAddMonCatIso]
def mulEquivIsoMonCatIso {X Y : Type u} [Monoid X] [Monoid Y] :
  X ≃* Y ≅ MonCat.of X ≅ MonCat.of Y where
  hom e := e.toMonCatIso
  inv i := i.monCatIsoToMulEquiv
set_option linter.uppercaseLean3 false in
#align mul_equiv_iso_Mon_iso mulEquivIsoMonCatIso
set_option linter.uppercaseLean3 false in
#align add_equiv_iso_AddMon_iso addEquivIsoAddMonCatIso

/-- additive equivalences between `AddMonoid`s are the same
as (isomorphic to) isomorphisms in `AddMonCat` -/
add_decl_doc addEquivIsoAddMonCatIso

/-- multiplicative equivalences between `CommMonoid`s are the same as (isomorphic to) isomorphisms
in `CommMonCat` -/
@[to_additive addEquivIsoAddCommMonCatIso]
def mulEquivIsoCommMonCatIso {X Y : Type u} [CommMonoid X] [CommMonoid Y] :
    X ≃* Y ≅ CommMonCat.of X ≅ CommMonCat.of Y
    where
  hom e := e.toCommMonCatIso
  inv i := i.commMonCatIsoToMulEquiv
set_option linter.uppercaseLean3 false in
#align mul_equiv_iso_CommMon_iso mulEquivIsoCommMonCatIso
set_option linter.uppercaseLean3 false in
#align add_equiv_iso_AddCommMon_iso addEquivIsoAddCommMonCatIso

/-- additive equivalences between `AddCommMonoid`s are
the same as (isomorphic to) isomorphisms in `AddCommMonCat` -/
add_decl_doc addEquivIsoAddCommMonCatIso

@[to_additive]
instance MonCat.forget_reflects_isos : ReflectsIsomorphisms (forget MonCat.{u}) where
  reflects {X Y} f _ := by
    let i := asIso ((forget MonCat).map f)
    let e : X ≃* Y := MulEquiv.mk i.toEquiv (by aesop)
    exact IsIso.of_iso e.toMonCatIso
set_option linter.uppercaseLean3 false in
#align Mon.forget_reflects_isos MonCat.forget_reflects_isos
set_option linter.uppercaseLean3 false in
#align AddMon.forget_reflects_isos AddMonCat.forget_reflects_isos

@[to_additive]
instance CommMonCat.forget_reflects_isos : ReflectsIsomorphisms (forget CommMonCat.{u}) where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommMonCat).map f)
    let e : X ≃* Y := MulEquiv.mk i.toEquiv
    -- porting note: same remark as for `MonCat.forget_reflects_iso`
      (MonoidHom.map_mul (show MonoidHom X Y from f))
    exact IsIso.of_iso e.toCommMonCatIso
set_option linter.uppercaseLean3 false in
#align CommMon.forget_reflects_isos CommMonCat.forget_reflects_isos
set_option linter.uppercaseLean3 false in
#align AddCommMon.forget_reflects_isos AddCommMonCat.forget_reflects_isos

-- porting note: this was added in order to ensure that `forget₂ CommMonCat MonCat`
-- automatically reflects isomorphisms
-- we could have used `CategoryTheory.ConcreteCategory.ReflectsIso` alternatively
instance : Full (forget₂ CommMonCat MonCat) where preimage f := f

example : ReflectsIsomorphisms (forget₂ CommMonCat MonCat) := inferInstance
