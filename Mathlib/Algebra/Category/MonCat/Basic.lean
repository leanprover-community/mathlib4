/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.category.Mon.basic
! leanprover-community/mathlib commit 4125b9adf2e268d1cf438092d690a78f7c664743
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
@[to_additive
      "`AddMonoidHom` doesn't actually assume associativity. This alias is needed to make\nthe category theory machinery work."]
abbrev AssocMonoidHom (M N : Type _) [Monoid M] [Monoid N] :=
  MonoidHom M N
set_option linter.uppercaseLean3 false in
#align Mon.assoc_monoid_hom MonCat.AssocMonoidHom
set_option linter.uppercaseLean3 false in
#align AddMon.assoc_add_monoid_hom AddMonCat.AssocAddMonoidHom

@[to_additive]
instance bundledHom : BundledHom AssocMonoidHom where
  -- porting note: it was originally `MonoidHom.toFun`, is there a way
  -- to coerce directly to functions?
  toFun  _ _ f := (@MonoidHom.toMulHom _ _ _ _ f).toFun
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

@[simp]
theorem ofHom_apply {X Y : Type u} [Monoid X] [Monoid Y] (f : X →* Y) (x : X) :
  (ofHom f) x = f x := rfl
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

end CommMonCat

-- We verify that the coercions of morphisms to functions work correctly:
example {R S : MonCat} (f : R ⟶ S) : ↑R → ↑S := f

example {R S : CommMonCat} (f : R ⟶ S) : ↑R → ↑S := f

-- We verify that when constructing a morphism in `CommMonCat`,
-- when we construct the `toFun` field, the types are presented as `↥R`,
-- rather than `R.α` or (as we used to have) `↥(bundled.map comm_monoid.to_monoid R)`.
example (R : CommMonCat.{u}) : R ⟶ R :=
  { toFun := fun x => by
      match_target(R : Type u)
      match_hyp x : (R : Type u)
      exact x * x
    map_one' := by simp
    map_mul' := fun x y => by
      rw [mul_assoc x y (x * y), ← mul_assoc y x y, mul_comm y x, mul_assoc, mul_assoc] }

variable {X Y : Type u}

section

variable [Monoid X] [Monoid Y]

/-- Build an isomorphism in the category `MonCat` from a `MulEquiv` between `Monoid`s. -/
@[to_additive AddEquiv.toAddMonCatIso
      "Build an isomorphism in the category `AddMonCat` from\nan `AddEquiv` between `AddMonoid`s.",
  simps]
def MulEquiv.toMonCatIso (e : X ≃* Y) : MonCat.of X ≅ MonCat.of Y where
  hom := e.toMonoidHom
  inv := e.symm.toMonoidHom
  -- porting note: this fields were filled automatically in mathlib
  hom_inv_id := sorry
  inv_hom_id := sorry
set_option linter.uppercaseLean3 false in
#align mul_equiv.to_Mon_iso MulEquiv.toMonCatIso
set_option linter.uppercaseLean3 false in
#align add_equiv.to_AddMon_iso AddEquiv.toAddMonCatIso

end

section

variable [CommMonoid X] [CommMonoid Y]

/-- Build an isomorphism in the category `CommMonCat` from a `MulEquiv` between `CommMonoid`s. -/
@[to_additive AddEquiv.toAddCommMonCatIso
      "Build an isomorphism in the category `AddCommMonCat`\nfrom an `AddEquiv` between `AddCommMonoid`s.",
  simps]
def MulEquiv.toCommMonCatIso (e : X ≃* Y) : CommMonCat.of X ≅ CommMonCat.of Y where
  hom := e.toMonoidHom
  inv := e.symm.toMonoidHom
  -- porting note: this fields were filled automatically in mathlib
  hom_inv_id := sorry
  inv_hom_id := sorry
set_option linter.uppercaseLean3 false in
#align mul_equiv.to_CommMon_iso MulEquiv.toCommMonCatIso
set_option linter.uppercaseLean3 false in
#align add_equiv.to_AddCommMon_iso AddEquiv.toAddCommMonCatIso

end

namespace CategoryTheory.Iso

/-- Build a `MulEquiv` from an isomorphism in the category `MonCat`. -/
@[to_additive addMonCatIsoToAddEquiv
      "Build an `AddEquiv` from an isomorphism in the category\n`AddMonCat`."]
def monCatIsoToMulEquiv {X Y : MonCat} (i : X ≅ Y) : X ≃* Y :=
  i.hom.toMulEquiv i.inv i.hom_inv_id i.inv_hom_id
set_option linter.uppercaseLean3 false in
#align category_theory.iso.Mon_iso_to_mul_equiv CategoryTheory.Iso.monCatIsoToMulEquiv
set_option linter.uppercaseLean3 false in
#align category_theory.iso.AddMon_iso_to_add_equiv CategoryTheory.Iso.addMonCatIsoToAddEquiv

/-- Build a `MulEquiv` from an isomorphism in the category `CommMonCat`. -/
@[to_additive "Build an `AddEquiv` from an isomorphism in the category\n`AddCommMonCat`."]
def commMonCatIsoToMulEquiv {X Y : CommMonCat} (i : X ≅ Y) : X ≃* Y :=
  i.hom.toMulEquiv i.inv i.hom_inv_id i.inv_hom_id
set_option linter.uppercaseLean3 false in
#align category_theory.iso.CommMon_iso_to_mul_equiv CategoryTheory.Iso.commMonCatIsoToMulEquiv
set_option linter.uppercaseLean3 false in
#align category_theory.iso.CommMon_iso_to_add_equiv CategoryTheory.Iso.commMonCatIsoToAddEquiv

end CategoryTheory.Iso

/-- multiplicative equivalences between `Monoid`s are the same as (isomorphic to) isomorphisms
in `MonCat` -/
@[to_additive addEquivIsoAddMonCatIso
      "additive equivalences between `AddMonoid`s are the same\nas (isomorphic to) isomorphisms in `AddMonCat`"]
def mulEquivIsoMonCatIso {X Y : Type u} [Monoid X] [Monoid Y] : X ≃* Y ≅ MonCat.of X ≅ MonCat.of Y
    where
  hom e := e.toMonIso
  inv i := i.monCatIsoToMulEquiv
set_option linter.uppercaseLean3 false in
#align mul_equiv_iso_Mon_iso mulEquivIsoMonCatIso
set_option linter.uppercaseLean3 false in
#align add_equiv_iso_AddMon_iso addEquivIsoAddMonCatIso

/-- multiplicative equivalences between `CommMonoid`s are the same as (isomorphic to) isomorphisms
in `CommMonCat` -/
@[to_additive addEquivIsoAddCommMonCatIso
      "additive equivalences between `AddCommMonoid`s are\nthe same as (isomorphic to) isomorphisms in `AddCommMonCat`"]
def mulEquivIsoCommMonCatIso {X Y : Type u} [CommMonoid X] [CommMonoid Y] :
    X ≃* Y ≅ CommMonCat.of X ≅ CommMonCat.of Y
    where
  hom e := e.toCommMonCatIso
  inv i := i.commMonCatIsoToMulEquiv
set_option linter.uppercaseLean3 false in
#align mul_equiv_iso_CommMon_iso mulEquivIsoCommMonCatIso
set_option linter.uppercaseLean3 false in
#align add_equiv_iso_AddCommMon_iso addEquivIsoAddCommMonCatIso

@[to_additive]
instance MonCat.forget_reflects_isos : ReflectsIsomorphisms (forget MonCat.{u}) where
  reflects {X Y} f _ := by
    let i := asIso ((forget MonCat).map f)
    -- porting note: it was `let e : X ≃* Y := { f, i.to_equiv with }`
    let e : X ≃* Y := by
      refine' ⟨i.toEquiv, _⟩
      intros x y
      dsimp
      simp
      sorry
    exact IsIso.of_iso e.toMonCatIso
#align Mon.forget_reflects_isos MonCat.forget_reflects_isos
#align AddMon.forget_reflects_isos AddMonCat.forget_reflects_isos

@[to_additive]
instance CommMonCat.forget_reflects_isos : ReflectsIsomorphisms (forget CommMon.{u})
    where reflects X Y f _ := by
    skip
    let i := as_iso ((forget CommMon).map f)
    let e : X ≃* Y := { f, i.to_equiv with }
    exact ⟨(is_iso.of_iso e.to_CommMon_iso).1⟩
#align CommMon.forget_reflects_isos CommMonCat.forget_reflects_isos
#align AddCommMon.forget_reflects_isos AddCommMonCat.forget_reflects_isos

/-!
Once we've shown that the forgetful functors to type reflect isomorphisms,
we automatically obtain that the `forget₂` functors between our concrete categories
reflect isomorphisms.
-/


example : ReflectsIsomorphisms (forget₂ CommMonCat MonCat) := by infer_instance
