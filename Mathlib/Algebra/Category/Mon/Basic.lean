/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.category.Mon.basic
! leanprover-community/mathlib commit 4125b9adf2e268d1cf438092d690a78f7c664743
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.ConcreteCategory.BundledHom
import Mathbin.Algebra.PunitInstances
import Mathbin.CategoryTheory.Functor.ReflectsIsomorphisms

/-!
# Category instances for monoid, add_monoid, comm_monoid, and add_comm_monoid.

We introduce the bundled categories:
* `Mon`
* `AddMon`
* `CommMon`
* `AddCommMon`
along with the relevant forgetful functors between them.
-/


universe u v

open CategoryTheory

/-- The category of monoids and monoid morphisms. -/
@[to_additive AddMon]
def Mon : Type (u + 1) :=
  Bundled Monoid
#align Mon Mon
#align AddMon AddMon

/-- The category of additive monoids and monoid morphisms. -/
add_decl_doc AddMon

namespace Mon

/-- `monoid_hom` doesn't actually assume associativity. This alias is needed to make the category
theory machinery work. -/
@[to_additive
      "`add_monoid_hom` doesn't actually assume associativity. This alias is needed to make\nthe category theory machinery work."]
abbrev AssocMonoidHom (M N : Type _) [Monoid M] [Monoid N] :=
  MonoidHom M N
#align Mon.assoc_monoid_hom Mon.AssocMonoidHom
#align AddMon.assoc_add_monoid_hom AddMon.AssocAddMonoidHom

@[to_additive]
instance bundledHom : BundledHom AssocMonoidHom :=
  ⟨fun M N [Monoid M] [Monoid N] => @MonoidHom.toFun M N _ _, fun M [Monoid M] => @MonoidHom.id M _,
    fun M N P [Monoid M] [Monoid N] [Monoid P] => @MonoidHom.comp M N P _ _ _,
    fun M N [Monoid M] [Monoid N] => @MonoidHom.coe_inj M N _ _⟩
#align Mon.bundled_hom Mon.bundledHom
#align AddMon.bundled_hom AddMon.bundledHom

deriving instance LargeCategory, ConcreteCategory for Mon

attribute [to_additive] Mon.largeCategory Mon.concreteCategory

@[to_additive]
instance : CoeSort Mon (Type _) :=
  Bundled.hasCoeToSort

/-- Construct a bundled `Mon` from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [Monoid M] : Mon :=
  Bundled.of M
#align Mon.of Mon.of
#align AddMon.of AddMon.of

/-- Construct a bundled `Mon` from the underlying type and typeclass. -/
add_decl_doc AddMon.of

/-- Typecheck a `monoid_hom` as a morphism in `Mon`. -/
@[to_additive]
def ofHom {X Y : Type u} [Monoid X] [Monoid Y] (f : X →* Y) : of X ⟶ of Y :=
  f
#align Mon.of_hom Mon.ofHom
#align AddMon.of_hom AddMon.ofHom

/-- Typecheck a `add_monoid_hom` as a morphism in `AddMon`. -/
add_decl_doc AddMon.ofHom

@[simp]
theorem ofHom_apply {X Y : Type u} [Monoid X] [Monoid Y] (f : X →* Y) (x : X) : ofHom f x = f x :=
  rfl
#align Mon.of_hom_apply Mon.ofHom_apply

@[to_additive]
instance : Inhabited Mon :=
  ⟨-- The default instance for `monoid punit` is derived via `punit.comm_ring`,
        -- which breaks to_additive.
        @of
        PUnit <|
      @Group.toMonoid _ <| @CommGroup.toGroup _ PUnit.commGroup⟩

@[to_additive]
instance (M : Mon) : Monoid M :=
  M.str

@[simp, to_additive]
theorem coe_of (R : Type u) [Monoid R] : (Mon.of R : Type u) = R :=
  rfl
#align Mon.coe_of Mon.coe_of
#align AddMon.coe_of AddMon.coe_of

end Mon

/-- The category of commutative monoids and monoid morphisms. -/
@[to_additive AddCommMon]
def CommMon : Type (u + 1) :=
  Bundled CommMonoid
#align CommMon CommMon
#align AddCommMon AddCommMon

/-- The category of additive commutative monoids and monoid morphisms. -/
add_decl_doc AddCommMon

namespace CommMon

@[to_additive]
instance : BundledHom.ParentProjection CommMonoid.toMonoid :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for CommMon

attribute [to_additive] CommMon.largeCategory CommMon.concreteCategory

@[to_additive]
instance : CoeSort CommMon (Type _) :=
  Bundled.hasCoeToSort

/-- Construct a bundled `CommMon` from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [CommMonoid M] : CommMon :=
  Bundled.of M
#align CommMon.of CommMon.of
#align AddCommMon.of AddCommMon.of

/-- Construct a bundled `AddCommMon` from the underlying type and typeclass. -/
add_decl_doc AddCommMon.of

@[to_additive]
instance : Inhabited CommMon :=
  ⟨-- The default instance for `comm_monoid punit` is derived via `punit.comm_ring`,
        -- which breaks to_additive.
        @of
        PUnit <|
      @CommGroup.toCommMonoid _ PUnit.commGroup⟩

@[to_additive]
instance (M : CommMon) : CommMonoid M :=
  M.str

@[simp, to_additive]
theorem coe_of (R : Type u) [CommMonoid R] : (CommMon.of R : Type u) = R :=
  rfl
#align CommMon.coe_of CommMon.coe_of
#align AddCommMon.coe_of AddCommMon.coe_of

@[to_additive has_forget_to_AddMon]
instance hasForgetToMon : HasForget₂ CommMon Mon :=
  BundledHom.forget₂ _ _
#align CommMon.has_forget_to_Mon CommMon.hasForgetToMon
#align AddCommMon.has_forget_to_AddMon AddCommMon.hasForgetToAddMon

@[to_additive]
instance : Coe CommMon.{u} Mon.{u} where coe := (forget₂ CommMon Mon).obj

end CommMon

-- We verify that the coercions of morphisms to functions work correctly:
example {R S : Mon} (f : R ⟶ S) : (R : Type) → (S : Type) :=
  f

example {R S : CommMon} (f : R ⟶ S) : (R : Type) → (S : Type) :=
  f

-- We verify that when constructing a morphism in `CommMon`,
-- when we construct the `to_fun` field, the types are presented as `↥R`,
-- rather than `R.α` or (as we used to have) `↥(bundled.map comm_monoid.to_monoid R)`.
example (R : CommMon.{u}) : R ⟶ R :=
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

/-- Build an isomorphism in the category `Mon` from a `mul_equiv` between `monoid`s. -/
@[to_additive AddEquiv.toAddMonIso
      "Build an isomorphism in the category `AddMon` from\nan `add_equiv` between `add_monoid`s.",
  simps]
def MulEquiv.toMonIso (e : X ≃* Y) : Mon.of X ≅ Mon.of Y
    where
  Hom := e.toMonoidHom
  inv := e.symm.toMonoidHom
#align mul_equiv.to_Mon_iso MulEquiv.toMonIso
#align add_equiv.to_AddMon_iso AddEquiv.toAddMonIso

end

section

variable [CommMonoid X] [CommMonoid Y]

/-- Build an isomorphism in the category `CommMon` from a `mul_equiv` between `comm_monoid`s. -/
@[to_additive AddEquiv.toAddCommMonIso
      "Build an isomorphism in the category `AddCommMon`\nfrom an `add_equiv` between `add_comm_monoid`s.",
  simps]
def MulEquiv.toCommMonIso (e : X ≃* Y) : CommMon.of X ≅ CommMon.of Y
    where
  Hom := e.toMonoidHom
  inv := e.symm.toMonoidHom
#align mul_equiv.to_CommMon_iso MulEquiv.toCommMonIso
#align add_equiv.to_AddCommMon_iso AddEquiv.toAddCommMonIso

end

namespace CategoryTheory.Iso

/-- Build a `mul_equiv` from an isomorphism in the category `Mon`. -/
@[to_additive AddMon_iso_to_add_equiv
      "Build an `add_equiv` from an isomorphism in the category\n`AddMon`."]
def monIsoToMulEquiv {X Y : Mon} (i : X ≅ Y) : X ≃* Y :=
  i.Hom.toMulEquiv i.inv i.hom_inv_id i.inv_hom_id
#align category_theory.iso.Mon_iso_to_mul_equiv CategoryTheory.Iso.monIsoToMulEquiv
#align category_theory.iso.AddMon_iso_to_add_equiv CategoryTheory.Iso.addMonIsoToAddEquiv

/-- Build a `mul_equiv` from an isomorphism in the category `CommMon`. -/
@[to_additive "Build an `add_equiv` from an isomorphism in the category\n`AddCommMon`."]
def commMonIsoToMulEquiv {X Y : CommMon} (i : X ≅ Y) : X ≃* Y :=
  i.Hom.toMulEquiv i.inv i.hom_inv_id i.inv_hom_id
#align category_theory.iso.CommMon_iso_to_mul_equiv CategoryTheory.Iso.commMonIsoToMulEquiv
#align category_theory.iso.CommMon_iso_to_add_equiv CategoryTheory.Iso.commMonIsoToAddEquiv

end CategoryTheory.Iso

/-- multiplicative equivalences between `monoid`s are the same as (isomorphic to) isomorphisms
in `Mon` -/
@[to_additive addEquivIsoAddMonIso
      "additive equivalences between `add_monoid`s are the same\nas (isomorphic to) isomorphisms in `AddMon`"]
def mulEquivIsoMonIso {X Y : Type u} [Monoid X] [Monoid Y] : X ≃* Y ≅ Mon.of X ≅ Mon.of Y
    where
  Hom e := e.toMonIso
  inv i := i.monIsoToMulEquiv
#align mul_equiv_iso_Mon_iso mulEquivIsoMonIso
#align add_equiv_iso_AddMon_iso addEquivIsoAddMonIso

/-- multiplicative equivalences between `comm_monoid`s are the same as (isomorphic to) isomorphisms
in `CommMon` -/
@[to_additive addEquivIsoAddCommMonIso
      "additive equivalences between `add_comm_monoid`s are\nthe same as (isomorphic to) isomorphisms in `AddCommMon`"]
def mulEquivIsoCommMonIso {X Y : Type u} [CommMonoid X] [CommMonoid Y] :
    X ≃* Y ≅ CommMon.of X ≅ CommMon.of Y
    where
  Hom e := e.toCommMonIso
  inv i := i.commMonIsoToMulEquiv
#align mul_equiv_iso_CommMon_iso mulEquivIsoCommMonIso
#align add_equiv_iso_AddCommMon_iso addEquivIsoAddCommMonIso

@[to_additive]
instance Mon.forget_reflects_isos : ReflectsIsomorphisms (forget Mon.{u})
    where reflects X Y f _ := by
    skip
    let i := as_iso ((forget Mon).map f)
    let e : X ≃* Y := { f, i.to_equiv with }
    exact ⟨(is_iso.of_iso e.to_Mon_iso).1⟩
#align Mon.forget_reflects_isos Mon.forget_reflects_isos
#align AddMon.forget_reflects_isos AddMon.forget_reflects_isos

@[to_additive]
instance CommMon.forget_reflects_isos : ReflectsIsomorphisms (forget CommMon.{u})
    where reflects X Y f _ := by
    skip
    let i := as_iso ((forget CommMon).map f)
    let e : X ≃* Y := { f, i.to_equiv with }
    exact ⟨(is_iso.of_iso e.to_CommMon_iso).1⟩
#align CommMon.forget_reflects_isos CommMon.forget_reflects_isos
#align AddCommMon.forget_reflects_isos AddCommMon.forget_reflects_isos

/-!
Once we've shown that the forgetful functors to type reflect isomorphisms,
we automatically obtain that the `forget₂` functors between our concrete categories
reflect isomorphisms.
-/


example : ReflectsIsomorphisms (forget₂ CommMon Mon) := by infer_instance

