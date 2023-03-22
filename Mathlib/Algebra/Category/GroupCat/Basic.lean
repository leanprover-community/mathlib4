/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module algebra.category.Group.basic
! leanprover-community/mathlib commit 524793de15bc4c52ee32d254e7d7867c7176b3af
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.CategoryTheory.Endomorphism

/-!
# Category instances for group, add_group, comm_group, and add_comm_group.

We introduce the bundled categories:
* `GroupCat`
* `AddGroupCat`
* `CommGroupCat`
* `AddCommGroupCat`
along with the relevant forgetful functors between them, and to the bundled monoid categories.
-/


universe u v

open CategoryTheory

/-- The category of groups and group morphisms. -/
@[to_additive]
def GroupCat : Type (u + 1) :=
  Bundled Group
set_option linter.uppercaseLean3 false in
#align Group GroupCat
set_option linter.uppercaseLean3 false in
#align AddGroup AddGroupCat

/-- The category of additive groups and group morphisms -/
add_decl_doc AddGroupCat

namespace GroupCat

@[to_additive]
instance : BundledHom.ParentProjection
  (fun {α : Type _} (h : Group α) => h.toDivInvMonoid.toMonoid) := ⟨⟩

instance largeCategory : LargeCategory GroupCat := by
  dsimp only [GroupCat]
  infer_instance

instance concreteCategory : ConcreteCategory GroupCat := by
  dsimp only [GroupCat]
  infer_instance

attribute [to_additive] GroupCat.largeCategory GroupCat.concreteCategory

@[to_additive]
instance : CoeSort GroupCat (Type _) := by
  dsimp only [GroupCat]
  infer_instance

/-- Construct a bundled `Group` from the underlying type and typeclass. -/
@[to_additive]
def of (X : Type u) [Group X] : GroupCat :=
  Bundled.of X
set_option linter.uppercaseLean3 false in
#align Group.of GroupCat.of
set_option linter.uppercaseLean3 false in
#align AddGroup.of AddGroupCat.of

/-- Construct a bundled `AddGroup` from the underlying type and typeclass. -/
add_decl_doc AddGroupCat.of

/-- Typecheck a `MonoidHom` as a morphism in `GroupCat`. -/
@[to_additive]
def ofHom {X Y : Type u} [Group X] [Group Y] (f : X →* Y) : of X ⟶ of Y :=
  f
set_option linter.uppercaseLean3 false in
#align Group.of_hom GroupCat.ofHom
set_option linter.uppercaseLean3 false in
#align AddGroup.of_hom AddGroupCat.ofHom

/-- Typecheck a `add_monoid_hom` as a morphism in `AddGroup`. -/
add_decl_doc AddGroupCat.ofHom

-- porting note: this instance was not necessary in mathlib
@[to_additive]
instance {X Y : GroupCat} : CoeFun (X ⟶ Y) fun _ => X → Y :=
  ConcreteCategory.hasCoeToFun

-- porting note: this was added to ease automation
@[to_additive (attr := simp)]
lemma id_apply {X : GroupCat} (x : X) :
  (𝟙 X) x = x := rfl

-- porting note: this was added to ease automation
@[to_additive (attr := simp)]
lemma comp_apply {X Y Z : GroupCat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
  (f ≫ g) x = g (f x) := rfl

@[to_additive (attr := simp)]
theorem ofHom_apply {X Y : Type _} [Group X] [Group Y] (f : X →* Y) (x : X) :
    (ofHom f) x = f x :=
  rfl
set_option linter.uppercaseLean3 false in
#align Group.of_hom_apply GroupCat.ofHom_apply
set_option linter.uppercaseLean3 false in
#align AddGroup.of_hom_apply AddGroupCat.ofHom_apply

@[to_additive]
instance (G : GroupCat) : Group G :=
  G.str

-- porting note: added to make `one_apply` work
@[to_additive]
instance (G : GroupCat) : Group ((forget GroupCat).obj G) :=
  G.str

-- porting note: simp attribute was removed to please the linter
@[to_additive]
theorem coe_of (R : Type u) [Group R] : ↑(GroupCat.of R) = R :=
  rfl
set_option linter.uppercaseLean3 false in
#align Group.coe_of GroupCat.coe_of
set_option linter.uppercaseLean3 false in
#align AddGroup.coe_of AddGroupCat.coe_of

@[to_additive]
instance : Inhabited GroupCat :=
  ⟨GroupCat.of PUnit⟩

@[to_additive]
instance ofUnique (G : Type _) [Group G] [i : Unique G] : Unique (GroupCat.of G) :=
  i
set_option linter.uppercaseLean3 false in
#align Group.of_unique GroupCat.ofUnique
set_option linter.uppercaseLean3 false in
#align AddGroup.of_unique AddGroupCat.ofUnique

-- porting note: this instance was not necessary in mathlib
@[to_additive]
instance (G H : GroupCat) : One (G ⟶ H) := (inferInstance : One (MonoidHom G H))

@[to_additive (attr := simp)]
theorem one_apply (G H : GroupCat) (g : G) : ((forget GroupCat).map (1 : G ⟶ H)) g = 1 :=
  rfl
set_option linter.uppercaseLean3 false in
#align Group.one_apply GroupCat.one_apply
set_option linter.uppercaseLean3 false in
#align AddGroup.zero_apply AddGroupCat.zero_apply

@[to_additive (attr := ext)]
theorem ext (G H : GroupCat) (f₁ f₂ : G ⟶ H) (w : ∀ (x : ↑G), f₁ x = f₂ x) : f₁ = f₂ :=
  ConcreteCategory.hom_ext _ _ w
set_option linter.uppercaseLean3 false in
#align Group.ext GroupCat.ext
set_option linter.uppercaseLean3 false in
#align AddGroup.ext AddGroupCat.ext

@[to_additive hasForgetToAddMonCat]
instance hasForgetToMonCat : HasForget₂ GroupCat MonCat :=
  BundledHom.forget₂ _ _
set_option linter.uppercaseLean3 false in
#align Group.has_forget_to_Mon GroupCat.hasForgetToMonCat
set_option linter.uppercaseLean3 false in
#align AddGroup.has_forget_to_AddMon AddGroupCat.hasForgetToAddMonCat

@[to_additive]
instance : Coe GroupCat.{u} MonCat.{u} where coe := (forget₂ GroupCat MonCat).obj

-- porting note: this was added to ease the port
/-- the morphism in `GroupCat` associated to a `MonoidHom` -/
@[to_additive]
def Hom.mk {X Y : GroupCat} (f : X →* Y) : X ⟶ Y := f

/-- the morphism in `AddGroupCat` associated to a `AddMonoidHom` -/
add_decl_doc AddGroupCat.Hom.mk

@[to_additive (attr := simp)]
lemma Hom.mk_apply {X Y : GroupCat} (f : X →* Y) (x : X) :
  (Hom.mk f) x = f x := rfl

-- porting note: added to ease automation
@[to_additive (attr := simp)]
lemma Hom.map_mul {X Y : GroupCat} (f : X ⟶ Y) (x y : X) : f (x * y) = f x * f y := by
  apply MonoidHom.map_mul (show MonoidHom X Y from f)

-- porting note: added to ease automation
@[to_additive (attr := simp)]
lemma Hom.map_one {X Y : GroupCat} (f : X ⟶ Y) : f (1 : X) = 1 := by
  apply MonoidHom.map_one (show MonoidHom X Y from f)

end GroupCat

/-- The category of commutative groups and group morphisms. -/
@[to_additive]
def CommGroupCat : Type (u + 1) :=
  Bundled CommGroup
set_option linter.uppercaseLean3 false in
#align CommGroup CommGroupCat
set_option linter.uppercaseLean3 false in
#align AddCommGroup AddCommGroupCat

/-- The category of additive commutative groups and group morphisms. -/
add_decl_doc AddCommGroupCat

/-- `Ab` is an abbreviation for `AddCommGroup`, for the sake of mathematicians' sanity. -/
abbrev Ab :=
  AddCommGroupCat
set_option linter.uppercaseLean3 false in
#align Ab Ab

namespace CommGroupCat

@[to_additive]
instance : BundledHom.ParentProjection @CommGroup.toGroup :=
  ⟨⟩

instance largeCategory : LargeCategory CommGroupCat := by
  dsimp only [CommGroupCat]
  infer_instance

instance concreteCategory : ConcreteCategory CommGroupCat := by
  dsimp only [CommGroupCat]
  infer_instance

attribute [to_additive] CommGroupCat.largeCategory CommGroupCat.concreteCategory

@[to_additive]
instance : CoeSort CommGroupCat (Type _) := by
  dsimp only [CommGroupCat]
  infer_instance

/-- Construct a bundled `CommGroup` from the underlying type and typeclass. -/
@[to_additive]
def of (G : Type u) [CommGroup G] : CommGroupCat :=
  Bundled.of G
set_option linter.uppercaseLean3 false in
#align CommGroup.of CommGroupCat.of
set_option linter.uppercaseLean3 false in
#align AddCommGroup.of AddCommGroupCat.of

/-- Construct a bundled `AddCommGroup` from the underlying type and typeclass. -/
add_decl_doc AddCommGroupCat.of

/-- Typecheck a `MonoidHom` as a morphism in `CommGroup`. -/
@[to_additive]
def ofHom {X Y : Type u} [CommGroup X] [CommGroup Y] (f : X →* Y) : of X ⟶ of Y :=
  f
set_option linter.uppercaseLean3 false in
#align CommGroup.of_hom CommGroupCat.ofHom
set_option linter.uppercaseLean3 false in
#align AddCommGroup.of_hom AddCommGroupCat.ofHom

/-- Typecheck a `AddMonoidHom` as a morphism in `AddCommGroup`. -/
add_decl_doc AddCommGroupCat.ofHom

-- porting note: this instance was not necessary in mathlib
@[to_additive]
instance {X Y : CommGroupCat} : CoeFun (X ⟶ Y) fun _ => X → Y :=
  ConcreteCategory.hasCoeToFun

-- porting note: added to ease automation
@[to_additive (attr := simp)]
lemma id_apply {X : CommGroupCat} (x : X) :
  (𝟙 X) x = x := rfl

-- porting note: added to ease automation
@[to_additive (attr := simp)]
lemma comp_apply {X Y Z : CommGroupCat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
  (f ≫ g) x = g (f x) := by apply CategoryTheory.comp_apply

@[to_additive (attr := simp)]
theorem ofHom_apply {X Y : Type _} [CommGroup X] [CommGroup Y] (f : X →* Y) (x : X) :
    (ofHom f) x = f x :=
  rfl
set_option linter.uppercaseLean3 false in
#align CommGroup.of_hom_apply CommGroupCat.ofHom_apply
set_option linter.uppercaseLean3 false in
#align AddCommGroup.of_hom_apply AddCommGroupCat.ofHom_apply

@[to_additive]
instance commGroupInstance (G : CommGroupCat) : CommGroup G :=
  G.str
set_option linter.uppercaseLean3 false in
#align CommGroup.comm_group_instance CommGroupCat.commGroupInstance
set_option linter.uppercaseLean3 false in
#align AddCommGroup.add_comm_group_instance AddCommGroupCat.addCommGroupInstance

-- porting note: simp attribute was removed to please the linter
@[to_additive]
theorem coe_of (R : Type u) [CommGroup R] : (CommGroupCat.of R : Type u) = R :=
  rfl
set_option linter.uppercaseLean3 false in
#align CommGroup.coe_of CommGroupCat.coe_of
set_option linter.uppercaseLean3 false in
#align AddCommGroup.coe_of AddCommGroupCat.coe_of

@[to_additive]
instance : Inhabited CommGroupCat :=
  ⟨CommGroupCat.of PUnit⟩

@[to_additive]
instance ofUnique (G : Type _) [CommGroup G] [i : Unique G] : Unique (CommGroupCat.of G) :=
  i
set_option linter.uppercaseLean3 false in
#align CommGroup.of_unique CommGroupCat.ofUnique
set_option linter.uppercaseLean3 false in
#align AddCommGroup.of_unique AddCommGroupCat.ofUnique

-- porting note: this instance was not necessary in mathlib
@[to_additive]
instance (G H : CommGroupCat) : One (G ⟶ H) := (inferInstance : One (MonoidHom G H))

@[to_additive (attr := simp)]
theorem one_apply (G H : CommGroupCat) (g : G) : (1 : G ⟶ H) g = 1 :=
  rfl
set_option linter.uppercaseLean3 false in
#align CommGroup.one_apply CommGroupCat.one_apply
set_option linter.uppercaseLean3 false in
#align AddCommGroup.zero_apply AddCommGroupCat.zero_apply

@[to_additive (attr := ext)]
theorem ext (G H : CommGroupCat) (f₁ f₂ : G ⟶ H) (w : ∀ x, f₁ x = f₂ x) : f₁ = f₂ :=
  ConcreteCategory.hom_ext _ _ w
set_option linter.uppercaseLean3 false in
#align CommGroup.ext CommGroupCat.ext
set_option linter.uppercaseLean3 false in
#align AddCommGroup.ext AddCommGroupCat.ext

@[to_additive]
instance hasForgetToGroup : HasForget₂ CommGroupCat GroupCat :=
  BundledHom.forget₂ _ _
set_option linter.uppercaseLean3 false in
#align CommGroup.has_forget_to_Group CommGroupCat.hasForgetToGroup
set_option linter.uppercaseLean3 false in
#align AddCommGroup.has_forget_to_AddGroup AddCommGroupCat.hasForgetToAddGroup

@[to_additive]
instance : Coe CommGroupCat.{u} GroupCat.{u} where coe := (forget₂ CommGroupCat GroupCat).obj

@[to_additive hasForgetToAddCommMonCat]
instance hasForgetToCommMonCat : HasForget₂ CommGroupCat CommMonCat :=
  InducedCategory.hasForget₂ fun G : CommGroupCat => CommMonCat.of G
set_option linter.uppercaseLean3 false in
#align CommGroup.has_forget_to_CommMon CommGroupCat.hasForgetToCommMonCat
set_option linter.uppercaseLean3 false in
#align AddCommGroup.has_forget_to_AddCommMon AddCommGroupCat.hasForgetToAddCommMonCat

@[to_additive]
instance : Coe CommGroupCat.{u} CommMonCat.{u} where coe := (forget₂ CommGroupCat CommMonCat).obj

-- porting note: this was added to ease the port
/-- the morphism in `CommGroupCat` associated to a `MonoidHom` -/
@[to_additive]
def Hom.mk {X Y : CommGroupCat} (f : X →* Y) : X ⟶ Y := f

/-- the morphism in `AddCommGroupCat` associated to a `AddMonoidHom` -/
add_decl_doc AddCommGroupCat.Hom.mk

@[to_additive (attr := simp)]
lemma Hom.mk_apply {X Y : CommGroupCat} (f : X →* Y) (x : X) :
  (Hom.mk f) x = f x := rfl

-- porting note: added to ease automation
@[to_additive (attr := simp)]
lemma Hom.map_mul {X Y : CommGroupCat} (f : X ⟶ Y) (x y : X) : f (x * y) = f x * f y := by
  apply MonoidHom.map_mul (show MonoidHom X Y from f)

-- porting note: added to ease automation
@[to_additive (attr := simp)]
lemma Hom.map_one {X Y : CommGroupCat} (f : X ⟶ Y) : f (1 : X) = 1 := by
  apply MonoidHom.map_one (show MonoidHom X Y from f)

-- This example verifies an improvement possible in Lean 3.8.
-- Before that, to have `monoid_hom.map_map` usable by `simp` here,
-- we had to mark all the concrete category `has_coe_to_sort` instances reducible.
-- Now, it just works.
@[to_additive]
example {R S : CommGroupCat} (i : R ⟶ S) (r : R) (h : r = 1) : i r = 1 := by simp [h]

end CommGroupCat

namespace AddCommGroupCat

-- Note that because `ℤ : Type 0`, this forces `G : AddCommGroup.{0}`,
-- so we write this explicitly to be clear.
-- TODO generalize this, requiring a `ulift_instances.lean` file
/-- Any element of an abelian group gives a unique morphism from `ℤ` sending
`1` to that element. -/
def asHom {G : AddCommGroupCat.{0}} (g : G) : AddCommGroupCat.of ℤ ⟶ G :=
  zmultiplesHom G g
set_option linter.uppercaseLean3 false in
#align AddCommGroup.as_hom AddCommGroupCat.asHom

@[simp]
theorem asHom_apply {G : AddCommGroupCat.{0}} (g : G) (i : ℤ) : (asHom g) i = i • g :=
  rfl
set_option linter.uppercaseLean3 false in
#align AddCommGroup.as_hom_apply AddCommGroupCat.asHom_apply

theorem asHom_injective {G : AddCommGroupCat.{0}} : Function.Injective (@asHom G) := fun h k w => by
  convert congr_arg (fun k : AddCommGroupCat.of ℤ ⟶ G => (k : ℤ → G) (1 : ℤ)) w <;> simp
set_option linter.uppercaseLean3 false in
#align AddCommGroup.as_hom_injective AddCommGroupCat.asHom_injective

@[ext]
theorem int_hom_ext {G : AddCommGroupCat.{0}} (f g : AddCommGroupCat.of ℤ ⟶ G)
    (w : f (1 : ℤ) = g (1 : ℤ)) : f = g :=
  @AddMonoidHom.ext_int G _ f g w
set_option linter.uppercaseLean3 false in
#align AddCommGroup.int_hom_ext AddCommGroupCat.int_hom_ext

-- TODO: this argument should be generalised to the situation where
-- the forgetful functor is representable.
theorem injective_of_mono {G H : AddCommGroupCat.{0}} (f : G ⟶ H) [Mono f] : Function.Injective f :=
  fun g₁ g₂ h => by
  have t0 : asHom g₁ ≫ f = asHom g₂ ≫ f := by
    apply int_hom_ext
    simpa using h
  have t1 : asHom g₁ = asHom g₂ := (cancel_mono _).1 t0
  apply asHom_injective t1
set_option linter.uppercaseLean3 false in
#align AddCommGroup.injective_of_mono AddCommGroupCat.injective_of_mono

end AddCommGroupCat

/-- Build an isomorphism in the category `GroupCat` from a `MulEquiv` between `Group`s. -/
@[to_additive (attr := simps)]
def MulEquiv.toGroupIso {X Y : GroupCat} (e : X ≃* Y) : X ≅ Y where
  hom := GroupCat.Hom.mk e.toMonoidHom
  inv := GroupCat.Hom.mk e.symm.toMonoidHom
set_option linter.uppercaseLean3 false in
#align mul_equiv.to_Group_iso MulEquiv.toGroupIso
set_option linter.uppercaseLean3 false in
#align add_equiv.to_AddGroup_iso AddEquiv.toAddGroupIso

/-- Build an isomorphism in the category `AddGroup` from an `AddEquiv` between `AddGroup`s. -/
add_decl_doc AddEquiv.toAddGroupIso

/-- Build an isomorphism in the category `CommGroupCat` from a `MulEquiv`
between `CommGroup`s. -/
@[to_additive (attr := simps)]
def MulEquiv.toCommGroupIso {X Y : CommGroupCat} (e : X ≃* Y) : X ≅ Y
    where
  hom := CommGroupCat.Hom.mk e.toMonoidHom
  inv := CommGroupCat.Hom.mk e.symm.toMonoidHom
set_option linter.uppercaseLean3 false in
#align mul_equiv.to_CommGroup_iso MulEquiv.toCommGroupIso
set_option linter.uppercaseLean3 false in
#align add_equiv.to_AddCommGroup_iso AddEquiv.toAddCommGroupIso

/-- Build an isomorphism in the category `AddCommGroupCat` from a `AddEquiv`
between `AddCommGroup`s. -/
add_decl_doc AddEquiv.toAddCommGroupIso

namespace CategoryTheory.Iso

/-- Build a `mul_equiv` from an isomorphism in the category `Group`. -/
@[to_additive AddGroup_iso_to_add_equiv
      "Build an `add_equiv` from an isomorphism in the category\n`AddGroup`.",
  simps]
def groupIsoToMulEquiv {X Y : GroupCat} (i : X ≅ Y) : X ≃* Y :=
  i.Hom.toMulEquiv i.inv i.hom_inv_id i.inv_hom_id
set_option linter.uppercaseLean3 false in
#align category_theory.iso.Group_iso_to_mul_equiv CategoryTheory.Iso.groupIsoToMulEquiv
set_option linter.uppercaseLean3 false in
#align category_theory.iso.AddGroup_iso_to_add_equiv CategoryTheory.Iso.addGroupIsoToAddEquiv

/-- Build a `mul_equiv` from an isomorphism in the category `CommGroup`. -/
@[to_additive AddCommGroup_iso_to_add_equiv
      "Build an `add_equiv` from an isomorphism\nin the category `AddCommGroup`.",
  simps]
def commGroupIsoToMulEquiv {X Y : CommGroupCat} (i : X ≅ Y) : X ≃* Y :=
  i.Hom.toMulEquiv i.inv i.hom_inv_id i.inv_hom_id
set_option linter.uppercaseLean3 false in
#align category_theory.iso.CommGroup_iso_to_mul_equiv CategoryTheory.Iso.commGroupIsoToMulEquiv
set_option linter.uppercaseLean3 false in
#align category_theory.iso.AddCommGroup_iso_to_add_equiv CategoryTheory.Iso.addCommGroupIsoToAddEquiv

end CategoryTheory.Iso

/-- multiplicative equivalences between `group`s are the same as (isomorphic to) isomorphisms
in `Group` -/
@[to_additive addEquivIsoAddGroupIso
      "additive equivalences between `add_group`s are the same\nas (isomorphic to) isomorphisms in `AddGroup`"]
def mulEquivIsoGroupIso {X Y : GroupCat.{u}} : X ≃* Y ≅ X ≅ Y
    where
  Hom e := e.toGroupIso
  inv i := i.groupIsoToMulEquiv
set_option linter.uppercaseLean3 false in
#align mul_equiv_iso_Group_iso mulEquivIsoGroupIso
set_option linter.uppercaseLean3 false in
#align add_equiv_iso_AddGroup_iso addEquivIsoAddGroupIso

/-- multiplicative equivalences between `comm_group`s are the same as (isomorphic to) isomorphisms
in `CommGroup` -/
@[to_additive addEquivIsoAddCommGroupIso
      "additive equivalences between `add_comm_group`s are\nthe same as (isomorphic to) isomorphisms in `AddCommGroup`"]
def mulEquivIsoCommGroupIso {X Y : CommGroupCat.{u}} : X ≃* Y ≅ X ≅ Y
    where
  Hom e := e.toCommGroupIso
  inv i := i.commGroupIsoToMulEquiv
set_option linter.uppercaseLean3 false in
#align mul_equiv_iso_CommGroup_iso mulEquivIsoCommGroupIso
set_option linter.uppercaseLean3 false in
#align add_equiv_iso_AddCommGroup_iso addEquivIsoAddCommGroupIso

namespace CategoryTheory.Aut

/-- The (bundled) group of automorphisms of a type is isomorphic to the (bundled) group
of permutations. -/
def isoPerm {α : Type u} : GroupCat.of (Aut α) ≅ GroupCat.of (Equiv.Perm α)
    where
  Hom := ⟨fun g => g.toEquiv, by tidy, by tidy⟩
  inv := ⟨fun g => g.toIso, by tidy, by tidy⟩
#align category_theory.Aut.iso_perm CategoryTheory.Aut.isoPerm

/-- The (unbundled) group of automorphisms of a type is `mul_equiv` to the (unbundled) group
of permutations. -/
def mulEquivPerm {α : Type u} : Aut α ≃* Equiv.Perm α :=
  isoPerm.groupIsoToMulEquiv
#align category_theory.Aut.mul_equiv_perm CategoryTheory.Aut.mulEquivPerm

end CategoryTheory.Aut

@[to_additive]
instance GroupCat.forget_reflects_isos : ReflectsIsomorphisms (forget GroupCat.{u})
    where reflects X Y f _ := by
    skip
    let i := as_iso ((forget GroupCat).map f)
    let e : X ≃* Y := { f, i.to_equiv with }
    exact ⟨(is_iso.of_iso e.to_Group_iso).1⟩
set_option linter.uppercaseLean3 false in
#align Group.forget_reflects_isos GroupCat.forget_reflects_isos
set_option linter.uppercaseLean3 false in
#align AddGroup.forget_reflects_isos AddGroupCat.forget_reflects_isos

@[to_additive]
instance CommGroupCat.forget_reflects_isos : ReflectsIsomorphisms (forget CommGroupCat.{u})
    where reflects X Y f _ := by
    skip
    let i := as_iso ((forget CommGroupCat).map f)
    let e : X ≃* Y := { f, i.to_equiv with }
    exact ⟨(is_iso.of_iso e.to_CommGroup_iso).1⟩
set_option linter.uppercaseLean3 false in
#align CommGroup.forget_reflects_isos CommGroupCat.forget_reflects_isos
set_option linter.uppercaseLean3 false in
#align AddCommGroup.forget_reflects_isos AddCommGroupCat.forget_reflects_isos
