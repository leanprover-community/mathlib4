/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.CategoryTheory.Endomorphism

#align_import algebra.category.Group.basic from "leanprover-community/mathlib"@"524793de15bc4c52ee32d254e7d7867c7176b3af"

/-!
# Category instances for Group, AddGroup, CommGroup, and AddCommGroup.

We introduce the bundled categories:
* `Grp`
* `AddGrp`
* `CommGrp`
* `AddCommGrp`
along with the relevant forgetful functors between them, and to the bundled monoid categories.
-/

set_option autoImplicit true


universe u v

open CategoryTheory

/-- The category of groups and group morphisms. -/
@[to_additive]
def Grp : Type (u + 1) :=
  Bundled Group
set_option linter.uppercaseLean3 false in
#align Group Grp
set_option linter.uppercaseLean3 false in
#align AddGroup AddGrp

/-- The category of additive groups and group morphisms -/
add_decl_doc AddGrp

namespace Grp

@[to_additive]
instance : BundledHom.ParentProjection
  (fun {α : Type*} (h : Group α) => h.toDivInvMonoid.toMonoid) := ⟨⟩

deriving instance LargeCategory for Grp
attribute [to_additive] instGrpLargeCategory

@[to_additive]
instance concreteCategory : ConcreteCategory Grp := by
  dsimp only [Grp]
  infer_instance

@[to_additive]
instance : CoeSort Grp (Type*) where
  coe X := X.α

@[to_additive]
instance (X : Grp) : Group X := X.str

-- porting note (#10670): this instance was not necessary in mathlib
@[to_additive]
instance {X Y : Grp} : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe (f : X →* Y) := f

@[to_additive]
instance instFunLike (X Y : Grp) : FunLike (X ⟶ Y) X Y :=
  show FunLike (X →* Y) X Y from inferInstance

-- porting note (#10756): added lemma
@[to_additive (attr := simp)]
lemma coe_id {X : Grp} : (𝟙 X : X → X) = id := rfl

-- porting note (#10756): added lemma
@[to_additive (attr := simp)]
lemma coe_comp {X Y Z : Grp} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[to_additive]
lemma comp_def {X Y Z : Grp} {f : X ⟶ Y} {g : Y ⟶ Z} : f ≫ g = g.comp f := rfl

-- porting note (#10756): added lemma
@[simp] lemma forget_map (f : X ⟶ Y) : (forget Grp).map f = (f : X → Y) := rfl

@[to_additive (attr := ext)]
lemma ext {X Y : Grp} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  MonoidHom.ext w

/-- Construct a bundled `Group` from the underlying type and typeclass. -/
@[to_additive]
def of (X : Type u) [Group X] : Grp :=
  Bundled.of X
set_option linter.uppercaseLean3 false in
#align Group.of Grp.of
set_option linter.uppercaseLean3 false in
#align AddGroup.of AddGrp.of

/-- Construct a bundled `AddGroup` from the underlying type and typeclass. -/
add_decl_doc AddGrp.of

@[to_additive (attr := simp)]
theorem coe_of (R : Type u) [Group R] : ↑(Grp.of R) = R :=
  rfl
set_option linter.uppercaseLean3 false in
#align Group.coe_of Grp.coe_of
set_option linter.uppercaseLean3 false in
#align AddGroup.coe_of AddGrp.coe_of

@[to_additive]
instance : Inhabited Grp :=
  ⟨Grp.of PUnit⟩

@[to_additive hasForgetToAddMonCat]
instance hasForgetToMonCat : HasForget₂ Grp MonCat :=
  BundledHom.forget₂ _ _
set_option linter.uppercaseLean3 false in
#align Group.has_forget_to_Mon Grp.hasForgetToMonCat
set_option linter.uppercaseLean3 false in
#align AddGroup.has_forget_to_AddMon AddGrp.hasForgetToAddMonCat

@[to_additive]
instance : Coe Grp.{u} MonCat.{u} where coe := (forget₂ Grp MonCat).obj

-- porting note (#10670): this instance was not necessary in mathlib
@[to_additive]
instance (G H : Grp) : One (G ⟶ H) := (inferInstance : One (MonoidHom G H))

@[to_additive (attr := simp)]
theorem one_apply (G H : Grp) (g : G) : ((1 : G ⟶ H) : G → H) g = 1 :=
  rfl
set_option linter.uppercaseLean3 false in
#align Group.one_apply Grp.one_apply
set_option linter.uppercaseLean3 false in
#align AddGroup.zero_apply AddGrp.zero_apply

/-- Typecheck a `MonoidHom` as a morphism in `Grp`. -/
@[to_additive]
def ofHom {X Y : Type u} [Group X] [Group Y] (f : X →* Y) : of X ⟶ of Y :=
  f
set_option linter.uppercaseLean3 false in
#align Group.of_hom Grp.ofHom
set_option linter.uppercaseLean3 false in
#align AddGroup.of_hom AddGrp.ofHom

/-- Typecheck an `AddMonoidHom` as a morphism in `AddGroup`. -/
add_decl_doc AddGrp.ofHom

@[to_additive]
theorem ofHom_apply {X Y : Type _} [Group X] [Group Y] (f : X →* Y) (x : X) :
    (ofHom f) x = f x :=
  rfl
set_option linter.uppercaseLean3 false in
#align Group.of_hom_apply Grp.ofHom_apply
set_option linter.uppercaseLean3 false in
#align AddGroup.of_hom_apply AddGrp.ofHom_apply

@[to_additive]
instance ofUnique (G : Type*) [Group G] [i : Unique G] : Unique (Grp.of G) := i
set_option linter.uppercaseLean3 false in
#align Group.of_unique Grp.ofUnique
set_option linter.uppercaseLean3 false in
#align AddGroup.of_unique AddGrp.ofUnique

-- We verify that simp lemmas apply when coercing morphisms to functions.
@[to_additive]
example {R S : Grp} (i : R ⟶ S) (r : R) (h : r = 1) : i r = 1 := by simp [h]

end Grp

/-- The category of commutative groups and group morphisms. -/
@[to_additive]
def CommGrp : Type (u + 1) :=
  Bundled CommGroup
set_option linter.uppercaseLean3 false in
#align CommGroup CommGrp
set_option linter.uppercaseLean3 false in
#align AddCommGroup AddCommGrp

/-- The category of additive commutative groups and group morphisms. -/
add_decl_doc AddCommGrp

/-- `Ab` is an abbreviation for `AddCommGroup`, for the sake of mathematicians' sanity. -/
abbrev Ab := AddCommGrp
set_option linter.uppercaseLean3 false in
#align Ab Ab

namespace CommGrp

@[to_additive]
instance : BundledHom.ParentProjection @CommGroup.toGroup := ⟨⟩

deriving instance LargeCategory for CommGrp
attribute [to_additive] instCommGrpLargeCategory

@[to_additive]
instance concreteCategory : ConcreteCategory CommGrp := by
  dsimp only [CommGrp]
  infer_instance

@[to_additive]
instance : CoeSort CommGrp (Type*) where
  coe X := X.α

@[to_additive]
instance commGroupInstance (X : CommGrp) : CommGroup X := X.str
set_option linter.uppercaseLean3 false in
#align CommGroup.comm_group_instance CommGrp.commGroupInstance
set_option linter.uppercaseLean3 false in
#align AddCommGroup.add_comm_group_instance AddCommGrp.addCommGroupInstance

-- porting note (#10670): this instance was not necessary in mathlib
@[to_additive]
instance {X Y : CommGrp} : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe (f : X →* Y) := f

@[to_additive]
instance instFunLike (X Y : CommGrp) : FunLike (X ⟶ Y) X Y :=
  show FunLike (X →* Y) X Y from inferInstance

-- porting note (#10756): added lemma
@[to_additive (attr := simp)]
lemma coe_id {X : CommGrp} : (𝟙 X : X → X) = id := rfl

-- porting note (#10756): added lemma
@[to_additive (attr := simp)]
lemma coe_comp {X Y Z : CommGrp} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[to_additive]
lemma comp_def {X Y Z : CommGrp} {f : X ⟶ Y} {g : Y ⟶ Z} : f ≫ g = g.comp f := rfl

-- porting note (#10756): added lemma
@[to_additive (attr := simp)]
lemma forget_map {X Y : CommGrp} (f : X ⟶ Y) :
    (forget CommGrp).map f = (f : X → Y) :=
  rfl

@[to_additive (attr := ext)]
lemma ext {X Y : CommGrp} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  MonoidHom.ext w

/-- Construct a bundled `CommGroup` from the underlying type and typeclass. -/
@[to_additive]
def of (G : Type u) [CommGroup G] : CommGrp :=
  Bundled.of G
set_option linter.uppercaseLean3 false in
#align CommGroup.of CommGrp.of
set_option linter.uppercaseLean3 false in
#align AddCommGroup.of AddCommGrp.of

/-- Construct a bundled `AddCommGroup` from the underlying type and typeclass. -/
add_decl_doc AddCommGrp.of

@[to_additive]
instance : Inhabited CommGrp :=
  ⟨CommGrp.of PUnit⟩

-- Porting note: removed `@[simp]` here, as it makes it harder to tell when to apply
-- bundled or unbundled lemmas.
-- (This change seems dangerous!)
@[to_additive]
theorem coe_of (R : Type u) [CommGroup R] : (CommGrp.of R : Type u) = R :=
  rfl
set_option linter.uppercaseLean3 false in
#align CommGroup.coe_of CommGrp.coe_of
set_option linter.uppercaseLean3 false in
#align AddCommGroup.coe_of AddCommGrp.coe_of

@[to_additive]
instance ofUnique (G : Type*) [CommGroup G] [i : Unique G] : Unique (CommGrp.of G) :=
  i
set_option linter.uppercaseLean3 false in
#align CommGroup.of_unique CommGrp.ofUnique
set_option linter.uppercaseLean3 false in
#align AddCommGroup.of_unique AddCommGrp.ofUnique

@[to_additive]
instance hasForgetToGroup : HasForget₂ CommGrp Grp :=
  BundledHom.forget₂ _ _
set_option linter.uppercaseLean3 false in
#align CommGroup.has_forget_to_Group CommGrp.hasForgetToGroup
set_option linter.uppercaseLean3 false in
#align AddCommGroup.has_forget_to_AddGroup AddCommGrp.hasForgetToAddGroup

@[to_additive]
instance : Coe CommGrp.{u} Grp.{u} where coe := (forget₂ CommGrp Grp).obj

@[to_additive hasForgetToAddCommMonCat]
instance hasForgetToCommMonCat : HasForget₂ CommGrp CommMonCat :=
  InducedCategory.hasForget₂ fun G : CommGrp => CommMonCat.of G
set_option linter.uppercaseLean3 false in
#align CommGroup.has_forget_to_CommMon CommGrp.hasForgetToCommMonCat
set_option linter.uppercaseLean3 false in
#align AddCommGroup.has_forget_to_AddCommMon AddCommGrp.hasForgetToAddCommMonCat

@[to_additive]
instance : Coe CommGrp.{u} CommMonCat.{u} where coe := (forget₂ CommGrp CommMonCat).obj

-- porting note (#10670): this instance was not necessary in mathlib
@[to_additive]
instance (G H : CommGrp) : One (G ⟶ H) := (inferInstance : One (MonoidHom G H))

@[to_additive (attr := simp)]
theorem one_apply (G H : CommGrp) (g : G) : ((1 : G ⟶ H) : G → H) g = 1 :=
  rfl
set_option linter.uppercaseLean3 false in
#align CommGroup.one_apply CommGrp.one_apply
set_option linter.uppercaseLean3 false in
#align AddCommGroup.zero_apply AddCommGrp.zero_apply

/-- Typecheck a `MonoidHom` as a morphism in `CommGroup`. -/
@[to_additive]
def ofHom {X Y : Type u} [CommGroup X] [CommGroup Y] (f : X →* Y) : of X ⟶ of Y :=
  f
set_option linter.uppercaseLean3 false in
#align CommGroup.of_hom CommGrp.ofHom
set_option linter.uppercaseLean3 false in
#align AddCommGroup.of_hom AddCommGrp.ofHom

/-- Typecheck an `AddMonoidHom` as a morphism in `AddCommGroup`. -/
add_decl_doc AddCommGrp.ofHom

@[to_additive (attr := simp)]
theorem ofHom_apply {X Y : Type _} [CommGroup X] [CommGroup Y] (f : X →* Y) (x : X) :
    (ofHom f) x = f x :=
  rfl
set_option linter.uppercaseLean3 false in
#align CommGroup.of_hom_apply CommGrp.ofHom_apply
set_option linter.uppercaseLean3 false in
#align AddCommGroup.of_hom_apply AddCommGrp.ofHom_apply

-- We verify that simp lemmas apply when coercing morphisms to functions.
@[to_additive]
example {R S : CommGrp} (i : R ⟶ S) (r : R) (h : r = 1) : i r = 1 := by simp [h]

end CommGrp

namespace AddCommGrp

-- Note that because `ℤ : Type 0`, this forces `G : AddCommGroup.{0}`,
-- so we write this explicitly to be clear.
-- TODO generalize this, requiring a `ULiftInstances.lean` file
/-- Any element of an abelian group gives a unique morphism from `ℤ` sending
`1` to that element. -/
def asHom {G : AddCommGrp.{0}} (g : G) : AddCommGrp.of ℤ ⟶ G :=
  zmultiplesHom G g
set_option linter.uppercaseLean3 false in
#align AddCommGroup.as_hom AddCommGrp.asHom

@[simp]
theorem asHom_apply {G : AddCommGrp.{0}} (g : G) (i : ℤ) : (asHom g) i = i • g :=
  rfl
set_option linter.uppercaseLean3 false in
#align AddCommGroup.as_hom_apply AddCommGrp.asHom_apply

theorem asHom_injective {G : AddCommGrp.{0}} : Function.Injective (@asHom G) := fun h k w => by
  convert congr_arg (fun k : AddCommGrp.of ℤ ⟶ G => (k : ℤ → G) (1 : ℤ)) w <;> simp
set_option linter.uppercaseLean3 false in
#align AddCommGroup.as_hom_injective AddCommGrp.asHom_injective

@[ext]
theorem int_hom_ext {G : AddCommGrp.{0}} (f g : AddCommGrp.of ℤ ⟶ G)
    (w : f (1 : ℤ) = g (1 : ℤ)) : f = g :=
  @AddMonoidHom.ext_int G _ f g w
set_option linter.uppercaseLean3 false in
#align AddCommGroup.int_hom_ext AddCommGrp.int_hom_ext

-- TODO: this argument should be generalised to the situation where
-- the forgetful functor is representable.
theorem injective_of_mono {G H : AddCommGrp.{0}} (f : G ⟶ H) [Mono f] : Function.Injective f :=
  fun g₁ g₂ h => by
  have t0 : asHom g₁ ≫ f = asHom g₂ ≫ f := by aesop_cat
  have t1 : asHom g₁ = asHom g₂ := (cancel_mono _).1 t0
  apply asHom_injective t1
set_option linter.uppercaseLean3 false in
#align AddCommGroup.injective_of_mono AddCommGrp.injective_of_mono

end AddCommGrp

/-- Build an isomorphism in the category `Grp` from a `MulEquiv` between `Group`s. -/
@[to_additive (attr := simps)]
def MulEquiv.toGrpIso {X Y : Grp} (e : X ≃* Y) : X ≅ Y where
  hom := e.toMonoidHom
  inv := e.symm.toMonoidHom
set_option linter.uppercaseLean3 false in
#align mul_equiv.to_Group_iso MulEquiv.toGrpIso
set_option linter.uppercaseLean3 false in
#align add_equiv.to_AddGroup_iso AddEquiv.toAddGrpIso

/-- Build an isomorphism in the category `AddGroup` from an `AddEquiv` between `AddGroup`s. -/
add_decl_doc AddEquiv.toAddGrpIso

/-- Build an isomorphism in the category `CommGrp` from a `MulEquiv`
between `CommGroup`s. -/
@[to_additive (attr := simps)]
def MulEquiv.toCommGrpIso {X Y : CommGrp} (e : X ≃* Y) : X ≅ Y where
  hom := e.toMonoidHom
  inv := e.symm.toMonoidHom
set_option linter.uppercaseLean3 false in
#align mul_equiv.to_CommGroup_iso MulEquiv.toCommGrpIso
set_option linter.uppercaseLean3 false in
#align add_equiv.to_AddCommGroup_iso AddEquiv.toAddCommGrpIso

/-- Build an isomorphism in the category `AddCommGrp` from an `AddEquiv`
between `AddCommGroup`s. -/
add_decl_doc AddEquiv.toAddCommGrpIso

namespace CategoryTheory.Iso

/-- Build a `MulEquiv` from an isomorphism in the category `Grp`. -/
@[to_additive (attr := simp)]
def groupIsoToMulEquiv {X Y : Grp} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom i.inv i.hom_inv_id i.inv_hom_id
set_option linter.uppercaseLean3 false in
#align category_theory.iso.Group_iso_to_mul_equiv CategoryTheory.Iso.groupIsoToMulEquiv
set_option linter.uppercaseLean3 false in
#align category_theory.iso.AddGroup_iso_to_add_equiv CategoryTheory.Iso.addGroupIsoToAddEquiv

/-- Build an `addEquiv` from an isomorphism in the category `AddGroup` -/
add_decl_doc addGroupIsoToAddEquiv

/-- Build a `MulEquiv` from an isomorphism in the category `CommGroup`. -/
@[to_additive (attr := simps!)]
def commGroupIsoToMulEquiv {X Y : CommGrp} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom i.inv i.hom_inv_id i.inv_hom_id
set_option linter.uppercaseLean3 false in
#align category_theory.iso.CommGroup_iso_to_mul_equiv CategoryTheory.Iso.commGroupIsoToMulEquiv
set_option linter.uppercaseLean3 false in
#align category_theory.iso.AddCommGroup_iso_to_add_equiv CategoryTheory.Iso.addCommGroupIsoToAddEquiv

/-- Build an `AddEquiv` from an isomorphism in the category `AddCommGroup`. -/
add_decl_doc addCommGroupIsoToAddEquiv

end CategoryTheory.Iso

/-- multiplicative equivalences between `Group`s are the same as (isomorphic to) isomorphisms
in `Grp` -/
@[to_additive]
def mulEquivIsoGroupIso {X Y : Grp.{u}} : X ≃* Y ≅ X ≅ Y where
  hom e := e.toGrpIso
  inv i := i.groupIsoToMulEquiv
set_option linter.uppercaseLean3 false in
#align mul_equiv_iso_Group_iso mulEquivIsoGroupIso
set_option linter.uppercaseLean3 false in
#align add_equiv_iso_AddGroup_iso addEquivIsoAddGroupIso

/-- "additive equivalences between `add_group`s are the same
as (isomorphic to) isomorphisms in `AddGroup` -/
add_decl_doc addEquivIsoAddGroupIso

/-- multiplicative equivalences between `comm_group`s are the same as (isomorphic to) isomorphisms
in `CommGroup` -/
@[to_additive]
def mulEquivIsoCommGroupIso {X Y : CommGrp.{u}} : X ≃* Y ≅ X ≅ Y where
  hom e := e.toCommGrpIso
  inv i := i.commGroupIsoToMulEquiv
set_option linter.uppercaseLean3 false in
#align mul_equiv_iso_CommGroup_iso mulEquivIsoCommGroupIso
set_option linter.uppercaseLean3 false in
#align add_equiv_iso_AddCommGroup_iso addEquivIsoAddCommGroupIso

/-- additive equivalences between `AddCommGroup`s are
the same as (isomorphic to) isomorphisms in `AddCommGroup` -/
add_decl_doc addEquivIsoAddCommGroupIso

namespace CategoryTheory.Aut

/-- The (bundled) group of automorphisms of a type is isomorphic to the (bundled) group
of permutations. -/
def isoPerm {α : Type u} : Grp.of (Aut α) ≅ Grp.of (Equiv.Perm α) where
  hom :=
    { toFun := fun g => g.toEquiv
      map_one' := by aesop
      map_mul' := by aesop }
  inv :=
    { toFun := fun g => g.toIso
      map_one' := by aesop
      map_mul' := by aesop }
set_option linter.uppercaseLean3 false in
#align category_theory.Aut.iso_perm CategoryTheory.Aut.isoPerm

/-- The (unbundled) group of automorphisms of a type is `mul_equiv` to the (unbundled) group
of permutations. -/
def mulEquivPerm {α : Type u} : Aut α ≃* Equiv.Perm α :=
  isoPerm.groupIsoToMulEquiv
set_option linter.uppercaseLean3 false in
#align category_theory.Aut.mul_equiv_perm CategoryTheory.Aut.mulEquivPerm

end CategoryTheory.Aut

@[to_additive]
instance Grp.forget_reflects_isos : ReflectsIsomorphisms (forget Grp.{u}) where
  reflects {X Y} f _ := by
    let i := asIso ((forget Grp).map f)
    let e : X ≃* Y := { i.toEquiv with map_mul' := map_mul _ }
    exact IsIso.of_iso e.toGrpIso
set_option linter.uppercaseLean3 false in
#align Group.forget_reflects_isos Grp.forget_reflects_isos
set_option linter.uppercaseLean3 false in
#align AddGroup.forget_reflects_isos AddGrp.forget_reflects_isos

@[to_additive]
instance CommGrp.forget_reflects_isos : ReflectsIsomorphisms (forget CommGrp.{u}) where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommGrp).map f)
    let e : X ≃* Y := { i.toEquiv with map_mul' := map_mul _}
    exact IsIso.of_iso e.toCommGrpIso
set_option linter.uppercaseLean3 false in
#align CommGroup.forget_reflects_isos CommGrp.forget_reflects_isos
set_option linter.uppercaseLean3 false in
#align AddCommGroup.forget_reflects_isos AddCommGrp.forget_reflects_isos

-- note: in the following definitions, there is a problem with `@[to_additive]`
-- as the `Category` instance is not found on the additive variant
-- this variant is then renamed with a `Aux` suffix

/-- An alias for `Grp.{max u v}`, to deal around unification issues. -/
@[to_additive (attr := nolint checkUnivs) GrpMaxAux
  "An alias for `AddGrp.{max u v}`, to deal around unification issues."]
abbrev GrpMax.{u1, u2} := Grp.{max u1 u2}
/-- An alias for `AddGrp.{max u v}`, to deal around unification issues. -/
@[nolint checkUnivs]
abbrev AddGrpMax.{u1, u2} := AddGrp.{max u1 u2}

/-- An alias for `CommGrp.{max u v}`, to deal around unification issues. -/
@[to_additive (attr := nolint checkUnivs) AddCommGrpMaxAux
  "An alias for `AddCommGrp.{max u v}`, to deal around unification issues."]
abbrev CommGrpMax.{u1, u2} := CommGrp.{max u1 u2}
/-- An alias for `AddCommGrp.{max u v}`, to deal around unification issues. -/
@[nolint checkUnivs]
abbrev AddCommGrpMax.{u1, u2} := AddCommGrp.{max u1 u2}
