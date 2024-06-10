/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.Algebra.Group.ULift
import Mathlib.CategoryTheory.Endomorphism

#align_import algebra.category.Group.basic from "leanprover-community/mathlib"@"524793de15bc4c52ee32d254e7d7867c7176b3af"

/-!
# Category instances for Group, AddGroup, CommGroup, and AddCommGroup.

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
  (fun {α : Type*} (h : Group α) => h.toDivInvMonoid.toMonoid) := ⟨⟩

deriving instance LargeCategory for GroupCat
attribute [to_additive] instGroupCatLargeCategory

@[to_additive]
instance concreteCategory : ConcreteCategory GroupCat := by
  dsimp only [GroupCat]
  infer_instance

@[to_additive]
instance : CoeSort GroupCat Type* where
  coe X := X.α

@[to_additive]
instance (X : GroupCat) : Group X := X.str

-- porting note (#10670): this instance was not necessary in mathlib
@[to_additive]
instance {X Y : GroupCat} : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe (f : X →* Y) := f

@[to_additive]
instance instFunLike (X Y : GroupCat) : FunLike (X ⟶ Y) X Y :=
  show FunLike (X →* Y) X Y from inferInstance

-- porting note (#10756): added lemma
@[to_additive (attr := simp)]
lemma coe_id {X : GroupCat} : (𝟙 X : X → X) = id := rfl

-- porting note (#10756): added lemma
@[to_additive (attr := simp)]
lemma coe_comp {X Y Z : GroupCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[to_additive]
lemma comp_def {X Y Z : GroupCat} {f : X ⟶ Y} {g : Y ⟶ Z} : f ≫ g = g.comp f := rfl

-- porting note (#10756): added lemma
@[simp] lemma forget_map {X Y : GroupCat} (f : X ⟶ Y) : (forget GroupCat).map f = (f : X → Y) := rfl

@[to_additive (attr := ext)]
lemma ext {X Y : GroupCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  MonoidHom.ext w

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

@[to_additive (attr := simp)]
theorem coe_of (R : Type u) [Group R] : ↑(GroupCat.of R) = R :=
  rfl
set_option linter.uppercaseLean3 false in
#align Group.coe_of GroupCat.coe_of
set_option linter.uppercaseLean3 false in
#align AddGroup.coe_of AddGroupCat.coe_of

@[to_additive (attr := simp)]
theorem coe_comp' {G H K : Type _} [Group G] [Group H] [Group K] (f : G →* H) (g : H →* K) :
    @DFunLike.coe (G →* K) G (fun _ ↦ K) MonoidHom.instFunLike (CategoryStruct.comp
      (X := GroupCat.of G) (Y := GroupCat.of H) (Z := GroupCat.of K) f g) = g ∘ f :=
  rfl

@[to_additive (attr := simp)]
theorem coe_id' {G : Type _} [Group G] :
    @DFunLike.coe (G →* G) G (fun _ ↦ G) MonoidHom.instFunLike
      (CategoryStruct.id (X := GroupCat.of G)) = id :=
  rfl

@[to_additive]
instance : Inhabited GroupCat :=
  ⟨GroupCat.of PUnit⟩

@[to_additive hasForgetToAddMonCat]
instance hasForgetToMonCat : HasForget₂ GroupCat MonCat :=
  BundledHom.forget₂ _ _
set_option linter.uppercaseLean3 false in
#align Group.has_forget_to_Mon GroupCat.hasForgetToMonCat
set_option linter.uppercaseLean3 false in
#align AddGroup.has_forget_to_AddMon AddGroupCat.hasForgetToAddMonCat

@[to_additive]
instance : Coe GroupCat.{u} MonCat.{u} where coe := (forget₂ GroupCat MonCat).obj

-- porting note (#10670): this instance was not necessary in mathlib
@[to_additive]
instance (G H : GroupCat) : One (G ⟶ H) := (inferInstance : One (MonoidHom G H))

@[to_additive (attr := simp)]
theorem one_apply (G H : GroupCat) (g : G) : ((1 : G ⟶ H) : G → H) g = 1 :=
  rfl
set_option linter.uppercaseLean3 false in
#align Group.one_apply GroupCat.one_apply
set_option linter.uppercaseLean3 false in
#align AddGroup.zero_apply AddGroupCat.zero_apply

/-- Typecheck a `MonoidHom` as a morphism in `GroupCat`. -/
@[to_additive]
def ofHom {X Y : Type u} [Group X] [Group Y] (f : X →* Y) : of X ⟶ of Y :=
  f
set_option linter.uppercaseLean3 false in
#align Group.of_hom GroupCat.ofHom
set_option linter.uppercaseLean3 false in
#align AddGroup.of_hom AddGroupCat.ofHom

/-- Typecheck an `AddMonoidHom` as a morphism in `AddGroup`. -/
add_decl_doc AddGroupCat.ofHom

@[to_additive]
theorem ofHom_apply {X Y : Type _} [Group X] [Group Y] (f : X →* Y) (x : X) :
    (ofHom f) x = f x :=
  rfl
set_option linter.uppercaseLean3 false in
#align Group.of_hom_apply GroupCat.ofHom_apply
set_option linter.uppercaseLean3 false in
#align AddGroup.of_hom_apply AddGroupCat.ofHom_apply

@[to_additive]
instance ofUnique (G : Type*) [Group G] [i : Unique G] : Unique (GroupCat.of G) := i
set_option linter.uppercaseLean3 false in
#align Group.of_unique GroupCat.ofUnique
set_option linter.uppercaseLean3 false in
#align AddGroup.of_unique AddGroupCat.ofUnique

-- We verify that simp lemmas apply when coercing morphisms to functions.
@[to_additive]
example {R S : GroupCat} (i : R ⟶ S) (r : R) (h : r = 1) : i r = 1 := by simp [h]

/-- Universe lift functor for groups. -/
@[to_additive (attr := simps)
  "Universe lift functor for additive groups."]
def uliftFunctor : GroupCat.{u} ⥤ GroupCat.{max u v} where
  obj X := GroupCat.of (ULift.{v, u} X)
  map {X Y} f := GroupCat.ofHom <|
    MulEquiv.ulift.symm.toMonoidHom.comp <| f.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

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
abbrev Ab := AddCommGroupCat
set_option linter.uppercaseLean3 false in
#align Ab Ab

namespace CommGroupCat

@[to_additive]
instance : BundledHom.ParentProjection @CommGroup.toGroup := ⟨⟩

deriving instance LargeCategory for CommGroupCat
attribute [to_additive] instCommGroupCatLargeCategory

@[to_additive]
instance concreteCategory : ConcreteCategory CommGroupCat := by
  dsimp only [CommGroupCat]
  infer_instance

@[to_additive]
instance : CoeSort CommGroupCat Type* where
  coe X := X.α

@[to_additive]
instance commGroupInstance (X : CommGroupCat) : CommGroup X := X.str
set_option linter.uppercaseLean3 false in
#align CommGroup.comm_group_instance CommGroupCat.commGroupInstance
set_option linter.uppercaseLean3 false in
#align AddCommGroup.add_comm_group_instance AddCommGroupCat.addCommGroupInstance

-- porting note (#10670): this instance was not necessary in mathlib
@[to_additive]
instance {X Y : CommGroupCat} : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe (f : X →* Y) := f

@[to_additive]
instance instFunLike (X Y : CommGroupCat) : FunLike (X ⟶ Y) X Y :=
  show FunLike (X →* Y) X Y from inferInstance

-- porting note (#10756): added lemma
@[to_additive (attr := simp)]
lemma coe_id {X : CommGroupCat} : (𝟙 X : X → X) = id := rfl

-- porting note (#10756): added lemma
@[to_additive (attr := simp)]
lemma coe_comp {X Y Z : CommGroupCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[to_additive]
lemma comp_def {X Y Z : CommGroupCat} {f : X ⟶ Y} {g : Y ⟶ Z} : f ≫ g = g.comp f := rfl

-- porting note (#10756): added lemma
@[to_additive (attr := simp)]
lemma forget_map {X Y : CommGroupCat} (f : X ⟶ Y) :
    (forget CommGroupCat).map f = (f : X → Y) :=
  rfl

@[to_additive (attr := ext)]
lemma ext {X Y : CommGroupCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  MonoidHom.ext w

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

@[to_additive]
instance : Inhabited CommGroupCat :=
  ⟨CommGroupCat.of PUnit⟩

@[to_additive (attr := simp)]
theorem coe_of (R : Type u) [CommGroup R] : (CommGroupCat.of R : Type u) = R :=
  rfl
set_option linter.uppercaseLean3 false in
#align CommGroup.coe_of CommGroupCat.coe_of
set_option linter.uppercaseLean3 false in
#align AddCommGroup.coe_of AddCommGroupCat.coe_of

@[to_additive (attr := simp)]
theorem coe_comp' {G H K : Type _} [CommGroup G] [CommGroup H] [CommGroup K]
    (f : G →* H) (g : H →* K) :
    @DFunLike.coe (G →* K) G (fun _ ↦ K) MonoidHom.instFunLike (CategoryStruct.comp
      (X := CommGroupCat.of G) (Y := CommGroupCat.of H) (Z := CommGroupCat.of K) f g) = g ∘ f :=
  rfl

@[to_additive (attr := simp)]
theorem coe_id' {G : Type _} [CommGroup G] :
    @DFunLike.coe (G →* G) G (fun _ ↦ G) MonoidHom.instFunLike
      (CategoryStruct.id (X := CommGroupCat.of G)) = id :=
  rfl

@[to_additive]
instance ofUnique (G : Type*) [CommGroup G] [i : Unique G] : Unique (CommGroupCat.of G) :=
  i
set_option linter.uppercaseLean3 false in
#align CommGroup.of_unique CommGroupCat.ofUnique
set_option linter.uppercaseLean3 false in
#align AddCommGroup.of_unique AddCommGroupCat.ofUnique

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

-- porting note (#10670): this instance was not necessary in mathlib
@[to_additive]
instance (G H : CommGroupCat) : One (G ⟶ H) := (inferInstance : One (MonoidHom G H))

@[to_additive (attr := simp)]
theorem one_apply (G H : CommGroupCat) (g : G) : ((1 : G ⟶ H) : G → H) g = 1 :=
  rfl
set_option linter.uppercaseLean3 false in
#align CommGroup.one_apply CommGroupCat.one_apply
set_option linter.uppercaseLean3 false in
#align AddCommGroup.zero_apply AddCommGroupCat.zero_apply

/-- Typecheck a `MonoidHom` as a morphism in `CommGroup`. -/
@[to_additive]
def ofHom {X Y : Type u} [CommGroup X] [CommGroup Y] (f : X →* Y) : of X ⟶ of Y :=
  f
set_option linter.uppercaseLean3 false in
#align CommGroup.of_hom CommGroupCat.ofHom
set_option linter.uppercaseLean3 false in
#align AddCommGroup.of_hom AddCommGroupCat.ofHom

/-- Typecheck an `AddMonoidHom` as a morphism in `AddCommGroup`. -/
add_decl_doc AddCommGroupCat.ofHom

@[to_additive (attr := simp)]
theorem ofHom_apply {X Y : Type _} [CommGroup X] [CommGroup Y] (f : X →* Y) (x : X) :
    @DFunLike.coe (X →* Y) X (fun _ ↦ Y) _ (ofHom f) x = f x :=
  rfl
set_option linter.uppercaseLean3 false in
#align CommGroup.of_hom_apply CommGroupCat.ofHom_apply
set_option linter.uppercaseLean3 false in
#align AddCommGroup.of_hom_apply AddCommGroupCat.ofHom_apply

-- We verify that simp lemmas apply when coercing morphisms to functions.
@[to_additive]
example {R S : CommGroupCat} (i : R ⟶ S) (r : R) (h : r = 1) : i r = 1 := by simp [h]

/-- Universe lift functor for commutative groups. -/
@[to_additive (attr := simps)
  "Universe lift functor for additive commutative groups."]
def uliftFunctor : CommGroupCat.{u} ⥤ CommGroupCat.{max u v} where
  obj X := CommGroupCat.of (ULift.{v, u} X)
  map {X Y} f := CommGroupCat.ofHom <|
    MulEquiv.ulift.symm.toMonoidHom.comp <| f.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

end CommGroupCat

namespace AddCommGroupCat

-- Note that because `ℤ : Type 0`, this forces `G : AddCommGroup.{0}`,
-- so we write this explicitly to be clear.
-- TODO generalize this, requiring a `ULiftInstances.lean` file
/-- Any element of an abelian group gives a unique morphism from `ℤ` sending
`1` to that element. -/
def asHom {G : AddCommGroupCat.{0}} (g : G) : AddCommGroupCat.of ℤ ⟶ G :=
  zmultiplesHom G g
set_option linter.uppercaseLean3 false in
#align AddCommGroup.as_hom AddCommGroupCat.asHom

@[simp]
theorem asHom_apply {G : AddCommGroupCat.{0}} (g : G) (i : ℤ) :
    @DFunLike.coe (ℤ →+ ↑G) ℤ (fun _ ↦ ↑G) _ (asHom g) i = i • g :=
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
  have t0 : asHom g₁ ≫ f = asHom g₂ ≫ f := by aesop_cat
  have t1 : asHom g₁ = asHom g₂ := (cancel_mono _).1 t0
  apply asHom_injective t1
set_option linter.uppercaseLean3 false in
#align AddCommGroup.injective_of_mono AddCommGroupCat.injective_of_mono

end AddCommGroupCat

/-- Build an isomorphism in the category `GroupCat` from a `MulEquiv` between `Group`s. -/
@[to_additive (attr := simps)]
def MulEquiv.toGroupCatIso {X Y : GroupCat} (e : X ≃* Y) : X ≅ Y where
  hom := e.toMonoidHom
  inv := e.symm.toMonoidHom
set_option linter.uppercaseLean3 false in
#align mul_equiv.to_Group_iso MulEquiv.toGroupCatIso
set_option linter.uppercaseLean3 false in
#align add_equiv.to_AddGroup_iso AddEquiv.toAddGroupCatIso

/-- Build an isomorphism in the category `AddGroup` from an `AddEquiv` between `AddGroup`s. -/
add_decl_doc AddEquiv.toAddGroupCatIso

/-- Build an isomorphism in the category `CommGroupCat` from a `MulEquiv`
between `CommGroup`s. -/
@[to_additive (attr := simps)]
def MulEquiv.toCommGroupCatIso {X Y : CommGroupCat} (e : X ≃* Y) : X ≅ Y where
  hom := e.toMonoidHom
  inv := e.symm.toMonoidHom
set_option linter.uppercaseLean3 false in
#align mul_equiv.to_CommGroup_iso MulEquiv.toCommGroupCatIso
set_option linter.uppercaseLean3 false in
#align add_equiv.to_AddCommGroup_iso AddEquiv.toAddCommGroupCatIso

/-- Build an isomorphism in the category `AddCommGroupCat` from an `AddEquiv`
between `AddCommGroup`s. -/
add_decl_doc AddEquiv.toAddCommGroupCatIso

namespace CategoryTheory.Iso

/-- Build a `MulEquiv` from an isomorphism in the category `GroupCat`. -/
@[to_additive (attr := simp)]
def groupIsoToMulEquiv {X Y : GroupCat} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom i.inv i.hom_inv_id i.inv_hom_id
set_option linter.uppercaseLean3 false in
#align category_theory.iso.Group_iso_to_mul_equiv CategoryTheory.Iso.groupIsoToMulEquiv
set_option linter.uppercaseLean3 false in
#align category_theory.iso.AddGroup_iso_to_add_equiv CategoryTheory.Iso.addGroupIsoToAddEquiv

/-- Build an `addEquiv` from an isomorphism in the category `AddGroup` -/
add_decl_doc addGroupIsoToAddEquiv

/-- Build a `MulEquiv` from an isomorphism in the category `CommGroup`. -/
@[to_additive (attr := simps!)]
def commGroupIsoToMulEquiv {X Y : CommGroupCat} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom i.inv i.hom_inv_id i.inv_hom_id
set_option linter.uppercaseLean3 false in
#align category_theory.iso.CommGroup_iso_to_mul_equiv CategoryTheory.Iso.commGroupIsoToMulEquiv
set_option linter.uppercaseLean3 false in
#align category_theory.iso.AddCommGroup_iso_to_add_equiv CategoryTheory.Iso.addCommGroupIsoToAddEquiv

/-- Build an `AddEquiv` from an isomorphism in the category `AddCommGroup`. -/
add_decl_doc addCommGroupIsoToAddEquiv

end CategoryTheory.Iso

/-- multiplicative equivalences between `Group`s are the same as (isomorphic to) isomorphisms
in `GroupCat` -/
@[to_additive]
def mulEquivIsoGroupIso {X Y : GroupCat.{u}} : X ≃* Y ≅ X ≅ Y where
  hom e := e.toGroupCatIso
  inv i := i.groupIsoToMulEquiv
set_option linter.uppercaseLean3 false in
#align mul_equiv_iso_Group_iso mulEquivIsoGroupIso
set_option linter.uppercaseLean3 false in
#align add_equiv_iso_AddGroup_iso addEquivIsoAddGroupIso

/-- Additive equivalences between `AddGroup`s are the same
as (isomorphic to) isomorphisms in `AddGroupCat`. -/
add_decl_doc addEquivIsoAddGroupIso

/-- Multiplicative equivalences between `CommGroup`s are the same as (isomorphic to) isomorphisms
in `CommGroupCat`. -/
@[to_additive]
def mulEquivIsoCommGroupIso {X Y : CommGroupCat.{u}} : X ≃* Y ≅ X ≅ Y where
  hom e := e.toCommGroupCatIso
  inv i := i.commGroupIsoToMulEquiv
set_option linter.uppercaseLean3 false in
#align mul_equiv_iso_CommGroup_iso mulEquivIsoCommGroupIso
set_option linter.uppercaseLean3 false in
#align add_equiv_iso_AddCommGroup_iso addEquivIsoAddCommGroupIso

/-- Additive equivalences between `AddCommGroup`s are
the same as (isomorphic to) isomorphisms in `AddCommGroupCat`. -/
add_decl_doc addEquivIsoAddCommGroupIso

namespace CategoryTheory.Aut

/-- The (bundled) group of automorphisms of a type is isomorphic to the (bundled) group
of permutations. -/
def isoPerm {α : Type u} : GroupCat.of (Aut α) ≅ GroupCat.of (Equiv.Perm α) where
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

/-- The (unbundled) group of automorphisms of a type is `MulEquiv` to the (unbundled) group
of permutations. -/
def mulEquivPerm {α : Type u} : Aut α ≃* Equiv.Perm α :=
  isoPerm.groupIsoToMulEquiv
set_option linter.uppercaseLean3 false in
#align category_theory.Aut.mul_equiv_perm CategoryTheory.Aut.mulEquivPerm

end CategoryTheory.Aut

@[to_additive]
instance GroupCat.forget_reflects_isos : (forget GroupCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget GroupCat).map f)
    let e : X ≃* Y := { i.toEquiv with map_mul' := map_mul _ }
    exact e.toGroupCatIso.isIso_hom
set_option linter.uppercaseLean3 false in
#align Group.forget_reflects_isos GroupCat.forget_reflects_isos
set_option linter.uppercaseLean3 false in
#align AddGroup.forget_reflects_isos AddGroupCat.forget_reflects_isos

@[to_additive]
instance CommGroupCat.forget_reflects_isos : (forget CommGroupCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommGroupCat).map f)
    let e : X ≃* Y := { i.toEquiv with map_mul' := map_mul _}
    exact e.toCommGroupCatIso.isIso_hom
set_option linter.uppercaseLean3 false in
#align CommGroup.forget_reflects_isos CommGroupCat.forget_reflects_isos
set_option linter.uppercaseLean3 false in
#align AddCommGroup.forget_reflects_isos AddCommGroupCat.forget_reflects_isos

-- note: in the following definitions, there is a problem with `@[to_additive]`
-- as the `Category` instance is not found on the additive variant
-- this variant is then renamed with a `Aux` suffix

/-- An alias for `GroupCat.{max u v}`, to deal around unification issues. -/
@[to_additive (attr := nolint checkUnivs) GroupCatMaxAux
  "An alias for `AddGroupCat.{max u v}`, to deal around unification issues."]
abbrev GroupCatMax.{u1, u2} := GroupCat.{max u1 u2}
/-- An alias for `AddGroupCat.{max u v}`, to deal around unification issues. -/
@[nolint checkUnivs]
abbrev AddGroupCatMax.{u1, u2} := AddGroupCat.{max u1 u2}

/-- An alias for `CommGroupCat.{max u v}`, to deal around unification issues. -/
@[to_additive (attr := nolint checkUnivs) AddCommGroupCatMaxAux
  "An alias for `AddCommGroupCat.{max u v}`, to deal around unification issues."]
abbrev CommGroupCatMax.{u1, u2} := CommGroupCat.{max u1 u2}
/-- An alias for `AddCommGroupCat.{max u v}`, to deal around unification issues. -/
@[nolint checkUnivs]
abbrev AddCommGroupCatMax.{u1, u2} := AddCommGroupCat.{max u1 u2}

/-!
`@[simp]` lemmas for `MonoidHom.comp` and categorical identities.
-/

@[to_additive (attr := simp)] theorem MonoidHom.comp_id_groupCat
    {G : GroupCat.{u}} {H : Type u} [Group H] (f : G →* H) : f.comp (𝟙 G) = f :=
  Category.id_comp (GroupCat.ofHom f)
@[to_additive (attr := simp)] theorem MonoidHom.id_groupCat_comp
    {G : Type u} [Group G] {H : GroupCat.{u}} (f : G →* H) : MonoidHom.comp (𝟙 H) f = f :=
  Category.comp_id (GroupCat.ofHom f)

@[to_additive (attr := simp)] theorem MonoidHom.comp_id_commGroupCat
    {G : CommGroupCat.{u}} {H : Type u} [CommGroup H] (f : G →* H) : f.comp (𝟙 G) = f :=
  Category.id_comp (CommGroupCat.ofHom f)
@[to_additive (attr := simp)] theorem MonoidHom.id_commGroupCat_comp
    {G : Type u} [CommGroup G] {H : CommGroupCat.{u}} (f : G →* H) : MonoidHom.comp (𝟙 H) f = f :=
  Category.comp_id (CommGroupCat.ofHom f)
