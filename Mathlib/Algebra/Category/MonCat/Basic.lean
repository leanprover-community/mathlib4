/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.Algebra.PUnitInstances
import Mathlib.Algebra.Group.ULift
import Mathlib.CategoryTheory.Functor.ReflectsIso

#align_import algebra.category.Mon.basic from "leanprover-community/mathlib"@"0caf3701139ef2e69c215717665361cda205a90b"

/-!
# Category instances for `Monoid`, `AddMonoid`, `CommMonoid`, and `AddCommMmonoid`.

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
abbrev AssocMonoidHom (M N : Type*) [Monoid M] [Monoid N] :=
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
  toFun {X Y} _ _ f := ⇑f
  id _ := MonoidHom.id _
  comp _ _ _ := MonoidHom.comp
set_option linter.uppercaseLean3 false in
#align Mon.bundled_hom MonCat.bundledHom
set_option linter.uppercaseLean3 false in
#align AddMon.bundled_hom AddMonCat.bundledHom

deriving instance LargeCategory for MonCat
attribute [to_additive instAddMonCatLargeCategory] instMonCatLargeCategory

-- Porting note: https://github.com/leanprover-community/mathlib4/issues/5020
@[to_additive]
instance concreteCategory : ConcreteCategory MonCat :=
  BundledHom.concreteCategory _

@[to_additive]
instance : CoeSort MonCat Type* where
  coe X := X.α

@[to_additive]
instance (X : MonCat) : Monoid X := X.str

-- porting note (#10670): this instance was not necessary in mathlib
@[to_additive]
instance {X Y : MonCat} : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe (f : X →* Y) := f

@[to_additive]
instance instFunLike (X Y : MonCat) : FunLike (X ⟶ Y) X Y :=
  inferInstanceAs <| FunLike (X →* Y) X Y

@[to_additive]
instance instMonoidHomClass (X Y : MonCat) : MonoidHomClass (X ⟶ Y) X Y :=
  inferInstanceAs <| MonoidHomClass (X →* Y) X Y

@[to_additive (attr := simp)]
lemma coe_id {X : MonCat} : (𝟙 X : X → X) = id := rfl

@[to_additive (attr := simp)]
lemma coe_comp {X Y Z : MonCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[to_additive (attr := simp)] lemma forget_map {X Y : MonCat} (f : X ⟶ Y) :
    (forget MonCat).map f = f := rfl

@[to_additive (attr := ext)]
lemma ext {X Y : MonCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  MonoidHom.ext w

/-- Construct a bundled `MonCat` from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [Monoid M] : MonCat :=
  Bundled.of M
set_option linter.uppercaseLean3 false in
#align Mon.of MonCat.of
set_option linter.uppercaseLean3 false in
#align AddMon.of AddMonCat.of

/-- Construct a bundled `AddMonCat` from the underlying type and typeclass. -/
add_decl_doc AddMonCat.of

-- Porting note: removed `@[simp]` here, as it makes it harder to tell when to apply
-- bundled or unbundled lemmas.
-- (This change seems dangerous!)
@[to_additive]
theorem coe_of (R : Type u) [Monoid R] : (MonCat.of R : Type u) = R := rfl
set_option linter.uppercaseLean3 false in
#align Mon.coe_of MonCat.coe_of
set_option linter.uppercaseLean3 false in
#align AddMon.coe_of AddMonCat.coe_of

@[to_additive]
instance : Inhabited MonCat :=
  -- The default instance for `Monoid PUnit` is derived via `CommRing` which breaks to_additive
  ⟨@of PUnit (@DivInvMonoid.toMonoid _ (@Group.toDivInvMonoid _
    (@CommGroup.toGroup _ PUnit.commGroup)))⟩

/-- Typecheck a `MonoidHom` as a morphism in `MonCat`. -/
@[to_additive]
def ofHom {X Y : Type u} [Monoid X] [Monoid Y] (f : X →* Y) : of X ⟶ of Y := f
set_option linter.uppercaseLean3 false in
#align Mon.of_hom MonCat.ofHom
set_option linter.uppercaseLean3 false in
#align AddMon.of_hom AddMonCat.ofHom

/-- Typecheck an `AddMonoidHom` as a morphism in `AddMonCat`. -/
add_decl_doc AddMonCat.ofHom

@[to_additive (attr := simp)]
lemma ofHom_apply {X Y : Type u} [Monoid X] [Monoid Y] (f : X →* Y) (x : X) :
    (ofHom f) x = f x := rfl
set_option linter.uppercaseLean3 false in
#align Mon.of_hom_apply MonCat.ofHom_apply

---- Porting note: added to ease the port of `RepresentationTheory.Action.Basic`
@[to_additive]
instance (X Y : MonCat.{u}) : One (X ⟶ Y) := ⟨ofHom 1⟩

@[to_additive (attr := simp)]
lemma oneHom_apply (X Y : MonCat.{u}) (x : X) : (1 : X ⟶ Y) x = 1 := rfl

---- Porting note: added to ease the port of `RepresentationTheory.Action.Basic`
@[to_additive (attr := simp)]
lemma one_of {A : Type*} [Monoid A] : (1 : MonCat.of A) = (1 : A) := rfl

@[to_additive (attr := simp)]
lemma mul_of {A : Type*} [Monoid A] (a b : A) :
    @HMul.hMul (MonCat.of A) (MonCat.of A) (MonCat.of A) _ a b = a * b := rfl

@[to_additive]
instance {G : Type*} [Group G] : Group (MonCat.of G) := by assumption

/-- Universe lift functor for monoids. -/
@[to_additive (attr := simps)
  "Universe lift functor for additive monoids."]
def uliftFunctor : MonCat.{u} ⥤ MonCat.{max u v} where
  obj X := MonCat.of (ULift.{v, u} X)
  map {X Y} f := MonCat.ofHom <|
    MulEquiv.ulift.symm.toMonoidHom.comp <| f.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

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

deriving instance LargeCategory for CommMonCat
attribute [to_additive instAddCommMonCatLargeCategory] instCommMonCatLargeCategory

-- Porting note: https://github.com/leanprover-community/mathlib4/issues/5020
@[to_additive]
instance concreteCategory : ConcreteCategory CommMonCat := by
  dsimp only [CommMonCat]
  infer_instance

@[to_additive]
instance : CoeSort CommMonCat Type* where
  coe X := X.α

@[to_additive]
instance (X : CommMonCat) : CommMonoid X := X.str

-- porting note (#10670): this instance was not necessary in mathlib
@[to_additive]
instance {X Y : CommMonCat} : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe (f : X →* Y) := f

@[to_additive]
instance instFunLike (X Y : CommMonCat) : FunLike (X ⟶ Y) X Y :=
  show FunLike (X →* Y) X Y by infer_instance

@[to_additive (attr := simp)]
lemma coe_id {X : CommMonCat} : (𝟙 X : X → X) = id := rfl

@[to_additive (attr := simp)]
lemma coe_comp {X Y Z : CommMonCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[to_additive (attr := simp)]
lemma forget_map {X Y : CommMonCat} (f : X ⟶ Y) :
    (forget CommMonCat).map f = (f : X → Y) :=
  rfl

@[to_additive (attr := ext)]
lemma ext {X Y : CommMonCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  MonoidHom.ext w

/-- Construct a bundled `CommMonCat` from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [CommMonoid M] : CommMonCat :=
  Bundled.of M
set_option linter.uppercaseLean3 false in
#align CommMon.of CommMonCat.of
set_option linter.uppercaseLean3 false in
#align AddCommMon.of AddCommMonCat.of

/-- Construct a bundled `AddCommMonCat` from the underlying type and typeclass. -/
add_decl_doc AddCommMonCat.of

@[to_additive]
instance : Inhabited CommMonCat :=
  -- The default instance for `CommMonoid PUnit` is derived via `CommRing` which breaks to_additive
  ⟨@of PUnit (@CommGroup.toCommMonoid _ PUnit.commGroup)⟩

-- Porting note: removed `@[simp]` here, as it makes it harder to tell when to apply
-- bundled or unbundled lemmas.
-- (This change seems dangerous!)
@[to_additive]
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

-- Porting note: this was added to make automation work (it already exists for MonCat)
/-- Typecheck a `MonoidHom` as a morphism in `CommMonCat`. -/
@[to_additive]
def ofHom {X Y : Type u} [CommMonoid X] [CommMonoid Y] (f : X →* Y) : of X ⟶ of Y := f

/-- Typecheck an `AddMonoidHom` as a morphism in `AddCommMonCat`. -/
add_decl_doc AddCommMonCat.ofHom

@[to_additive (attr := simp)]
lemma ofHom_apply {X Y : Type u} [CommMonoid X] [CommMonoid Y] (f : X →* Y) (x : X) :
    (ofHom f) x = f x := rfl

/-- Universe lift functor for commutative monoids. -/
@[to_additive (attr := simps)
  "Universe lift functor for additive commutative monoids."]
def uliftFunctor : CommMonCat.{u} ⥤ CommMonCat.{max u v} where
  obj X := CommMonCat.of (ULift.{v, u} X)
  map {X Y} f := CommMonCat.ofHom <|
    MulEquiv.ulift.symm.toMonoidHom.comp <| f.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

end CommMonCat

variable {X Y : Type u}

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
    X ≃* Y ≅ CommMonCat.of X ≅ CommMonCat.of Y where
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
instance MonCat.forget_reflects_isos : (forget MonCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget MonCat).map f)
    -- Again a problem that exists already creeps into other things leanprover/lean4#2644
    -- this used to be `by aesop`; see next declaration
    let e : X ≃* Y := MulEquiv.mk i.toEquiv (MonoidHom.map_mul (show MonoidHom X Y from f))
    exact e.toMonCatIso.isIso_hom
set_option linter.uppercaseLean3 false in
#align Mon.forget_reflects_isos MonCat.forget_reflects_isos
set_option linter.uppercaseLean3 false in
#align AddMon.forget_reflects_isos AddMonCat.forget_reflects_isos

@[to_additive]
instance CommMonCat.forget_reflects_isos : (forget CommMonCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommMonCat).map f)
    let e : X ≃* Y := MulEquiv.mk i.toEquiv
      -- Porting FIXME: this would ideally be `by aesop`, as in `MonCat.forget_reflects_isos`
      (MonoidHom.map_mul (show MonoidHom X Y from f))
    exact e.toCommMonCatIso.isIso_hom
set_option linter.uppercaseLean3 false in
#align CommMon.forget_reflects_isos CommMonCat.forget_reflects_isos
set_option linter.uppercaseLean3 false in
#align AddCommMon.forget_reflects_isos AddCommMonCat.forget_reflects_isos

-- Porting note: this was added in order to ensure that `forget₂ CommMonCat MonCat`
-- automatically reflects isomorphisms
-- we could have used `CategoryTheory.ConcreteCategory.ReflectsIso` alternatively
@[to_additive]
instance CommMonCat.forget₂_full : (forget₂ CommMonCat MonCat).Full where
  map_surjective f := ⟨f, rfl⟩

example : (forget₂ CommMonCat MonCat).ReflectsIsomorphisms := inferInstance

/-!
`@[simp]` lemmas for `MonoidHom.comp` and categorical identities.
-/

@[to_additive (attr := simp)] theorem MonoidHom.comp_id_monCat
    {G : MonCat.{u}} {H : Type u} [Monoid H] (f : G →* H) : f.comp (𝟙 G) = f :=
  Category.id_comp (MonCat.ofHom f)
@[to_additive (attr := simp)] theorem MonoidHom.id_monCat_comp
    {G : Type u} [Monoid G] {H : MonCat.{u}} (f : G →* H) : MonoidHom.comp (𝟙 H) f = f :=
  Category.comp_id (MonCat.ofHom f)

@[to_additive (attr := simp)] theorem MonoidHom.comp_id_commMonCat
    {G : CommMonCat.{u}} {H : Type u} [CommMonoid H] (f : G →* H) : f.comp (𝟙 G) = f :=
  Category.id_comp (CommMonCat.ofHom f)
@[to_additive (attr := simp)] theorem MonoidHom.id_commMonCat_comp
    {G : Type u} [CommMonoid G] {H : CommMonCat.{u}} (f : G →* H) : MonoidHom.comp (𝟙 H) f = f :=
  Category.comp_id (CommMonCat.ofHom f)
