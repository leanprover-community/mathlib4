/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.Algebra.PUnitInstances
import Mathlib.CategoryTheory.Functor.ReflectsIso

#align_import algebra.category.Mon.basic from "leanprover-community/mathlib"@"0caf3701139ef2e69c215717665361cda205a90b"

/-!
# Category instances for monoid, add_monoid, comm_monoid, and add_comm_monoid.

We introduce the bundled categories:
* `MonCat`
* `AddMonCat`
* `CommMonCat`
* `AddCommMonCat`
along with the relevant forgetful functors between them.
-/

set_option autoImplicit true


universe u v

open CategoryTheory

/-- The category of monoids and monoid morphisms. -/
@[to_additive AddMonCat]
def MonCat : Type (u + 1) :=
  Bundled Monoid

/-- The category of additive monoids and monoid morphisms. -/
add_decl_doc AddMonCat

namespace MonCat

/-- `MonoidHom` doesn't actually assume associativity. This alias is needed to make the category
theory machinery work. -/
@[to_additive]
abbrev AssocMonoidHom (M N : Type*) [Monoid M] [Monoid N] :=
  MonoidHom M N

/-- `AddMonoidHom` doesn't actually assume associativity. This alias is needed to make
the category theory machinery work. -/
add_decl_doc AddMonCat.AssocAddMonoidHom

@[to_additive]
instance bundledHom : BundledHom AssocMonoidHom where
  toFun {X Y} _ _ f := ⇑f
  id _ := MonoidHom.id _
  comp _ _ _ := MonoidHom.comp

deriving instance LargeCategory for MonCat
attribute [to_additive instAddMonCatLargeCategory] instMonCatLargeCategory

-- Porting note: https://github.com/leanprover-community/mathlib4/issues/5020
@[to_additive]
instance concreteCategory : ConcreteCategory MonCat :=
  BundledHom.concreteCategory _

@[to_additive]
instance : CoeSort MonCat (Type*) where
  coe X := X.α

@[to_additive]
instance (X : MonCat) : Monoid X := X.str

-- porting note: this instance was not necessary in mathlib
@[to_additive]
instance {X Y : MonCat} : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe (f : X →* Y) := f

@[to_additive]
instance Hom_FunLike (X Y : MonCat) : FunLike (X ⟶ Y) X (fun _ => Y) :=
  show FunLike (X →* Y) X (fun _ => Y) by infer_instance

-- porting note: added
@[to_additive (attr := simp)]
lemma coe_id {X : MonCat} : (𝟙 X : X → X) = id := rfl

-- porting note: added
@[to_additive (attr := simp)]
lemma coe_comp {X Y Z : MonCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

-- porting note: added
@[to_additive (attr := simp)] lemma forget_map (f : X ⟶ Y) : (forget MonCat).map f = f := rfl

@[to_additive (attr := ext)]
lemma ext {X Y : MonCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  MonoidHom.ext w

/-- Construct a bundled `MonCat` from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [Monoid M] : MonCat :=
  Bundled.of M

/-- Construct a bundled `AddMonCat` from the underlying type and typeclass. -/
add_decl_doc AddMonCat.of

-- Porting note: removed `@[simp]` here, as it makes it harder to tell when to apply
-- bundled or unbundled lemmas.
-- (This change seems dangerous!)
@[to_additive]
theorem coe_of (R : Type u) [Monoid R] : (MonCat.of R : Type u) = R := rfl

@[to_additive]
instance : Inhabited MonCat :=
  -- The default instance for `Monoid PUnit` is derived via `CommRing` which breaks to_additive
  ⟨@of PUnit (@DivInvMonoid.toMonoid _ (@Group.toDivInvMonoid _
    (@CommGroup.toGroup _ PUnit.commGroup)))⟩

/-- Typecheck a `MonoidHom` as a morphism in `MonCat`. -/
@[to_additive]
def ofHom {X Y : Type u} [Monoid X] [Monoid Y] (f : X →* Y) : of X ⟶ of Y := f

/-- Typecheck an `AddMonoidHom` as a morphism in `AddMonCat`. -/
add_decl_doc AddMonCat.ofHom

@[to_additive (attr := simp)]
lemma ofHom_apply {X Y : Type u} [Monoid X] [Monoid Y] (f : X →* Y) (x : X) :
    (ofHom f) x = f x := rfl

---- porting note: added to ease the port of `RepresentationTheory.Action`
@[to_additive]
instance (X Y : MonCat.{u}) : One (X ⟶ Y) := ⟨ofHom 1⟩

@[to_additive (attr := simp)]
lemma oneHom_apply (X Y : MonCat.{u}) (x : X) : (1 : X ⟶ Y) x = 1 := rfl

---- porting note: added to ease the port of `RepresentationTheory.Action`
@[to_additive (attr := simp)]
lemma one_of {A : Type*} [Monoid A] : (1 : MonCat.of A) = (1 : A) := rfl

@[to_additive (attr := simp)]
lemma mul_of {A : Type*} [Monoid A] (a b : A) :
    @HMul.hMul (MonCat.of A) (MonCat.of A) (MonCat.of A) _ a b = a * b := rfl

@[to_additive]
instance {G : Type*} [Group G] : Group (MonCat.of G) := by assumption

end MonCat

/-- The category of commutative monoids and monoid morphisms. -/
@[to_additive AddCommMonCat]
def CommMonCat : Type (u + 1) :=
  Bundled CommMonoid

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
instance : CoeSort CommMonCat (Type*) where
  coe X := X.α

@[to_additive]
instance (X : CommMonCat) : CommMonoid X := X.str

-- porting note: this instance was not necessary in mathlib
@[to_additive]
instance {X Y : CommMonCat} : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe (f : X →* Y) := f

@[to_additive]
instance Hom_FunLike (X Y : CommMonCat) : FunLike (X ⟶ Y) X (fun _ => Y) :=
  show FunLike (X →* Y) X (fun _ => Y) by infer_instance

-- porting note: added
@[to_additive (attr := simp)]
lemma coe_id {X : CommMonCat} : (𝟙 X : X → X) = id := rfl

-- porting note: added
@[to_additive (attr := simp)]
lemma coe_comp {X Y Z : CommMonCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

-- porting note: added
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

/-- Construct a bundled `AddCommMon` from the underlying type and typeclass. -/
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

@[to_additive hasForgetToAddMonCat]
instance hasForgetToMonCat : HasForget₂ CommMonCat MonCat :=
  BundledHom.forget₂ _ _

@[to_additive]
instance : Coe CommMonCat.{u} MonCat.{u} where coe := (forget₂ CommMonCat MonCat).obj

-- porting note: this was added to make automation work (it already exists for MonCat)
/-- Typecheck a `MonoidHom` as a morphism in `CommMonCat`. -/
@[to_additive]
def ofHom {X Y : Type u} [CommMonoid X] [CommMonoid Y] (f : X →* Y) : of X ⟶ of Y := f

/-- Typecheck an `AddMonoidHom` as a morphism in `AddCommMonCat`. -/
add_decl_doc AddCommMonCat.ofHom

@[to_additive (attr := simp)]
lemma ofHom_apply {X Y : Type u} [CommMonoid X] [CommMonoid Y] (f : X →* Y) (x : X) :
    (ofHom f) x = f x := rfl

end CommMonCat

-- We verify that the coercions of morphisms to functions work correctly:
example {R S : MonCat} (f : R ⟶ S) : ↑R → ↑S := f

-- Porting note: it's essential that simp lemmas for `→*` apply to morphisms.
example {R S : MonCat} (i : R ⟶ S) (r : R) (h : r = 1) : i r = 1 := by simp [h]

example {R S : CommMonCat} (f : R ⟶ S) : ↑R → ↑S := f

example {R S : CommMonCat} (i : R ⟶ S) (r : R) (h : r = 1) : i r = 1 := by simp [h]

-- We verify that when constructing a morphism in `CommMonCat`,
-- when we construct the `toFun` field, the types are presented as `↑R`.
example (R : CommMonCat.{u}) : R ⟶ R :=
  { toFun := fun x => by
      match_target (R : Type u)
      guard_hyp x : (R : Type u)
      exact x * x
    map_one' := by simp
    map_mul' := fun x y => by
      dsimp
      rw [mul_assoc x y (x * y), ← mul_assoc y x y, mul_comm y x, mul_assoc, mul_assoc] }

variable {X Y : Type u}

section

variable [Monoid X] [Monoid Y]

/-- Build an isomorphism in the category `MonCat` from a `MulEquiv` between `Monoid`s. -/
@[to_additive (attr := simps) AddEquiv.toAddMonCatIso
      "Build an isomorphism in the category `AddMonCat` from\nan `AddEquiv` between `AddMonoid`s."]
def MulEquiv.toMonCatIso (e : X ≃* Y) : MonCat.of X ≅ MonCat.of Y where
  hom := MonCat.ofHom e.toMonoidHom
  inv := MonCat.ofHom e.symm.toMonoidHom

end

section

variable [CommMonoid X] [CommMonoid Y]

/-- Build an isomorphism in the category `CommMonCat` from a `MulEquiv` between `CommMonoid`s. -/
@[to_additive (attr := simps) AddEquiv.toAddCommMonCatIso]
def MulEquiv.toCommMonCatIso (e : X ≃* Y) : CommMonCat.of X ≅ CommMonCat.of Y where
  hom := CommMonCat.ofHom e.toMonoidHom
  inv := CommMonCat.ofHom e.symm.toMonoidHom

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

/-- Build a `MulEquiv` from an isomorphism in the category `CommMonCat`. -/
@[to_additive "Build an `AddEquiv` from an isomorphism in the category\n`AddCommMonCat`."]
def commMonCatIsoToMulEquiv {X Y : CommMonCat} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom i.inv i.hom_inv_id i.inv_hom_id

end CategoryTheory.Iso

/-- multiplicative equivalences between `Monoid`s are the same as (isomorphic to) isomorphisms
in `MonCat` -/
@[to_additive addEquivIsoAddMonCatIso]
def mulEquivIsoMonCatIso {X Y : Type u} [Monoid X] [Monoid Y] :
    X ≃* Y ≅ MonCat.of X ≅ MonCat.of Y where
  hom e := e.toMonCatIso
  inv i := i.monCatIsoToMulEquiv

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

/-- additive equivalences between `AddCommMonoid`s are
the same as (isomorphic to) isomorphisms in `AddCommMonCat` -/
add_decl_doc addEquivIsoAddCommMonCatIso

@[to_additive]
instance MonCat.forget_reflects_isos : ReflectsIsomorphisms (forget MonCat.{u}) where
  reflects {X Y} f _ := by
    let i := asIso ((forget MonCat).map f)
    -- Again a problem that exists already creeps into other things leanprover/lean4#2644
    -- this used to be `by aesop`; see next declaration
    let e : X ≃* Y := MulEquiv.mk i.toEquiv (MonoidHom.map_mul (show MonoidHom X Y from f))
    exact IsIso.of_iso e.toMonCatIso

@[to_additive]
instance CommMonCat.forget_reflects_isos : ReflectsIsomorphisms (forget CommMonCat.{u}) where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommMonCat).map f)
    let e : X ≃* Y := MulEquiv.mk i.toEquiv
      -- Porting FIXME: this would ideally be `by aesop`, as in `MonCat.forget_reflects_isos`
      (MonoidHom.map_mul (show MonoidHom X Y from f))
    exact IsIso.of_iso e.toCommMonCatIso

-- porting note: this was added in order to ensure that `forget₂ CommMonCat MonCat`
-- automatically reflects isomorphisms
-- we could have used `CategoryTheory.ConcreteCategory.ReflectsIso` alternatively
@[to_additive]
instance CommMonCat.forget₂Full : Full (forget₂ CommMonCat MonCat) where preimage f := f

example : ReflectsIsomorphisms (forget₂ CommMonCat MonCat) := inferInstance
