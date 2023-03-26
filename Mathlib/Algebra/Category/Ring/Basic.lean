/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.category.Ring.basic
! leanprover-community/mathlib commit 34b2a989ad80bce3a5de749d935a4f23726e26e9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Category.GroupCat.Basic
import Mathlib.CategoryTheory.ConcreteCategory.ReflectsIso
import Mathlib.CategoryTheory.Elementwise
import Mathlib.Algebra.Ring.Equiv

/-!
# Category instances for semiring, ring, comm_semiring, and comm_ring.

We introduce the bundled categories:
* `SemiRing`
* `Ring`
* `CommSemiRing`
* `CommRing`
along with the relevant forgetful functors between them.
-/


universe u v

open CategoryTheory

/-- The category of semirings. -/
def SemiRingCat : Type (u + 1) :=
  Bundled Semiring
set_option linter.uppercaseLean3 false in
#align SemiRing SemiRingCat

namespace SemiRingCat

/-- `ring_hom` doesn't actually assume associativity. This alias is needed to make the category
theory machinery work. We use the same trick in `category_theory.Mon.assoc_monoid_hom`. -/
abbrev AssocRingHom (M N : Type _) [Semiring M] [Semiring N] :=
  RingHom M N
set_option linter.uppercaseLean3 false in
#align SemiRing.assoc_ring_hom SemiRingCat.AssocRingHom
/-
  toFun : ∀ {α β : Type u} (Iα : c α) (Iβ : c β), hom Iα Iβ → α → β
  /-- the identity as a bundled morphism -/
  id : ∀ {α : Type u} (I : c α), hom I I
  /-- composition of bundled morphisms -/
  comp : ∀ {α β γ : Type u} (Iα : c α) (Iβ : c β) (Iγ : c γ), hom Iβ Iγ → hom Iα Iβ → hom Iα Iγ
  /-- a bundled morphism is determined by the underlying map -/
  hom_ext : ∀ {α β : Type u} (Iα : c α) (Iβ : c β), Function.Injective (toFun Iα Iβ) := by
   aesop_cat
  /-- compatibility with identities -/
  id_toFun : ∀ {α : Type u} (I : c α), toFun I I (id I) = _root_.id := by aesop_cat
  /-- compatibility with the composition -/
  comp_toFun
-/

instance bundledHom : BundledHom AssocRingHom where
  toFun := fun {M N} _ _ f => f
  id := fun {A} _ => RingHom.id _
  comp := fun {M N L} _ _ _ f g => f.comp g
  hom_ext := fun {A B} _ _ f g h => by ext x ; exact congrFun h x
  id_toFun := fun {A} _ => by ext x ; rfl
  comp_toFun := fun {A B C} _ _ _ f g => rfl
  /-
  Porting note: The ported proof is this:
  ⟨fun M N [Semiring M] [Semiring N] => @RingHom.toFun M N _ _, fun M [Semiring M] =>
    @RingHom.id M _, fun M N P [Semiring M] [Semiring N] [Semiring P] => @RingHom.comp M N P _ _ _,
    fun M N [Semiring M] [Semiring N] => @RingHom.coe_inj M N _ _⟩
  -/
set_option linter.uppercaseLean3 false in
#align SemiRing.bundled_hom SemiRingCat.bundledHom

--Porting note: deriving fails for ConcreteCategory, adding instance manually.
--deriving instance LargeCategory, ConcreteCategory for SemiRingCat

deriving instance LargeCategory for SemiRingCat

instance : ConcreteCategory SemiRingCat := by
  dsimp [SemiRingCat]
  infer_instance

instance : CoeSort SemiRingCat (Type _) := by
  dsimp [SemiRingCat]
  infer_instance

/-- Construct a bundled SemiRing from the underlying type and typeclass. -/
def of (R : Type u) [Semiring R] : SemiRingCat :=
  Bundled.of R
set_option linter.uppercaseLean3 false in
#align SemiRing.of SemiRingCat.of

/-- Typecheck a `ring_hom` as a morphism in `SemiRing`. -/
def ofHom {R S : Type u} [Semiring R] [Semiring S] (f : R →+* S) : of R ⟶ of S :=
  f
set_option linter.uppercaseLean3 false in
#align SemiRing.of_hom SemiRingCat.ofHom

-- Porting note: needed for several lemmas below.
-- I assume this is correct, given the useful bits of `FunLike` are now part of
--  bundledHom` in some sense.
instance {X Y : SemiRingCat} : CoeFun (X ⟶ Y) (fun _ => X → Y) :=
  ConcreteCategory.hasCoeToFun

@[simp]
theorem ofHom_apply {R S : Type u} [Semiring R] [Semiring S] (f : R →+* S) (x : R) :
    ofHom f x = f x :=
  rfl
set_option linter.uppercaseLean3 false in
#align SemiRing.of_hom_apply SemiRingCat.ofHom_apply

instance : Inhabited SemiRingCat :=
  ⟨of PUnit⟩

instance (R : SemiRingCat) : Semiring R :=
  R.str

@[simp]
theorem coe_of (R : Type u) [Semiring R] : (SemiRingCat.of R : Type u) = R :=
  rfl
set_option linter.uppercaseLean3 false in
#align SemiRing.coe_of SemiRingCat.coe_of

instance hasForgetToMon : HasForget₂ SemiRingCat MonCat :=
  BundledHom.mkHasForget₂
    (fun R hR => @MonoidWithZero.toMonoid R (@Semiring.toMonoidWithZero R hR))
    (fun {X Y} =>
      -- Porting note: without these lets, the following line fails.
      letI : Semiring X := X.2
      letI : Semiring Y := Y.2
      RingHom.toMonoidHom)
    (fun _ => rfl) -- (fun R₁ R₂ => RingHom.toMonoidHom) fun _ _ _ => rfl
set_option linter.uppercaseLean3 false in
#align SemiRing.has_forget_to_Mon SemiRingCat.hasForgetToMon

instance hasForgetToAddCommMon : HasForget₂ SemiRingCat AddCommMonCat
    where  -- can't use bundled_hom.mk_has_forget₂, since AddCommMon is an induced category
  forget₂ :=
    { obj := fun R => AddCommMonCat.of R
      -- Porting note: Error in the next line, again due to TC search failure.
      map := fun {R₁ R₂} f => RingHom.toAddMonoidHom f
      map_comp := sorry
      map_id := sorry }
  forget_comp := sorry
set_option linter.uppercaseLean3 false in
#align SemiRing.has_forget_to_AddCommMon SemiRingCat.hasForgetToAddCommMon

end SemiRingCat

/-- The category of rings. -/
def RingCat : Type (u + 1) :=
  Bundled Ring
#align Ring RingCat

namespace RingCat

instance : BundledHom.ParentProjection @Ring.toSemiring :=
  ⟨⟩

/- ./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler λ Ring,
has_coe_to_sort[has_coe_to_sort] Ring (Type*) -/
deriving instance
  «./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler λ Ring,
  has_coe_to_sort[has_coe_to_sort] Ring (Type*)», LargeCategory, ConcreteCategory for RingCat

/-- Construct a bundled Ring from the underlying type and typeclass. -/
def of (R : Type u) [Ring R] : RingCat :=
  Bundled.of R
#align Ring.of RingCat.of

/-- Typecheck a `ring_hom` as a morphism in `Ring`. -/
def ofHom {R S : Type u} [Ring R] [Ring S] (f : R →+* S) : of R ⟶ of S :=
  f
#align Ring.of_hom RingCat.ofHom

@[simp]
theorem ofHom_apply {R S : Type u} [Ring R] [Ring S] (f : R →+* S) (x : R) : ofHom f x = f x :=
  rfl
#align Ring.of_hom_apply RingCat.ofHom_apply

instance : Inhabited RingCat :=
  ⟨of PUnit⟩

instance (R : RingCat) : Ring R :=
  R.str

@[simp]
theorem coe_of (R : Type u) [Ring R] : (RingCat.of R : Type u) = R :=
  rfl
#align Ring.coe_of RingCat.coe_of

instance hasForgetToSemiRing : HasForget₂ RingCat SemiRing :=
  BundledHom.forget₂ _ _
#align Ring.has_forget_to_SemiRing RingCat.hasForgetToSemiRing

instance hasForgetToAddCommGroup : HasForget₂ RingCat AddCommGroupCat
    where-- can't use bundled_hom.mk_has_forget₂, since AddCommGroup is an induced category
  forget₂ :=
    { obj := fun R => AddCommGroupCat.of R
      map := fun R₁ R₂ f => RingHom.toAddMonoidHom f }
#align Ring.has_forget_to_AddCommGroup RingCat.hasForgetToAddCommGroup

end RingCat

/-- The category of commutative semirings. -/
def CommSemiRing : Type (u + 1) :=
  Bundled CommSemiring
#align CommSemiRing CommSemiRing

namespace CommSemiRing

instance : BundledHom.ParentProjection @CommSemiring.toSemiring :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for CommSemiRing

instance : CoeSort CommSemiRing (Type _) :=
  Bundled.hasCoeToSort

/-- Construct a bundled CommSemiRing from the underlying type and typeclass. -/
def of (R : Type u) [CommSemiring R] : CommSemiRing :=
  Bundled.of R
#align CommSemiRing.of CommSemiRing.of

/-- Typecheck a `ring_hom` as a morphism in `CommSemiRing`. -/
def ofHom {R S : Type u} [CommSemiring R] [CommSemiring S] (f : R →+* S) : of R ⟶ of S :=
  f
#align CommSemiRing.of_hom CommSemiRing.ofHom

@[simp]
theorem ofHom_apply {R S : Type u} [CommSemiring R] [CommSemiring S] (f : R →+* S) (x : R) :
    ofHom f x = f x :=
  rfl
#align CommSemiRing.of_hom_apply CommSemiRing.ofHom_apply

instance : Inhabited CommSemiRing :=
  ⟨of PUnit⟩

instance (R : CommSemiRing) : CommSemiring R :=
  R.str

@[simp]
theorem coe_of (R : Type u) [CommSemiring R] : (CommSemiRing.of R : Type u) = R :=
  rfl
#align CommSemiRing.coe_of CommSemiRing.coe_of

instance hasForgetToSemiRing : HasForget₂ CommSemiRing SemiRing :=
  BundledHom.forget₂ _ _
#align CommSemiRing.has_forget_to_SemiRing CommSemiRing.hasForgetToSemiRing

/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
instance hasForgetToCommMon : HasForget₂ CommSemiRing CommMonCat :=
  HasForget₂.mk' (fun R : CommSemiRing => CommMonCat.of R) (fun R => rfl)
    (fun R₁ R₂ f => f.toMonoidHom) (by tidy)
#align CommSemiRing.has_forget_to_CommMon CommSemiRing.hasForgetToCommMon

end CommSemiRing

/-- The category of commutative rings. -/
def CommRingCat : Type (u + 1) :=
  Bundled CommRing
#align CommRing CommRingCat

namespace CommRingCat

instance : BundledHom.ParentProjection @CommRing.toRing :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for CommRingCat

instance : CoeSort CommRingCat (Type _) :=
  Bundled.hasCoeToSort

/-- Construct a bundled CommRing from the underlying type and typeclass. -/
def of (R : Type u) [CommRing R] : CommRingCat :=
  Bundled.of R
#align CommRing.of CommRingCat.of

/-- Typecheck a `ring_hom` as a morphism in `CommRing`. -/
def ofHom {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : of R ⟶ of S :=
  f
#align CommRing.of_hom CommRingCat.ofHom

@[simp]
theorem ofHom_apply {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (x : R) :
    ofHom f x = f x :=
  rfl
#align CommRing.of_hom_apply CommRingCat.ofHom_apply

instance : Inhabited CommRingCat :=
  ⟨of PUnit⟩

instance (R : CommRingCat) : CommRing R :=
  R.str

@[simp]
theorem coe_of (R : Type u) [CommRing R] : (CommRingCat.of R : Type u) = R :=
  rfl
#align CommRing.coe_of CommRingCat.coe_of

instance hasForgetToRing : HasForget₂ CommRingCat RingCat :=
  BundledHom.forget₂ _ _
#align CommRing.has_forget_to_Ring CommRingCat.hasForgetToRing

/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
instance hasForgetToCommSemiRing : HasForget₂ CommRingCat CommSemiRing :=
  HasForget₂.mk' (fun R : CommRingCat => CommSemiRing.of R) (fun R => rfl) (fun R₁ R₂ f => f)
    (by tidy)
#align CommRing.has_forget_to_CommSemiRing CommRingCat.hasForgetToCommSemiRing

instance : Full (forget₂ CommRingCat CommSemiRing) where preimage X Y f := f

end CommRingCat

-- This example verifies an improvement possible in Lean 3.8.
-- Before that, to have `add_ring_hom.map_zero` usable by `simp` here,
-- we had to mark all the concrete category `has_coe_to_sort` instances reducible.
-- Now, it just works.
example {R S : CommRingCat} (i : R ⟶ S) (r : R) (h : r = 0) : i r = 0 := by simp [h]

namespace RingEquiv

variable {X Y : Type u}

/-- Build an isomorphism in the category `Ring` from a `ring_equiv` between `ring`s. -/
@[simps]
def toRingIso [Ring X] [Ring Y] (e : X ≃+* Y) : RingCat.of X ≅ RingCat.of Y
    where
  Hom := e.toRingHom
  inv := e.symm.toRingHom
#align ring_equiv.to_Ring_iso RingEquiv.toRingIso

/-- Build an isomorphism in the category `CommRing` from a `ring_equiv` between `comm_ring`s. -/
@[simps]
def toCommRingIso [CommRing X] [CommRing Y] (e : X ≃+* Y) : CommRingCat.of X ≅ CommRingCat.of Y
    where
  Hom := e.toRingHom
  inv := e.symm.toRingHom
#align ring_equiv.to_CommRing_iso RingEquiv.toCommRingIso

end RingEquiv

namespace CategoryTheory.Iso

/-- Build a `ring_equiv` from an isomorphism in the category `Ring`. -/
def ringIsoToRingEquiv {X Y : RingCat} (i : X ≅ Y) : X ≃+* Y
    where
  toFun := i.Hom
  invFun := i.inv
  left_inv := by tidy
  right_inv := by tidy
  map_add' := by tidy
  map_mul' := by tidy
#align category_theory.iso.Ring_iso_to_ring_equiv CategoryTheory.Iso.ringIsoToRingEquiv

/-- Build a `ring_equiv` from an isomorphism in the category `CommRing`. -/
def commRingIsoToRingEquiv {X Y : CommRingCat} (i : X ≅ Y) : X ≃+* Y
    where
  toFun := i.Hom
  invFun := i.inv
  left_inv := by tidy
  right_inv := by tidy
  map_add' := by tidy
  map_mul' := by tidy
#align category_theory.iso.CommRing_iso_to_ring_equiv CategoryTheory.Iso.commRingIsoToRingEquiv

@[simp]
theorem commRingIsoToRingEquiv_toRingHom {X Y : CommRingCat} (i : X ≅ Y) :
    i.commRingIsoToRingEquiv.toRingHom = i.Hom := by
  ext
  rfl
#align category_theory.iso.CommRing_iso_to_ring_equiv_to_ring_hom CategoryTheory.Iso.commRingIsoToRingEquiv_toRingHom

@[simp]
theorem commRingIsoToRingEquiv_symm_toRingHom {X Y : CommRingCat} (i : X ≅ Y) :
    i.commRingIsoToRingEquiv.symm.toRingHom = i.inv := by
  ext
  rfl
#align category_theory.iso.CommRing_iso_to_ring_equiv_symm_to_ring_hom CategoryTheory.Iso.commRingIsoToRingEquiv_symm_toRingHom

end CategoryTheory.Iso

/-- Ring equivalences between `ring`s are the same as (isomorphic to) isomorphisms in `Ring`. -/
def ringEquivIsoRingIso {X Y : Type u} [Ring X] [Ring Y] : X ≃+* Y ≅ RingCat.of X ≅ RingCat.of Y
    where
  Hom e := e.toRingIso
  inv i := i.ringIsoToRingEquiv
#align ring_equiv_iso_Ring_iso ringEquivIsoRingIso

/-- Ring equivalences between `comm_ring`s are the same as (isomorphic to) isomorphisms
in `CommRing`. -/
def ringEquivIsoCommRingIso {X Y : Type u} [CommRing X] [CommRing Y] :
    X ≃+* Y ≅ CommRingCat.of X ≅ CommRingCat.of Y
    where
  Hom e := e.toCommRingIso
  inv i := i.commRingIsoToRingEquiv
#align ring_equiv_iso_CommRing_iso ringEquivIsoCommRingIso

instance RingCat.forget_reflects_isos : ReflectsIsomorphisms (forget RingCat.{u})
    where reflects X Y f _ := by
    skip
    let i := as_iso ((forget RingCat).map f)
    let e : X ≃+* Y := { f, i.to_equiv with }
    exact ⟨(is_iso.of_iso e.to_Ring_iso).1⟩
#align Ring.forget_reflects_isos RingCat.forget_reflects_isos

instance CommRingCat.forget_reflects_isos : ReflectsIsomorphisms (forget CommRingCat.{u})
    where reflects X Y f _ := by
    skip
    let i := as_iso ((forget CommRingCat).map f)
    let e : X ≃+* Y := { f, i.to_equiv with }
    exact ⟨(is_iso.of_iso e.to_CommRing_iso).1⟩
#align CommRing.forget_reflects_isos CommRingCat.forget_reflects_isos

theorem CommRingCat.comp_eq_ring_hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    f ≫ g = g.comp f :=
  rfl
#align CommRing.comp_eq_ring_hom_comp CommRingCat.comp_eq_ring_hom_comp

theorem CommRingCat.ringHom_comp_eq_comp {R S T : Type _} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) : g.comp f = CommRingCat.ofHom f ≫ CommRingCat.ofHom g :=
  rfl
#align CommRing.ring_hom_comp_eq_comp CommRingCat.ringHom_comp_eq_comp

-- It would be nice if we could have the following,
-- but it requires making `reflects_isomorphisms_forget₂` an instance,
-- which can cause typeclass loops:
attribute [local instance] reflects_isomorphisms_forget₂

example : ReflectsIsomorphisms (forget₂ RingCat AddCommGroupCat) := by infer_instance
