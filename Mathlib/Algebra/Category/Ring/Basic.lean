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

instance hasForgetToMonCat : HasForget₂ SemiRingCat MonCat :=
  BundledHom.mkHasForget₂
    (fun R hR => @MonoidWithZero.toMonoid R (@Semiring.toMonoidWithZero R hR))
    (fun {X Y} =>
      -- Porting note: without these lets, the following line fails.
      letI : Semiring X := X.2
      letI : Semiring Y := Y.2
      RingHom.toMonoidHom)
    (fun _ => rfl) -- (fun R₁ R₂ => RingHom.toMonoidHom) fun _ _ _ => rfl
set_option linter.uppercaseLean3 false in
#align SemiRing.has_forget_to_Mon SemiRingCat.hasForgetToMonCat

instance hasForgetToAddCommMonCat : HasForget₂ SemiRingCat AddCommMonCat
    where  -- can't use bundled_hom.mk_has_forget₂, since AddCommMon is an induced category
  forget₂ :=
    { obj := fun R => AddCommMonCat.of R
      -- Porting note: This doesn't work without the `(_ := _)` trick.
      map := fun {R₁ R₂} f => RingHom.toAddMonoidHom (α := R₁) (β := R₂) f }
set_option linter.uppercaseLean3 false in
#align SemiRing.has_forget_to_AddCommMon SemiRingCat.hasForgetToAddCommMonCat

end SemiRingCat

/-- The category of rings. -/
def RingCat : Type (u + 1) :=
  Bundled Ring
set_option linter.uppercaseLean3 false in
#align Ring RingCat

namespace RingCat

instance : BundledHom.ParentProjection @Ring.toSemiring :=
  ⟨⟩

-- Porting note: Another place where mathlib4 had derived a concrete category
-- but this does not work here, so we add the instance manually.
deriving instance LargeCategory for RingCat

instance : ConcreteCategory RingCat := by
  dsimp [RingCat]
  infer_instance

instance : CoeSort RingCat (Type _) := by
  dsimp [RingCat]
  infer_instance

/-- Construct a bundled Ring from the underlying type and typeclass. -/
def of (R : Type u) [Ring R] : RingCat :=
  Bundled.of R
set_option linter.uppercaseLean3 false in
#align Ring.of RingCat.of

/-- Typecheck a `ring_hom` as a morphism in `Ring`. -/
def ofHom {R S : Type u} [Ring R] [Ring S] (f : R →+* S) : of R ⟶ of S :=
  f
set_option linter.uppercaseLean3 false in
#align Ring.of_hom RingCat.ofHom

instance {R S : RingCat} : CoeFun (R ⟶ S) (fun _ => R → S) :=
  ConcreteCategory.hasCoeToFun

@[simp]
theorem ofHom_apply {R S : Type u} [Ring R] [Ring S] (f : R →+* S) (x : R) : ofHom f x = f x :=
  rfl
set_option linter.uppercaseLean3 false in
#align Ring.of_hom_apply RingCat.ofHom_apply

instance : Inhabited RingCat :=
  ⟨of PUnit⟩

instance (R : RingCat) : Ring R :=
  R.str

@[simp]
theorem coe_of (R : Type u) [Ring R] : (RingCat.of R : Type u) = R :=
  rfl
set_option linter.uppercaseLean3 false in
#align Ring.coe_of RingCat.coe_of

instance hasForgetToSemiRingCat : HasForget₂ RingCat SemiRingCat :=
  BundledHom.forget₂ _ _
set_option linter.uppercaseLean3 false in
#align Ring.has_forget_to_SemiRing RingCat.hasForgetToSemiRingCat

instance hasForgetToAddCommGroupCat : HasForget₂ RingCat AddCommGroupCat
    where -- can't use bundled_hom.mk_has_forget₂, since AddCommGroup is an induced category
  forget₂ :=
    { obj := fun R => AddCommGroupCat.of R
      -- Porting note: use `(_ := _)` similar to above.
      map := fun {R₁ R₂} f => RingHom.toAddMonoidHom (α := R₁) (β := R₂) f }
set_option linter.uppercaseLean3 false in
#align Ring.has_forget_to_AddCommGroup RingCat.hasForgetToAddCommGroupCat

end RingCat

/-- The category of commutative semirings. -/
def CommSemiRingCat : Type (u + 1) :=
  Bundled CommSemiring
set_option linter.uppercaseLean3 false in
#align CommSemiRing CommSemiRingCat

namespace CommSemiRing

instance : BundledHom.ParentProjection @CommSemiring.toSemiring :=
  ⟨⟩

-- Porting note: again, deriving fails for concrete category instances.
deriving instance LargeCategory for CommSemiRingCat

instance : ConcreteCategory CommSemiRingCat := by
  dsimp [CommSemiRingCat]
  infer_instance

instance : CoeSort CommSemiRingCat (Type _) := by
  dsimp [CommSemiRingCat]
  infer_instance

/-- Construct a bundled CommSemiRing from the underlying type and typeclass. -/
def of (R : Type u) [CommSemiring R] : CommSemiRingCat :=
  Bundled.of R
set_option linter.uppercaseLean3 false in
#align CommSemiRing.of CommSemiRing.of

/-- Typecheck a `ring_hom` as a morphism in `CommSemiRing`. -/
def ofHom {R S : Type u} [CommSemiring R] [CommSemiring S] (f : R →+* S) : of R ⟶ of S :=
  f
set_option linter.uppercaseLean3 false in
#align CommSemiRing.of_hom CommSemiRing.ofHom

instance {X Y : CommSemiRingCat} : CoeFun (X ⟶ Y) (fun _ => X → Y) :=
  ConcreteCategory.hasCoeToFun

@[simp]
theorem ofHom_apply {R S : Type u} [CommSemiring R] [CommSemiring S] (f : R →+* S) (x : R) :
    ofHom f x = f x :=
  rfl
set_option linter.uppercaseLean3 false in
#align CommSemiRing.of_hom_apply CommSemiRing.ofHom_apply

instance : Inhabited CommSemiRingCat :=
  ⟨of PUnit⟩

instance (R : CommSemiRingCat) : CommSemiring R :=
  R.str

@[simp]
theorem coe_of (R : Type u) [CommSemiring R] : (CommSemiRing.of R : Type u) = R :=
  rfl
set_option linter.uppercaseLean3 false in
#align CommSemiRing.coe_of CommSemiRing.coe_of

instance hasForgetToSemiRingCat : HasForget₂ CommSemiRingCat SemiRingCat :=
  BundledHom.forget₂ _ _
set_option linter.uppercaseLean3 false in
#align CommSemiRing.has_forget_to_SemiRing CommSemiRing.hasForgetToSemiRingCat

/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
instance hasForgetToCommMonCat : HasForget₂ CommSemiRingCat CommMonCat :=
  HasForget₂.mk' (fun R : CommSemiRingCat => CommMonCat.of R) (fun R => rfl)
    -- Porting note: `(_ := _)` trick
    (fun {R₁ R₂} f => RingHom.toMonoidHom (α := R₁) (β := R₂) f) (by rfl)
set_option linter.uppercaseLean3 false in
#align CommSemiRing.has_forget_to_CommMon CommSemiRing.hasForgetToCommMonCat

end CommSemiRing

/-- The category of commutative rings. -/
def CommRingCat : Type (u + 1) :=
  Bundled CommRing
set_option linter.uppercaseLean3 false in
#align CommRing CommRingCat

namespace CommRingCat

instance : BundledHom.ParentProjection @CommRing.toRing :=
  ⟨⟩

-- Porting note: deriving dails for concrete category.
deriving instance LargeCategory for CommRingCat

instance : ConcreteCategory CommRingCat := by
  dsimp [CommRingCat]
  infer_instance

instance : CoeSort CommRingCat (Type _) := by
  dsimp [CommRingCat]
  infer_instance

/-- Construct a bundled CommRing from the underlying type and typeclass. -/
def of (R : Type u) [CommRing R] : CommRingCat :=
  Bundled.of R
set_option linter.uppercaseLean3 false in
#align CommRing.of CommRingCat.of

/-- Typecheck a `ring_hom` as a morphism in `CommRing`. -/
def ofHom {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : of R ⟶ of S :=
  f
set_option linter.uppercaseLean3 false in
#align CommRing.of_hom CommRingCat.ofHom

instance {X Y : CommRingCat} : CoeFun (X ⟶ Y) (fun _ => X → Y) :=
  ConcreteCategory.hasCoeToFun

@[simp]
theorem ofHom_apply {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (x : R) :
    ofHom f x = f x :=
  rfl
set_option linter.uppercaseLean3 false in
#align CommRing.of_hom_apply CommRingCat.ofHom_apply

instance : Inhabited CommRingCat :=
  ⟨of PUnit⟩

instance (R : CommRingCat) : CommRing R :=
  R.str

@[simp]
theorem coe_of (R : Type u) [CommRing R] : (CommRingCat.of R : Type u) = R :=
  rfl
set_option linter.uppercaseLean3 false in
#align CommRing.coe_of CommRingCat.coe_of

instance hasForgetToRingCat : HasForget₂ CommRingCat RingCat :=
  BundledHom.forget₂ _ _
set_option linter.uppercaseLean3 false in
#align CommRing.has_forget_to_Ring CommRingCat.hasForgetToRingCat

/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
instance hasForgetToCommSemiRingCat : HasForget₂ CommRingCat CommSemiRingCat :=
  HasForget₂.mk' (fun R : CommRingCat => CommSemiRing.of R) (fun R => rfl)
    (fun {R₁ R₂} f => f) (by rfl)
set_option linter.uppercaseLean3 false in
#align CommRing.has_forget_to_CommSemiRing CommRingCat.hasForgetToCommSemiRingCat

instance : Full (forget₂ CommRingCat CommSemiRingCat) where preimage {X Y} f := f

end CommRingCat

-- This example verifies an improvement possible in Lean 3.8.
-- Before that, to have `add_ring_hom.map_zero` usable by `simp` here,
-- we had to mark all the concrete category `has_coe_to_sort` instances reducible.
-- Now, it just works.
-- Porting note: ^^^ no it doesn't :( (with Lean4/Mathlib4)
-- example {R S : CommRingCat} (i : R ⟶ S) (r : R) (h : r = 0) : i r = 0 := by simp [h]

namespace RingEquiv

variable {X Y : Type u}

/-- Build an isomorphism in the category `Ring` from a `ring_equiv` between `ring`s. -/
@[simps]
def toRingCatIso [Ring X] [Ring Y] (e : X ≃+* Y) : RingCat.of X ≅ RingCat.of Y
    where
  hom := e.toRingHom
  inv := e.symm.toRingHom
  -- Porting note: aesop_cat fails here, but `tidy` was able to close the goal.
  -- It seems that morphism applications are not being simplified away properly.
  hom_inv_id := by ext x ; exact e.symm_apply_apply x
  inv_hom_id := by ext x ; exact e.apply_symm_apply x
set_option linter.uppercaseLean3 false in
#align ring_equiv.to_Ring_iso RingEquiv.toRingCatIso

/-- Build an isomorphism in the category `CommRing` from a `ring_equiv` between `comm_ring`s. -/
@[simps]
def toCommRingCatIso [CommRing X] [CommRing Y] (e : X ≃+* Y) : CommRingCat.of X ≅ CommRingCat.of Y
    where
  hom := e.toRingHom
  inv := e.symm.toRingHom
  -- Porting note: aesop_cat fails here, but `tidy` was able to close the goal.
  -- It seems that morphism applications are not being simplified away properly.
  hom_inv_id := by ext x ; exact e.symm_apply_apply x
  inv_hom_id := by ext x ; exact e.apply_symm_apply x
set_option linter.uppercaseLean3 false in
#align ring_equiv.to_CommRing_iso RingEquiv.toCommRingCatIso

end RingEquiv

namespace CategoryTheory.Iso

/-- Build a `ring_equiv` from an isomorphism in the category `RingCat`. -/
def ringCatIsoToRingEquiv {X Y : RingCat} (i : X ≅ Y) : X ≃+* Y
    where
  toFun := i.hom
  invFun := i.inv
  -- Porting note: All these proofs were much easier in lean3.
  left_inv := fun x => show (i.hom ≫ i.inv) x = x by rw [i.hom_inv_id] ; rfl
  right_inv := fun x => show (i.inv ≫ i.hom) x = x by rw [i.inv_hom_id] ; rfl
  map_add' := fun x y => let ii : X →+* Y := i.hom ; ii.map_add x y
  map_mul' := fun x y => let ii : X →+* Y := i.hom ; ii.map_mul x y
set_option linter.uppercaseLean3 false in
#align category_theory.iso.Ring_iso_to_ring_equiv CategoryTheory.Iso.ringCatIsoToRingEquiv

/-- Build a `ring_equiv` from an isomorphism in the category `CommRing`. -/
def commRingCatIsoToRingEquiv {X Y : CommRingCat} (i : X ≅ Y) : X ≃+* Y
    where
  toFun := i.hom
  invFun := i.inv
  -- Porting note: All these proofs were much easier in lean3.
  left_inv := fun x => show (i.hom ≫ i.inv) x = x by rw [i.hom_inv_id] ; rfl
  right_inv := fun x => show (i.inv ≫ i.hom) x = x by rw [i.inv_hom_id] ; rfl
  map_add' := fun x y => let ii : X →+* Y := i.hom ; ii.map_add x y
  map_mul' := fun x y => let ii : X →+* Y := i.hom ; ii.map_mul x y
set_option linter.uppercaseLean3 false in
#align category_theory.iso.CommRing_iso_to_ring_equiv CategoryTheory.Iso.commRingCatIsoToRingEquiv

@[simp]
theorem commRingIsoToRingEquiv_toRingHom {X Y : CommRingCat} (i : X ≅ Y) :
    i.commRingCatIsoToRingEquiv.toRingHom = i.hom := by
  ext
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.iso.CommRing_iso_to_ring_equiv_to_ring_hom CategoryTheory.Iso.commRingIsoToRingEquiv_toRingHom

@[simp]
theorem commRingIsoToRingEquiv_symm_toRingHom {X Y : CommRingCat} (i : X ≅ Y) :
    i.commRingCatIsoToRingEquiv.symm.toRingHom = i.inv := by
  ext
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.iso.CommRing_iso_to_ring_equiv_symm_to_ring_hom CategoryTheory.Iso.commRingIsoToRingEquiv_symm_toRingHom

end CategoryTheory.Iso

/-- Ring equivalences between `ring`s are the same as (isomorphic to) isomorphisms in `Ring`. -/
def ringEquivIsoRingIso {X Y : Type u} [Ring X] [Ring Y] : X ≃+* Y ≅ RingCat.of X ≅ RingCat.of Y
    where
  hom e := e.toRingCatIso
  inv i := i.ringCatIsoToRingEquiv
set_option linter.uppercaseLean3 false in
#align ring_equiv_iso_Ring_iso ringEquivIsoRingIso

/-- Ring equivalences between `comm_ring`s are the same as (isomorphic to) isomorphisms
in `CommRing`. -/
def ringEquivIsoCommRingIso {X Y : Type u} [CommRing X] [CommRing Y] :
    X ≃+* Y ≅ CommRingCat.of X ≅ CommRingCat.of Y
    where
  hom e := e.toCommRingCatIso
  inv i := i.commRingCatIsoToRingEquiv
set_option linter.uppercaseLean3 false in
#align ring_equiv_iso_CommRing_iso ringEquivIsoCommRingIso

instance RingCat.forget_reflects_isos : ReflectsIsomorphisms (forget RingCat.{u})
    where
  reflects {X Y} f _ := by
    let i := asIso ((forget RingCat).map f)
    let ff : X →+* Y := f
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact ⟨(IsIso.of_iso e.toRingCatIso).1⟩
set_option linter.uppercaseLean3 false in
#align Ring.forget_reflects_isos RingCat.forget_reflects_isos

instance CommRingCat.forget_reflects_isos : ReflectsIsomorphisms (forget CommRingCat.{u})
    where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommRingCat).map f)
    let ff : X →+* Y := f
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact ⟨(IsIso.of_iso e.toCommRingCatIso).1⟩
set_option linter.uppercaseLean3 false in
#align CommRing.forget_reflects_isos CommRingCat.forget_reflects_isos

theorem CommRingCat.comp_eq_ring_hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    f ≫ g = g.comp f :=
  rfl
set_option linter.uppercaseLean3 false in
#align CommRing.comp_eq_ring_hom_comp CommRingCat.comp_eq_ring_hom_comp

theorem CommRingCat.ringHom_comp_eq_comp {R S T : Type _} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) : g.comp f = CommRingCat.ofHom f ≫ CommRingCat.ofHom g :=
  rfl
set_option linter.uppercaseLean3 false in
#align CommRing.ring_hom_comp_eq_comp CommRingCat.ringHom_comp_eq_comp

-- Porting note: Again, the following attribute and example fail in lean 4, unfortunately.

-- It would be nice if we could have the following,
-- but it requires making `reflects_isomorphisms_forget₂` an instance,
-- which can cause typeclass loops:
-- attribute [local instance] reflects_isomorphisms_forget₂

-- example : ReflectsIsomorphisms (forget₂ RingCat AddCommGroupCat) := by infer_instance
