/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Algebra.Category.GroupCat.Basic
import Mathlib.CategoryTheory.ConcreteCategory.ReflectsIso
import Mathlib.Algebra.Ring.Equiv

#align_import algebra.category.Ring.basic from "leanprover-community/mathlib"@"34b2a989ad80bce3a5de749d935a4f23726e26e9"

/-!
# Category instances for `Semiring`, `Ring`, `CommSemiring`, and `CommRing`.

We introduce the bundled categories:
* `SemiRingCat`
* `RingCat`
* `CommSemiRingCat`
* `CommRingCat`
along with the relevant forgetful functors between them.
-/

universe u v

open CategoryTheory

/-- The category of semirings. -/
abbrev SemiRingCat : Type (u + 1) :=
  Bundled Semiring
set_option linter.uppercaseLean3 false in
#align SemiRing SemiRingCat

-- Porting note: typemax hack to fix universe complaints
/-- An alias for `Semiring.{max u v}`, to deal around unification issues. -/
@[nolint checkUnivs]
abbrev SemiRingCatMax.{u1, u2} := SemiRingCat.{max u1 u2}

namespace SemiRingCat

/-- `RingHom` doesn't actually assume associativity. This alias is needed to make the category
theory machinery work. We use the same trick in `MonCat.AssocMonoidHom`. -/
abbrev AssocRingHom (M N : Type*) [Semiring M] [Semiring N] :=
  RingHom M N
set_option linter.uppercaseLean3 false in
#align SemiRing.assoc_ring_hom SemiRingCat.AssocRingHom

instance bundledHom : BundledHom AssocRingHom where
  toFun _ _ f := f
  id _ := RingHom.id _
  comp _ _ _ f g := f.comp g
set_option linter.uppercaseLean3 false in
#align SemiRing.bundled_hom SemiRingCat.bundledHom

-- Porting note: deriving fails for ConcreteCategory, adding instance manually.
--deriving instance LargeCategory, ConcreteCategory for SemiRingCat
-- see https://github.com/leanprover-community/mathlib4/issues/5020

-- Porting note: Hinting to Lean that `forget R` and `R` are the same
unif_hint forget_obj_eq_coe (R : SemiRingCat) where ⊢
  (forget SemiRingCat).obj R ≟ R

instance instSemiring (X : SemiRingCat) : Semiring X := X.str

instance instFunLike {X Y : SemiRingCat} : FunLike (X ⟶ Y) X Y :=
  ConcreteCategory.instFunLike

-- Porting note (#10754): added instance
instance instRingHomClass {X Y : SemiRingCat} : RingHomClass (X ⟶ Y) X Y :=
  RingHom.instRingHomClass

-- Porting note (#10756): added lemma
lemma coe_id {X : SemiRingCat} : (𝟙 X : X → X) = id := rfl

-- Porting note (#10756): added lemma
lemma coe_comp {X Y Z : SemiRingCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

-- porting note (#10756): added lemma
@[simp] lemma forget_map {X Y : SemiRingCat} (f : X ⟶ Y) :
    (forget SemiRingCat).map f = (f : X → Y) := rfl

lemma ext {X Y : SemiRingCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  RingHom.ext w

/-- Construct a bundled SemiRing from the underlying type and typeclass. -/
def of (R : Type u) [Semiring R] : SemiRingCat :=
  Bundled.of R
set_option linter.uppercaseLean3 false in
#align SemiRing.of SemiRingCat.of

@[simp]
theorem coe_of (R : Type u) [Semiring R] : (SemiRingCat.of R : Type u) = R :=
  rfl
set_option linter.uppercaseLean3 false in
#align SemiRing.coe_of SemiRingCat.coe_of

-- Coercing the identity morphism, as a ring homomorphism, gives the identity function.
@[simp] theorem coe_ringHom_id {X : SemiRingCat} :
    @DFunLike.coe (X →+* X) X (fun _ ↦ X) _ (𝟙 X) = id :=
  rfl

-- Coercing `𝟙 (of X)` to a function should be expressed as the coercion of `RingHom.id X`.
@[simp] theorem coe_id_of {X : Type u} [Semiring X] :
    @DFunLike.coe no_index (SemiRingCat.of X ⟶ SemiRingCat.of X) X
      (fun _ ↦ X) _
      (𝟙 (of X)) =
    @DFunLike.coe (X →+* X) X (fun _ ↦ X) _ (RingHom.id X) :=
  rfl

-- Coercing `f ≫ g`, where `f : of X ⟶ of Y` and `g : of Y ⟶ of Z`, to a function should be
-- expressed in terms of the coercion of `g.comp f`.
@[simp] theorem coe_comp_of {X Y Z : Type u} [Semiring X] [Semiring Y] [Semiring Z]
    (f : X →+* Y) (g : Y →+* Z) :
    @DFunLike.coe no_index (SemiRingCat.of X ⟶ SemiRingCat.of Z) X
      (fun _ ↦ Z) _
      (CategoryStruct.comp (X := SemiRingCat.of X) (Y := SemiRingCat.of Y) (Z := SemiRingCat.of Z)
        f g) =
    @DFunLike.coe (X →+* Z) X (fun _ ↦ Z) _ (RingHom.comp g f) :=
  rfl

-- Sometimes neither the `ext` lemma for `SemiRingCat` nor for `RingHom` is applicable,
-- because of incomplete unfolding of `SemiRingCat.of X ⟶ SemiRingCat.of Y := X →+* Y`,
-- but this one will fire.
@[ext] theorem ext_of {X Y : Type u} [Semiring X] [Semiring Y] (f g : X →+* Y)
    (h : ∀ x, f x = g x) :
    @Eq (SemiRingCat.of X ⟶ SemiRingCat.of Y) f g :=
  RingHom.ext h

@[simp]
lemma RingEquiv_coe_eq {X Y : Type _} [Semiring X] [Semiring Y] (e : X ≃+* Y) :
    (@DFunLike.coe (SemiRingCat.of X ⟶ SemiRingCat.of Y) _ (fun _ => (forget SemiRingCat).obj _)
      ConcreteCategory.instFunLike (e : X →+* Y) : X → Y) = ↑e :=
  rfl

instance : Inhabited SemiRingCat :=
  ⟨of PUnit⟩

instance hasForgetToMonCat : HasForget₂ SemiRingCat MonCat :=
  BundledHom.mkHasForget₂
    (fun R hR => @MonoidWithZero.toMonoid R (@Semiring.toMonoidWithZero R hR))
    (fun {_ _} => RingHom.toMonoidHom)
    (fun _ => rfl)
set_option linter.uppercaseLean3 false in
#align SemiRing.has_forget_to_Mon SemiRingCat.hasForgetToMonCat

instance hasForgetToAddCommMonCat : HasForget₂ SemiRingCat AddCommMonCat where
   -- can't use BundledHom.mkHasForget₂, since AddCommMon is an induced category
  forget₂ :=
    { obj := fun R => AddCommMonCat.of R
      -- Porting note: This doesn't work without the `(_ := _)` trick.
      map := fun {R₁ R₂} f => RingHom.toAddMonoidHom (α := R₁) (β := R₂) f }
set_option linter.uppercaseLean3 false in
#align SemiRing.has_forget_to_AddCommMon SemiRingCat.hasForgetToAddCommMonCat

/-- Typecheck a `RingHom` as a morphism in `SemiRingCat`. -/
def ofHom {R S : Type u} [Semiring R] [Semiring S] (f : R →+* S) : of R ⟶ of S :=
  f
set_option linter.uppercaseLean3 false in
#align SemiRing.of_hom SemiRingCat.ofHom

-- Porting note: `simpNF` should not trigger on `rfl` lemmas.
-- see https://github.com/leanprover/std4/issues/86
@[simp, nolint simpNF]
theorem ofHom_apply {R S : Type u} [Semiring R] [Semiring S] (f : R →+* S) (x : R) :
    ofHom f x = f x :=
  rfl
set_option linter.uppercaseLean3 false in
#align SemiRing.of_hom_apply SemiRingCat.ofHom_apply

/--
Ring equivalence are isomorphisms in category of semirings
-/
@[simps]
def _root_.RingEquiv.toSemiRingCatIso {X Y : Type u} [Semiring X] [Semiring Y] (e : X ≃+* Y) :
    SemiRingCat.of X ≅ SemiRingCat.of Y where
  hom := e.toRingHom
  inv := e.symm.toRingHom

instance forgetReflectIsos : (forget SemiRingCat).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget SemiRingCat).map f)
    let ff : X →+* Y := f
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact e.toSemiRingCatIso.isIso_hom

end SemiRingCat

/-- The category of rings. -/
abbrev RingCat : Type (u + 1) :=
  Bundled Ring
set_option linter.uppercaseLean3 false in
#align Ring RingCat

namespace RingCat

instance : BundledHom.ParentProjection @Ring.toSemiring :=
  ⟨⟩

-- Porting note: Another place where mathlib had derived a concrete category
-- but this does not work here, so we add the instance manually.
-- see https://github.com/leanprover-community/mathlib4/issues/5020

instance (X : RingCat) : Ring X := X.str

-- Porting note: Hinting to Lean that `forget R` and `R` are the same
unif_hint forget_obj_eq_coe (R : RingCat) where ⊢
  (forget RingCat).obj R ≟ R

instance instRing (X : RingCat) : Ring X := X.str

instance instFunLike {X Y : RingCat} : FunLike (X ⟶ Y) X Y :=
  -- Note: this is apparently _not_ defeq to RingHom.instFunLike with reducible transparency
  ConcreteCategory.instFunLike

-- Porting note (#10754): added instance
instance instRingHomClass {X Y : RingCat} : RingHomClass (X ⟶ Y) X Y :=
  RingHom.instRingHomClass

-- Porting note (#10756): added lemma
lemma coe_id {X : RingCat} : (𝟙 X : X → X) = id := rfl

-- Porting note (#10756): added lemma
lemma coe_comp {X Y Z : RingCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

-- porting note (#10756): added lemma
@[simp] lemma forget_map {X Y : RingCat} (f : X ⟶ Y) : (forget RingCat).map f = (f : X → Y) := rfl

lemma ext {X Y : RingCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  RingHom.ext w

/-- Construct a bundled `RingCat` from the underlying type and typeclass. -/
def of (R : Type u) [Ring R] : RingCat :=
  Bundled.of R
set_option linter.uppercaseLean3 false in
#align Ring.of RingCat.of

/-- Typecheck a `RingHom` as a morphism in `RingCat`. -/
def ofHom {R S : Type u} [Ring R] [Ring S] (f : R →+* S) : of R ⟶ of S :=
  f
set_option linter.uppercaseLean3 false in
#align Ring.of_hom RingCat.ofHom

-- Porting note: I think this is now redundant.
-- @[simp]
-- theorem ofHom_apply {R S : Type u} [Ring R] [Ring S] (f : R →+* S) (x : R) : ofHom f x = f x :=
--   rfl
-- set_option linter.uppercaseLean3 false in
-- #align Ring.of_hom_apply RingCat.ofHom_apply

instance : Inhabited RingCat :=
  ⟨of PUnit⟩

instance (R : RingCat) : Ring R :=
  R.str

@[simp]
theorem coe_of (R : Type u) [Ring R] : (RingCat.of R : Type u) = R :=
  rfl
set_option linter.uppercaseLean3 false in
#align Ring.coe_of RingCat.coe_of

-- Coercing the identity morphism, as a ring homomorphism, gives the identity function.
@[simp] theorem coe_ringHom_id {X : RingCat} :
    @DFunLike.coe (X →+* X) X (fun _ ↦ X) _ (𝟙 X) = id :=
  rfl

-- Coercing `𝟙 (of X)` to a function should be expressed as the coercion of `RingHom.id X`.
@[simp] theorem coe_id_of {X : Type u} [Ring X] :
    @DFunLike.coe no_index (RingCat.of X ⟶ RingCat.of X) X
      (fun _ ↦ X) _
      (𝟙 (of X)) =
    @DFunLike.coe (X →+* X) X (fun _ ↦ X) _ (RingHom.id X) :=
  rfl

-- Coercing `f ≫ g`, where `f : of X ⟶ of Y` and `g : of Y ⟶ of Z`, to a function should be
-- expressed in terms of the coercion of `g.comp f`.
@[simp] theorem coe_comp_of {X Y Z : Type u} [Ring X] [Ring Y] [Ring Z]
    (f : X →+* Y) (g : Y →+* Z) :
    @DFunLike.coe no_index (RingCat.of X ⟶ RingCat.of Z) X
      (fun _ ↦ Z) _
      (CategoryStruct.comp (X := RingCat.of X) (Y := RingCat.of Y) (Z := RingCat.of Z)
        f g) =
    @DFunLike.coe (X →+* Z) X (fun _ ↦ Z) _ (RingHom.comp g f) :=
  rfl

-- Sometimes neither the `ext` lemma for `RingCat` nor for `RingHom` is applicable,
-- because of incomplete unfolding of `RingCat.of X ⟶ RingCat.of Y := X →+* Y`,
-- but this one will fire.
@[ext] theorem ext_of {X Y : Type u} [Ring X] [Ring Y] (f g : X →+* Y)
    (h : ∀ x, f x = g x) :
    @Eq (RingCat.of X ⟶ RingCat.of Y) f g :=
  RingHom.ext h

@[simp]
lemma RingEquiv_coe_eq {X Y : Type _} [Ring X] [Ring Y] (e : X ≃+* Y) :
    (@DFunLike.coe (RingCat.of X ⟶ RingCat.of Y) _ (fun _ => (forget RingCat).obj _)
      ConcreteCategory.instFunLike (e : X →+* Y) : X → Y) = ↑e :=
  rfl

instance hasForgetToSemiRingCat : HasForget₂ RingCat SemiRingCat :=
  BundledHom.forget₂ _ _
set_option linter.uppercaseLean3 false in
#align Ring.has_forget_to_SemiRing RingCat.hasForgetToSemiRingCat

instance hasForgetToAddCommGroupCat : HasForget₂ RingCat AddCommGroupCat where
  -- can't use BundledHom.mkHasForget₂, since AddCommGroup is an induced category
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

namespace CommSemiRingCat

instance : BundledHom.ParentProjection @CommSemiring.toSemiring :=
  ⟨⟩

-- Porting note: again, deriving fails for concrete category instances.
-- see https://github.com/leanprover-community/mathlib4/issues/5020
deriving instance LargeCategory for CommSemiRingCat

instance : ConcreteCategory CommSemiRingCat := by
  dsimp [CommSemiRingCat]
  infer_instance

instance : CoeSort CommSemiRingCat Type* where
  coe X := X.α

instance (X : CommSemiRingCat) : CommSemiring X := X.str

-- Porting note: Hinting to Lean that `forget R` and `R` are the same
unif_hint forget_obj_eq_coe (R : CommSemiRingCat) where ⊢
  (forget CommSemiRingCat).obj R ≟ R

instance instCommSemiring (X : CommSemiRingCat) : CommSemiring X := X.str

instance instCommSemiring' (X : CommSemiRingCat) : CommSemiring <| (forget CommSemiRingCat).obj X :=
  X.str

instance instFunLike {X Y : CommSemiRingCat} : FunLike (X ⟶ Y) X Y :=
  -- Note: this is apparently _not_ defeq to RingHom.instFunLike with reducible transparency
  ConcreteCategory.instFunLike

-- Porting note (#10754): added instance
instance instRingHomClass {X Y : CommSemiRingCat} : RingHomClass (X ⟶ Y) X Y :=
  RingHom.instRingHomClass

-- Porting note (#10756): added lemma
lemma coe_id {X : CommSemiRingCat} : (𝟙 X : X → X) = id := rfl

-- Porting note (#10756): added lemma
lemma coe_comp {X Y Z : CommSemiRingCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

-- porting note (#10756): added lemma
@[simp] lemma forget_map {X Y : CommSemiRingCat} (f : X ⟶ Y) :
  (forget CommSemiRingCat).map f = (f : X → Y) := rfl

lemma ext {X Y : CommSemiRingCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  RingHom.ext w

/-- Construct a bundled `CommSemiRingCat` from the underlying type and typeclass. -/
def of (R : Type u) [CommSemiring R] : CommSemiRingCat :=
  Bundled.of R
set_option linter.uppercaseLean3 false in
#align CommSemiRing.of CommSemiRingCat.of

/-- Typecheck a `RingHom` as a morphism in `CommSemiRingCat`. -/
def ofHom {R S : Type u} [CommSemiring R] [CommSemiring S] (f : R →+* S) : of R ⟶ of S :=
  f
set_option linter.uppercaseLean3 false in
#align CommSemiRing.of_hom CommSemiRingCat.ofHom

@[simp]
lemma RingEquiv_coe_eq {X Y : Type _} [CommSemiring X] [CommSemiring Y] (e : X ≃+* Y) :
    (@DFunLike.coe (CommSemiRingCat.of X ⟶ CommSemiRingCat.of Y) _
      (fun _ => (forget CommSemiRingCat).obj _)
      ConcreteCategory.instFunLike (e : X →+* Y) : X → Y) = ↑e :=
  rfl

-- Porting note: I think this is now redundant.
-- @[simp]
-- theorem ofHom_apply {R S : Type u} [CommSemiring R] [CommSemiring S] (f : R →+* S) (x : R) :
--     ofHom f x = f x :=
--   rfl
-- set_option linter.uppercaseLean3 false in
#noalign CommSemiRing.of_hom_apply

instance : Inhabited CommSemiRingCat :=
  ⟨of PUnit⟩

instance (R : CommSemiRingCat) : CommSemiring R :=
  R.str

@[simp]
theorem coe_of (R : Type u) [CommSemiring R] : (CommSemiRingCat.of R : Type u) = R :=
  rfl
set_option linter.uppercaseLean3 false in
#align CommSemiRing.coe_of CommSemiRingCat.coe_of

-- Coercing the identity morphism, as a ring homomorphism, gives the identity function.
@[simp] theorem coe_ringHom_id {X : CommSemiRingCat} :
    @DFunLike.coe (X →+* X) X (fun _ ↦ X) _ (𝟙 X) = id :=
  rfl

-- Coercing `𝟙 (of X)` to a function should be expressed as the coercion of `RingHom.id X`.
@[simp] theorem coe_id_of {X : Type u} [CommSemiring X] :
    @DFunLike.coe no_index (CommSemiRingCat.of X ⟶ CommSemiRingCat.of X) X
      (fun _ ↦ X) _
      (𝟙 (of X)) =
    @DFunLike.coe (X →+* X) X (fun _ ↦ X) _ (RingHom.id X) :=
  rfl

-- Coercing `f ≫ g`, where `f : of X ⟶ of Y` and `g : of Y ⟶ of Z`, to a function should be
-- expressed in terms of the coercion of `g.comp f`.
@[simp] theorem coe_comp_of {X Y Z : Type u} [CommSemiring X] [CommSemiring Y] [CommSemiring Z]
    (f : X →+* Y) (g : Y →+* Z) :
    @DFunLike.coe no_index (CommSemiRingCat.of X ⟶ CommSemiRingCat.of Z) X
      (fun _ ↦ Z) _
      (CategoryStruct.comp (X := CommSemiRingCat.of X) (Y := CommSemiRingCat.of Y)
        (Z := CommSemiRingCat.of Z) f g) =
    @DFunLike.coe (X →+* Z) X (fun _ ↦ Z) _ (RingHom.comp g f) :=
  rfl

-- Sometimes neither the `ext` lemma for `CommSemiRingCat` nor for `RingHom` is applicable,
-- because of incomplete unfolding of `CommSemiRingCat.of X ⟶ CommSemiRingCat.of Y := X →+* Y`,
-- but this one will fire.
@[ext] theorem ext_of {X Y : Type u} [CommSemiring X] [CommSemiring Y] (f g : X →+* Y)
    (h : ∀ x, f x = g x) :
    @Eq (CommSemiRingCat.of X ⟶ CommSemiRingCat.of Y) f g :=
  RingHom.ext h

instance hasForgetToSemiRingCat : HasForget₂ CommSemiRingCat SemiRingCat :=
  BundledHom.forget₂ _ _
set_option linter.uppercaseLean3 false in
#align CommSemiRing.has_forget_to_SemiRing CommSemiRingCat.hasForgetToSemiRingCat

/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
instance hasForgetToCommMonCat : HasForget₂ CommSemiRingCat CommMonCat :=
  HasForget₂.mk' (fun R : CommSemiRingCat => CommMonCat.of R) (fun R => rfl)
    -- Porting note: `(_ := _)` trick
    (fun {R₁ R₂} f => RingHom.toMonoidHom (α := R₁) (β := R₂) f) (by rfl)
set_option linter.uppercaseLean3 false in
#align CommSemiRing.has_forget_to_CommMon CommSemiRingCat.hasForgetToCommMonCat

/--
Ring equivalence are isomorphisms in category of commutative semirings
-/
@[simps]
def _root_.RingEquiv.toCommSemiRingCatIso {X Y : Type u} [CommSemiring X] [CommSemiring Y]
    (e : X ≃+* Y) : CommSemiRingCat.of X ≅ CommSemiRingCat.of Y where
  hom := e.toRingHom
  inv := e.symm.toRingHom

instance forgetReflectIsos : (forget CommSemiRingCat).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommSemiRingCat).map f)
    let ff : X →+* Y := f
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact ⟨e.toSemiRingCatIso.isIso_hom.1⟩

end CommSemiRingCat

/-- The category of commutative rings. -/
def CommRingCat : Type (u + 1) :=
  Bundled CommRing
set_option linter.uppercaseLean3 false in
#align CommRing CommRingCat

namespace CommRingCat

instance : BundledHom.ParentProjection @CommRing.toRing :=
  ⟨⟩

-- Porting note: deriving fails for concrete category.
-- see https://github.com/leanprover-community/mathlib4/issues/5020
deriving instance LargeCategory for CommRingCat

instance : ConcreteCategory CommRingCat := by
  dsimp [CommRingCat]
  infer_instance

instance : CoeSort CommRingCat Type* where
  coe X := X.α

-- Porting note: Hinting to Lean that `forget R` and `R` are the same
unif_hint forget_obj_eq_coe (R : CommRingCat) where ⊢
  (forget CommRingCat).obj R ≟ R

instance instCommRing (X : CommRingCat) : CommRing X := X.str

instance instCommRing' (X : CommRingCat) : CommRing <| (forget CommRingCat).obj X := X.str

instance instFunLike {X Y : CommRingCat} : FunLike (X ⟶ Y) X Y :=
  -- Note: this is apparently _not_ defeq to RingHom.instFunLike with reducible transparency
  ConcreteCategory.instFunLike

-- Porting note (#10754): added instance
instance instRingHomClass {X Y : CommRingCat} : RingHomClass (X ⟶ Y) X Y :=
  RingHom.instRingHomClass

-- Porting note (#10756): added lemma
lemma coe_id {X : CommRingCat} : (𝟙 X : X → X) = id := rfl

-- Porting note (#10756): added lemma
lemma coe_comp {X Y Z : CommRingCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

-- porting note (#10756): added lemma
@[simp] lemma forget_map {X Y : CommRingCat} (f : X ⟶ Y) :
    (forget CommRingCat).map f = (f : X → Y) := rfl

lemma ext {X Y : CommRingCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  RingHom.ext w

/-- Construct a bundled `CommRingCat` from the underlying type and typeclass. -/
def of (R : Type u) [CommRing R] : CommRingCat :=
  Bundled.of R
set_option linter.uppercaseLean3 false in
#align CommRing.of CommRingCat.of

instance instFunLike' {X : Type*} [CommRing X] {Y : CommRingCat} :
    FunLike (CommRingCat.of X ⟶ Y) X Y :=
  -- Note: this is apparently _not_ defeq to RingHom.instFunLike with reducible transparency
  ConcreteCategory.instFunLike

instance instFunLike'' {X : CommRingCat} {Y : Type*} [CommRing Y] :
    FunLike (X ⟶ CommRingCat.of Y) X Y :=
  -- Note: this is apparently _not_ defeq to RingHom.instFunLike with reducible transparency
  ConcreteCategory.instFunLike

instance instFunLike''' {X Y : Type _} [CommRing X] [CommRing Y] :
    FunLike (CommRingCat.of X ⟶ CommRingCat.of Y) X Y :=
  -- Note: this is apparently _not_ defeq to RingHom.instFunLike with reducible transparency
  ConcreteCategory.instFunLike

/-- Typecheck a `RingHom` as a morphism in `CommRingCat`. -/
def ofHom {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : of R ⟶ of S :=
  f
set_option linter.uppercaseLean3 false in
#align CommRing.of_hom CommRingCat.ofHom

@[simp]
lemma RingEquiv_coe_eq {X Y : Type _} [CommRing X] [CommRing Y] (e : X ≃+* Y) :
    (@DFunLike.coe (CommRingCat.of X ⟶ CommRingCat.of Y) _ (fun _ => (forget CommRingCat).obj _)
      ConcreteCategory.instFunLike (e : X →+* Y) : X → Y) = ↑e :=
  rfl

-- Porting note: I think this is now redundant.
-- @[simp]
-- theorem ofHom_apply {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (x : R) :
--     ofHom f x = f x :=
--   rfl
-- set_option linter.uppercaseLean3 false in
#noalign CommRing.of_hom_apply

instance : Inhabited CommRingCat :=
  ⟨of PUnit⟩

instance (R : CommRingCat) : CommRing R :=
  R.str

@[simp]
theorem coe_of (R : Type u) [CommRing R] : (CommRingCat.of R : Type u) = R :=
  rfl
set_option linter.uppercaseLean3 false in
#align CommRing.coe_of CommRingCat.coe_of

-- Coercing the identity morphism, as a ring homomorphism, gives the identity function.
@[simp] theorem coe_ringHom_id {X : CommRingCat} :
    @DFunLike.coe (X →+* X) X (fun _ ↦ X) _ (𝟙 X) = id :=
  rfl

-- Coercing `𝟙 (of X)` to a function should be expressed as the coercion of `RingHom.id X`.
@[simp] theorem coe_id_of {X : Type u} [CommRing X] :
    @DFunLike.coe no_index (CommRingCat.of X ⟶ CommRingCat.of X) X
      (fun _ ↦ X) _
      (𝟙 (of X)) =
    @DFunLike.coe (X →+* X) X (fun _ ↦ X) _ (RingHom.id X) :=
  rfl

-- Coercing `f ≫ g`, where `f : of X ⟶ of Y` and `g : of Y ⟶ of Z`, to a function should be
-- expressed in terms of the coercion of `g.comp f`.
@[simp] theorem coe_comp_of {X Y Z : Type u} [CommRing X] [CommRing Y] [CommRing Z]
    (f : X →+* Y) (g : Y →+* Z) :
    @DFunLike.coe no_index (CommRingCat.of X ⟶ CommRingCat.of Z) X
      (fun _ ↦ Z) _
      (CategoryStruct.comp (X := CommRingCat.of X) (Y := CommRingCat.of Y) (Z := CommRingCat.of Z)
        f g) =
    @DFunLike.coe (X →+* Z) X (fun _ ↦ Z) _ (RingHom.comp g f) :=
  rfl

-- Sometimes neither the `ext` lemma for `CommRingCat` nor for `RingHom` is applicable,
-- because of incomplete unfolding of `CommRingCat.of X ⟶ CommRingCat.of Y := X →+* Y`,
-- but this one will fire.
@[ext] theorem ext_of {X Y : Type u} [CommRing X] [CommRing Y] (f g : X →+* Y)
    (h : ∀ x, f x = g x) :
    @Eq (CommRingCat.of X ⟶ CommRingCat.of Y) f g :=
  RingHom.ext h

instance hasForgetToRingCat : HasForget₂ CommRingCat RingCat :=
  BundledHom.forget₂ _ _
set_option linter.uppercaseLean3 false in
#align CommRing.has_forget_to_Ring CommRingCat.hasForgetToRingCat

/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
instance hasForgetToCommSemiRingCat : HasForget₂ CommRingCat CommSemiRingCat :=
  HasForget₂.mk' (fun R : CommRingCat => CommSemiRingCat.of R) (fun R => rfl)
    (fun {R₁ R₂} f => f) (by rfl)
set_option linter.uppercaseLean3 false in
#align CommRing.has_forget_to_CommSemiRing CommRingCat.hasForgetToCommSemiRingCat

instance : (forget₂ CommRingCat CommSemiRingCat).Full where map_surjective f := ⟨f, rfl⟩

end CommRingCat

-- We verify that simp lemmas apply when coercing morphisms to functions.
example {R S : CommRingCat} (i : R ⟶ S) (r : R) (h : r = 0) : i r = 0 := by simp [h]

namespace RingEquiv

variable {X Y : Type u}

/-- Build an isomorphism in the category `RingCat` from a `RingEquiv` between `RingCat`s. -/
@[simps]
def toRingCatIso [Ring X] [Ring Y] (e : X ≃+* Y) : RingCat.of X ≅ RingCat.of Y where
  hom := e.toRingHom
  inv := e.symm.toRingHom
set_option linter.uppercaseLean3 false in
#align ring_equiv.to_Ring_iso RingEquiv.toRingCatIso

/-- Build an isomorphism in the category `CommRingCat` from a `RingEquiv` between `CommRingCat`s. -/
@[simps]
def toCommRingCatIso [CommRing X] [CommRing Y] (e : X ≃+* Y) :
    CommRingCat.of X ≅ CommRingCat.of Y where
  hom := e.toRingHom
  inv := e.symm.toRingHom
set_option linter.uppercaseLean3 false in
#align ring_equiv.to_CommRing_iso RingEquiv.toCommRingCatIso

end RingEquiv

namespace CategoryTheory.Iso

/-- Build a `RingEquiv` from an isomorphism in the category `RingCat`. -/
def ringCatIsoToRingEquiv {X Y : RingCat} (i : X ≅ Y) : X ≃+* Y :=
  RingEquiv.ofHomInv i.hom i.inv i.hom_inv_id i.inv_hom_id
set_option linter.uppercaseLean3 false in
#align category_theory.iso.Ring_iso_to_ring_equiv CategoryTheory.Iso.ringCatIsoToRingEquiv

/-- Build a `RingEquiv` from an isomorphism in the category `CommRingCat`. -/
def commRingCatIsoToRingEquiv {X Y : CommRingCat} (i : X ≅ Y) : X ≃+* Y :=
  RingEquiv.ofHomInv i.hom i.inv i.hom_inv_id i.inv_hom_id
set_option linter.uppercaseLean3 false in
#align category_theory.iso.CommRing_iso_to_ring_equiv CategoryTheory.Iso.commRingCatIsoToRingEquiv

-- Porting note: make this high priority to short circuit simplifier
@[simp (high)]
theorem commRingIsoToRingEquiv_toRingHom {X Y : CommRingCat} (i : X ≅ Y) :
    i.commRingCatIsoToRingEquiv.toRingHom = i.hom := by
  ext
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.iso.CommRing_iso_to_ring_equiv_to_ring_hom CategoryTheory.Iso.commRingIsoToRingEquiv_toRingHom

-- Porting note: make this high priority to short circuit simplifier
@[simp (high)]
theorem commRingIsoToRingEquiv_symm_toRingHom {X Y : CommRingCat} (i : X ≅ Y) :
    i.commRingCatIsoToRingEquiv.symm.toRingHom = i.inv := by
  ext
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.iso.CommRing_iso_to_ring_equiv_symm_to_ring_hom CategoryTheory.Iso.commRingIsoToRingEquiv_symm_toRingHom

end CategoryTheory.Iso

/-- Ring equivalences between `RingCat`s are the same as (isomorphic to) isomorphisms in
`RingCat`. -/
def ringEquivIsoRingIso {X Y : Type u} [Ring X] [Ring Y] :
    X ≃+* Y ≅ RingCat.of X ≅ RingCat.of Y where
  hom e := e.toRingCatIso
  inv i := i.ringCatIsoToRingEquiv
set_option linter.uppercaseLean3 false in
#align ring_equiv_iso_Ring_iso ringEquivIsoRingIso

/-- Ring equivalences between `CommRingCat`s are the same as (isomorphic to) isomorphisms
in `CommRingCat`. -/
def ringEquivIsoCommRingIso {X Y : Type u} [CommRing X] [CommRing Y] :
    X ≃+* Y ≅ CommRingCat.of X ≅ CommRingCat.of Y where
  hom e := e.toCommRingCatIso
  inv i := i.commRingCatIsoToRingEquiv
set_option linter.uppercaseLean3 false in
#align ring_equiv_iso_CommRing_iso ringEquivIsoCommRingIso

instance RingCat.forget_reflects_isos : (forget RingCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget RingCat).map f)
    let ff : X →+* Y := f
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact e.toRingCatIso.isIso_hom
set_option linter.uppercaseLean3 false in
#align Ring.forget_reflects_isos RingCat.forget_reflects_isos

instance CommRingCat.forget_reflects_isos : (forget CommRingCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommRingCat).map f)
    let ff : X →+* Y := f
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact e.toCommRingCatIso.isIso_hom
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

-- It would be nice if we could have the following,
-- but it requires making `reflectsIsomorphisms_forget₂` an instance,
-- which can cause typeclass loops:
-- Porting note: This was the case in mathlib3, perhaps it is different now?
attribute [local instance] reflectsIsomorphisms_forget₂

example : (forget₂ RingCat AddCommGroupCat).ReflectsIsomorphisms := by infer_instance

/-!
`@[simp]` lemmas for `RingHom.comp` and categorical identities.
-/

@[simp] theorem RingHom.comp_id_semiringCat
    {G : SemiRingCat.{u}} {H : Type u} [Semiring H] (f : G →+* H) : f.comp (𝟙 G) = f :=
  Category.id_comp (SemiRingCat.ofHom f)
@[simp] theorem RingHom.id_semiringCat_comp
    {G : Type u} [Semiring G] {H : SemiRingCat.{u}} (f : G →+* H) : RingHom.comp (𝟙 H) f = f :=
  Category.comp_id (SemiRingCat.ofHom f)

@[simp] theorem RingHom.comp_id_commSemiringCat
    {G : CommSemiRingCat.{u}} {H : Type u} [CommSemiring H] (f : G →+* H) : f.comp (𝟙 G) = f :=
  Category.id_comp (CommSemiRingCat.ofHom f)
@[simp] theorem RingHom.id_commSemiringCat_comp
    {G : Type u} [CommSemiring G] {H : CommSemiRingCat.{u}} (f : G →+* H) :
    RingHom.comp (𝟙 H) f = f :=
  Category.comp_id (CommSemiRingCat.ofHom f)

@[simp] theorem RingHom.comp_id_ringCat
    {G : RingCat.{u}} {H : Type u} [Ring H] (f : G →+* H) : f.comp (𝟙 G) = f :=
  Category.id_comp (RingCat.ofHom f)
@[simp] theorem RingHom.id_ringCat_comp
    {G : Type u} [Ring G] {H : RingCat.{u}} (f : G →+* H) : RingHom.comp (𝟙 H) f = f :=
  Category.comp_id (RingCat.ofHom f)

@[simp] theorem RingHom.comp_id_commRingCat
    {G : CommRingCat.{u}} {H : Type u} [CommRing H] (f : G →+* H) : f.comp (𝟙 G) = f :=
  Category.id_comp (CommRingCat.ofHom f)
@[simp] theorem RingHom.id_commRingCat_comp
    {G : Type u} [CommRing G] {H : CommRingCat.{u}} (f : G →+* H) : RingHom.comp (𝟙 H) f = f :=
  Category.comp_id (CommRingCat.ofHom f)
