/-
Copyright (c) 2025 Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang
-/
import Mathlib.Algebra.Category.AlgebraCat.Basic
import Mathlib.Algebra.Category.Ring.Under.Basic

/-!
# The category of commutative algebras over a commutative ring

This file defines the bundled category `CommAlg` of commutative algebras over a fixed commutative
ring `R` along with the forgetful functors to `RingCat` and `AlgebraCat`.
-/

namespace CategoryTheory

open Limits

universe v u

variable {R : Type u} [CommRing R]

variable (R) in
/-- The category of R-algebras and their morphisms. -/
structure CommAlg where
  private mk ::
  /-- The underlying type. -/
  carrier : Type v
  [commRing : CommRing carrier]
  [algebra : Algebra R carrier]

namespace CommAlg
variable {A B C : CommAlg.{v} R} {X Y Z : Type v} [CommRing X] [Algebra R X]
  [CommRing Y] [Algebra R Y] [CommRing Z] [Algebra R Z]

attribute [instance] commRing algebra

initialize_simps_projections CommAlg (-commRing, -algebra)

instance : CoeSort (CommAlg R) (Type v) := ⟨carrier⟩

attribute [coe] carrier

variable (R) in
/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. This is the preferred way to construct a term of `CommAlg R`. -/
abbrev of (X : Type v) [CommRing X] [Algebra R X] : CommAlg.{v} R := ⟨X⟩

variable (R) in
lemma coe_of (X : Type v) [CommRing X] [Algebra R X] : (of R X : Type v) = X := rfl

/-- The type of morphisms in `CommAlg R`. -/
@[ext]
structure Hom (A B : CommAlg.{v} R) where
  private mk ::
  /-- The underlying algebra map. -/
  hom' : A →ₐ[R] B

instance : Category (CommAlg.{v} R) where
  Hom A B := Hom A B
  id A := ⟨AlgHom.id R A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory (CommAlg.{v} R) (· →ₐ[R] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `CommAlg` back into an `AlgHom`. -/
abbrev Hom.hom (f : Hom A B) := ConcreteCategory.hom (C := CommAlg R) f

/-- Typecheck an `AlgHom` as a morphism in `CommAlg`. -/
abbrev ofHom (f : X →ₐ[R] Y) : of R X ⟶ of R Y := ConcreteCategory.ofHom (C := CommAlg R) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (A B : CommAlg.{v} R) (f : Hom A B) := f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp] lemma hom_id : (𝟙 A : A ⟶ A).hom = AlgHom.id R A := rfl

/- Provided for rewriting. -/
lemma id_apply (A : CommAlg.{v} R) (a : A) : (𝟙 A : A ⟶ A) a = a := by simp

@[simp] lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := by simp

@[ext] lemma hom_ext {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g := Hom.ext hf

@[simp] lemma hom_ofHom (f : X →ₐ[R] Y) : (ofHom f).hom = f := rfl
@[simp] lemma ofHom_hom (f : A ⟶ B) : ofHom f.hom = f := rfl

@[simp] lemma ofHom_id : ofHom (.id R X) = 𝟙 (of R X) := rfl

@[simp]
lemma ofHom_comp (f : X →ₐ[R] Y) (g : Y →ₐ[R] Z) : ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

lemma ofHom_apply (f : X →ₐ[R] Y) (x : X) : ofHom f x = f x := rfl

lemma inv_hom_apply (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by simp [← comp_apply]
lemma hom_inv_apply (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by simp [← comp_apply]

instance : Inhabited (CommAlg R) := ⟨of R R⟩

lemma forget_obj (A : CommAlg.{v} R) : (forget (CommAlg.{v} R)).obj A = A := rfl

lemma forget_map (f : A ⟶ B) : (forget (CommAlg.{v} R)).map f = f := rfl

instance : Ring ((forget (CommAlg R)).obj A) := inferInstanceAs <| Ring A

instance : Algebra R ((forget (CommAlg R)).obj A) := inferInstanceAs <| Algebra R A

instance hasForgetToCommRing : HasForget₂ (CommAlg.{v} R) CommRingCat.{v} where
  forget₂.obj A := .of A
  forget₂.map f := CommRingCat.ofHom f.hom.toRingHom

instance hasForgetToAlg : HasForget₂ (CommAlg.{v} R) (AlgebraCat.{v} R) where
  forget₂.obj A := .of R A
  forget₂.map f := AlgebraCat.ofHom f.hom

@[simp] lemma forget₂_commAlg_obj (A : CommAlg.{v} R) :
    (forget₂ (CommAlg.{v} R) (AlgebraCat.{v} R)).obj A = .of R A := rfl

@[simp] lemma forget₂_commAlg_map (f : A ⟶ B) :
    (forget₂ (CommAlg.{v} R) (AlgebraCat.{v} R)).map f = AlgebraCat.ofHom f.hom := rfl

/-- Forgetting to the underlying type and then building the bundled object returns the original
algebra. -/
@[simps]
def ofSelfIso (A : CommAlg.{v} R) : of R A ≅ A where
  hom := 𝟙 A
  inv := 𝟙 A

/-- Build an isomorphism in the category `CommAlg R` from a `AlgEquiv` between `Algebra`s. -/
@[simps]
def isoMk {X Y : Type v} {_ : CommRing X} {_ : CommRing Y} {_ : Algebra R X} {_ : Algebra R Y}
    (e : X ≃ₐ[R] Y) : of R X ≅ of R Y where
  hom := ofHom (e : X →ₐ[R] Y)
  inv := ofHom (e.symm : Y →ₐ[R] X)

/-- Build a `AlgEquiv` from an isomorphism in the category `CommAlg R`. -/
@[simps]
def ofIso (i : A ≅ B) : A ≃ₐ[R] B where
  __ := i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp

/-- Algebra equivalences between `Algebra`s are the same as (isomorphic to) isomorphisms in
`CommAlg`. -/
@[simps]
def isoEquivalgEquiv : (of R X ≅ of R Y) ≅ (X ≃ₐ[R] Y) where
  hom := ofIso
  inv := isoMk

instance reflectsIsomorphisms_forget_commAlg : (forget (CommAlg.{u} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (CommAlg.{u} R)).map f)
    let e : X ≃ₐ[R] Y := { f.hom, i.toEquiv with }
    exact (isoMk e).isIso_hom

end CommAlg

/-- The category of commutative algebras over a commutative ring `R` is the same as rings under `R`.
-/
@[simps]
def commAlgEquivUnder (R : CommRingCat) : CommAlg R ≌ Under R where
  functor.obj A := R.mkUnder A
  functor.map {A B} f := f.hom.toUnder
  inverse.obj A := .of _ A
  inverse.map {A B} f := CommAlg.ofHom <| CommRingCat.toAlgHom f
  unitIso := NatIso.ofComponents fun A ↦
    CommAlg.isoMk { toRingEquiv := .refl A, commutes' _ := rfl }
  counitIso := .refl _

end CategoryTheory
