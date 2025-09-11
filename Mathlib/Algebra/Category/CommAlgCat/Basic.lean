/-
Copyright (c) 2025 Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang
-/
import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.WithTerminal.Cone

/-!
# The category of commutative algebras over a commutative ring

This file defines the bundled category `CommAlgCat` of commutative algebras over a fixed commutative
ring `R` along with the forgetful functors to `CommRingCat` and `AlgCat`.
-/

open CategoryTheory Limits

universe w v u

variable {R : Type u} [CommRing R]

variable (R) in
/-- The category of R-algebras and their morphisms. -/
structure CommAlgCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type v
  [commRing : CommRing carrier]
  [algebra : Algebra R carrier]

namespace CommAlgCat
variable {A B C : CommAlgCat.{v} R} {X Y Z : Type v} [CommRing X] [Algebra R X]
  [CommRing Y] [Algebra R Y] [CommRing Z] [Algebra R Z]

attribute [instance] commRing algebra

initialize_simps_projections CommAlgCat (-commRing, -algebra)

instance : CoeSort (CommAlgCat R) (Type v) := ⟨carrier⟩

attribute [coe] carrier

variable (R) in
/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. This is the preferred way to construct a term of `CommAlgCat R`. -/
abbrev of (X : Type v) [CommRing X] [Algebra R X] : CommAlgCat.{v} R := ⟨X⟩

variable (R) in
lemma coe_of (X : Type v) [CommRing X] [Algebra R X] : (of R X : Type v) = X := rfl

/-- The type of morphisms in `CommAlgCat R`. -/
@[ext]
structure Hom (A B : CommAlgCat.{v} R) where
  private mk ::
  /-- The underlying algebra map. -/
  hom' : A →ₐ[R] B

instance : Category (CommAlgCat.{v} R) where
  Hom A B := Hom A B
  id A := ⟨AlgHom.id R A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory (CommAlgCat.{v} R) (· →ₐ[R] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `CommAlgCat` back into an `AlgHom`. -/
abbrev Hom.hom (f : Hom A B) := ConcreteCategory.hom (C := CommAlgCat R) f

/-- Typecheck an `AlgHom` as a morphism in `CommAlgCat`. -/
abbrev ofHom (f : X →ₐ[R] Y) : of R X ⟶ of R Y := ConcreteCategory.ofHom (C := CommAlgCat R) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (A B : CommAlgCat.{v} R) (f : Hom A B) := f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp] lemma hom_id : (𝟙 A : A ⟶ A).hom = AlgHom.id R A := rfl

/- Provided for rewriting. -/
lemma id_apply (A : CommAlgCat.{v} R) (a : A) : (𝟙 A : A ⟶ A) a = a := by simp

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

lemma inv_hom_apply (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by simp
lemma hom_inv_apply (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by simp

instance : Inhabited (CommAlgCat R) := ⟨of R R⟩

lemma forget_obj (A : CommAlgCat.{v} R) : (forget (CommAlgCat.{v} R)).obj A = A := rfl

lemma forget_map (f : A ⟶ B) : (forget (CommAlgCat.{v} R)).map f = f := rfl

instance : CommRing ((forget (CommAlgCat R)).obj A) := inferInstanceAs <| CommRing A

instance : Algebra R ((forget (CommAlgCat R)).obj A) := inferInstanceAs <| Algebra R A

instance hasForgetToCommRingCat : HasForget₂ (CommAlgCat.{v} R) CommRingCat.{v} where
  forget₂.obj A := .of A
  forget₂.map f := CommRingCat.ofHom f.hom.toRingHom

instance hasForgetToAlgCat : HasForget₂ (CommAlgCat.{v} R) (AlgCat.{v} R) where
  forget₂.obj A := .of R A
  forget₂.map f := AlgCat.ofHom f.hom

@[simp] lemma forget₂_commRingCat_obj (A : CommAlgCat.{v} R) :
    (forget₂ (CommAlgCat.{v} R) CommRingCat.{v}).obj A = .of A := rfl

@[simp] lemma forget₂_commRingCat_map (f : A ⟶ B) :
    (forget₂ (CommAlgCat.{v} R) CommRingCat.{v}).map f = CommRingCat.ofHom f.hom := rfl

@[simp] lemma forget₂_algCat_obj (A : CommAlgCat.{v} R) :
    (forget₂ (CommAlgCat.{v} R) (AlgCat.{v} R)).obj A = .of R A := rfl

@[simp] lemma forget₂_algCat_map (f : A ⟶ B) :
    (forget₂ (CommAlgCat.{v} R) (AlgCat.{v} R)).map f = AlgCat.ofHom f.hom := rfl

/-- Build an isomorphism in the category `CommAlgCat R` from an `AlgEquiv` between commutative
`Algebra`s. -/
@[simps]
def isoMk {X Y : Type v} {_ : CommRing X} {_ : CommRing Y} {_ : Algebra R X} {_ : Algebra R Y}
    (e : X ≃ₐ[R] Y) : of R X ≅ of R Y where
  hom := ofHom (e : X →ₐ[R] Y)
  inv := ofHom (e.symm : Y →ₐ[R] X)

/-- Build an `AlgEquiv` from an isomorphism in the category `CommAlgCat R`. -/
@[simps]
def ofIso (i : A ≅ B) : A ≃ₐ[R] B where
  __ := i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp

/-- Algebra equivalences between `Algebra`s are the same as isomorphisms in `CommAlgCat`. -/
@[simps]
def isoEquivAlgEquiv : (of R X ≅ of R Y) ≃ (X ≃ₐ[R] Y) where
  toFun := ofIso
  invFun := isoMk

instance reflectsIsomorphisms_forget : (forget (CommAlgCat.{u} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (CommAlgCat.{u} R)).map f)
    let e : X ≃ₐ[R] Y := { f.hom, i.toEquiv with }
    exact (isoMk e).isIso_hom

variable (R)

/-- Universe lift functor for commutative algebras. -/
def uliftFunctor : CommAlgCat.{v} R ⥤ CommAlgCat.{max v w} R where
  obj A := .of R <| ULift A
  map {A B} f := CommAlgCat.ofHom <|
    ULift.algEquiv.symm.toAlgHom.comp <| f.hom.comp ULift.algEquiv.toAlgHom

/-- The universe lift functor for commutative algebras is fully faithful. -/
def fullyFaithfulUliftFunctor : (uliftFunctor R).FullyFaithful where
  preimage {A B} f :=
    CommAlgCat.ofHom <| ULift.algEquiv.toAlgHom.comp <| f.hom.comp ULift.algEquiv.symm.toAlgHom

instance : (uliftFunctor R).Full :=
  (fullyFaithfulUliftFunctor R).full

instance : (uliftFunctor R).Faithful :=
  (fullyFaithfulUliftFunctor R).faithful

end CommAlgCat

/-- The category of commutative algebras over a commutative ring `R` is the same as commutative
rings under `R`. -/
@[simps]
def commAlgCatEquivUnder (R : CommRingCat) : CommAlgCat R ≌ Under R where
  functor.obj A := R.mkUnder A
  functor.map {A B} f := f.hom.toUnder
  inverse.obj A := .of _ A
  inverse.map {A B} f := CommAlgCat.ofHom <| CommRingCat.toAlgHom f
  unitIso := NatIso.ofComponents fun A ↦
    CommAlgCat.isoMk { toRingEquiv := .refl A, commutes' _ := rfl }
  counitIso := .refl _

-- TODO: Generalize to `UnivLE.{u, v}` once `commAlgCatEquivUnder` is generalized.
instance : HasColimits (CommAlgCat.{u} R) :=
  Adjunction.has_colimits_of_equivalence (commAlgCatEquivUnder (.of R)).functor

-- TODO: Generalize to `UnivLE.{u, v}` once `commAlgCatEquivUnder` is generalized.
instance : HasLimits (CommAlgCat.{u} R) :=
  Adjunction.has_limits_of_equivalence (commAlgCatEquivUnder (.of R)).functor
