/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Category instance for algebras over a commutative ring

We introduce the bundled category `AlgCat` of algebras over a fixed commutative ring `R` along
with the forgetful functors to `RingCat` and `ModuleCat`. We furthermore show that the functor
associating to a type the free `R`-algebra on that type is left adjoint to the forgetful functor.
-/

open CategoryTheory Limits

universe v u

variable (R : Type u) [CommRing R]

/-- The category of R-algebras and their morphisms. -/
structure AlgCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type v
  [isRing : Ring carrier]
  [isAlgebra : Algebra R carrier]

attribute [instance] AlgCat.isRing AlgCat.isAlgebra

initialize_simps_projections AlgCat (-isRing, -isAlgebra)

namespace AlgCat

instance : CoeSort (AlgCat R) (Type v) :=
  ⟨AlgCat.carrier⟩

attribute [coe] AlgCat.carrier

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. This is the preferred way to construct a term of `AlgCat R`. -/
abbrev of (X : Type v) [Ring X] [Algebra R X] : AlgCat.{v} R :=
  ⟨X⟩

lemma coe_of (X : Type v) [Ring X] [Algebra R X] : (of R X : Type v) = X :=
  rfl

variable {R} in
/-- The type of morphisms in `AlgCat R`. -/
@[ext]
structure Hom (A B : AlgCat.{v} R) where
  private mk ::
  /-- The underlying algebra map. -/
  hom' : A →ₐ[R] B

instance : Category (AlgCat.{v} R) where
  Hom A B := Hom A B
  id A := ⟨AlgHom.id R A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory (AlgCat.{v} R) (· →ₐ[R] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

variable {R} in
/-- Turn a morphism in `AlgCat` back into an `AlgHom`. -/
abbrev Hom.hom {A B : AlgCat.{v} R} (f : Hom A B) :=
  ConcreteCategory.hom (C := AlgCat R) f

variable {R} in
/-- Typecheck an `AlgHom` as a morphism in `AlgCat`. -/
abbrev ofHom {A B : Type v} [Ring A] [Ring B] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    of R A ⟶ of R B :=
  ConcreteCategory.ofHom (C := AlgCat R) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (A B : AlgCat.{v} R) (f : Hom A B) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
lemma hom_id {A : AlgCat.{v} R} : (𝟙 A : A ⟶ A).hom = AlgHom.id R A := rfl

/- Provided for rewriting. -/
lemma id_apply (A : AlgCat.{v} R) (a : A) :
    (𝟙 A : A ⟶ A) a = a := by simp

@[simp]
lemma hom_comp {A B C : AlgCat.{v} R} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply {A B C : AlgCat.{v} R} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
    (f ≫ g) a = g (f a) := by simp

@[ext]
lemma hom_ext {A B : AlgCat.{v} R} {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
lemma hom_ofHom {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [Algebra R X] [Ring Y]
    [Algebra R Y] (f : X →ₐ[R] Y) : (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom {A B : AlgCat.{v} R} (f : A ⟶ B) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {X : Type v} [Ring X] [Algebra R X] : ofHom (AlgHom.id R X) = 𝟙 (of R X) := rfl

@[simp]
lemma ofHom_comp {X Y Z : Type v} [Ring X] [Ring Y] [Ring Z] [Algebra R X] [Algebra R Y]
    [Algebra R Z] (f : X →ₐ[R] Y) (g : Y →ₐ[R] Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [Algebra R X] [Ring Y]
    [Algebra R Y] (f : X →ₐ[R] Y) (x : X) : ofHom f x = f x := rfl

lemma inv_hom_apply {A B : AlgCat.{v} R} (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by
  rw [← comp_apply]
  simp

lemma hom_inv_apply {A B : AlgCat.{v} R} (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by
  rw [← comp_apply]
  simp

instance : Inhabited (AlgCat R) :=
  ⟨of R R⟩

lemma forget_obj {A : AlgCat.{v} R} : (forget (AlgCat.{v} R)).obj A = A := rfl

lemma forget_map {A B : AlgCat.{v} R} (f : A ⟶ B) :
    (forget (AlgCat.{v} R)).map f = f :=
  rfl

instance {S : AlgCat.{v} R} : Ring ((forget (AlgCat R)).obj S) :=
  (inferInstance : Ring S.carrier)

instance {S : AlgCat.{v} R} : Algebra R ((forget (AlgCat R)).obj S) :=
  (inferInstance : Algebra R S.carrier)

instance hasForgetToRing : HasForget₂ (AlgCat.{v} R) RingCat.{v} where
  forget₂ :=
    { obj := fun A => RingCat.of A
      map := fun f => RingCat.ofHom f.hom.toRingHom }

instance hasForgetToModule : HasForget₂ (AlgCat.{v} R) (ModuleCat.{v} R) where
  forget₂ :=
    { obj := fun M => ModuleCat.of R M
      map := fun f => ModuleCat.ofHom f.hom.toLinearMap }

@[simp]
lemma forget₂_module_obj (X : AlgCat.{v} R) :
    (forget₂ (AlgCat.{v} R) (ModuleCat.{v} R)).obj X = ModuleCat.of R X :=
  rfl

@[simp]
lemma forget₂_module_map {X Y : AlgCat.{v} R} (f : X ⟶ Y) :
    (forget₂ (AlgCat.{v} R) (ModuleCat.{v} R)).map f = ModuleCat.ofHom f.hom.toLinearMap :=
  rfl

variable {R} in
/-- Forgetting to the underlying type and then building the bundled object returns the original
algebra. -/
@[deprecated Iso.refl (since := "2025-05-15")]
def ofSelfIso (M : AlgCat.{v} R) : AlgCat.of R M ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M

/-- The "free algebra" functor, sending a type `S` to the free algebra on `S`. -/
@[simps! obj map]
def free : Type u ⥤ AlgCat.{u} R where
  obj S := of R (FreeAlgebra R S)
  map f := ofHom <| FreeAlgebra.lift _ <| FreeAlgebra.ι _ ∘ f

/-- The free/forget adjunction for `R`-algebras. -/
def adj : free.{u} R ⊣ forget (AlgCat.{u} R) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := fun f ↦ (FreeAlgebra.lift _).symm f.hom
          invFun := fun f ↦ ofHom <| (FreeAlgebra.lift _) f
          left_inv := fun f ↦ by aesop
          right_inv := fun f ↦ by simp [forget_obj] } }

instance : (forget (AlgCat.{u} R)).IsRightAdjoint := (adj R).isRightAdjoint

end AlgCat

variable {R}
variable {X₁ X₂ : Type u}

/-- Build an isomorphism in the category `AlgCat R` from a `AlgEquiv` between `Algebra`s. -/
@[simps]
def AlgEquiv.toAlgebraIso {g₁ : Ring X₁} {g₂ : Ring X₂} {m₁ : Algebra R X₁} {m₂ : Algebra R X₂}
    (e : X₁ ≃ₐ[R] X₂) : AlgCat.of R X₁ ≅ AlgCat.of R X₂ where
  hom := AlgCat.ofHom (e : X₁ →ₐ[R] X₂)
  inv := AlgCat.ofHom (e.symm : X₂ →ₐ[R] X₁)

namespace CategoryTheory.Iso

/-- Build a `AlgEquiv` from an isomorphism in the category `AlgCat R`. -/
@[simps]
def toAlgEquiv {X Y : AlgCat R} (i : X ≅ Y) : X ≃ₐ[R] Y :=
  { i.hom.hom with
    toFun := i.hom
    invFun := i.inv
    left_inv := fun x ↦ by simp
    right_inv := fun x ↦ by simp }

end CategoryTheory.Iso

/-- Algebra equivalences between `Algebra`s are the same as (isomorphic to) isomorphisms in
`AlgCat`. -/
@[simps]
def algEquivIsoAlgebraIso {X Y : Type u} [Ring X] [Ring Y] [Algebra R X] [Algebra R Y] :
    (X ≃ₐ[R] Y) ≅ AlgCat.of R X ≅ AlgCat.of R Y where
  hom e := e.toAlgebraIso
  inv i := i.toAlgEquiv

instance AlgCat.forget_reflects_isos : (forget (AlgCat.{u} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (AlgCat.{u} R)).map f)
    let e : X ≃ₐ[R] Y := { f.hom, i.toEquiv with }
    exact e.toAlgebraIso.isIso_hom
