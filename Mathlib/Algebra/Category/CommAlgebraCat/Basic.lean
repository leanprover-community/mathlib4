/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Category.AlgebraCat.Basic
import Mathlib.Algebra.Category.Ring.Basic

/-!
# The category of commutative algebras

This file mimics `Mathlib.LinearAlgebra.QuadraticForm.QuadraticModuleCat`.

-/

open CategoryTheory

universe v u w v' w'

variable (R : Type u) [CommRing R]

/-- The category of commutative `R`-algebras. -/
structure CommAlgebraCat extends Bundled CommRing.{v} where
  [isAlgebra : Algebra R α]

attribute [instance] CommAlgebraCat.isAlgebra

variable {R}

namespace CommAlgebraCat

open Algebra

instance : CoeSort (CommAlgebraCat.{v} R) (Type v) :=
  ⟨(·.α)⟩

@[simp] theorem CommRingCat_of_toCommRingCat (X : CommAlgebraCat.{v} R) :
    CommRingCat.of X.α = X.α :=
  rfl

variable (R)

/-- The object in the category of commutative `R`-algebras associated to a
commutative `R`-algebra. -/
@[simps]
def of (X : Type v) [CommRing X] [Algebra R X] :
    CommAlgebraCat R where
  isAlgebra := (inferInstance : Algebra R X)

variable {R}

/-- A type alias for `AlgHom` to avoid confusion between the categorical and
algebraic spellings of composition. -/
@[ext]
structure Hom (V W : CommAlgebraCat.{v} R) :=
  /-- The underlying `AlgHom` -/
  toAlgHom : V →ₐ[R] W

lemma Hom.toAlgHom_injective (V W : CommAlgebraCat.{v} R) :
    Function.Injective (Hom.toAlgHom : Hom V W → _) :=
  fun ⟨f⟩ ⟨g⟩ _ => by congr

instance category : Category (CommAlgebraCat.{v} R) where
  Hom M N := Hom M N
  id M := ⟨AlgHom.id R M⟩
  comp f g := ⟨AlgHom.comp g.toAlgHom f.toAlgHom⟩

-- TODO: if `Quiver.Hom` and the instance above were `reducible`, this wouldn't be needed.
@[ext]
lemma hom_ext {M N : CommAlgebraCat.{v} R} (f g : M ⟶ N) (h : f.toAlgHom = g.toAlgHom) :
    f = g :=
  Hom.ext _ _ h

/-- Typecheck a `AlgHom` as a morphism in `CommAlgebraCat R`. -/
abbrev ofHom {X Y : Type v} [CommRing X] [Algebra R X] [CommRing Y] [Algebra R Y]
    (f : X →ₐ[R] Y) : of R X ⟶ of R Y :=
  ⟨f⟩

@[simp] theorem toAlgHom_comp {M N U : CommAlgebraCat.{v} R} (f : M ⟶ N) (g : N ⟶ U) :
    (f ≫ g).toAlgHom = g.toAlgHom.comp f.toAlgHom :=
  rfl

@[simp] theorem toAlgHom_id {M : CommAlgebraCat.{v} R} :
    Hom.toAlgHom (𝟙 M) = AlgHom.id _ _ :=
  rfl

instance concreteCategory : ConcreteCategory.{v} (CommAlgebraCat.{v} R) where
  forget :=
    { obj := fun M => M
      map := fun f => f.toAlgHom }
  forget_faithful :=
    { map_injective := fun {M N} f g h => hom_ext _ _ <| DFunLike.coe_injective h }

instance hasForgetToAlgebra : HasForget₂ (CommAlgebraCat R) (AlgebraCat R) where
  forget₂ :=
    { obj := fun M => AlgebraCat.of R M
      map := fun f => f.toAlgHom }

@[simp]
theorem forget₂_algebra_obj (X : CommAlgebraCat R) :
    (forget₂ (CommAlgebraCat R) (AlgebraCat R)).obj X = AlgebraCat.of R X :=
  rfl

@[simp]
theorem forget₂_algebra_map (X Y : CommAlgebraCat R) (f : X ⟶ Y) :
    (forget₂ (CommAlgebraCat R) (AlgebraCat R)).map f = f.toAlgHom :=
  rfl

instance hasForgetToCommRing : HasForget₂ (CommAlgebraCat R) CommRingCat where
  forget₂ :=
    { obj := fun A => CommRingCat.of A
      map := fun {A B} f => (f.toAlgHom : A →+* B) }

@[simp]
theorem forget₂_commRing_obj (X : CommAlgebraCat R) :
    (forget₂ (CommAlgebraCat R) CommRingCat).obj X = CommRingCat.of X :=
  rfl

@[simp]
theorem forget₂_commRing_map (X Y : CommAlgebraCat R) (f : X ⟶ Y) :
    (forget₂ (CommAlgebraCat R) CommRingCat).map f = (f.toAlgHom : X →+* Y) :=
  rfl

end CommAlgebraCat

namespace AlgEquiv

open CommAlgebraCat

variable {X Y Z : Type v}
variable [CommRing X] [Algebra R X] [CommRing Y] [Algebra R Y] [CommRing Z] [Algebra R Z]

/-- Build an isomorphism in the category `CommAlgebraCat R` from a
`AlgEquiv`. -/
@[simps]
def toCommAlgebraIso (e : X ≃ₐ[R] Y) : CommAlgebraCat.of R X ≅ CommAlgebraCat.of R Y where
  hom := CommAlgebraCat.ofHom e
  inv := CommAlgebraCat.ofHom e.symm

@[simp] theorem toCommAlgebraIso_refl :
    toCommAlgebraIso (AlgEquiv.refl (R := R) (A₁ := X)) = .refl _ :=
  rfl

@[simp] theorem toCommAlgebraIso_symm (e : X ≃ₐ[R] Y) :
    toCommAlgebraIso e.symm = (toCommAlgebraIso e).symm :=
  rfl

@[simp] theorem toCommAlgebraIso_trans (e : X ≃ₐ[R] Y) (f : Y ≃ₐ[R] Z) :
    toCommAlgebraIso (e.trans f) = toCommAlgebraIso e ≪≫ toCommAlgebraIso f :=
  rfl

end AlgEquiv

namespace CategoryTheory.Iso

open Algebra

variable {X Y Z : CommAlgebraCat.{v} R}

/-- Build a `AlgEquiv` from an isomorphism in the category
`CommAlgebraCat R`. -/
def toCommAlgEquiv (i : X ≅ Y) : X ≃ₐ[R] Y :=
  { i.hom.toAlgHom with
    invFun := i.inv.toAlgHom
    left_inv := fun x => AlgHom.congr_fun (congr_arg CommAlgebraCat.Hom.toAlgHom i.3) x
    right_inv := fun x => AlgHom.congr_fun (congr_arg CommAlgebraCat.Hom.toAlgHom i.4) x }

@[simp] theorem toCommAlgEquiv_toAlgHom (i : X ≅ Y) :
    i.toCommAlgEquiv = i.hom.toAlgHom := rfl

@[simp] theorem toCommAlgEquiv_refl : toCommAlgEquiv (.refl X) = .refl :=
  rfl

@[simp] theorem toCommAlgEquiv_symm (e : X ≅ Y) :
    toCommAlgEquiv e.symm = (toCommAlgEquiv e).symm :=
  rfl

@[simp] theorem toCommAlgEquiv_trans (e : X ≅ Y) (f : Y ≅ Z) :
    toCommAlgEquiv (e ≪≫ f) = e.toCommAlgEquiv.trans f.toCommAlgEquiv :=
  rfl

end CategoryTheory.Iso
