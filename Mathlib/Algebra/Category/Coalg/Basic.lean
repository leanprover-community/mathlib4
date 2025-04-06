/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.Coalgebra.Equiv

/-!
# The category of coalgebras over a commutative ring

We introduce the bundled category `Coalg` of coalgebras over a fixed commutative ring `R`
along with the forgetful functor to `ModuleCat`.

This file mimics `Mathlib.LinearAlgebra.QuadraticForm.QuadraticModuleCat`.

-/

open CategoryTheory

universe v u

variable (R : Type u) [CommRing R]

/-- The category of `R`-coalgebras. -/
structure Coalg extends ModuleCat.{v} R where
  instCoalgebra : Coalgebra R carrier

attribute [instance] Coalg.instCoalgebra

variable {R}

namespace Coalg

open Coalgebra

instance : CoeSort (Coalg.{v} R) (Type v) :=
  ⟨(·.carrier)⟩

@[simp] theorem moduleCat_of_toModuleCat (X : Coalg.{v} R) :
    ModuleCat.of R X.toModuleCat = X.toModuleCat :=
  rfl

variable (R) in
/-- The object in the category of `R`-coalgebras associated to an `R`-coalgebra. -/
abbrev of (X : Type v) [AddCommGroup X] [Module R X] [Coalgebra R X] :
    Coalg R :=
  { ModuleCat.of R X with
    instCoalgebra := (inferInstance : Coalgebra R X) }

@[simp]
lemma of_comul {X : Type v} [AddCommGroup X] [Module R X] [Coalgebra R X] :
    Coalgebra.comul (A := of R X) = Coalgebra.comul (R := R) (A := X) := rfl

@[simp]
lemma of_counit {X : Type v} [AddCommGroup X] [Module R X] [Coalgebra R X] :
    Coalgebra.counit (A := of R X) = Coalgebra.counit (R := R) (A := X) := rfl

/-- A type alias for `CoalgHom` to avoid confusion between the categorical and
algebraic spellings of composition. -/
@[ext]
structure Hom (V W : Coalg.{v} R) where
  /-- The underlying `CoalgHom` -/
  toCoalgHom' : V →ₗc[R] W

instance category : Category (Coalg.{v} R) where
  Hom M N := Hom M N
  id M := ⟨CoalgHom.id R M⟩
  comp f g := ⟨CoalgHom.comp g.toCoalgHom' f.toCoalgHom'⟩

instance concreteCategory : ConcreteCategory (Coalg.{v} R) (· →ₗc[R] ·) where
  hom f := f.toCoalgHom'
  ofHom f := ⟨f⟩

/-- Turn a morphism in `Coalg` back into a `CoalgHom`. -/
abbrev Hom.toCoalgHom {X Y : Coalg.{v} R} (f : Hom X Y) : X →ₗc[R] Y :=
  ConcreteCategory.hom (C := Coalg.{v} R) f

/-- Typecheck a `CoalgHom` as a morphism in `Coalg R`. -/
abbrev ofHom {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [Coalgebra R X] [Coalgebra R Y] (f : X →ₗc[R] Y) :
    of R X ⟶ of R Y :=
  ConcreteCategory.ofHom f

lemma Hom.toCoalgHom_injective (V W : Coalg.{v} R) :
    Function.Injective (Hom.toCoalgHom' : Hom V W → _) :=
  fun ⟨f⟩ ⟨g⟩ _ => by congr

@[ext]
lemma hom_ext {M N : Coalg.{v} R} (f g : M ⟶ N) (h : f.toCoalgHom = g.toCoalgHom) :
    f = g :=
  Hom.ext h

@[simp] theorem toCoalgHom_comp {M N U : Coalg.{v} R} (f : M ⟶ N) (g : N ⟶ U) :
    (f ≫ g).toCoalgHom = g.toCoalgHom.comp f.toCoalgHom :=
  rfl

@[simp] theorem toCoalgHom_id {M : Coalg.{v} R} :
    Hom.toCoalgHom (𝟙 M) = CoalgHom.id _ _ :=
  rfl

instance hasForgetToModule : HasForget₂ (Coalg R) (ModuleCat R) where
  forget₂ :=
    { obj := fun M => ModuleCat.of R M
      map := fun f => ModuleCat.ofHom f.toCoalgHom.toLinearMap }

@[simp]
theorem forget₂_obj (X : Coalg R) :
    (forget₂ (Coalg R) (ModuleCat R)).obj X = ModuleCat.of R X :=
  rfl

@[simp]
theorem forget₂_map (X Y : Coalg R) (f : X ⟶ Y) :
    (forget₂ (Coalg R) (ModuleCat R)).map f = ModuleCat.ofHom (f.toCoalgHom : X →ₗ[R] Y) :=
  rfl

end Coalg

namespace CoalgEquiv

open Coalg

variable {X Y Z : Type v}
variable [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]
variable [Coalgebra R X] [Coalgebra R Y] [Coalgebra R Z]

/-- Build an isomorphism in the category `Coalg R` from a
`CoalgEquiv`. -/
@[simps]
def toCoalgIso (e : X ≃ₗc[R] Y) : Coalg.of R X ≅ Coalg.of R Y where
  hom := Coalg.ofHom e
  inv := Coalg.ofHom e.symm
  hom_inv_id := Hom.ext <| DFunLike.ext _ _ e.left_inv
  inv_hom_id := Hom.ext <| DFunLike.ext _ _ e.right_inv

@[simp] theorem toCoalgIso_refl :
    toCoalgIso (CoalgEquiv.refl R X) = .refl _ :=
  rfl

@[simp] theorem toCoalgIso_symm (e : X ≃ₗc[R] Y) :
    toCoalgIso e.symm = (toCoalgIso e).symm :=
  rfl

@[simp] theorem toCoalgIso_trans (e : X ≃ₗc[R] Y) (f : Y ≃ₗc[R] Z) :
    toCoalgIso (e.trans f) = toCoalgIso e ≪≫ toCoalgIso f :=
  rfl

end CoalgEquiv

namespace CategoryTheory.Iso

open Coalgebra

variable {X Y Z : Coalg.{v} R}

/-- Build a `CoalgEquiv` from an isomorphism in the category
`Coalg R`. -/
def toCoalgEquiv (i : X ≅ Y) : X ≃ₗc[R] Y :=
  { i.hom.toCoalgHom with
    invFun := i.inv.toCoalgHom
    left_inv := fun x => CoalgHom.congr_fun (congr_arg Coalg.Hom.toCoalgHom i.3) x
    right_inv := fun x => CoalgHom.congr_fun (congr_arg Coalg.Hom.toCoalgHom i.4) x }

@[simp] theorem toCoalgEquiv_toCoalgHom (i : X ≅ Y) :
    i.toCoalgEquiv = i.hom.toCoalgHom := rfl

@[simp] theorem toCoalgEquiv_refl : toCoalgEquiv (.refl X) = .refl _ _ :=
  rfl

@[simp] theorem toCoalgEquiv_symm (e : X ≅ Y) :
    toCoalgEquiv e.symm = (toCoalgEquiv e).symm :=
  rfl

@[simp] theorem toCoalgEquiv_trans (e : X ≅ Y) (f : Y ≅ Z) :
    toCoalgEquiv (e ≪≫ f) = e.toCoalgEquiv.trans f.toCoalgEquiv :=
  rfl

end CategoryTheory.Iso

instance Coalg.forget_reflects_isos :
    (forget (Coalg.{v} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (Coalg.{v} R)).map f)
    let e : X ≃ₗc[R] Y := { f.toCoalgHom, i.toEquiv with }
    exact ⟨e.toCoalgIso.isIso_hom.1⟩
