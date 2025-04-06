/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Category.Coalg.Basic
import Mathlib.Algebra.Category.Alg.Basic
import Mathlib.RingTheory.Bialgebra.Equiv

/-!
# The category of bialgebras over a commutative ring

We introduce the bundled category `Bialg` of bialgebras over a fixed commutative ring `R`
along with the forgetful functors to `Coalg` and `Alg`.

This file mimics `Mathlib.LinearAlgebra.QuadraticForm.QuadraticModuleCat`.

-/

open CategoryTheory

universe v u

variable (R : Type u) [CommRing R]

/-- The category of `R`-bialgebras. -/
structure Bialg where
  /-- The underlying type. -/
  carrier : Type v
  [instRing : Ring carrier]
  [instBialgebra : Bialgebra R carrier]

attribute [instance] Bialg.instBialgebra Bialg.instRing

variable {R}

namespace Bialg

open Bialgebra

instance : CoeSort (Bialg.{v} R) (Type v) :=
  ⟨(·.carrier)⟩

variable (R) in
/-- The object in the category of `R`-bialgebras associated to an `R`-bialgebra. -/
@[simps]
def of (X : Type v) [Ring X] [Bialgebra R X] :
    Bialg R where
  carrier := X

@[simp]
lemma of_comul {X : Type v} [Ring X] [Bialgebra R X] :
    Coalgebra.comul (A := of R X) = Coalgebra.comul (R := R) (A := X) := rfl

@[simp]
lemma of_counit {X : Type v} [Ring X] [Bialgebra R X] :
    Coalgebra.counit (A := of R X) = Coalgebra.counit (R := R) (A := X) := rfl

/-- A type alias for `BialgHom` to avoid confusion between the categorical and
algebraic spellings of composition. -/
@[ext]
structure Hom (V W : Bialg.{v} R) where
  /-- The underlying `BialgHom` -/
  toBialgHom' : V →ₐc[R] W

instance category : Category (Bialg.{v} R) where
  Hom X Y := Hom X Y
  id X := ⟨BialgHom.id R X⟩
  comp f g := ⟨BialgHom.comp g.toBialgHom' f.toBialgHom'⟩

instance concreteCategory : ConcreteCategory (Bialg.{v} R) (· →ₐc[R] ·) where
  hom f := f.toBialgHom'
  ofHom f := ⟨f⟩

/-- Turn a morphism in `Bialg` back into a `BialgHom`. -/
abbrev Hom.toBialgHom {X Y : Bialg R} (f : Hom X Y) :=
  ConcreteCategory.hom (C := Bialg R) f

/-- Typecheck a `BialgHom` as a morphism in `Bialg R`. -/
abbrev ofHom {X Y : Type v} [Ring X] [Ring Y]
    [Bialgebra R X] [Bialgebra R Y] (f : X →ₐc[R] Y) :
    of R X ⟶ of R Y :=
  ConcreteCategory.ofHom f

lemma Hom.toBialgHom_injective (V W : Bialg.{v} R) :
    Function.Injective (Hom.toBialgHom : Hom V W → _) :=
  fun ⟨f⟩ ⟨g⟩ _ => by congr

-- TODO: if `Quiver.Hom` and the instance above were `reducible`, this wouldn't be needed.
@[ext]
lemma hom_ext {X Y : Bialg.{v} R} (f g : X ⟶ Y) (h : f.toBialgHom = g.toBialgHom) :
    f = g :=
  Hom.ext h

@[simp] theorem toBialgHom_comp {X Y Z : Bialg.{v} R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toBialgHom = g.toBialgHom.comp f.toBialgHom :=
  rfl

@[simp] theorem toBialgHom_id {M : Bialg.{v} R} :
    Hom.toBialgHom (𝟙 M) = BialgHom.id _ _ :=
  rfl

instance hasForget : HasForget.{v} (Bialg.{v} R) where
  forget :=
    { obj := fun M => M
      map := fun f => f.toBialgHom }
  forget_faithful :=
    { map_injective := fun {_ _} => DFunLike.coe_injective.comp <| Hom.toBialgHom_injective _ _ }

instance hasForgetToAlgebra : HasForget₂ (Bialg R) (Alg R) where
  forget₂ :=
    { obj := fun X => Alg.of R X
      map := fun {X Y} f => Alg.ofHom f.toBialgHom }

@[simp]
theorem forget₂_algebra_obj (X : Bialg R) :
    (forget₂ (Bialg R) (Alg R)).obj X = Alg.of R X :=
  rfl

@[simp]
theorem forget₂_algebra_map (X Y : Bialg R) (f : X ⟶ Y) :
    (forget₂ (Bialg R) (Alg R)).map f = Alg.ofHom f.toBialgHom :=
  rfl

instance hasForgetToCoalgebra : HasForget₂ (Bialg R) (Coalg R) where
  forget₂ :=
    { obj := fun X => Coalg.of R X
      map := fun {_ _} f => Coalg.ofHom f.toBialgHom }

@[simp]
theorem forget₂_coalgebra_obj (X : Bialg R) :
    (forget₂ (Bialg R) (Coalg R)).obj X = Coalg.of R X :=
  rfl

@[simp]
theorem forget₂_coalgebra_map (X Y : Bialg R) (f : X ⟶ Y) :
    (forget₂ (Bialg R) (Coalg R)).map f = Coalg.ofHom f.toBialgHom :=
  rfl

end Bialg

namespace BialgEquiv

open Bialg

variable {X Y Z : Type v}
variable [Ring X] [Ring Y] [Ring Z]
variable [Bialgebra R X] [Bialgebra R Y] [Bialgebra R Z]

/-- Build an isomorphism in the category `Bialg R` from a
`BialgEquiv`. -/
@[simps]
def toBialgIso (e : X ≃ₐc[R] Y) : Bialg.of R X ≅ Bialg.of R Y where
  hom := Bialg.ofHom e
  inv := Bialg.ofHom e.symm
  hom_inv_id := Hom.ext <| DFunLike.ext _ _ e.left_inv
  inv_hom_id := Hom.ext <| DFunLike.ext _ _ e.right_inv

@[simp] theorem toBialgIso_refl : toBialgIso (BialgEquiv.refl R X) = .refl _ :=
  rfl

@[simp] theorem toBialgIso_symm (e : X ≃ₐc[R] Y) :
    toBialgIso e.symm = (toBialgIso e).symm :=
  rfl

@[simp] theorem toBialgIso_trans (e : X ≃ₐc[R] Y) (f : Y ≃ₐc[R] Z) :
    toBialgIso (e.trans f) = toBialgIso e ≪≫ toBialgIso f :=
  rfl

end BialgEquiv

namespace CategoryTheory.Iso

open Bialgebra

variable {X Y Z : Bialg.{v} R}

/-- Build a `BialgEquiv` from an isomorphism in the category
`Bialg R`. -/
def toBialgEquiv (i : X ≅ Y) : X ≃ₐc[R] Y :=
  { i.hom.toBialgHom with
    invFun := i.inv.toBialgHom
    left_inv := fun x => BialgHom.congr_fun (congr_arg Bialg.Hom.toBialgHom i.3) x
    right_inv := fun x => BialgHom.congr_fun (congr_arg Bialg.Hom.toBialgHom i.4) x }

@[simp] theorem toBialgEquiv_toBialgHom (i : X ≅ Y) :
    (i.toBialgEquiv : X →ₐc[R] Y) = i.hom.1 := rfl

@[simp] theorem toBialgEquiv_refl : toBialgEquiv (.refl X) = .refl _ _ :=
  rfl

@[simp] theorem toBialgEquiv_symm (e : X ≅ Y) :
    toBialgEquiv e.symm = (toBialgEquiv e).symm :=
  rfl

@[simp] theorem toBialgEquiv_trans (e : X ≅ Y) (f : Y ≅ Z) :
    toBialgEquiv (e ≪≫ f) = e.toBialgEquiv.trans f.toBialgEquiv :=
  rfl

end CategoryTheory.Iso

instance Bialg.forget_reflects_isos :
    (forget (Bialg.{v} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (Bialg.{v} R)).map f)
    let e : X ≃ₐc[R] Y := { f.toBialgHom, i.toEquiv with }
    exact ⟨e.toBialgIso.isIso_hom.1⟩
