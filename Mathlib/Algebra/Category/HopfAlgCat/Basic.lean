/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Category.BialgCat.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# The category of Hopf algebras over a commutative ring

We introduce the bundled category `HopfAlgCat` of Hopf algebras over a fixed commutative ring
`R` along with the forgetful functor to `BialgCat`.

This file mimics `Mathlib/LinearAlgebra/QuadraticForm/QuadraticModuleCat.lean`.

-/

open CategoryTheory

universe v u

variable (R : Type u) [CommRing R]

/-- The category of `R`-Hopf algebras. -/
structure HopfAlgCat where
  /-- The underlying type. -/
  carrier : Type v
  [instRing : Ring carrier]
  [instHopfAlgebra : HopfAlgebra R carrier]

attribute [instance] HopfAlgCat.instHopfAlgebra HopfAlgCat.instRing

variable {R}

namespace HopfAlgCat

open HopfAlgebra

instance : CoeSort (HopfAlgCat.{v} R) (Type v) :=
  ⟨(·.carrier)⟩

variable (R) in
/-- The object in the category of `R`-Hopf algebras associated to an `R`-Hopf algebra. -/
abbrev of (X : Type v) [Ring X] [HopfAlgebra R X] :
    HopfAlgCat R where
  carrier := X

@[simp]
lemma of_comul {X : Type v} [Ring X] [HopfAlgebra R X] :
    Coalgebra.comul (A := of R X) = Coalgebra.comul (R := R) (A := X) := rfl

@[simp]
lemma of_counit {X : Type v} [Ring X] [HopfAlgebra R X] :
    Coalgebra.counit (A := of R X) = Coalgebra.counit (R := R) (A := X) := rfl

/-- A type alias for `BialgHom` to avoid confusion between the categorical and
algebraic spellings of composition. -/
@[ext]
structure Hom (V W : HopfAlgCat.{v} R) where
  /-- The underlying `BialgHom`. -/
  toBialgHom' : V →ₐc[R] W

instance category : Category (HopfAlgCat.{v} R) where
  Hom X Y := Hom X Y
  id X := ⟨BialgHom.id R X⟩
  comp f g := ⟨BialgHom.comp g.toBialgHom' f.toBialgHom'⟩

instance concreteCategory : ConcreteCategory (HopfAlgCat.{v} R) (· →ₐc[R] ·) where
  hom f := f.toBialgHom'
  ofHom f := ⟨f⟩

/-- Turn a morphism in `HopfAlgCat` back into a `BialgHom`. -/
abbrev Hom.toBialgHom {X Y : HopfAlgCat R} (f : Hom X Y) :=
  ConcreteCategory.hom (C := HopfAlgCat R) f

/-- Typecheck a `BialgHom` as a morphism in `HopfAlgCat R`. -/
abbrev ofHom {X Y : Type v} [Ring X] [Ring Y]
    [HopfAlgebra R X] [HopfAlgebra R Y] (f : X →ₐc[R] Y) :
    of R X ⟶ of R Y :=
  ConcreteCategory.ofHom f

lemma Hom.toBialgHom_injective (V W : HopfAlgCat.{v} R) :
    Function.Injective (Hom.toBialgHom : Hom V W → _) :=
  fun ⟨f⟩ ⟨g⟩ _ => by congr

@[ext]
lemma hom_ext {X Y : HopfAlgCat.{v} R} (f g : X ⟶ Y) (h : f.toBialgHom = g.toBialgHom) :
    f = g :=
  Hom.ext h

@[simp] theorem toBialgHom_comp {X Y Z : HopfAlgCat.{v} R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toBialgHom = g.toBialgHom.comp f.toBialgHom :=
  rfl

@[simp] theorem toBialgHom_id {M : HopfAlgCat.{v} R} :
    Hom.toBialgHom (𝟙 M) = BialgHom.id _ _ :=
  rfl

instance hasForgetToBialgebra : HasForget₂ (HopfAlgCat R) (BialgCat R) where
  forget₂ :=
    { obj := fun X => BialgCat.of R X
      map := fun {_ _} f => BialgCat.ofHom f.toBialgHom }

@[simp]
theorem forget₂_bialgebra_obj (X : HopfAlgCat R) :
    (forget₂ (HopfAlgCat R) (BialgCat R)).obj X = BialgCat.of R X :=
  rfl

@[simp]
theorem forget₂_bialgebra_map (X Y : HopfAlgCat R) (f : X ⟶ Y) :
    (forget₂ (HopfAlgCat R) (BialgCat R)).map f = BialgCat.ofHom f.toBialgHom :=
  rfl

end HopfAlgCat

namespace BialgEquiv

open HopfAlgCat

variable {X Y Z : Type v}
variable [Ring X] [Ring Y] [Ring Z]
variable [HopfAlgebra R X] [HopfAlgebra R Y] [HopfAlgebra R Z]

/-- Build an isomorphism in the category `HopfAlgCat R` from a
`BialgEquiv`. -/
@[simps]
def toHopfAlgIso (e : X ≃ₐc[R] Y) : HopfAlgCat.of R X ≅ HopfAlgCat.of R Y where
  hom := HopfAlgCat.ofHom e
  inv := HopfAlgCat.ofHom e.symm
  hom_inv_id := Hom.ext <| DFunLike.ext _ _ e.left_inv
  inv_hom_id := Hom.ext <| DFunLike.ext _ _ e.right_inv

@[simp] theorem toHopfAlgIso_refl :
    toHopfAlgIso (BialgEquiv.refl R X) = .refl _ :=
  rfl

@[simp] theorem toHopfAlgIso_symm (e : X ≃ₐc[R] Y) :
    toHopfAlgIso e.symm = (toHopfAlgIso e).symm :=
  rfl

@[simp] theorem toHopfAlgIso_trans (e : X ≃ₐc[R] Y) (f : Y ≃ₐc[R] Z) :
    toHopfAlgIso (e.trans f) = toHopfAlgIso e ≪≫ toHopfAlgIso f :=
  rfl

end BialgEquiv

namespace CategoryTheory.Iso

open HopfAlgebra

variable {X Y Z : HopfAlgCat.{v} R}

/-- Build a `BialgEquiv` from an isomorphism in the category
`HopfAlgCat R`. -/
def toHopfAlgEquiv (i : X ≅ Y) : X ≃ₐc[R] Y :=
  { i.hom.toBialgHom with
    invFun := i.inv.toBialgHom
    left_inv := fun x => BialgHom.congr_fun (congr_arg HopfAlgCat.Hom.toBialgHom i.3) x
    right_inv := fun x => BialgHom.congr_fun (congr_arg HopfAlgCat.Hom.toBialgHom i.4) x }

@[simp] theorem toHopfAlgEquiv_toBialgHom (i : X ≅ Y) :
    (i.toHopfAlgEquiv : X →ₐc[R] Y) = i.hom.1 := rfl

@[simp] theorem toHopfAlgEquiv_refl : toHopfAlgEquiv (.refl X) = .refl _ _ :=
  rfl

@[simp] theorem toHopfAlgEquiv_symm (e : X ≅ Y) :
    toHopfAlgEquiv e.symm = (toHopfAlgEquiv e).symm :=
  rfl

@[simp] theorem toHopfAlgEquiv_trans (e : X ≅ Y) (f : Y ≅ Z) :
    toHopfAlgEquiv (e ≪≫ f) = e.toHopfAlgEquiv.trans f.toHopfAlgEquiv :=
  rfl

end CategoryTheory.Iso

instance HopfAlgCat.forget_reflects_isos :
    (forget (HopfAlgCat.{v} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (HopfAlgCat.{v} R)).map f)
    let e : X ≃ₐc[R] Y := { f.toBialgHom, i.toEquiv with }
    exact ⟨e.toHopfAlgIso.isIso_hom.1⟩
