/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Category.CoalgebraCat.Basic
import Mathlib.Algebra.Category.AlgebraCat.Basic
import Mathlib.RingTheory.Bialgebra.Equiv

/-!
# The category of bialgebras

This file mimics `Mathlib.LinearAlgebra.QuadraticForm.QuadraticModuleCat`.

-/

open CategoryTheory

universe v u

variable (R : Type u) [CommRing R]

/-- The category of `R`-bialgebras. -/
structure BialgebraCat extends Bundled Ring.{v} where
  isBialgebra : Bialgebra R α

attribute [instance] BialgebraCat.isBialgebra

variable {R}

namespace BialgebraCat

open Bialgebra

instance : CoeSort (BialgebraCat.{v} R) (Type v) :=
  ⟨(·.α)⟩

-- I guess I'm only making this because I wanted to extend `RingCat` but can't.
/-- The object in `RingCat` underlying an object in `BialgebraCat R`. -/
def toRingCat (X : BialgebraCat.{v} R) : RingCat := toBundled X

@[simp] theorem ringCat_of_toRingCat (X : BialgebraCat.{v} R) :
    RingCat.of X.toRingCat = X.toRingCat :=
  rfl

variable (R)

/-- The object in the category of `R`-bialgebras associated to an `R`-bialgebra. -/
@[simps]
def of (X : Type v) [Ring X] [Bialgebra R X] :
    BialgebraCat R where
  isBialgebra := (inferInstance : Bialgebra R X)

variable {R}

@[simp]
lemma of_comul {X : Type v} [Ring X] [Bialgebra R X] :
    Coalgebra.comul (A := of R X) = Coalgebra.comul (R := R) (A := X) := rfl

@[simp]
lemma of_counit {X : Type v} [Ring X] [Bialgebra R X] :
    Coalgebra.counit (A := of R X) = Coalgebra.counit (R := R) (A := X) := rfl

/-- A type alias for `BialgHom` to avoid confusion between the categorical and
algebraic spellings of composition. -/
@[ext]
structure Hom (V W : BialgebraCat.{v} R) :=
  /-- The underlying isometry -/
  toBialgHom : V →ₐc[R] W

lemma Hom.toBialgHom_injective (V W : BialgebraCat.{v} R) :
    Function.Injective (Hom.toBialgHom : Hom V W → _) :=
  fun ⟨f⟩ ⟨g⟩ _ => by congr

instance category : Category (BialgebraCat.{v} R) where
  Hom X Y := Hom X Y
  id X := ⟨BialgHom.id R X⟩
  comp f g := ⟨BialgHom.comp g.toBialgHom f.toBialgHom⟩
  id_comp g := Hom.ext _ _ <| BialgHom.id_comp g.toBialgHom
  comp_id f := Hom.ext _ _ <| BialgHom.comp_id f.toBialgHom
  assoc f g h := Hom.ext _ _ <| BialgHom.comp_assoc h.toBialgHom g.toBialgHom f.toBialgHom

-- TODO: if `Quiver.Hom` and the instance above were `reducible`, this wouldn't be needed.
@[ext]
lemma hom_ext {X Y : BialgebraCat.{v} R} (f g : X ⟶ Y) (h : f.toBialgHom = g.toBialgHom) :
    f = g :=
  Hom.ext _ _ h

/-- Typecheck a `BialgHom` as a morphism in `BialgebraCat R`. -/
abbrev ofHom {X Y : Type v} [Ring X] [Ring Y]
    [Bialgebra R X] [Bialgebra R Y] (f : X →ₐc[R] Y) :
    of R X ⟶ of R Y :=
  ⟨f⟩

@[simp] theorem toBialgHom_comp {X Y Z : BialgebraCat.{v} R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toBialgHom = g.toBialgHom.comp f.toBialgHom :=
  rfl

@[simp] theorem toBialgHom_id {M : BialgebraCat.{v} R} :
    Hom.toBialgHom (𝟙 M) = BialgHom.id _ _ :=
  rfl

instance concreteCategory : ConcreteCategory.{v} (BialgebraCat.{v} R) where
  forget :=
    { obj := fun M => M
      map := @fun M N f => f.toBialgHom }
  forget_faithful :=
    { map_injective := @fun M N => DFunLike.coe_injective.comp <| Hom.toBialgHom_injective _ _ }

instance hasForgetToAlgebra : HasForget₂ (BialgebraCat R) (AlgebraCat R) where
  forget₂ :=
    { obj := fun X => AlgebraCat.of R X
      map := fun {X Y} f => (f.toBialgHom : X →ₐ[R] Y) }

@[simp]
theorem forget₂_algebra_obj (X : BialgebraCat R) :
    (forget₂ (BialgebraCat R) (AlgebraCat R)).obj X = AlgebraCat.of R X :=
  rfl

@[simp]
theorem forget₂_algebra_map (X Y : BialgebraCat R) (f : X ⟶ Y) :
    (forget₂ (BialgebraCat R) (AlgebraCat R)).map f = (f.toBialgHom : X →ₐ[R] Y) :=
  rfl

instance hasForgetToCoalgebra : HasForget₂ (BialgebraCat R) (CoalgebraCat R) where
  forget₂ :=
    { obj := fun X => CoalgebraCat.of R X
      map := fun {X Y} f => CoalgebraCat.ofHom f.toBialgHom }

@[simp]
theorem forget₂_coalgebra_obj (X : BialgebraCat R) :
    (forget₂ (BialgebraCat R) (CoalgebraCat R)).obj X = CoalgebraCat.of R X :=
  rfl

@[simp]
theorem forget₂_coalgebra_map (X Y : BialgebraCat R) (f : X ⟶ Y) :
    (forget₂ (BialgebraCat R) (CoalgebraCat R)).map f = CoalgebraCat.ofHom f.toBialgHom :=
  rfl

end BialgebraCat

namespace BialgEquiv

open BialgebraCat

variable {X Y Z : Type v}
variable [Ring X] [Ring Y] [Ring Z]
variable [Bialgebra R X] [Bialgebra R Y] [Bialgebra R Z]

/-- Build an isomorphism in the category `BialgebraCat R` from a
`BialgEquiv`. -/
@[simps]
def toIso (e : X ≃ₐc[R] Y) : BialgebraCat.of R X ≅ BialgebraCat.of R Y where
  hom := ⟨e.toBialgHom⟩
  inv := ⟨e.symm.toBialgHom⟩
  hom_inv_id := Hom.ext _ _ <| DFunLike.ext _ _ e.left_inv
  inv_hom_id := Hom.ext _ _ <| DFunLike.ext _ _ e.right_inv

@[simp] theorem toIso_refl : toIso (BialgEquiv.refl R X) = .refl _ :=
  rfl

@[simp] theorem toIso_symm (e : X ≃ₐc[R] Y) :
    toIso e.symm = (toIso e).symm :=
  rfl

@[simp] theorem toIso_trans (e : X ≃ₐc[R] Y) (f : Y ≃ₐc[R] Z) :
    toIso (e.trans f) = toIso e ≪≫ toIso f :=
  rfl

end BialgEquiv

namespace CategoryTheory.Iso

open Bialgebra

variable {X Y Z : BialgebraCat.{v} R}

/-- Build a `BialgEquiv` from an isomorphism in the category
`BialgebraCat R`. -/
def toBialgEquiv (i : X ≅ Y) : X ≃ₐc[R] Y :=
  { i.hom.toBialgHom with
    invFun := i.inv.toBialgHom
    left_inv := fun x => BialgHom.congr_fun (congr_arg BialgebraCat.Hom.toBialgHom i.3) x
    right_inv := fun x => BialgHom.congr_fun (congr_arg BialgebraCat.Hom.toBialgHom i.4) x }

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
