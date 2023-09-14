/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.Algebra.Category.AlgebraCat.Basic

/-!
# The category of quadratic modules
-/

open CategoryTheory

universe v u

variable (R : Type u) [CommRing R]

/-- The category of quadratic modules; modules with an associated quadratic form-/
structure QuadraticModuleCat extends ModuleCat.{v} R where
  form' : QuadraticForm R carrier

variable {R}

namespace QuadraticModuleCat

instance : CoeSort (QuadraticModuleCat.{v} R) (Type v) :=
  ⟨(·.carrier)⟩

instance (V : QuadraticModuleCat.{v} R) : AddCommGroup V :=
  V.isAddCommGroup

instance (V : QuadraticModuleCat.{v} R) : Module R V :=
  V.isModule

/-- The quadratic form associated with the module. -/
def form (V : QuadraticModuleCat.{v} R) : QuadraticForm R V := V.form'

/-- The object in the category of quadratic R-modules associated to a quadratic R-module. -/
def of {X : Type v} [AddCommGroup X] [Module R X] (Q : QuadraticForm R X) :
    QuadraticModuleCat R where
  form' := Q

/-- A type alias for `QuadraticForm.LinearIsometry` to avoid confusion between the categorical and
algebraic spellings of composition. -/
@[ext]
structure Hom (V W : QuadraticModuleCat.{v} R) :=
  toIsometry : V.form →qᵢ W.form

lemma Hom.toIsometry_injective (V W : QuadraticModuleCat.{v} R) :
    Function.Injective (Hom.toIsometry : Hom V W → _) :=
  fun ⟨f⟩ ⟨g⟩ _ => by congr

instance category : Category (QuadraticModuleCat.{v} R) where
  Hom M N := Hom M N
  id M := ⟨QuadraticForm.Isometry.id M.form⟩
  comp f g := ⟨QuadraticForm.Isometry.comp g.toIsometry f.toIsometry⟩
  id_comp g := Hom.ext _ _ <| QuadraticForm.Isometry.id_comp g.toIsometry
  comp_id f := Hom.ext _ _ <| QuadraticForm.Isometry.comp_id f.toIsometry
  assoc f g h := Hom.ext _ _ <|
    QuadraticForm.Isometry.comp_assoc h.toIsometry g.toIsometry f.toIsometry

/-- Typecheck a `QuadraticForm.Isometry` as a morphism in `Module R`. -/
abbrev ofHom {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    {Q₁ : QuadraticForm R X} {Q₂ : QuadraticForm R X} (f : Q₁ →qᵢ Q₂) :
    of Q₁ ⟶ of Q₂ := ⟨f⟩

@[simp] theorem toIsometry_comp {M N U : QuadraticModuleCat.{v} R} (f : M ⟶ N) (g : N ⟶ U) :
    (f ≫ g).toIsometry = g.toIsometry.comp f.toIsometry :=
  rfl

@[simp] theorem toIsometry_id {M : QuadraticModuleCat.{v} R}  :
    Hom.toIsometry (𝟙 M) = QuadraticForm.Isometry.id _ :=
  rfl

instance concreteCategory : ConcreteCategory.{v} (QuadraticModuleCat.{v} R) where
  forget :=
    { obj := fun M => M
      map := @fun M N f => f.toIsometry }
  forget_faithful :=
    { map_injective := @fun M N => FunLike.coe_injective.comp <| Hom.toIsometry_injective _ _ }

instance hasForgetToModule : HasForget₂ (QuadraticModuleCat R) (ModuleCat R) where
  forget₂ :=
    { obj := fun M => ModuleCat.of R M
      map := fun f => f.toIsometry.toLinearMap }

@[simp]
theorem forget₂_obj (X : QuadraticModuleCat R) :
    (forget₂ (QuadraticModuleCat R) (ModuleCat R)).obj X = ModuleCat.of R X :=
  rfl

@[simp]
theorem forget₂_map (X Y : QuadraticModuleCat R) (f : X ⟶ Y) :
    (forget₂ (QuadraticModuleCat R) (ModuleCat R)).map f = f.toIsometry.toLinearMap :=
  rfl

end QuadraticModuleCat
