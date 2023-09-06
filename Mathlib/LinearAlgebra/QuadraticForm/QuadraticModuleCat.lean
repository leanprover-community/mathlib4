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

instance category : Category (QuadraticModuleCat.{v} R) where
  Hom M N := M.form →qᵢ N.form
  id M := QuadraticForm.Isometry.id M.form
  comp f g := QuadraticForm.Isometry.comp g f
  id_comp := QuadraticForm.Isometry.id_comp
  comp_id := QuadraticForm.Isometry.comp_id
  assoc f g h := QuadraticForm.Isometry.comp_assoc h g f

theorem comp_def {M N U : QuadraticModuleCat.{v} R} (f : M ⟶ N) (g : N ⟶ U) : f ≫ g = g.comp f :=
  rfl

instance concreteCategory : ConcreteCategory.{v} (QuadraticModuleCat.{v} R) where
  forget :=
    { obj := fun M => M
      map := @fun M N f => letI f' : M.form →qᵢ N.form := f; ((f' : M.form →qᵢ N.form) : M → N) }
  forget_faithful :=
    { map_injective := @fun M N => FunLike.coe_injective (F := M.form →qᵢ N.form) }

instance hasForgetToModule : HasForget₂ (QuadraticModuleCat R) (ModuleCat R) where
  forget₂ :=
    { obj := fun M => ModuleCat.of R M
      map := @fun M₁ M₂ => QuadraticForm.Isometry.toLinearMap }

@[simp]
theorem forget₂_obj (X : QuadraticModuleCat R) :
    (forget₂ (QuadraticModuleCat R) (ModuleCat R)).obj X = ModuleCat.of R X :=
  rfl

instance (M N : QuadraticModuleCat R) : LinearMapClass (M ⟶ N) R M N :=
  { QuadraticForm.Isometry.instLinearMapClass with
    coe := fun f => f }

end QuadraticModuleCat
