/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The pullback of a shift by a monoid morphism

Given a shift by a monoid `B` on a category `C` and a monoid morphism  `φ : A →+ B`,
we define a shift by `A` on a category `PullbackShift C φ` which is a type synonym for `C`.

-/

namespace CategoryTheory

open Limits Category

variable (C : Type*) [Category C] {A B : Type*} [AddMonoid A] [AddMonoid B]
  (φ : A →+ B) [HasShift C B]

/-- The category `PullbackShift C φ` is equipped with a shift such that for all `a`,
the shift functor by `a` is `shiftFunctor C (φ a)`. -/
@[nolint unusedArguments]
def PullbackShift (_ : A →+ B) [HasShift C B] := C

instance : Category (PullbackShift C φ) := by
  dsimp only [PullbackShift]
  infer_instance

attribute [local instance] endofunctorMonoidalCategory

/-- The shift on `PullbackShift C φ` is obtained by precomposing the shift on `C` with
the monoidal functor `Discrete.addMonoidalFunctor φ : Discrete A ⥤ Discrete B`. -/
noncomputable instance : HasShift (PullbackShift C φ) A where
  shift := Discrete.addMonoidalFunctor φ ⋙ shiftMonoidalFunctor C B

instance [HasZeroObject C] : HasZeroObject (PullbackShift C φ) := by
  dsimp [PullbackShift]
  infer_instance

instance [Preadditive C] : Preadditive (PullbackShift C φ) := by
  dsimp [PullbackShift]
  infer_instance

instance [Preadditive C] (a : A) [(shiftFunctor C (φ a)).Additive] :
    (shiftFunctor (PullbackShift C φ) a).Additive := by
  change (shiftFunctor C (φ a)).Additive
  infer_instance

/-- When `b = φ a`, this is the canonical
isomorphism `shiftFunctor (PullbackShift C φ) a ≅ shiftFunctor C b`. -/
noncomputable def pullbackShiftIso (a : A) (b : B) (h : b = φ a) :
    shiftFunctor (PullbackShift C φ) a ≅ shiftFunctor C b := eqToIso (by subst h; rfl)

variable {C}
variable (X : PullbackShift C φ) (a₁ a₂ a₃ : A) (h : a₁ + a₂ = a₃) (b₁ b₂ b₃ : B)
  (h₁ : b₁ = φ a₁) (h₂ : b₂ = φ a₂) (h₃ : b₃ = φ a₃)

lemma pullbackShiftFunctorZero_inv_app :
    (shiftFunctorZero _ A).inv.app X =
      (shiftFunctorZero C B).inv.app X ≫ (pullbackShiftIso C φ 0 0 (by simp)).inv.app X := by
  change (shiftFunctorZero C B).inv.app X ≫ _ = _
  dsimp [Discrete.eqToHom, Discrete.addMonoidalFunctor_ε]
  congr 2
  apply eqToHom_map

lemma pullbackShiftFunctorZero_hom_app :
    (shiftFunctorZero _ A).hom.app X =
      (pullbackShiftIso C φ 0 0 (by simp)).hom.app X ≫ (shiftFunctorZero C B).hom.app X := by
  rw [← cancel_epi ((shiftFunctorZero _ A).inv.app X), Iso.inv_hom_id_app,
    pullbackShiftFunctorZero_inv_app, assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  rfl

lemma pullbackShiftFunctorAdd'_inv_app :
    (shiftFunctorAdd' _ a₁ a₂ a₃ h).inv.app X =
      (shiftFunctor (PullbackShift C φ) a₂).map ((pullbackShiftIso C φ a₁ b₁ h₁).hom.app X) ≫
        (pullbackShiftIso C φ a₂ b₂ h₂).hom.app _ ≫
        (shiftFunctorAdd' C b₁ b₂ b₃ (by rw [h₁, h₂, h₃, ← h, φ.map_add])).inv.app X ≫
        (pullbackShiftIso C φ a₃ b₃ h₃).inv.app X := by
  subst h₁ h₂ h
  obtain rfl : b₃ = φ a₁ + φ a₂ := by rw [h₃, φ.map_add]
  erw [Functor.map_id, id_comp, id_comp, shiftFunctorAdd'_eq_shiftFunctorAdd,
    shiftFunctorAdd'_eq_shiftFunctorAdd]
  change _ ≫ _ = _
  congr 1
  rw [Discrete.addMonoidalFunctor_μ]
  dsimp [Discrete.eqToHom]
  congr 2
  apply eqToHom_map

lemma pullbackShiftFunctorAdd'_hom_app :
    (shiftFunctorAdd' _ a₁ a₂ a₃ h).hom.app X =
      (pullbackShiftIso C φ a₃ b₃ h₃).hom.app X ≫
      (shiftFunctorAdd' C b₁ b₂ b₃ (by rw [h₁, h₂, h₃, ← h, φ.map_add])).hom.app X ≫
      (pullbackShiftIso C φ a₂ b₂ h₂).inv.app _ ≫
      (shiftFunctor (PullbackShift C φ) a₂).map ((pullbackShiftIso C φ a₁ b₁ h₁).inv.app X) := by
  rw [← cancel_epi ((shiftFunctorAdd' _ a₁ a₂ a₃ h).inv.app X), Iso.inv_hom_id_app,
    pullbackShiftFunctorAdd'_inv_app φ X a₁ a₂ a₃ h b₁ b₂ b₃ h₁ h₂ h₃, assoc, assoc, assoc,
    Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
  rfl

end CategoryTheory
