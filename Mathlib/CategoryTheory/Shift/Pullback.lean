/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The pullback of a shift by a monoid morphism

Given a shift by a monoid `B` on a category `C` and a monoid morphism  `φ : A →+ B`,
we define a shift by `A` on a category `PullbackShift C φ` which is a type synonym for `C`.

-/

namespace CategoryTheory

open Limits Category

variable (C D : Type*) [Category C] [Category D]
  (F : C ⥤ D) {A B : Type*} [AddMonoid A] [AddMonoid B]
  (φ : A →+ B) [HasShift C B] [HasShift D B]

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
  shift := (Discrete.addMonoidalFunctor φ).comp (@HasShift.shift C B _ _ _)

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
  dsimp [Discrete.eqToHom]
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

namespace Functor

variable {D}
variable [F.CommShift B]

def pullbackShift : PullbackShift C φ ⥤ PullbackShift D φ := F

namespace pullbackShiftCommShift

def iso (a : A) :
    shiftFunctor (PullbackShift C φ) a ⋙ pullbackShift F φ ≅
      pullbackShift F φ ⋙ shiftFunctor (PullbackShift D φ) a :=
  F.commShiftIso (φ a)

lemma iso_eq (a : A) (b : B) (h : b = φ a) :
    iso F φ a =
      isoWhiskerRight (pullbackShiftIso C φ a b h) _ ≪≫ F.commShiftIso b ≪≫
        isoWhiskerLeft _ (pullbackShiftIso D φ a b h).symm := by
  ext X
  subst h
  dsimp [pullbackShiftIso]
  rw [map_id]
  erw [id_comp, comp_id]
  rfl

end pullbackShiftCommShift

open pullbackShiftCommShift in
instance : (F.pullbackShift φ).CommShift A where
  iso a := iso F φ a
  zero := by
    ext X
    dsimp
    rw [iso_eq F φ 0 0 (by simp), F.commShiftIso_zero, CommShift.isoZero_hom_app]
    dsimp
    rw [CommShift.isoZero_hom_app, assoc,
      pullbackShiftFunctorZero_hom_app, pullbackShiftFunctorZero_inv_app,
      map_comp, assoc]
    rfl
  add a b := by
    ext X
    dsimp
    rw [iso_eq F φ (a + b) (φ a + φ b) (by simp), CommShift.isoAdd_hom_app,
      F.commShiftIso_add]
    dsimp
    simp only [CommShift.isoAdd_hom_app, comp_obj, assoc,
      iso_eq F φ a (φ a) rfl, iso_eq F φ b (φ b) rfl]
    dsimp
    conv_rhs => rw [← shiftFunctorAdd'_eq_shiftFunctorAdd]
    rw [pullbackShiftFunctorAdd'_hom_app φ X a b (a + b) rfl (φ a) (φ b) (φ a + φ b)
      rfl rfl (by simp)]
    conv_rhs => rw [shiftFunctorAdd'_eq_shiftFunctorAdd]
    dsimp
    simp only [map_comp, assoc]
    congr 2
    dsimp [pullbackShiftIso]
    simp only [eqToHom_app, map_id]
    erw [Functor.map_id, Functor.map_id, Functor.map_id, Functor.map_id, Functor.map_id,
      id_comp, id_comp, id_comp, id_comp, id_comp, id_comp]
    congr 2
    conv_rhs => rw [← shiftFunctorAdd'_eq_shiftFunctorAdd]
    erw [pullbackShiftFunctorAdd'_inv_app φ (F.obj X) a b (a + b) rfl (φ a) (φ b) (φ a + φ b)
      rfl rfl (by simp)]
    rw [shiftFunctorAdd'_eq_shiftFunctorAdd]
    dsimp [pullbackShiftIso]
    simp only [map_id, eqToHom_app, id_comp]
    rfl

end Functor

end CategoryTheory
