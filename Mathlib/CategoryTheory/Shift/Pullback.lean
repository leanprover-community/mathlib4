/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Shift.CommShift
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

lemma pullbackShiftFunctorZero'_inv_app :
    (shiftFunctorZero _ A).inv.app X = (shiftFunctorZero' C (φ 0) (by rw [map_zero])).inv.app X ≫
    (pullbackShiftIso C φ 0 (φ 0) rfl).inv.app X := by
  rw [pullbackShiftFunctorZero_inv_app]
  simp only [Functor.id_obj, pullbackShiftIso, eqToIso.inv, eqToHom_app, shiftFunctorZero',
    Iso.trans_inv, NatTrans.comp_app, eqToIso_refl, Iso.refl_inv, NatTrans.id_app, assoc]
  erw [comp_id]

lemma pullbackShiftFunctorZero'_hom_app :
    (shiftFunctorZero _ A).hom.app X = (pullbackShiftIso C φ 0 (φ 0) rfl).hom.app X ≫
    (shiftFunctorZero' C (φ 0) (by rw [map_zero])).hom.app X := by
  rw [← cancel_epi ((shiftFunctorZero _ A).inv.app X), Iso.inv_hom_id_app,
    pullbackShiftFunctorZero'_inv_app, assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
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

-- This is proved by `simp`, but useful for rewrites.-/
lemma pullbackShiftIso_hom_naturality {F G : C ⥤ C} (z : F ⟶ G)
    (X : C) (a : A) (b : B) (h : b = φ a) :
    F.map ((pullbackShiftIso C φ a b h).hom.app X) ≫ z.app _ =
    z.app _ ≫ G.map ((pullbackShiftIso C φ a b h).hom.app X)  := by simp

/-- This is proved by `simp`, but useful for rewrites.-/
lemma pullbackShiftIso_inv_naturality {F G : C ⥤ C} (z : F ⟶ G)
    (X : C) (a : A) (b : B) (h : b = φ a) :
    F.map ((pullbackShiftIso C φ a b h).inv.app X) ≫ z.app _ =
    z.app _ ≫ G.map ((pullbackShiftIso C φ a b h).inv.app X) := by simp

section CommShift

variable {D : Type*} [Category D] [HasShift D B] (F : C ⥤ D) [F.CommShift B]

abbrev Functor.pullbackShift : PullbackShift C φ ⥤ PullbackShift D φ := F

/-- If `F : C ⥤ D` commutes with the shifts on `C` and `D`, then it also commutes with
their pullbacks by an additive map. Scoped instance between we might not want it to be global.
-/
noncomputable scoped instance Functor.pullbackCommShift : Functor.CommShift (F.pullbackShift φ) A
    where
  iso a := isoWhiskerRight (pullbackShiftIso C φ a (φ a) rfl) (pullbackShift φ F) ≪≫
    CommShift.iso (F := F) (φ a) ≪≫ isoWhiskerLeft _  (pullbackShiftIso D φ a (φ a) rfl).symm
  zero := by
    ext _
    simp only [comp_obj, Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom, Iso.symm_hom,
      NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, CommShift.isoZero_hom_app,
      pullbackShiftFunctorZero'_hom_app, id_obj, map_comp, pullbackShiftFunctorZero'_inv_app, assoc]
    conv_lhs => congr; rfl; congr; change (F.commShiftIso (φ 0)).hom.app _
                rw [F.commShiftIso_zero' (A := B) (φ 0) (by rw [map_zero])]
    simp
  add a b := by
    ext _
    simp only [comp_obj, Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom, Iso.symm_hom,
      NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, CommShift.isoAdd_hom_app, map_comp,
      assoc]
    conv_lhs => congr; rfl; congr; change (F.commShiftIso (φ (a + b))).hom.app _
                rw [F.commShiftIso_add' (a := φ a) (b := φ b) (by rw [φ.map_add])]
    rw [← shiftFunctorAdd'_eq_shiftFunctorAdd, ← shiftFunctorAdd'_eq_shiftFunctorAdd]
    rw [pullbackShiftFunctorAdd'_hom_app φ _ a b (a + b) rfl (φ a) (φ b) (φ (a + b)) rfl rfl rfl]
    rw [pullbackShiftFunctorAdd'_inv_app φ _ a b (a + b) rfl (φ a) (φ b) (φ (a + b)) rfl rfl rfl]
    simp only [CommShift.isoAdd'_hom_app, assoc, comp_obj, map_comp, NatTrans.naturality_assoc,
      Iso.inv_hom_id_app_assoc]
    slice_rhs 9 10 => rw [← map_comp, Iso.inv_hom_id_app, map_id]
    erw [id_comp]
    slice_rhs 6 7 => erw [← (CommShift.iso (φ b)).hom.naturality]
    slice_rhs 4 5 => rw [← map_comp, (pullbackShiftIso C φ b (φ b) rfl).hom.naturality, map_comp]
    simp only [comp_obj, comp_map, assoc]
    slice_rhs 3 4 => rw [← map_comp, Iso.inv_hom_id_app, map_id]
    slice_rhs 4 5 => rw [← map_comp]; erw [← map_comp]; rw [Iso.inv_hom_id_app, map_id, map_id]
    rw [id_comp, id_comp, assoc, assoc]; rfl

open Functor

lemma pullbackCommShift_iso_hom_app (a : A) (X : C) :
    (CommShift.iso (F := (F.pullbackShift φ)) a).hom.app X =
    F.map ((pullbackShiftIso C φ a (φ a) rfl).hom.app X) ≫ (F.commShiftIso (φ a)).hom.app X ≫
    (pullbackShiftIso D φ a (φ a) rfl).inv.app (F.obj X) := by
  simp [Functor.CommShift.iso, Functor.pullbackCommShift]; rfl

lemma pullbackCommShift_iso_inv_app (a : A) (X : C) :
    (CommShift.iso (F := F.pullbackShift φ) a).inv.app X =
    ((pullbackShiftIso D φ a (φ a) rfl).hom.app (F.obj X)) ≫ (F.commShiftIso (φ a)).inv.app X ≫
    F.map ((pullbackShiftIso C φ a (φ a) rfl).inv.app X) := by
  rw [← cancel_mono ((CommShift.iso (F := F.pullbackShift φ) a).hom.app X), Iso.inv_hom_id_app,
    pullbackCommShift_iso_hom_app]
  slice_rhs 3 4 => rw [← map_comp, Iso.inv_hom_id_app, map_id]
  simp

end CommShift

end CategoryTheory
