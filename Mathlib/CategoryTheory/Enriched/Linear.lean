/-
Copyright (c) 2025 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Equiv.TransferInstance
import Mathlib.Tactic.CategoryTheory.Coherence
/-!
# Linear categories as `ModuleCat R`-enriched categories

Makes the statement "`R`-linear categories are categories enriched over `ModuleCat R`" concrete by
deriving an `EnrichedOrdinaryCategory (ModuleCat R) C` from `Linear R C` and, conversely, an
instance of `Linear R C` from `EnrichedOrdinaryCategory (ModuleCat R) C`.

Ideally this construction should be extended to an equivalence of suitable bicategories in the
future.

-/

universe w v v' u u'

namespace CategoryTheory

open TensorProduct MonoidalCategory

section EnrichedOfLinear

variable {R : Type u} [CommRing R]
variable {C : Type u} [Category.{u} C] [Preadditive C] [Linear R C]

lemma lift_comp_lift_comp_rTensor_eq {W X Y Z : C} (f : ((W ⟶ X) ⊗[R] (X ⟶ Y)) ⊗[R] (Y ⟶ Z)) :
    lift (Linear.comp W Y Z) (((lift (Linear.comp W X Y)).rTensor (Y ⟶ Z)) f) =
      lift (Linear.comp W X Z)
        ((lift (Linear.comp X Y Z)).lTensor (W ⟶ X) ((TensorProduct.assoc R _ _ _) f)) :=
  TensorProduct.induction_on f rfl
    (fun fg _ => TensorProduct.induction_on fg (by simp) (by simp)
      (fun _ _ h₂ h₃ => by simp [add_tmul, LinearEquiv.map_add, ← h₂, ← h₃]))
    (fun _ _ h₂ h₃ => by simp [h₂, h₃, LinearEquiv.map_add])

open ModuleCat Hom

/-- The `ModuleCat R`-enriched category induced by the structure of an `R`-linear category on a
category `C`. -/
noncomputable abbrev enrichedOrdinaryCategoryModuleCat :
    EnrichedOrdinaryCategory (ModuleCat R) C where
  Hom X Y := .of R (X ⟶ Y)
  id X := ModuleCat.ofHom <| (LinearMap.ringLmapEquivSelf R R (X ⟶ X)).symm (𝟙 X)
  comp X Y Z := ModuleCat.ofHom <| lift (Linear.comp X Y Z)
  id_comp X Y := by
    ext f
    simp only [LinearMap.ringLmapEquivSelf_symm_apply, ModuleCat.hom_comp,
      ModuleCat.MonoidalCategory.carrier_of_tensorObj_of, hom_ofHom,
      LinearMap.coe_comp, Function.comp_apply, ModuleCat.hom_id, LinearMap.id_coe, id_eq] at f ⊢
    rw [ModuleCat.MonoidalCategory.leftUnitor_inv_hom_apply]
    simp [ModuleCat.MonoidalCategory.tensorUnit_eq]
  comp_id X Y := by
    ext f
    simp only [LinearMap.ringLmapEquivSelf_symm_apply, ModuleCat.hom_comp,
      ModuleCat.MonoidalCategory.carrier_of_tensorObj_of, hom_ofHom,
      LinearMap.coe_comp, Function.comp_apply, ModuleCat.hom_id, LinearMap.id_coe, id_eq] at f ⊢
    rw [ModuleCat.MonoidalCategory.rightUnitor_inv_hom_apply]
    simp [ModuleCat.MonoidalCategory.tensorUnit_eq]
  assoc W X Y Z := by
    ext f
    change _ ⊗[R] _ ⊗[R] _ at f
    simp only [ModuleCat.hom_comp, ModuleCat.MonoidalCategory.carrier_of_tensorObj_of, hom_ofHom,
      LinearMap.coe_comp, Function.comp_apply] at f ⊢
    erw [lift_comp_lift_comp_rTensor_eq]
    congr
    exact (TensorProduct.assoc R (W ⟶ X) (X ⟶ Y) (Y ⟶ Z)).right_inv f
  homEquiv {X Y} := (ModuleCat.homEquiv.trans
      (LinearMap.ringLmapEquivSelf R R (X ⟶ Y)).toEquiv).symm
  homEquiv_id X := rfl
  homEquiv_comp {X Y Z} f g := by
    ext
    change (LinearMap.toSpanSingleton R (X ⟶ Z) (f ≫ g)) 1 =
      (lift (Linear.comp X Y Z))
        ((ModuleCat.Hom.hom
          (ModuleCat.ofHom (LinearMap.toSpanSingleton R (X ⟶ Y) f) ⊗
            ModuleCat.ofHom (LinearMap.toSpanSingleton R (Y ⟶ Z) g)))
          (1 ⊗ₜ 1))
    simp

end EnrichedOfLinear

noncomputable section LinearOfEnriched

variable {R : Type u} [CommRing R]
variable {C : Type u} [Category.{u} C] [EnrichedOrdinaryCategory (ModuleCat R) C]

variable (R)

abbrev addCommGroupEnrichedModuleCatHom (X Y : C) : AddCommGroup (X ⟶ Y) :=
  (eHomEquiv (V := ModuleCat R)).addCommGroup

instance moduleModuleCatHom {X Y : C} :
    letI : AddCommGroup (X ⟶ Y) := addCommGroupEnrichedModuleCatHom R X Y
    Module R (X ⟶ Y) :=
  EnrichedOrdinaryCategory.homEquiv.module R

abbrev preadditiveEnrichedModuleCat : Preadditive C where
  homGroup X Y := addCommGroupEnrichedModuleCatHom R X Y
  add_comp X Y Z f f' g := by
    apply (eHomEquiv (ModuleCat R)).injective
    simp [Equiv.add_def, eHomEquiv_comp, MonoidalPreadditive.add_tensor]
  comp_add X Y Z f g g' := by
    apply (eHomEquiv (ModuleCat R)).injective
    simp [Equiv.add_def, eHomEquiv_comp, MonoidalPreadditive.tensor_add]

variable {R}

example : MonoidalLinear R (ModuleCat R) := inferInstance

instance linearEnrichedModuleCat :
    letI : Preadditive C := preadditiveEnrichedModuleCat R
    Linear R C :=
  letI : Preadditive C := preadditiveEnrichedModuleCat R
  { smul_comp X Y Z r f g := by
      apply (eHomEquiv (ModuleCat R)).injective
      simp only [Equiv.smul_def]
      rw [eHomEquiv_comp, ← eHomEquiv, ← eHomEquiv]
      simp [eHomEquiv_comp]
    comp_smul X Y Z f r g := by
      apply (eHomEquiv (ModuleCat R)).injective
      simp only [Equiv.smul_def]
      rw [eHomEquiv_comp, ← eHomEquiv, ← eHomEquiv]
      simp [eHomEquiv_comp] }

end LinearOfEnriched

end CategoryTheory
