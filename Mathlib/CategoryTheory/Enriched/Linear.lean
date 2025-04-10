/-
Copyright (c) 2025 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Equiv.TransferInstance
/-!
# Linear categories as `ModuleCat R`-enriched categories

-/

universe w v v' u u'

namespace CategoryTheory

open TensorProduct MonoidalCategory

section EnrichedOfLinear

variable {R : Type u} [CommRing R]
variable {C : Type u} [Category.{u} C] [Preadditive C] [Linear R C]

@[simp]
lemma aux6 {X Y : Type u} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] :
    (tensorObj (𝒞 := ModuleCat.moduleCategory R) (ModuleCat.of R X) (ModuleCat.of R Y)).carrier =
    X ⊗[R] Y := by
  rfl

@[simp]
lemma aux1 {X Y : C} {Z W : Type u} [AddCommGroup Z] [Module R Z]
    [AddCommGroup W] [Module R W] (f : Z →ₗ[R] W) :
    (ModuleCat.ofHom f ▷ ModuleCat.of R (X ⟶ Y)).hom = f.rTensor (X ⟶ Y) :=
  rfl

@[simp]
lemma aux1' {X Y : C} {Z W : Type u} [AddCommGroup Z] [Module R Z]
    [AddCommGroup W] [Module R W] (f : Z →ₗ[R] W) :
    (ModuleCat.of R (X ⟶ Y) ◁ ModuleCat.ofHom f).hom = f.lTensor (X ⟶ Y) :=
  rfl

lemma aux2 {X : ModuleCat R} (x : X) : (λ_ X).inv.hom x = (TensorProduct.lid R X).symm x :=
  rfl

lemma aux2' {X : ModuleCat R} (x : X) : (ρ_ X).inv.hom x = (TensorProduct.rid R X).symm x :=
  rfl

lemma lift_comp_lift_comp_rTensor_eq {W X Y Z : C} (f : ((W ⟶ X) ⊗[R] (X ⟶ Y)) ⊗[R] (Y ⟶ Z)) :
    lift (Linear.comp W Y Z) (((lift (Linear.comp W X Y)).rTensor (Y ⟶ Z)) f) =
      lift (Linear.comp W X Z)
        ((lift (Linear.comp X Y Z)).lTensor (W ⟶ X) ((TensorProduct.assoc R _ _ _) f)) :=
  TensorProduct.induction_on f rfl
    (fun fg _ => TensorProduct.induction_on fg (by simp) (by simp)
      (fun _ _ h₂ h₃ => by simp [add_tmul, LinearEquiv.map_add, ← h₂, ← h₃]))
    (fun _ _ h₂ h₃ => by simp [h₂, h₃, LinearEquiv.map_add])


open ModuleCat Hom

noncomputable instance : EnrichedOrdinaryCategory (ModuleCat R) C where
  Hom X Y := .of R (X ⟶ Y)
  id X := ModuleCat.ofHom <| (LinearMap.ringLmapEquivSelf R R (X ⟶ X)).symm (𝟙 X)
  comp X Y Z := ModuleCat.ofHom <| lift (Linear.comp X Y Z)
  id_comp X Y := by
    ext f
    simp only [LinearMap.ringLmapEquivSelf_symm_apply, ModuleCat.hom_comp, aux6, hom_ofHom,
      LinearMap.coe_comp, Function.comp_apply, ModuleCat.hom_id, LinearMap.id_coe, id_eq] at f ⊢
    rw [aux2, lid_symm_apply, aux1]
    erw [LinearMap.rTensor_tmul _ (LinearMap.smulRight (1 : R →ₗ[R] R) (𝟙 X)) f 1]
    simp
  comp_id X Y := by
    ext f
    simp only [LinearMap.ringLmapEquivSelf_symm_apply, ModuleCat.hom_comp, aux6, hom_ofHom,
      LinearMap.coe_comp, Function.comp_apply, ModuleCat.hom_id, LinearMap.id_coe, id_eq] at f ⊢
    rw [aux2', rid_symm_apply, aux1']
    erw [LinearMap.lTensor_tmul _ (LinearMap.smulRight (1 : R →ₗ[R] R) (𝟙 Y)) f 1]
    simp
  assoc W X Y Z := by
    ext f
    change _ ⊗[R] _ ⊗[R] _ at f
    simp only [ModuleCat.hom_comp, aux6, hom_ofHom, LinearMap.coe_comp, Function.comp_apply] at f ⊢
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

abbrev addCommGroupModuleCatHom {X Y : C} : AddCommGroup (X ⟶ Y) :=
  (EnrichedOrdinaryCategory.homEquiv (V := ModuleCat R)).addCommGroup

instance moduleModuleCatHom {X Y : C} :
    letI : AddCommGroup (X ⟶ Y) := addCommGroupModuleCatHom R
    Module R (X ⟶ Y) :=
  EnrichedOrdinaryCategory.homEquiv.module R

variable {X Y : C} (f g : X ⟶ Y) (r : R)

-- Can't check `f + g` here because `addCommGroupModuleCatHom` can't be made an instance
#check r • f

end LinearOfEnriched

end CategoryTheory
