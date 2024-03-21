/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.RingTheory.Kaehler

universe v u v₁ u₁

open CategoryTheory LinearMap Opposite

attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike

instance : HasForget₂ CommRingCat AddCommGroupCat where
  forget₂ :=
    { obj := fun R => AddCommGroupCat.of R.α
      map := fun {R R'} φ => AddCommGroupCat.ofHom (AddMonoidHom.mk' φ.toFun (by simp)) }

variable {C : Type u₁} [Category.{v₁} C]

namespace PresheafOfModules

abbrev smul {R : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{v} R) {X : Cᵒᵖ}
    (r : R.obj X) (m : M.obj X) : M.obj X := r • m

variable {R : Cᵒᵖ ⥤ CommRingCat.{u}} (M : PresheafOfModules.{u}
  (R ⋙ forget₂ CommRingCat RingCat))

structure AbsoluteDerivation where
  d : R ⋙ forget₂ _ AddCommGroupCat ⟶ M.presheaf
  d_one (X : Cᵒᵖ) : d.app X (1 : R.obj X) = 0
  d_mul {X : Cᵒᵖ} (a b : R.obj X) : d.app X (a * b) = M.smul a (d.app X b) + M.smul b (d.app X a)

variable (R)

noncomputable def absoluteDifferentialsBundledCore :
    BundledCorePresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) where
  obj X := ModuleCat.of (R.obj X) (Ω[(R.obj X)⁄ℤ])
  map {X Y} f := by
    letI := (R.map f).toAlgebra
    exact KaehlerDifferential.map ℤ ℤ (R.obj X) (R.obj Y)
  map_id X := by
    convert KaehlerDifferential.linearMap_ext ℤ (R.obj X) _ _ _
    intro x
    dsimp
    erw [ModuleCat.restrictScalarsId'_inv_apply, KaehlerDifferential.map_D, R.map_id]
    rfl
  map_comp {X Y Z} f g := by
    convert KaehlerDifferential.linearMap_ext ℤ (R.obj X) _ _ _
    intro x
    dsimp
    letI := (R.map f).toAlgebra
    letI := (R.map g).toAlgebra
    erw [KaehlerDifferential.map_D, ModuleCat.restrictScalarsComp'_inv_apply,
      ModuleCat.restrictScalars.map_apply,
      KaehlerDifferential.map_D ℤ ℤ (R.obj X) (R.obj Y),
      KaehlerDifferential.map_D ℤ ℤ (R.obj Y) (R.obj Z),
      R.map_comp]
    rfl

noncomputable abbrev absoluteDifferentials :
    PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) :=
  PresheafOfModules.mk'' (absoluteDifferentialsBundledCore R)

@[simp]
lemma absoluteDifferentials_presheaf_obj (X : Cᵒᵖ) :
    ((absoluteDifferentials R).presheaf.obj X : Type _) = Ω[(R.obj X)⁄ℤ] := rfl

noncomputable def absoluteDerivation : (absoluteDifferentials R).AbsoluteDerivation where
  d :=
    { app := fun X => AddMonoidHom.mk' (fun (x : R.obj X) => KaehlerDifferential.D ℤ (R.obj X) x)
        (by simp)
      naturality := fun X Y f => by
        ext x
        erw [KaehlerDifferential.map_D]
        rfl }
  d_one _ := by dsimp; simp
  d_mul _ _ := by dsimp; simp

end PresheafOfModules
