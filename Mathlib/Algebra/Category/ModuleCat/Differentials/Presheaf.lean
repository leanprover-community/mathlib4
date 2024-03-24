/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.RingTheory.Kaehler

/-!
# The presheaf of differentials of a presheaf of modules

-/

universe v u v₁ u₁

open CategoryTheory LinearMap Opposite

attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike

instance : HasForget₂ CommRingCat AddCommGroupCat where
  forget₂ :=
    { obj := fun R => AddCommGroupCat.of R.α
      map := fun {R R'} φ => AddCommGroupCat.ofHom (AddMonoidHom.mk' φ.toFun (by simp)) }

lemma ModuleCat.comp_apply {R : Type*} [Ring R] {M₁ M₂ M₃ : ModuleCat R} (f : M₁ ⟶ M₂)
    (g : M₂ ⟶ M₃) (x : M₁) :
    (f ≫ g) x = g (f x) := rfl

variable {C : Type u₁} [Category.{v₁} C]

namespace PresheafOfModules

abbrev smul {R : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{v} R) {X : Cᵒᵖ}
    (r : R.obj X) (m : M.obj X) : M.obj X := r • m

variable {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

structure AbsoluteDerivation where
  d {X : Cᵒᵖ} : R.obj X →+ M.obj X
  d_one (X : Cᵒᵖ) : d (X := X) 1 = 0 := by aesop_cat
  d_mul {X : Cᵒᵖ} (a b : R.obj X) : d (a * b) = a • d b + b • d a := by aesop_cat
  d_map {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : R.obj X) :
    d (R.map f x) = M.presheaf.map f (d x) := by aesop_cat

namespace AbsoluteDerivation

variable {M}
variable (d : M.AbsoluteDerivation)

attribute [simp] d_one d_mul d_map

variable {M' : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)} (f : M ⟶ M')

def postComp : AbsoluteDerivation M' where
  d {X} := (f.app X).toAddMonoidHom.comp d.d
  d_map {X Y} g x := by
    dsimp
    rw [d_map, naturality_apply]

structure Universal where
  desc {M' : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (d' : M'.AbsoluteDerivation) : M ⟶ M'
  fac {M' : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (d' : M'.AbsoluteDerivation) : d.postComp (desc d') = d'
  uniq {M' : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (d' : M'.AbsoluteDerivation) (φ : M ⟶ M') (hφ : d.postComp φ = d') :
      φ = desc d'

namespace Universal

variable {d}
variable (hR : d.Universal)

@[simps]
def homEquiv (M' : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    (M ⟶ M') ≃ M'.AbsoluteDerivation where
  toFun φ := d.postComp φ
  invFun d' := hR.desc d'
  left_inv φ := (hR.uniq _ φ rfl).symm
  right_inv d' := hR.fac d'

end Universal

end AbsoluteDerivation

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
    erw [ModuleCat.restrictScalarsId'App_inv_apply]
    rw [KaehlerDifferential.map_D, R.map_id, Algebra.id.map_eq_id, RingHom.id_apply]
  map_comp {X Y Z} f g := by
    convert KaehlerDifferential.linearMap_ext ℤ (R.obj X) _ _ _
    intro x
    letI := (R.map f).toAlgebra
    letI := (R.map g).toAlgebra
    dsimp
    erw [ModuleCat.comp_apply, ModuleCat.comp_apply]
    dsimp
    rw [KaehlerDifferential.map_D,
      ModuleCat.restrictScalarsComp'App_inv_apply]
    erw [KaehlerDifferential.map_D ℤ ℤ (R.obj X) (R.obj Y),
      KaehlerDifferential.map_D ℤ ℤ (R.obj Y) (R.obj Z), R.map_comp]
    rfl

noncomputable def absoluteDifferentials :
    PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) :=
  PresheafOfModules.mk'' (absoluteDifferentialsBundledCore R)

lemma absoluteDifferentials_presheaf_obj (X : Cᵒᵖ) :
    (absoluteDifferentials R).presheaf.obj X = AddCommGroupCat.of (Ω[(R.obj X)⁄ℤ]) := rfl

lemma absoluteDifferentials_presheaf_map_apply {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : Ω[(R.obj X)⁄ℤ]) :
    (absoluteDifferentials R).presheaf.map f x =
      letI := (R.map f).toAlgebra
      KaehlerDifferential.map ℤ ℤ (R.obj X) (R.obj Y) x := rfl

@[simp]
lemma absoluteDifferentials_presheaf_map_apply_d {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : R.obj X) :
    (absoluteDifferentials R).presheaf.map f (KaehlerDifferential.D ℤ _ x) =
      KaehlerDifferential.D ℤ _ (R.map f x) := by
  letI := (R.map f).toAlgebra
  rw [absoluteDifferentials_presheaf_map_apply]
  apply KaehlerDifferential.map_D

noncomputable def absoluteDerivation : (absoluteDifferentials R).AbsoluteDerivation where
  d {X} := AddMonoidHom.mk' (fun x => KaehlerDifferential.D ℤ (R.obj X) x) (by simp)
  d_one := by dsimp; simp
  d_mul := by dsimp; simp
  d_map {X Y} f x := ((absoluteDifferentials_presheaf_map_apply_d R f x)).symm

proof_wanted absoluteDerivationUniversal : Nonempty (absoluteDerivation R).Universal

end PresheafOfModules
