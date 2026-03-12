/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-!
# The colimit module of a presheaf of module on a cofiltered category is monoidal


-/

@[expose] public section

universe w v u

open CategoryTheory ModuleCat MonoidalCategory Limits

-- to be moved
namespace ModuleCat

variable {R S : Type w} [CommRing R] [CommRing S] (f : R →+* S)

@[simp]
lemma extendsScalars_map_leftUnitor_inv_one_tmul
    (M : ModuleCat R) (m : M) :
    letI := f.toAlgebra
    (extendScalars f).map (λ_ M).inv ((1 : S) ⊗ₜ[R] m) = (1 : S) ⊗ₜ[R] (1 ⊗ₜ m) := rfl

@[simp]
lemma extendsScalars_map_rightUnitor_inv_one_tmul
    (M : ModuleCat R) (m : M) :
    letI := f.toAlgebra
    (extendScalars f).map (ρ_ M).inv ((1 : S) ⊗ₜ[R] m) = (1 : S) ⊗ₜ[R] (m ⊗ₜ 1) := rfl

@[simp]
lemma extendRestrictScalarsAdj_counit_apply_one_tmul (M : ModuleCat S) (m : M) :
    dsimp% (extendRestrictScalarsAdj f).counit.app M ((1 : S) ⊗ₜ[R] m) = m := by
  apply ExtendRestrictScalarsAdj.Counit.map_apply_one_tmul

open Functor.LaxMonoidal Functor.OplaxMonoidal TensorProduct

open ModuleCat.MonoidalCategory in
noncomputable instance : (extendScalars.{w} f).Monoidal :=
  letI : Algebra R S := f.toAlgebra
  Functor.CoreMonoidal.toMonoidal
    (.mk'
      (εIso := (AlgebraTensorModule.rid R S S).symm.toModuleIso)
      (μIso := fun M₁ M₂ ↦ (AlgebraTensorModule.distribBaseChange R S M₁ M₂).symm.toModuleIso)
      (μIso_inv_natural_left := fun {M₁ M₁'} g M₂ ↦
        ((extendRestrictScalarsAdj f).homEquiv _ _).injective
          (tensor_ext (fun _ _ ↦ rfl)))
      (μIso_inv_natural_right := fun {M₂ M₂'} M₁ g ↦
        ((extendRestrictScalarsAdj f).homEquiv _ _).injective
          (tensor_ext (fun _ _ ↦ rfl)))
      (oplax_associativity := fun M₁ M₂ M₃ ↦
        ((extendRestrictScalarsAdj f).homEquiv _ _).injective
          (tensor_ext₃' (fun _ _ _ ↦ rfl)))
      (oplax_left_unitality := fun M ↦ by
        ext m
        dsimp
        rw [MonoidalCategory.leftUnitor_inv_apply]
        erw [AlgebraTensorModule.distribBaseChange_tmul,
          MonoidalCategory.whiskerRight_apply,
          AlgebraTensorModule.rid_tmul]
        rw [one_smul]
        rfl)
      (oplax_right_unitality := fun M ↦ by
        ext m
        dsimp
        rw [MonoidalCategory.rightUnitor_inv_apply]
        erw [AlgebraTensorModule.distribBaseChange_tmul,
          MonoidalCategory.whiskerLeft_apply,
          AlgebraTensorModule.rid_tmul]
        rw [one_smul]
        rfl))

@[simp]
lemma extendScalars_δ_tmul (M₁ M₂ : ModuleCat R) (m₁ : M₁) (m₂ : M₂) :
    letI := f.toAlgebra
    dsimp% δ (extendScalars.{w} f) M₁ M₂ (((1 : S) ⊗ₜ[R] (m₁ ⊗ₜ[R] m₂) :)) =
      ((1 : S) ⊗ₜ[R] m₁) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m₂) :=
  rfl

noncomputable instance : (restrictScalars.{w} f).LaxMonoidal :=
  (extendRestrictScalarsAdj.{w} f).rightAdjointLaxMonoidal

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma restrictScalars_μ_tmul (M₁ M₂ : ModuleCat.{w} S) (m₁ : M₁) (m₂ : M₂) :
    dsimp% μ (restrictScalars f) M₁ M₂ (m₁ ⊗ₜ m₂) = m₁ ⊗ₜ m₂ := by
  dsimp [Adjunction.rightAdjointLaxMonoidal_μ]
  rw [extendRestrictScalarsAdj_homEquiv_apply]
  dsimp
  rw [extendScalars_δ_tmul, tensorHom_tmul,
    extendRestrictScalarsAdj_counit_apply_one_tmul,
    extendRestrictScalarsAdj_counit_apply_one_tmul]

end ModuleCat

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C]
  {R : Cᵒᵖ ⥤ CommRingCat.{w}} (cR : Cocone R)

noncomputable abbrev constFunctorOfCommRing :
    ModuleCat.{w} cR.pt ⥤ PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat) :=
  (constFunctor.{w} ((forget₂ _ RingCat).mapCocone cR))

open Functor.LaxMonoidal ModuleCat TensorProduct in
noncomputable instance : (constFunctorOfCommRing.{w} cR).LaxMonoidal where
  ε :=
    { app U := ε (restrictScalars (cR.ι.app U).hom)
      naturality {V U} f := by
        ext
        change (cR.ι.app U (R.map f 1) : cR.pt) * 1 = (cR.ι.app V 1 * 1 :)
        rw [mul_one, mul_one, ← cR.w f]
        rfl }
  μ F₁ F₂ :=
    { app U := μ (restrictScalars (cR.ι.app U).hom) _ _
      naturality {V U} f := by
        ext : 1
        letI aV : R.obj V →+* cR.pt := (cR.ι.app V).hom
        letI aU : R.obj U →+* cR.pt := (cR.ι.app U).hom
        letI := Module.compHom F₁ aV
        letI := Module.compHom F₂ aV
        letI := Module.compHom (F₁ ⊗[cR.pt] F₂) aU
        letI := Module.compHom (F₁ ⊗[cR.pt] F₂) (R.map f).hom
        apply TensorProduct.ext' (σ₁₂ := .id (R.obj V)) (P₂ := F₁ ⊗[cR.pt] F₂)
        intro (m₁ : F₁) (m₂ : F₂)
        change μ (restrictScalars (cR.ι.app U).hom) F₁ F₂ (m₁ ⊗ₜ m₂) =
          μ (restrictScalars (cR.ι.app V).hom) F₁ F₂ (m₁ ⊗ₜ m₂)
        rw [restrictScalars_μ_tmul, restrictScalars_μ_tmul]
        rfl }
  μ_natural_left _ _ := by
    ext U : 1
    apply μ_natural_left (ModuleCat.restrictScalars.{w} (cR.ι.app U).hom)
  μ_natural_right _ _ := by
    ext U : 1
    apply μ_natural_right (ModuleCat.restrictScalars.{w} (cR.ι.app U).hom)
  associativity _ _ _ := by
    ext U : 1
    apply associativity (ModuleCat.restrictScalars.{w} (cR.ι.app U).hom)
  left_unitality _ := by
    ext U : 1
    apply left_unitality (ModuleCat.restrictScalars.{w} (cR.ι.app U).hom)
  right_unitality _ := by
    ext U : 1
    apply right_unitality (ModuleCat.restrictScalars.{w} (cR.ι.app U).hom)

end PresheafOfModules
