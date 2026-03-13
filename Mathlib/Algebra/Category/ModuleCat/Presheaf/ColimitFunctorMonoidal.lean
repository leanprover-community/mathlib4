/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-!
# The colimit module of a presheaf of module on a cofiltered category is monoidal


-/

@[expose] public section

universe w v u

open CategoryTheory ModuleCat MonoidalCategory Limits
  Functor.LaxMonoidal Functor.OplaxMonoidal

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C]
  {R : Cᵒᵖ ⥤ CommRingCat.{w}} (cR : Cocone R)

noncomputable abbrev constFunctorOfCommRing :
    ModuleCat.{w} cR.pt ⥤ PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat) :=
  (constFunctor.{w} ((forget₂ _ RingCat).mapCocone cR))

open TensorProduct in
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

variable {cR} (hcR : IsColimit cR) [LocallySmall.{w} C]
  [IsCofiltered C] [InitiallySmall.{w} C]

attribute [local instance] FinallySmall.preservesColimitsOfShape_of_isFiltered

noncomputable abbrev colimitFunctorOfCommRing :
    PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat) ⥤ ModuleCat.{w} cR.pt :=
  colimitFunctor (isColimitOfPreserves (forget₂ _ RingCat) hcR)

noncomputable abbrev colimitAdjunctionOfCommRing :
    colimitFunctorOfCommRing.{w} hcR ⊣ constFunctorOfCommRing.{w} cR :=
  colimitAdjunction _

noncomputable instance : (colimitFunctorOfCommRing hcR).OplaxMonoidal :=
  (colimitAdjunctionOfCommRing hcR).leftAdjointOplaxMonoidal

instance : IsIso (η (colimitFunctorOfCommRing hcR)) := sorry

instance (F₁ F₂ : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)) :
    IsIso (δ (colimitFunctorOfCommRing hcR) F₁ F₂) := sorry

noncomputable instance : (colimitFunctorOfCommRing hcR).Monoidal :=
  Functor.Monoidal.ofOplaxMonoidal _

end PresheafOfModules
