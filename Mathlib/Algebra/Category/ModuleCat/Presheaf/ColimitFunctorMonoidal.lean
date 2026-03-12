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

open CategoryTheory MonoidalCategory Limits

-- to be moved
namespace ModuleCat

variable {R S : Type w} [CommRing R] [CommRing S] (f : R →+* S)

open Functor.LaxMonoidal TensorProduct

noncomputable instance : (extendScalars.{w} f).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso :=
        letI : Algebra R S := f.toAlgebra
        (AlgebraTensorModule.rid R S S).symm.toModuleIso
      μIso M₁ M₂ :=
        letI : Algebra R S := f.toAlgebra
        (AlgebraTensorModule.distribBaseChange R S M₁ M₂).symm.toModuleIso
      μIso_hom_natural_left := sorry
      μIso_hom_natural_right := sorry
      associativity := sorry
      left_unitality := sorry
      right_unitality := sorry }

noncomputable instance : (restrictScalars.{w} f).LaxMonoidal :=
  (extendRestrictScalarsAdj.{w} f).rightAdjointLaxMonoidal

end ModuleCat

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C]
  {R : Cᵒᵖ ⥤ CommRingCat.{w}} (cR : Cocone R)

noncomputable abbrev constFunctorOfCommRing :
    ModuleCat.{w} cR.pt ⥤ PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat) :=
  (constFunctor.{w} ((forget₂ _ RingCat).mapCocone cR))

open Functor.LaxMonoidal ModuleCat in
noncomputable instance : (constFunctorOfCommRing.{w} cR).LaxMonoidal where
  ε :=
    { app U := ε (restrictScalars (cR.ι.app U).hom)
      naturality {V U} f := by
        dsimp
        sorry }
  μ F₁ F₂ :=
    { app U := μ (restrictScalars (cR.ι.app U).hom) _ _
      naturality := sorry }
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
