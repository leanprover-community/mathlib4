/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.AlgebraicGeometry.Modules.Presheaf

/-!
# The category of sheaves of modules over a scheme

In this file, we define the abelian category of sheaves of modules
`X.Modules` over a scheme `X`.

-/

universe u

open CategoryTheory Opposite PrimeSpectrum

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-- The category of sheaves of modules over a scheme. -/
abbrev Scheme.Modules := SheafOfModules.{u} X.ringCatSheaf

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
noncomputable instance : Abelian X.Modules := inferInstance

variable (R : Type*) [CommRing R]

/-- The forgetful functor from `𝒪_{Spec R}` modules to sheaves of `R`-modules. -/
noncomputable
def SpecModulesToSheaf :
    (Spec (.of R)).Modules ⥤ TopCat.Sheaf (ModuleCat R) (Spec (.of R)) :=
  SheafOfModules.forgetToSheafModuleCat (Spec (.of R)).ringCatSheaf (op ⊤)
    (Limits.initialOpOfTerminal Limits.isTerminalTop) ⋙
  sheafCompose _ (ModuleCat.restrictScalars (StructureSheaf.globalSectionsIso R).hom.hom)

/-- The forgetful functor from `𝒪_{Spec R}` modules to sheaves of `R`-modules is fully faithful. -/
noncomputable
def SpecModulesToSheafFullyFaithful : (SpecModulesToSheaf R).FullyFaithful where
  preimage {M N} f := ⟨fun U ↦ ModuleCat.ofHom ⟨(f.1.app U).hom.toAddHom, by
    intro t m
    apply TopCat.Presheaf.IsSheaf.section_ext ((SpecModulesToSheaf R).obj N).2
    intro x hxU
    obtain ⟨a, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrU : basicOpen _ ≤ _⟩ :=
      isBasis_basic_opens.exists_subset_of_mem_open hxU U.unop.2
    refine ⟨_, hrU, hxr, ?_⟩
    refine Eq.trans ?_ (N.val.map_smul (homOfLE hrU).op t _).symm
    show N.1.map (homOfLE hrU).op (f.1.app _ _) = _ • N.1.map (homOfLE hrU).op (f.1.app _ _)
    have (x) : f.1.app _ (M.1.map (homOfLE hrU).op _) = N.1.map (homOfLE hrU).op (f.1.app _ x) :=
      congr($(f.1.naturality (homOfLE hrU).op).hom x)
    rw [← this, ← this, M.val.map_smul]
    generalize (Spec (.of R)).ringCatSheaf.val.map (homOfLE hrU).op t = t
    letI := Module.compHom (M.val.obj (op <| basicOpen r))
      (StructureSheaf.toOpen R (basicOpen r)).hom
    haveI : IsScalarTower R ((Spec.structureSheaf R).presheaf.obj (op <| basicOpen r))
      (M.val.obj (op <| basicOpen r)) := .of_algebraMap_smul fun _ _ ↦ rfl
    letI := Module.compHom (N.val.obj (op <| basicOpen r))
      (StructureSheaf.toOpen R (basicOpen r)).hom
    haveI : IsScalarTower R ((Spec.structureSheaf R).presheaf.obj (op <| basicOpen r))
      (N.val.obj (op <| basicOpen r)) := .of_algebraMap_smul fun _ _ ↦ rfl
    exact (IsLocalization.linearMap_compatibleSMul (.powers (M := R) r)
      ((Spec.structureSheaf R).presheaf.obj (op <| basicOpen r))
      (M.val.obj (op <| basicOpen r)) (N.val.obj (op <| basicOpen r))).map_smul
      (f.val.app _).hom _ _⟩, fun i ↦ by ext x; exact congr($(f.1.naturality i).hom x)⟩
  map_preimage f := rfl
  preimage_map f := rfl

end AlgebraicGeometry
