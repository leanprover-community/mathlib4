/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Homology and exactness of short complexes of modules

In this file, the homology of a short complex `S` of abelian groups is identified
with the quotient of `LinearMap.ker S.g` by the image of the morphism
`S.moduleCatToCycles : S.X₁ →ₗ[R] LinearMap.ker S.g` induced by `S.f`.

-/

universe v u

variable {R : Type u} [Ring R]

namespace CategoryTheory

open Limits

namespace ShortComplex

noncomputable instance : (forget₂ (ModuleCat.{v} R) Ab).PreservesHomology where

/-- Constructor for short complexes in `ModuleCat.{v} R` taking as inputs
linear maps `f` and `g` and the vanishing of their composition. -/
@[simps]
def moduleCatMk {X₁ X₂ X₃ : Type v} [AddCommGroup X₁] [AddCommGroup X₂] [AddCommGroup X₃]
    [Module R X₁] [Module R X₂] [Module R X₃] (f : X₁ →ₗ[R] X₂) (g : X₂ →ₗ[R] X₃)
    (hfg : g.comp f = 0) : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g) (ModuleCat.hom_ext hfg)

variable (S : ShortComplex (ModuleCat.{v} R))

@[simp]
lemma moduleCat_zero_apply (x : S.X₁) : S.g (S.f x) = 0 :=
  S.zero_apply x

lemma moduleCat_exact_iff :
    S.Exact ↔ ∀ (x₂ : S.X₂) (_ : S.g x₂ = 0), ∃ (x₁ : S.X₁), S.f x₁ = x₂ :=
  S.exact_iff_of_hasForget

lemma moduleCat_exact_iff_ker_sub_range :
    S.Exact ↔ LinearMap.ker S.g.hom ≤ LinearMap.range S.f.hom := by
  rw [moduleCat_exact_iff]
  aesop

lemma moduleCat_exact_iff_range_eq_ker :
    S.Exact ↔ LinearMap.range S.f.hom = LinearMap.ker S.g.hom := by
  rw [moduleCat_exact_iff_ker_sub_range]
  aesop

variable {S}

lemma Exact.moduleCat_range_eq_ker (hS : S.Exact) :
    LinearMap.range S.f.hom = LinearMap.ker S.g.hom := by
  simpa only [moduleCat_exact_iff_range_eq_ker] using hS

lemma ShortExact.moduleCat_injective_f (hS : S.ShortExact) :
    Function.Injective S.f :=
  hS.injective_f

lemma ShortExact.moduleCat_surjective_g (hS : S.ShortExact) :
    Function.Surjective S.g :=
  hS.surjective_g

variable (S)

lemma ShortExact.moduleCat_exact_iff_function_exact :
    S.Exact ↔ Function.Exact S.f S.g := by
  rw [moduleCat_exact_iff_range_eq_ker, LinearMap.exact_iff]
  tauto

/-- Constructor for short complexes in `ModuleCat.{v} R` taking as inputs
morphisms `f` and `g` and the assumption `LinearMap.range f ≤ LinearMap.ker g`. -/
@[simps]
def moduleCatMkOfKerLERange {X₁ X₂ X₃ : ModuleCat.{v} R} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (hfg : LinearMap.range f.hom ≤ LinearMap.ker g.hom) : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk f g (by aesop)

lemma Exact.moduleCat_of_range_eq_ker {X₁ X₂ X₃ : ModuleCat.{v} R}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (hfg : LinearMap.range f.hom = LinearMap.ker g.hom) :
    (moduleCatMkOfKerLERange f g (by rw [hfg])).Exact := by
  simpa only [moduleCat_exact_iff_range_eq_ker] using hfg

/-- The canonical linear map `S.X₁ →ₗ[R] LinearMap.ker S.g` induced by `S.f`. -/
abbrev moduleCatToCycles : S.X₁ →ₗ[R] LinearMap.ker S.g.hom :=
  S.f.hom.codRestrict _ <| S.moduleCat_zero_apply

/-- The explicit left homology data of a short complex of modules that is
given by a kernel and a quotient given by the `LinearMap` API. The projections to `K` and `H` are
not simp lemmas because the generic lemmas about `LeftHomologyData` are more useful here. -/
@[simps! K H i_hom π_hom]
def moduleCatLeftHomologyData : S.LeftHomologyData where
  K := ModuleCat.of R (LinearMap.ker S.g.hom)
  H := ModuleCat.of R (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
  i := ModuleCat.ofHom (LinearMap.ker S.g.hom).subtype
  π := ModuleCat.ofHom (LinearMap.range S.moduleCatToCycles).mkQ
  wi := by aesop
  hi := ModuleCat.kernelIsLimit _
  wπ := by aesop
  hπ := ModuleCat.cokernelIsColimit (ModuleCat.ofHom S.moduleCatToCycles)

/-- The homology of a short complex of modules as a concrete quotient. -/
@[deprecated "This abbreviation is now inlined" (since := "2025-05-14")]
abbrev moduleCatHomology := S.moduleCatLeftHomologyData.H

/-- The natural projection map to the homology of a short complex of modules as a
concrete quotient. -/
@[deprecated "This abbreviation is now inlined" (since := "2025-05-14")]
abbrev moduleCatHomologyπ := S.moduleCatLeftHomologyData.π

@[deprecated (since := "2025-05-09")]
alias moduleCatLeftHomologyData_i := moduleCatLeftHomologyData_i_hom

@[deprecated (since := "2025-05-09")]
alias moduleCatLeftHomologyData_π := moduleCatLeftHomologyData_π_hom

@[simp]
lemma moduleCatLeftHomologyData_f'_hom :
    S.moduleCatLeftHomologyData.f'.hom = S.moduleCatToCycles := rfl

@[deprecated (since := "2025-05-09")]
alias moduleCatLeftHomologyData_f' := moduleCatLeftHomologyData_f'_hom

@[simp]
lemma moduleCatLeftHomologyData_descH_hom {M : ModuleCat R}
    (φ : S.moduleCatLeftHomologyData.K ⟶ M) (h : S.moduleCatLeftHomologyData.f' ≫ φ = 0) :
    (S.moduleCatLeftHomologyData.descH φ h).hom =
      (LinearMap.range <| ModuleCat.Hom.hom _).liftQ
         φ.hom (LinearMap.range_le_ker_iff.2 <| ModuleCat.hom_ext_iff.1 h) := rfl

@[simp]
lemma moduleCatLeftHomologyData_liftK_hom {M : ModuleCat R} (φ : M ⟶ S.X₂) (h : φ ≫ S.g = 0) :
    (S.moduleCatLeftHomologyData.liftK φ h).hom =
      φ.hom.codRestrict (LinearMap.ker S.g.hom) (fun m => congr($h m)) := rfl

/-- Given a short complex `S` of modules, this is the isomorphism between
the abstract `S.cycles` of the homology API and the more concrete description as
`LinearMap.ker S.g`. -/
noncomputable def moduleCatCyclesIso : S.cycles ≅ S.moduleCatLeftHomologyData.K :=
  S.moduleCatLeftHomologyData.cyclesIso

@[reassoc (attr := simp, elementwise)]
lemma moduleCatCyclesIso_hom_i :
    S.moduleCatCyclesIso.hom ≫ S.moduleCatLeftHomologyData.i = S.iCycles :=
  S.moduleCatLeftHomologyData.cyclesIso_hom_comp_i

@[deprecated (since := "2025-05-09")]
alias moduleCatCyclesIso_hom_subtype := moduleCatCyclesIso_hom_i

@[reassoc (attr := simp, elementwise)]
lemma moduleCatCyclesIso_inv_iCycles :
    S.moduleCatCyclesIso.inv ≫ S.iCycles = S.moduleCatLeftHomologyData.i :=
  S.moduleCatLeftHomologyData.cyclesIso_inv_comp_iCycles

@[reassoc (attr := simp, elementwise)]
lemma toCycles_moduleCatCyclesIso_hom :
    S.toCycles ≫ S.moduleCatCyclesIso.hom = S.moduleCatLeftHomologyData.f' := by
  simp [← cancel_mono S.moduleCatLeftHomologyData.i]

/-- Given a short complex `S` of modules, this is the isomorphism between
the abstract `S.homology` of the homology API and the more explicit
quotient of `LinearMap.ker S.g` by the image of
`S.moduleCatToCycles : S.X₁ →ₗ[R] LinearMap.ker S.g`. -/
noncomputable def moduleCatHomologyIso :
    S.homology ≅ S.moduleCatLeftHomologyData.H :=
  S.moduleCatLeftHomologyData.homologyIso

@[reassoc (attr := simp, elementwise)]
lemma π_moduleCatCyclesIso_hom :
    S.homologyπ ≫ S.moduleCatHomologyIso.hom =
      S.moduleCatCyclesIso.hom ≫ S.moduleCatLeftHomologyData.π :=
  S.moduleCatLeftHomologyData.homologyπ_comp_homologyIso_hom

@[reassoc (attr := simp, elementwise)]
lemma moduleCatCyclesIso_inv_π :
    S.moduleCatCyclesIso.inv ≫ S.homologyπ =
       S.moduleCatLeftHomologyData.π ≫ S.moduleCatHomologyIso.inv :=
  S.moduleCatLeftHomologyData.π_comp_homologyIso_inv

lemma exact_iff_surjective_moduleCatToCycles :
    S.Exact ↔ Function.Surjective S.moduleCatToCycles := by
  simp [S.moduleCatLeftHomologyData.exact_iff_epi_f',
    ModuleCat.epi_iff_surjective, moduleCatLeftHomologyData_K]

end ShortComplex

end CategoryTheory
