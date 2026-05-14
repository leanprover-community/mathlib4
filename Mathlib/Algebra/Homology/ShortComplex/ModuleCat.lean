/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.CategoryTheory.Elementwise
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.SetLike

/-!
# Homology and exactness of short complexes of modules

In this file, the homology of a short complex `S` of abelian groups is identified
with the quotient of `LinearMap.ker S.g` by the image of the morphism
`S.moduleCatToCycles : S.X₁ →ₗ[R] LinearMap.ker S.g` induced by `S.f`.

-/

@[expose] public section

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

set_option backward.isDefEq.respectTransparency false in
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

@[simp]
lemma moduleCatLeftHomologyData_f'_hom :
    S.moduleCatLeftHomologyData.f'.hom = S.moduleCatToCycles := rfl

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

@[reassoc (attr := simp, elementwise)]
lemma moduleCatCyclesIso_inv_iCycles :
    S.moduleCatCyclesIso.inv ≫ S.iCycles = S.moduleCatLeftHomologyData.i :=
  S.moduleCatLeftHomologyData.cyclesIso_inv_comp_iCycles

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp, elementwise)]
lemma toCycles_moduleCatCyclesIso_hom :
    S.toCycles ≫ S.moduleCatCyclesIso.hom = S.moduleCatLeftHomologyData.f' := by
  simp [← cancel_mono S.moduleCatLeftHomologyData.i]

/-- Given a short complex `S` of modules, this is the isomorphism between the abstract `S.opcycles`
of the homology API and the more concrete description as `S.X₂ ⧸ LinearMap.range S.f.hom`. -/
noncomputable def moduleCatOpcyclesIso :
    S.opcycles ≅ ModuleCat.of R (S.X₂ ⧸ LinearMap.range S.f.hom) :=
  S.opcyclesIsoCokernel ≪≫ ModuleCat.cokernelIsoRangeQuotient _

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem pOpcycles_comp_moduleCatOpcyclesIso_hom :
    S.pOpcycles ≫ S.moduleCatOpcyclesIso.hom = ModuleCat.ofHom (Submodule.mkQ _) := by
  simp [moduleCatOpcyclesIso]

theorem moduleCat_pOpcycles_eq_iff (x y : S.X₂) :
    S.pOpcycles x = S.pOpcycles y ↔ x - y ∈ LinearMap.range S.f.hom :=
  Iff.trans ⟨fun h => by simpa using congr(S.moduleCatOpcyclesIso.hom $h),
    fun h => (ModuleCat.mono_iff_injective S.moduleCatOpcyclesIso.hom).1 inferInstance (by simpa)⟩
    (Submodule.Quotient.eq _)

theorem moduleCat_pOpcycles_eq_zero_iff (x : S.X₂) :
    S.pOpcycles x = 0 ↔ x ∈ LinearMap.range S.f.hom := by
  simpa using moduleCat_pOpcycles_eq_iff _ x 0

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

set_option backward.isDefEq.respectTransparency false in
lemma exact_iff_surjective_moduleCatToCycles :
    S.Exact ↔ Function.Surjective S.moduleCatToCycles := by
  simp [S.moduleCatLeftHomologyData.exact_iff_epi_f',
    ModuleCat.epi_iff_surjective, moduleCatLeftHomologyData_K]

end ShortComplex

end CategoryTheory

section

variable {M : Type v} [AddCommGroup M] [Module R M] {N : Type v} [AddCommGroup N] [Module R N]

open CategoryTheory

/-- Given a linear map `f : M → N`, we can obtain a short complex `0 → ker(f) → M → N`. -/
abbrev LinearMap.shortComplexKer (f : M →ₗ[R] N) : ShortComplex (ModuleCat.{v} R) where
  f := ModuleCat.ofHom.{v} (LinearMap.ker f).subtype
  g := ModuleCat.ofHom.{v} f
  zero := by ext; simp

theorem LinearMap.shortExact_shortComplexKer {f : M →ₗ[R] N} (h : Function.Surjective f) :
    f.shortComplexKer.ShortExact where
  exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    fun _ ↦ by simp [shortComplexKer]
  mono_f := (ModuleCat.mono_iff_injective _).mpr (LinearMap.ker f).injective_subtype
  epi_g := (ModuleCat.epi_iff_surjective _).mpr h

variable {L : Type v} [AddCommGroup L] [Module R L]

/-- The short complex in `ModuleCat` obtained from two linear map with composition equal to zero. -/
abbrev ModuleCat.shortComplexOfCompEqZero (f : M →ₗ[R] N) (g : N →ₗ[R] L) (eq0 : g.comp f = 0) :
    ShortComplex (ModuleCat.{v} R) where
  f := ModuleCat.ofHom f
  g := ModuleCat.ofHom g

lemma ModuleCat.shortComplex_exact (S : ShortComplex (ModuleCat.{v} R))
    (exac : Function.Exact S.f S.g) : S.Exact :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr exac

lemma ModuleCat.shortComplex_shortExact (S : ShortComplex (ModuleCat.{v} R))
    (exac : Function.Exact S.f S.g) (inj : Function.Injective S.f)
    (surj : Function.Surjective S.g) : S.ShortExact where
  exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr exac
  mono_f := (ModuleCat.mono_iff_injective _).mpr inj
  epi_g := (ModuleCat.epi_iff_surjective _).mpr surj

end
