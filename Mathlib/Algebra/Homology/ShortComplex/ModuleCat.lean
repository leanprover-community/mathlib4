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
  ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g) hfg

variable (S : ShortComplex (ModuleCat.{v} R))

@[simp]
lemma moduleCat_zero_apply (x : S.X₁) : S.g (S.f x) = 0 :=
  S.zero_apply x

lemma moduleCat_exact_iff :
    S.Exact ↔ ∀ (x₂ : S.X₂) (_ : S.g x₂ = 0), ∃ (x₁ : S.X₁), S.f x₁ = x₂ :=
  S.exact_iff_of_concreteCategory

lemma moduleCat_exact_iff_ker_sub_range :
    S.Exact ↔ LinearMap.ker S.g ≤ LinearMap.range S.f := by
  rw [moduleCat_exact_iff]
  constructor
  · intro h x₂ hx₂
    exact h x₂ hx₂
  · intro h x₂ hx₂
    exact h hx₂

lemma moduleCat_exact_iff_range_eq_ker :
    S.Exact ↔ LinearMap.range S.f = LinearMap.ker S.g := by
  rw [moduleCat_exact_iff_ker_sub_range]
  constructor
  · intro h
    ext x
    constructor
    · rintro ⟨y, hy⟩
      rw [← hy]
      simp only [LinearMap.mem_ker, moduleCat_zero_apply]
    · intro hx
      exact h hx
  · intro h
    rw [h]

variable {S}

lemma Exact.moduleCat_range_eq_ker (hS : S.Exact) :
    LinearMap.range S.f = LinearMap.ker S.g := by
  simpa only [moduleCat_exact_iff_range_eq_ker] using hS

lemma ShortExact.moduleCat_injective_f (hS : S.ShortExact) :
    Function.Injective S.f :=
  hS.injective_f

lemma ShortExact.moduleCat_surjective_g (hS : S.ShortExact) :
    Function.Surjective S.g :=
  hS.surjective_g

/-- Constructor for short complexes in `ModuleCat.{v} R` taking as inputs
morphisms `f` and `g` and the assumption `LinearMap.range f ≤ LinearMap.ker g`. -/
@[simps]
def moduleCatMkOfKerLERange {X₁ X₂ X₃ : ModuleCat.{v} R} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (hfg : LinearMap.range f ≤ LinearMap.ker g) : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk f g (by
    ext
    exact hfg ⟨_, rfl⟩)

lemma Exact.moduleCat_of_range_eq_ker {X₁ X₂ X₃ : ModuleCat.{v} R}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (hfg : LinearMap.range f = LinearMap.ker g) :
    (moduleCatMkOfKerLERange f g (by rw [hfg])).Exact := by
  simpa only [moduleCat_exact_iff_range_eq_ker] using hfg

variable (S)

/-- The canonical linear map `S.X₁ →ₗ[R] LinearMap.ker S.g` induced by `S.f`. -/
@[simps]
def moduleCatToCycles : S.X₁ →ₗ[R] LinearMap.ker S.g where
  toFun x := ⟨S.f x, S.moduleCat_zero_apply x⟩
  map_add' x y := by aesop
  map_smul' a x := by aesop

/-- The explicit left homology data of a short complex of modules that is
given by a kernel and a quotient given by the `LinearMap` API. -/
@[simps]
def moduleCatLeftHomologyData : S.LeftHomologyData where
  K := ModuleCat.of R (LinearMap.ker S.g)
  H := ModuleCat.of R (LinearMap.ker S.g ⧸ LinearMap.range S.moduleCatToCycles)
  i := (LinearMap.ker S.g).subtype
  π := (LinearMap.range S.moduleCatToCycles).mkQ
  wi := by
    ext ⟨_, hx⟩
    exact hx
  hi := ModuleCat.kernelIsLimit _
  wπ := by
    ext (x : S.X₁)
    dsimp
    erw [Submodule.Quotient.mk_eq_zero]
    rw [LinearMap.mem_range]
    apply exists_apply_eq_apply
  hπ := ModuleCat.cokernelIsColimit (ModuleCat.ofHom S.moduleCatToCycles)

@[simp]
lemma moduleCatLeftHomologyData_f' :
    S.moduleCatLeftHomologyData.f' = S.moduleCatToCycles := rfl

/-- Given a short complex `S` of modules, this is the isomorphism between
the abstract `S.cycles` of the homology API and the more concrete description as
`LinearMap.ker S.g`. -/
noncomputable def moduleCatCyclesIso : S.cycles ≅ ModuleCat.of R (LinearMap.ker S.g) :=
  S.moduleCatLeftHomologyData.cyclesIso

/-- Given a short complex `S` of modules, this is the isomorphism between
the abstract `S.homology` of the homology API and the more explicit
quotient of `LinearMap.ker S.g` by the image of
`S.moduleCatToCycles : S.X₁ →ₗ[R] LinearMap.ker S.g`. -/
noncomputable def moduleCatHomologyIso :
    S.homology ≅
      ModuleCat.of R ((LinearMap.ker S.g) ⧸ LinearMap.range S.moduleCatToCycles) :=
  S.moduleCatLeftHomologyData.homologyIso

lemma exact_iff_surjective_moduleCatToCycles :
    S.Exact ↔ Function.Surjective S.moduleCatToCycles := by
  rw [S.moduleCatLeftHomologyData.exact_iff_epi_f', moduleCatLeftHomologyData_f',
    ModuleCat.epi_iff_surjective]
  rfl

end ShortComplex

end CategoryTheory
