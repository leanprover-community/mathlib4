<<<<<<< HEAD
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Colimits

=======
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

>>>>>>> origin/homology-sequence-computation
universe v u

variable {R : Type u} [Ring R]

namespace CategoryTheory

open Limits

<<<<<<< HEAD
noncomputable instance {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    PreservesColimit (parallelPair f 0) (forget₂ (ModuleCat.{v} R) Ab) :=
  preservesColimitOfPreservesColimitCocone (ModuleCat.cokernelIsColimit f) (by
    let e : parallelPair ((forget₂ (ModuleCat.{v} R) Ab).map f) 0 ≅
        parallelPair f 0 ⋙ forget₂ _ _ :=
      parallelPair.ext (Iso.refl _) (Iso.refl _) (by aesop_cat) (by aesop_cat)
    refine' IsColimit.precomposeHomEquiv e _ _
    refine' IsColimit.ofIsoColimit
      (AddCommGroupCat.cokernelIsColimit ((forget₂ (ModuleCat.{v} R) Ab).map f)) _
    refine' Cofork.ext (Iso.refl _) (by aesop_cat))

namespace ShortComplex

variable (S : ShortComplex (ModuleCat.{v} R))

noncomputable instance : (forget₂ (ModuleCat.{v} R) Ab).PreservesHomology where

=======
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

>>>>>>> origin/homology-sequence-computation
@[simp]
lemma moduleCat_zero_apply (x : S.X₁) : S.g (S.f x) = 0 :=
  S.zero_apply x

lemma moduleCat_exact_iff :
    S.Exact ↔ ∀ (x₂ : S.X₂) (_ : S.g x₂ = 0), ∃ (x₁ : S.X₁), S.f x₁ = x₂ :=
<<<<<<< HEAD
  S.exact_iff_of_concrete_category
=======
  S.exact_iff_of_concreteCategory
>>>>>>> origin/homology-sequence-computation

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

<<<<<<< HEAD
@[simps]
def moduleCat_mk_of_ker_le_range {X₁ X₂ X₃ : ModuleCat.{v} R} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
=======
/-- Constructor for short complexes in `ModuleCat.{v} R` taking as inputs
morphisms `f` and `g` and the assumption `LinearMap.range f ≤ LinearMap.ker g`. -/
@[simps]
def moduleCatMkOfKerLERange {X₁ X₂ X₃ : ModuleCat.{v} R} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
>>>>>>> origin/homology-sequence-computation
    (hfg : LinearMap.range f ≤ LinearMap.ker g) : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk f g (by
    ext
    exact hfg ⟨_, rfl⟩)

<<<<<<< HEAD
lemma Exact.moduleCat_mk_of_range_eq_ker {X₁ X₂ X₃ : ModuleCat.{v} R}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (hfg : LinearMap.range f = LinearMap.ker g) :
    (moduleCat_mk_of_ker_le_range f g (by rw [hfg])).Exact := by
=======
lemma Exact.moduleCat_of_range_eq_ker {X₁ X₂ X₃ : ModuleCat.{v} R}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (hfg : LinearMap.range f = LinearMap.ker g) :
    (moduleCatMkOfKerLERange f g (by rw [hfg])).Exact := by
>>>>>>> origin/homology-sequence-computation
  simpa only [moduleCat_exact_iff_range_eq_ker] using hfg

variable (S)

<<<<<<< HEAD
=======
/-- The canonical linear map `S.X₁ →ₗ[R] LinearMap.ker S.g` induced by `S.f`. -/
@[simps]
>>>>>>> origin/homology-sequence-computation
def moduleCatToCycles : S.X₁ →ₗ[R] LinearMap.ker S.g where
  toFun x := ⟨S.f x, S.moduleCat_zero_apply x⟩
  map_add' x y := by aesop
  map_smul' a x := by aesop

<<<<<<< HEAD
=======
/-- The explicit left homology data of a short complex of modules that is
given by a kernel and a quotient given by the `LinearMap` API. -/
>>>>>>> origin/homology-sequence-computation
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

<<<<<<< HEAD
=======
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

>>>>>>> origin/homology-sequence-computation
lemma exact_iff_surjective_moduleCatToCycles :
    S.Exact ↔ Function.Surjective S.moduleCatToCycles := by
  rw [S.moduleCatLeftHomologyData.exact_iff_epi_f', moduleCatLeftHomologyData_f',
    ModuleCat.epi_iff_surjective]
  rfl

<<<<<<< HEAD
noncomputable def moduleCatCyclesIso : S.cycles ≅ ModuleCat.of R (LinearMap.ker S.g) :=
  S.moduleCatLeftHomologyData.cyclesIso

noncomputable def moduleCatHomologyIso :
    S.homology ≅
      ModuleCat.of R ((LinearMap.ker S.g) ⧸ LinearMap.range S.moduleCatToCycles) :=
  S.moduleCatLeftHomologyData.homologyIso

=======
>>>>>>> origin/homology-sequence-computation
end ShortComplex

end CategoryTheory
