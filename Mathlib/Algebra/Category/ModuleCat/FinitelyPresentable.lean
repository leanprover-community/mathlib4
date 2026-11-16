/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.CategoryTheory.Presentable.Limits
public import Mathlib.LinearAlgebra.Span.Basic

import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-!
# Characterization of finitely presentable objects in `ModuleCat`


-/

universe w

public section

open CategoryTheory Opposite

attribute [local instance] Cardinal.fact_isRegular_aleph0

namespace ModuleCat

variable (R : Type w) [Ring R]

/-- The forget functor `ModuleCat R ⥤ Type _` is corepresentable by `R` as a module over itself. -/
@[expose, simps! +dsimpLhs]
def corepresentableByForget : (forget (ModuleCat.{w} R)).CorepresentableBy (.of R R) where
  homEquiv :=
    { toFun f := f.hom 1
      invFun x := ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ x)
      left_inv _ := by cat_disch
      right_inv _ := by simp }

/-- The forget functor `ModuleCat R ⥤ Type _` is corepresentable by `R` as a module over itself. -/
@[expose, simps! +dsimpLhs]
def coyonedaObjIsoForget : coyoneda.obj (op (ModuleCat.of R R)) ≅ forget _ :=
  NatIso.ofComponents (fun M ↦ (corepresentableByForget R).homEquiv.toIso)

instance (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    (forget (ModuleCat.{w} R)).IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    have := isFiltered_of_isCardinalFiltered J κ
    infer_instance

instance : (forget (ModuleCat.{w} R)).IsAccessible.{w} where
  exists_cardinal := ⟨.aleph0, inferInstance, inferInstance⟩

instance (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    IsCardinalPresentable (ModuleCat.of R R) κ :=
  Functor.isCardinalAccessible_of_natIso (coyonedaObjIsoForget R).symm κ

example : IsFinitelyPresentable.{w} (ModuleCat.of R R) := inferInstance

instance (ι : Type*) [Finite ι] :
    IsFinitelyPresentable.{w} (ModuleCat.of R (ι → R)) := by
  sorry

variable {R} in
lemma isFinitelyPresentable_iff (M : ModuleCat.{w} R) :
    IsFinitelyPresentable.{w} M ↔ Module.FinitePresentation R M := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · sorry
  · obtain ⟨n, m, g, f, hg, h⟩ := Module.FinitePresentation.exists_fin' R M
    let S := ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
      (by ext; apply h.apply_apply_eq_zero)
    have : Epi S.g := by rwa [ModuleCat.epi_iff_surjective]
    apply +allowSynthFailures isCardinalPresentable_of_isColimit.{w} _
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr h).gIsCokernel
    · simp only [hasCardinalLT_aleph0_iff]
      infer_instance
    · rintro (_ | _)
      all_goals dsimp; infer_instance

instance (M : ModuleCat.{w} R) [Module.FinitePresentation R M] :
    IsFinitelyPresentable.{w} M := by
  rwa [isFinitelyPresentable_iff]

end ModuleCat
