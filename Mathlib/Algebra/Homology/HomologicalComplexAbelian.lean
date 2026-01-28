/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # THe category of homological complexes is abelian

If `C` is an abelian category, then `HomologicalComplex C c` is an abelian
category for any complex shape `c : ComplexShape ι`.

We also obtain that a short complex in `HomologicalComplex C c`
is exact (resp. short exact) iff degreewise it is so.

-/

public section

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {C ι : Type*} {c : ComplexShape ι} [Category* C] [Abelian C]

noncomputable instance : IsNormalEpiCategory (HomologicalComplex C c) := ⟨fun p _ =>
  ⟨NormalEpi.mk _ (kernel.ι p) (kernel.condition _)
    (isColimitOfEval _ _ (fun _ =>
      Abelian.isColimitMapCoconeOfCokernelCoforkOfπ _ _))⟩⟩

noncomputable instance : IsNormalMonoCategory (HomologicalComplex C c) := ⟨fun p _ =>
  ⟨NormalMono.mk _ (cokernel.π p) (cokernel.condition _)
    (isLimitOfEval _ _ (fun _ =>
      Abelian.isLimitMapConeOfKernelForkOfι _ _))⟩⟩

noncomputable instance : Abelian (HomologicalComplex C c) where

variable (S : ShortComplex (HomologicalComplex C c))

lemma exact_of_degreewise_exact (hS : ∀ (i : ι), (S.map (eval C c i)).Exact) :
    S.Exact := by
  simp only [ShortComplex.exact_iff_isZero_homology] at hS ⊢
  rw [IsZero.iff_id_eq_zero]
  ext i
  apply (IsZero.of_iso (hS i) (S.mapHomologyIso (eval C c i)).symm).eq_of_src

lemma shortExact_of_degreewise_shortExact
    (hS : ∀ (i : ι), (S.map (eval C c i)).ShortExact) :
    S.ShortExact where
  mono_f := mono_of_mono_f _ (fun i => (hS i).mono_f)
  epi_g := epi_of_epi_f _ (fun i => (hS i).epi_g)
  exact := exact_of_degreewise_exact S (fun i => (hS i).exact)

lemma exact_iff_degreewise_exact :
    S.Exact ↔ ∀ (i : ι), (S.map (eval C c i)).Exact := by
  constructor
  · intro hS i
    exact hS.map (eval C c i)
  · exact exact_of_degreewise_exact S

lemma shortExact_iff_degreewise_shortExact :
    S.ShortExact ↔ ∀ (i : ι), (S.map (eval C c i)).ShortExact := by
  constructor
  · intro hS i
    have := hS.mono_f
    have := hS.epi_g
    exact hS.map (eval C c i)
  · exact shortExact_of_degreewise_shortExact S

end HomologicalComplex

universe u v u' v'

namespace CategoryTheory

open Limits Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

variable (F : C ⥤ D) [F.Additive]

variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]

lemma Functor.mapHomologicalComplex_map_exact {ι : Type*} (c : ComplexShape ι)
    (S : ShortComplex (HomologicalComplex C c)) (hS : S.Exact) :
    (S.map (F.mapHomologicalComplex c)).Exact := by
  refine (HomologicalComplex.exact_iff_degreewise_exact _).mpr (fun i ↦ ?_)
  have : (F.mapHomologicalComplex c) ⋙ (HomologicalComplex.eval D c i) =
    (HomologicalComplex.eval C c i) ⋙ F := by aesop_cat
  simp_rw [← ShortComplex.map_comp, this, ShortComplex.map_comp]
  exact ((HomologicalComplex.exact_iff_degreewise_exact S).mp hS i).map F

instance {ι : Type*} (c : ComplexShape ι) : PreservesFiniteLimits (F.mapHomologicalComplex c) := by
  have := ((F.mapHomologicalComplex c).exact_tfae.out 1 3).mp
  exact (this (F.mapHomologicalComplex_map_exact c)).1

instance {ι : Type*} (c : ComplexShape ι) :
    PreservesFiniteColimits (F.mapHomologicalComplex c) := by
  have := ((F.mapHomologicalComplex c).exact_tfae.out 1 3).mp
  exact (this (F.mapHomologicalComplex_map_exact c)).2

end CategoryTheory
