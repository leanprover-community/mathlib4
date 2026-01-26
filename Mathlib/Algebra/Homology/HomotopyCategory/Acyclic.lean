/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.Localization

/-!
# The triangulated subcategory of acyclic complex in the homotopy category

In this file, we define the triangulated subcategory
`HomotopyCategory.subcategoryAcyclic C` of the homotopy category of
cochain complexes in an abelian category `C`.
In the lemma `HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W` we obtain
that the class of quasiisomorphisms `HomotopyCategory.quasiIso C (ComplexShape.up ℤ)`
consists of morphisms whose cone belongs to the triangulated subcategory
`HomotopyCategory.subcategoryAcyclic C` of acyclic complexes.

-/

@[expose] public section

universe v u

open CategoryTheory Limits Pretriangulated

variable (C : Type u) [Category.{v} C] [Abelian C]

namespace HomotopyCategory

/-- The triangulated subcategory of `HomotopyCategory C (ComplexShape.up ℤ)` consisting
of acyclic complexes. -/
def subcategoryAcyclic : ObjectProperty (HomotopyCategory C (ComplexShape.up ℤ)) :=
  (homologyFunctor C (ComplexShape.up ℤ) 0).homologicalKernel

instance : (subcategoryAcyclic C).IsTriangulated := by
  dsimp [subcategoryAcyclic]
  infer_instance

instance : (subcategoryAcyclic C).IsClosedUnderIsomorphisms := by
  dsimp [subcategoryAcyclic]
  infer_instance

variable {C}

lemma mem_subcategoryAcyclic_iff (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    subcategoryAcyclic C X ↔ ∀ (n : ℤ), IsZero ((homologyFunctor _ _ n).obj X) :=
  Functor.mem_homologicalKernel_iff _ X

lemma quotient_obj_mem_subcategoryAcyclic_iff_exactAt (K : CochainComplex C ℤ) :
    subcategoryAcyclic C ((quotient _ _).obj K) ↔ ∀ (n : ℤ), K.ExactAt n := by
  rw [mem_subcategoryAcyclic_iff]
  refine forall_congr' (fun n => ?_)
  simp only [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((homologyFunctorFactors C (ComplexShape.up ℤ) n).app K).isZero_iff

lemma quotient_obj_mem_subcategoryAcyclic_iff_acyclic (K : CochainComplex C ℤ) :
    subcategoryAcyclic C ((quotient _ _).obj K) ↔ K.Acyclic :=
  quotient_obj_mem_subcategoryAcyclic_iff_exactAt _

variable (C)

lemma quasiIso_eq_subcategoryAcyclic_W :
    quasiIso C (ComplexShape.up ℤ) = (subcategoryAcyclic C).trW := by
  ext K L f
  exact ((homologyFunctor C (ComplexShape.up ℤ) 0).mem_homologicalKernel_trW_iff f).symm

end HomotopyCategory
