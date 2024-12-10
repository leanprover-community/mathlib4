/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

/-! The homological functor

In this file, it is shown that if `C` is an abelian category,
then `homologyFunctor C (ComplexShape.up ℤ) n` is a homological functor
`HomotopyCategory C (ComplexShape.up ℤ) ⥤ C`. As distinguished triangles
in the homotopy category can be characterized in terms of degreewise split
short exact sequences of cochain complexes, this follows from the homology
sequence of a short exact sequences of homological complexes.

-/

open CategoryTheory

variable {C : Type*} [Category C] [Abelian C]

namespace HomotopyCategory

instance (n : ℤ) : (homologyFunctor C (ComplexShape.up ℤ) n).IsHomological :=
  Functor.IsHomological.mk' _ (fun T hT => by
    rw [distinguished_iff_iso_trianglehOfDegreewiseSplit] at hT
    obtain ⟨S, σ, ⟨e⟩⟩ := hT
    have hS := HomologicalComplex.shortExact_of_degreewise_shortExact S
      (fun n => (σ n).shortExact)
    exact ⟨_, e, (ShortComplex.exact_iff_of_iso
      (S.mapNatIso (homologyFunctorFactors C (ComplexShape.up ℤ) n))).2 (hS.homology_exact₂ n)⟩)

end HomotopyCategory
