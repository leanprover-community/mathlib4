<<<<<<< HEAD
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.Algebra.Homology.Refinements

open CategoryTheory Category Limits Pretriangulated

variable {C : Type _} [Category C] [Abelian C]

namespace CochainComplex

open HomologicalComplex

namespace mappingCone

attribute [simp] comp_liftCycles_assoc

-- exactness of H^n K ⟶ H^n L ⟶ H^n cône
lemma homology_triangle_exact {K L : CochainComplex C ℤ}
    (φ : K ⟶ L) (n : ℤ) :
    (ShortComplex.mk ((homologyFunctor _ _ n).map φ)
      ((homologyFunctor _ _ n).map (inr φ)) (by
          dsimp
          rw [← homologyMap_comp, (inrCompHomotopy φ).homologyMap_eq,
            homologyMap_zero])).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  dsimp
  intro A x hx
  obtain ⟨A₁, π₁, hπ₁, z, hz, hz'⟩ :=
    L.eq_liftCycles_homologyπ_up_to_refinements x (n+1) (by simp)
  have hz'' := hz' =≫ homologyMap (inr φ) n
  simp [hx] at hz''
  replace hz'' := hz''.symm
  rw [liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements
    _ _ _ _ _ (n-1) (by simp)] at hz''
  obtain ⟨A₂, π₂, hπ₂, y, hy⟩ := hz''
  obtain ⟨y₁, y₂, hy₁₂⟩ := to_break _ y n (by rw [sub_add_cancel])
  cases hy₁₂
  simp [ext_to_iff _ _ (n+1) rfl] at hy
  refine' ⟨A₂, π₂ ≫ π₁, epi_comp _ _,
    K.liftCycles' y₁ (n+1) (by simp) hy.1 ≫ K.homologyπ n, _⟩
  simp [hz', hy.2]
  rw [liftCycles_comp_homologyπ_eq_iff_up_to_refinements _ _ _ _ _ _ _ (n-1) (by simp)]
  exact ⟨_, 𝟙 _, inferInstance, y₂, by simp⟩

end mappingCone

end CochainComplex
=======
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
>>>>>>> origin/derived-category

namespace HomotopyCategory

instance (n : ℤ) : (homologyFunctor C (ComplexShape.up ℤ) n).IsHomological :=
<<<<<<< HEAD
  Functor.IsHomological.mk' _ (by
    rintro T ⟨K, L, φ, ⟨e⟩⟩
    refine' ⟨_, e, _⟩
    refine' (ShortComplex.exact_iff_of_iso _).1
      (CochainComplex.mappingCone.homology_triangle_exact φ n)
    refine' ShortComplex.isoMk
      ((homologyFunctorFactors C (ComplexShape.up ℤ) n).app _).symm
      ((homologyFunctorFactors C (ComplexShape.up ℤ) n).app _).symm
      ((homologyFunctorFactors C (ComplexShape.up ℤ) n).app _).symm _ _
    all_goals
      dsimp
      erw [← NatTrans.naturality]
      rfl)
=======
  Functor.IsHomological.mk' _ (fun T hT => by
    rw [distinguished_iff_iso_trianglehOfDegreewiseSplit] at hT
    obtain ⟨S, σ, ⟨e⟩⟩ := hT
    have hS := HomologicalComplex.shortExact_of_degreewise_shortExact S
      (fun n => (σ n).shortExact)
    exact ⟨_, e, (ShortComplex.exact_iff_of_iso
      (S.mapNatIso (homologyFunctorFactors C (ComplexShape.up ℤ) n))).2 (hS.homology_exact₂ n)⟩)
>>>>>>> origin/derived-category

end HomotopyCategory
