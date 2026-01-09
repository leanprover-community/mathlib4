/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.CategoryTheory.Localization.SmallShiftedHom

/-!
# Cohomology of `HomComplex` and morphisms in the derived category

Let `K` and `L` be two cochain complexes in an abelian category `C`.
Given a class `x : HomComplex.CohomologyClass K L n`, we construct an
element in the type
`SmallShiftedHom (HomologicalComplex.quasiIso C (.up ℤ)) K L n`, and
compute its image as a morphism `Q.obj K ⟶ (Q.obj L)⟦n⟧` in the
derived category when `x` is given as the class of a cocycle.

-/

@[expose] public section

universe w v u

open CategoryTheory Localization

namespace CochainComplex.HomComplex.CohomologyClass

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K L : CochainComplex C ℤ} {n : ℤ}
  [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ K L]

/-- Given `x : CohomologyClass K L n`, this is the element in the type
`SmallShiftedHom` relatively to quasi-isomorphisms that is associated
to the `x`. -/
noncomputable def toSmallShiftedHom (x : CohomologyClass K L n) :
    SmallShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) K L n :=
  Quotient.lift (fun y ↦ SmallShiftedHom.mk _ (Cocycle.equivHomShift.symm y)) (by
    letI := HasDerivedCategory.standard C
    intro y₁ y₂ h
    refine (SmallShiftedHom.equiv _ DerivedCategory.Q).injective ?_
    simp only [SmallShiftedHom.equiv_mk, ShiftedHom.map]
    rw [cancel_mono, DerivedCategory.Q_map_eq_of_homotopy]
    apply HomotopyCategory.homotopyOfEq
    rw [← toHom_mk, ← toHom_mk]
    congr 1
    exact Quotient.sound h) x

lemma toSmallShiftedHom_mk (x : Cocycle K L n) :
    (mk x).toSmallShiftedHom =
      SmallShiftedHom.mk _ (Cocycle.equivHomShift.symm x) := rfl

@[simp]
lemma equiv_toSmallShiftedHom_mk [HasDerivedCategory C] (x : Cocycle K L n) :
    SmallShiftedHom.equiv _ DerivedCategory.Q (mk x).toSmallShiftedHom =
      ShiftedHom.map (Cocycle.equivHomShift.symm x) DerivedCategory.Q := by
  simp [toSmallShiftedHom_mk]

end CochainComplex.HomComplex.CohomologyClass
