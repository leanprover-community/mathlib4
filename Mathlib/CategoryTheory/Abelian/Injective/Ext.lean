/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.Injective.Extend

/-!
# Computing `Ext` using an injective resolution

-/

@[expose] public section

universe w v u

open CategoryTheory CochainComplex HomComplex Abelian Localization

def CochainComplex.HomComplex.equivOfIsKInjective
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : CochainComplex C ℤ} [L.IsKInjective] {n : ℤ}
    [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ K L] :
    CohomologyClass K L n ≃
      SmallShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ) ) K L n := sorry

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

namespace InjectiveResolution

variable {X Y : C} (R : InjectiveResolution Y) {n : ℕ}

instance : R.cochainComplex.IsKInjective := isKInjective_of_injective _ 0

-- should be generalized as a lemma
instance (K L : CochainComplex C ℤ) [K.IsGE 0] [K.IsLE 0] [L.IsGE 0] [L.IsLE 0] :
    HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso _ _) ℤ K L := sorry

noncomputable def extEquivCohomologyClass :
    Ext X Y n ≃ CohomologyClass ((singleFunctor C 0).obj X) R.cochainComplex n := by
  have hι' : HomologicalComplex.quasiIso C (ComplexShape.up ℤ) R.ι' := by
    simp only [HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  exact (SmallShiftedHom.postcompEquiv.{w} R.ι'
      (by rw [HomologicalComplex.mem_quasiIso_iff]; infer_instance)).trans
    CochainComplex.HomComplex.equivOfIsKInjective.{w}.symm

/-- Given an injective resolution `R` of an object `Y` of an abelian category,
this is a constructor for elements in `Ext X Y n` which takes as an input
a "cocycle" `f : X ⟶ R.cocomplex.X n`. -/
noncomputable def extMk {n : ℕ} (f : X ⟶ R.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0) :
    Ext X Y n :=
  R.extEquivCohomologyClass.symm
    (.mk (Cocycle.fromSingleMk (f ≫ (R.cochainComplexXIso n n rfl).inv) (zero_add _)
      m (by cutsat) (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hf])))

end InjectiveResolution

end CategoryTheory
