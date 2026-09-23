/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Adam Topaz, Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.Restriction
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import Mathlib.CategoryTheory.Linear.Yoneda

/-!
# ...

-/

universe v u

@[expose] public section

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace ChainComplex

/-- Given a chain complex `X` and an object `Y`, this is the cochain complex
which in degree `i` consists of the module of morphisms `X.X i ⟶ Y`. -/
@[simps! X d, implicit_reducible]
def linearYonedaObj
    {α : Type*} [AddRightCancelSemigroup α] [One α]
    (X : ChainComplex C α) (A : Type*) [Ring A] [Linear A C] (Y : C) :
    CochainComplex (ModuleCat A) α :=
  ((((linearYoneda A C).obj Y).rightOp.mapHomologicalComplex _).obj X).unop

open CochainComplex.HomComplex

variable (K : ChainComplex C ℕ) (R : Type*) [Ring R] [Linear R C] (Y : C)

def φ (n : ℤ) : ℤˣ := sorry

noncomputable def linearYonedaObjXIso (n : ℤ) (k : ℕ) (h : k = n := by lia) :
    (K.linearYonedaObj R Y).X k ≅
      (CochainComplex.linearHomComplex R (K.extend ComplexShape.embeddingDownNat)
        ((CochainComplex.singleFunctor C 0).obj Y)).X n :=
  φ n • LinearEquiv.toModuleIso
    ((Linear.homCongr R (HomologicalComplex.extendXIso K ComplexShape.embeddingDownNat
        (by simpa)).symm (Iso.refl Y)).trans
      (Cochain.toSingleLinearEquiv (Int.add_left_neg n)).symm)

noncomputable def linearYonedaObjIso :
    (K.linearYonedaObj R Y) ≅
    (CochainComplex.linearHomComplex R (K.extend ComplexShape.embeddingDownNat)
        ((CochainComplex.singleFunctor C 0).obj Y)).restriction ComplexShape.embeddingUpNat :=
  HomologicalComplex.Hom.isoOfComponents (fun k ↦ K.linearYonedaObjXIso R Y k k rfl) (by
    sorry)

def linearYonedaObjHomologyIso (n : ℤ) (k : ℕ) (h : k = n := by lia) :
    (K.linearYonedaObj R Y).homology k ≅
      ↧(CochainComplex.HomComplex.CohomologyClass (K.extend ComplexShape.embeddingDownNat)
        ((CochainComplex.singleFunctor _ 0).obj Y) n) := by
  sorry

end ChainComplex

namespace CategoryTheory.ProjectiveResolution

variable [HasExt.{v} C] {X : C} (P : ProjectiveResolution X) {R : Type*} [Ring R] [Linear R C]

noncomputable def extIsoHomologyLinearYonedaObj (Y : C) (n : ℕ) :
    ModuleCat.of R (Abelian.Ext X Y n) ≅
      (P.complex.linearYonedaObj R Y).homology n :=
  P.extLinearEquivCohomologyClass.toModuleIso ≪≫
    (P.complex.linearYonedaObjHomologyIso R Y n n).symm

end CategoryTheory.ProjectiveResolution
