/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Adam Topaz, Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
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

open CochainComplex.HomComplex HomologicalComplex

variable (K : ChainComplex C ℕ) (R : Type*) [Ring R] [Linear R C] (Y : C)

def φ (n : ℤ) : ℤˣ := ((n * (n + 1)) / 2).negOnePow

lemma φ_succ (n : ℤ) : φ (n + 1) = φ n * (n + 1).negOnePow := by
  simp [φ, ← Int.negOnePow_add]
  grind

noncomputable def linearYonedaObjXIso (n : ℤ) (k : ℕ) (h : k = n := by lia) :
    (K.linearYonedaObj R Y).X k ≅
      (CochainComplex.linearHomComplex R (K.extend ComplexShape.embeddingDownNat)
        ((CochainComplex.singleFunctor C 0).obj Y)).X n :=
  ((n * (n + 1)) / 2).negOnePow • LinearEquiv.toModuleIso
    ((Linear.homCongr R (K.extendXIso ComplexShape.embeddingDownNat
        (by simpa)).symm (Iso.refl Y)).trans
      (Cochain.toSingleLinearEquiv (Int.add_left_neg n)).symm)

set_option backward.isDefEq.respectTransparency false in
lemma linearYonedaObjXIso_hom_apply
    (m n : ℤ) (k : ℕ) (f : K.X k ⟶ Y) (hn : k = n := by lia) (hm : m + n = 0) :
    dsimp% (K.linearYonedaObjXIso R Y n k hn).hom f =
      ((n * (n + 1)) / 2).negOnePow • Cochain.toSingleMk
        ((K.extendXIso ComplexShape.embeddingDownNat (by simp; lia)).hom≫ f) hm := by
  obtain rfl : m = -n := by lia
  simp [linearYonedaObjXIso, Linear.homCongr]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
noncomputable def linearYonedaObjIso :
    K.linearYonedaObj R Y ≅
    (CochainComplex.linearHomComplex R (K.extend ComplexShape.embeddingDownNat)
        ((CochainComplex.singleFunctor C 0).obj Y)).restriction ComplexShape.embeddingUpNat :=
  Hom.isoOfComponents (fun k ↦ K.linearYonedaObjXIso R Y k k rfl)
    (fun n m h ↦ by
      ext (f : K.X n ⟶ Y) : 2
      dsimp
      simp only [dsimp% K.linearYonedaObjXIso_hom_apply R Y (-n) n n _ (by lia) (by lia),
        dsimp% K.linearYonedaObjXIso_hom_apply R Y (-m) m m _ (by lia) (by lia),
        Cochain.δ_toSingleMk (p := -n) (q := 0) (n := n) _ (by lia) m (-m) (by lia),
        K.extend_d_eq ComplexShape.embeddingDownNat (i' := -m) (j' := -n) (i := m) (j := n)
          (by simp) (by simp), smul_smul, δ_units_smul, Category.assoc, Iso.inv_hom_id_assoc]
      congr 1
      obtain rfl : n + 1 = m := by simpa using h
      rw [← Int.negOnePow_add]
      grind)

noncomputable def extendLinearYonedaObjIso :
    (K.linearYonedaObj R Y).extend ComplexShape.embeddingUpNat ≅
      CochainComplex.linearHomComplex R (K.extend ComplexShape.embeddingDownNat)
        ((CochainComplex.singleFunctor C 0).obj Y) :=
  (ComplexShape.embeddingUpNat.extendFunctor _).mapIso (K.linearYonedaObjIso R Y) ≪≫ by
    let Z := CochainComplex.linearHomComplex R (extend K ComplexShape.embeddingDownNat)
      ((CochainComplex.singleFunctor C 0).obj Y)
    change Z.stupidTrunc ComplexShape.embeddingUpNat ≅ Z
    sorry

noncomputable def linearYonedaObjHomologyIso (n : ℤ) (k : ℕ) (h : k = n := by lia) :
    (K.linearYonedaObj R Y).homology k ≅
      ↧(CochainComplex.HomComplex.CohomologyClass (K.extend ComplexShape.embeddingDownNat)
        ((CochainComplex.singleFunctor _ 0).obj Y) n) :=
  (extendHomologyIso (K.linearYonedaObj R Y) _ h).symm ≪≫
    homologyMapIso (K.extendLinearYonedaObjIso R Y) n ≪≫
    (CochainComplex.HomComplex.linearLeftHomologyData' R _ _ _ _ _ (by simp) (by simp)).homologyIso

end ChainComplex

namespace CategoryTheory.ProjectiveResolution

variable [HasExt.{v} C] {X : C} (P : ProjectiveResolution X) {R : Type*} [Ring R] [Linear R C]

noncomputable def extIsoHomologyLinearYonedaObj (Y : C) (n : ℕ) :
    ModuleCat.of R (Abelian.Ext X Y n) ≅
      (P.complex.linearYonedaObj R Y).homology n :=
  P.extLinearEquivCohomologyClass.toModuleIso ≪≫
    (P.complex.linearYonedaObjHomologyIso R Y n n).symm

end CategoryTheory.ProjectiveResolution
