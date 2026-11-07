/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Adam Topaz, Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexIsStrictlyGE
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import Mathlib.CategoryTheory.Linear.Yoneda

/-!
# Computing `Ext` groups using a projective resolution

Let `K` be a chain complex indexed by `ℕ` in a `R`-linear abelian category `C`.
Let `Y : C`. We consider the cochain complex `K.linearYonedaObj R Y`
which in degree `n` is given by the `R`-module of morphisms `K.X n ⟶ Y`,
and differential are the obvious morphisms (without added signs).

We show that if we extend (by zero) the cochain complex `K.linearYonedaObj R Y`
in order to obtain a cochain complex indexed by `ℤ`, we obtain a cochain
complex that is isomorphic (`extendLinearYonedaObjIso`) to the complex of
morphisms (`CochainComplex.linearHomComplex`) from the extension of `K`
to the single complex where `Y` lies in degree `0`. In each degree,
both cochain complexes are essentially the same, but as the differential
on `CochainComplex.linearHomComplex` involves signs, the isomorphism
is given by the multiplication by `(-1) ^ ((n * (n + 1)) / 2)` in degree `n`.

In the case the chain complex above is given by a projective resolution `P`
of an object `X : C`, we obtain that the `Ext`-group `Ext X Y n` identifies
to the homology of `(P.complex.linearYonedaObj R Y).homology n`,
see `ProjectiveResolution.extIsoHomologyLinearYonedaObj`.
(Using this definition is not recommended though: it is advisable to use
`ProjectiveResolution.extMk` and the related API from the file
`Mathlib/CategoryTheory/Abelian/Projective/Ext.lean` instead)

-/

universe v

@[expose] public section

open CategoryTheory Limits

variable {C : Type*} [Category.{v} C] [Abelian C]

namespace ChainComplex

/-- Given a chain complex `K` and an object `Y`, this is the cochain complex
which in degree `i` consists of the module of morphisms `K.X i ⟶ Y`. -/
@[simps! X d, implicit_reducible]
def linearYonedaObj
    {α : Type*} [AddRightCancelSemigroup α] [One α]
    (K : ChainComplex C α) (A : Type*) [Ring A] [Linear A C] (Y : C) :
    CochainComplex (ModuleCat A) α :=
  ((((linearYoneda A C).obj Y).rightOp.mapHomologicalComplex _).obj K).unop

open CochainComplex.HomComplex HomologicalComplex

variable (K : ChainComplex C ℕ) (R : Type*) [Ring R] [Linear R C] (Y : C)

/-- Auxiliary definition for `linearYonedaObjIso`. -/
noncomputable def linearYonedaObjXIso (n : ℤ) (k : ℕ) (h : k = n := by lia) :
    (K.linearYonedaObj R Y).X k ≅
      (CochainComplex.linearHomComplex R (K.extend ComplexShape.embeddingDownNat)
        ((CochainComplex.singleFunctor C 0).obj Y)).X n :=
  ((n * (n + 1)) / 2).negOnePow • LinearEquiv.toModuleIso
    ((Linear.homCongr R (K.extendXIso ComplexShape.embeddingDownNat
        (by simpa)).symm (Iso.refl Y)).trans
      (Cochain.toSingleLinearEquiv (Int.add_left_neg n)).symm)

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
/-- If `K` is a chain complex in a `R`-linear category `C` and `Y : C`, then
the cochain complex `K.linearYonedaObj R Y` identifies to the restriction to `ℕ`
of the cochain complex of morphisms from the extension of `K` to the single complex
where `Y` lies in degree `0`. This isomorphism is essentially given by the
multiplication by `(-1) ^ ((n * (n + 1)) / 2)` in degree `n`. -/
noncomputable def linearYonedaObjIso :
    K.linearYonedaObj R Y ≅
    (CochainComplex.linearHomComplex R (K.extend ComplexShape.embeddingDownNat)
        ((CochainComplex.singleFunctor C 0).obj Y)).restriction ComplexShape.embeddingUpNat :=
  Hom.isoOfComponents (fun k ↦ K.linearYonedaObjXIso R Y k k rfl)
    (fun n m h ↦ by
      ext (f : K.X n ⟶ Y) : 2
      dsimp
      simp only [K.linearYonedaObjXIso_hom_apply R Y (-n) n n _ (by lia) (by lia),
        K.linearYonedaObjXIso_hom_apply R Y (-m) m m _ (by lia) (by lia),
        Cochain.δ_toSingleMk (p := -n) (q := 0) (n := n) _ (by lia) m (-m) (by lia),
        K.extend_d_eq ComplexShape.embeddingDownNat (i' := -m) (j' := -n) (i := m) (j := n)
          (by simp) (by simp), smul_smul, δ_units_smul, Category.assoc, Iso.inv_hom_id_assoc]
      congr 1
      obtain rfl : n + 1 = m := by simpa using h
      rw [← Int.negOnePow_add]
      grind)

/-- If `K` is a chain complex in a `R`-linear category `C` and `Y : C`, then
the extension to `ℤ` of the cochain complex `K.linearYonedaObj R Y`
identifies to the cochain complex of morphisms from the extension of `K`
to the single complex where `Y` lies in degree `0`.
This isomorphism is essentially given by the
multiplication by `(-1) ^ ((n * (n + 1)) / 2)` in degree `n`. -/
noncomputable def extendLinearYonedaObjIso :
    (K.linearYonedaObj R Y).extend ComplexShape.embeddingUpNat ≅
      CochainComplex.linearHomComplex R (K.extend ComplexShape.embeddingDownNat)
        ((CochainComplex.singleFunctor C 0).obj Y) :=
  (ComplexShape.embeddingUpNat.extendFunctor _).mapIso (K.linearYonedaObjIso R Y) ≪≫
    (asIso ((CochainComplex.linearHomComplex R (K.extend ComplexShape.embeddingDownNat)
      ((CochainComplex.singleFunctor C 0).obj Y)).ιStupidTrunc ComplexShape.embeddingUpNat) :)

/-- The homology of a cochain complex `K.linearYonedaObj R Y` identifies to
cohomology classes for the complex of morphisms from the extension of `K`
to the single functor where `Y` lies in degree `0`. -/
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

--/- (Using this definition is not recommended though: it is advisable to use
--`ProjectiveResolution.extMk` and the related API from the file
--`Mathlib/CategoryTheory/Abelian/Projective/Ext.lean` instead) -/
/-- If `P` is a projective resolution of an object `X` in a `R`-linear category `C` and `Y : C`,
then the `R`-module `Ext X Y n` identifies to the homology of `P.complex.linearYonedaObj R Y`.
(It is not recommended to use this definition: it is advisable to use
`ProjectiveResolution.extMk` and the related API from the file
`Mathlib/CategoryTheory/Abelian/Projective/Ext.lean` instead). -/
noncomputable def extIsoHomologyLinearYonedaObj (Y : C) (n : ℕ) :
    ModuleCat.of R (Abelian.Ext X Y n) ≅
      (P.complex.linearYonedaObj R Y).homology n :=
  P.extLinearEquivCohomologyClass.toModuleIso ≪≫
    (P.complex.linearYonedaObjHomologyIso R Y n n).symm

end CategoryTheory.ProjectiveResolution
