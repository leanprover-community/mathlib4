/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Shift.InducedShiftSequence
import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.QuasiIso

/-! # Compatibilities of the homology functor with the shift

This files studies how homology of cochain complexes behaves with respect to
the shift: there is a natural isomorphism `(K⟦n⟧).homology a ≅ K.homology a`
when `n + a = a'`. This is summarized by instances
`(homologyFunctor C (ComplexShape.up ℤ) 0).ShiftSequence ℤ` in the `CochainComplex`
and `HomotopyCategory` namespaces.

-/

open CategoryTheory Category

variable (C : Type*) [Category C] [Preadditive C]

namespace CochainComplex

open HomologicalComplex

attribute [local simp] XIsoOfEq_hom_naturality smul_smul

set_option backward.isDefEq.lazyWhnfCore false in -- See https://github.com/leanprover-community/mathlib4/issues/12534
/-- The natural isomorphism `(K⟦n⟧).sc' i j k ≅ K.sc' i' j' k'` when `n + i = i'`,
`n + j = j'` and `n + k = k'`. -/
@[simps!]
def shiftShortComplexFunctor' (n i j k i' j' k' : ℤ)
    (hi : n + i = i') (hj : n + j = j') (hk : n + k = k') :
    (CategoryTheory.shiftFunctor (CochainComplex C ℤ) n) ⋙ shortComplexFunctor' C _ i j k ≅
      shortComplexFunctor' C _ i' j' k' :=
  NatIso.ofComponents (fun K => by
    dsimp [shortComplexFunctor']
    exact ShortComplex.isoMk
      (n.negOnePow • ((shiftEval C n i i' hi).app K))
      ((shiftEval C n j j' hj).app K) (n.negOnePow • ((shiftEval C n k k' hk).app K)))

/-- The natural isomorphism `(K⟦n⟧).sc i ≅ K.sc i'` when `n + i = i'`. -/
@[simps!]
noncomputable def shiftShortComplexFunctorIso (n i i' : ℤ) (hi : n + i = i') :
    shiftFunctor C n ⋙ shortComplexFunctor C _ i ≅ shortComplexFunctor C _ i' :=
  shiftShortComplexFunctor' C n _ i _ _ i' _
    (by simp only [prev]; omega) hi (by simp only [next]; omega)

variable {C}

lemma shiftShortComplexFunctorIso_zero_add_hom_app (a : ℤ) (K : CochainComplex C ℤ) :
    (shiftShortComplexFunctorIso C 0 a a (zero_add a)).hom.app K =
      (shortComplexFunctor C (ComplexShape.up ℤ) a).map
        ((shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app K) := by
  ext <;> dsimp <;> simp [one_smul, shiftFunctorZero_hom_app_f]

lemma shiftShortComplexFunctorIso_add'_hom_app
    (n m mn : ℤ) (hmn : m + n = mn) (a a' a'' : ℤ) (ha' : n + a = a') (ha'' : m + a' = a'')
    (K : CochainComplex C ℤ) :
    (shiftShortComplexFunctorIso C mn a a'' (by rw [← ha'', ← ha', ← add_assoc, hmn])).hom.app K =
      (shortComplexFunctor C (ComplexShape.up ℤ) a).map
        ((CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) m n mn hmn).hom.app K) ≫
        (shiftShortComplexFunctorIso C n a a' ha').hom.app (K⟦m⟧) ≫
        (shiftShortComplexFunctorIso C m a' a'' ha'' ).hom.app K := by
  ext <;> dsimp <;> simp only [← hmn, Int.negOnePow_add, shiftFunctorAdd'_hom_app_f',
    XIsoOfEq_shift, Linear.comp_units_smul, Linear.units_smul_comp,
    XIsoOfEq_hom_comp_XIsoOfEq_hom, smul_smul]

variable [CategoryWithHomology C]

namespace ShiftSequence

variable (C) in
/-- The natural isomorphism `(K⟦n⟧).homology a ≅ K.homology a'`when `n + a = a`. -/
noncomputable def shiftIso (n a a' : ℤ) (ha' : n + a = a') :
    (CategoryTheory.shiftFunctor _ n) ⋙ homologyFunctor C (ComplexShape.up ℤ) a ≅
      homologyFunctor C (ComplexShape.up ℤ) a' :=
  isoWhiskerLeft _ (homologyFunctorIso C (ComplexShape.up ℤ) a) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (shiftShortComplexFunctorIso C n a a' ha')
      (ShortComplex.homologyFunctor C) ≪≫
    (homologyFunctorIso C (ComplexShape.up ℤ) a').symm

lemma shiftIso_hom_app (n a a' : ℤ) (ha' : n + a = a') (K : CochainComplex C ℤ):
    (shiftIso C n a a' ha').hom.app K =
      ShortComplex.homologyMap ((shiftShortComplexFunctorIso C n a a' ha').hom.app K) := by
  dsimp [shiftIso]
  erw [id_comp, id_comp, comp_id]

lemma shiftIso_inv_app (n a a' : ℤ) (ha' : n + a = a') (K : CochainComplex C ℤ):
    (shiftIso C n a a' ha').inv.app K =
      ShortComplex.homologyMap ((shiftShortComplexFunctorIso C n a a' ha').inv.app K) := by
  dsimp [shiftIso]
  erw [id_comp, comp_id, comp_id]

end ShiftSequence

noncomputable instance :
    (homologyFunctor C (ComplexShape.up ℤ) 0).ShiftSequence ℤ where
  sequence n := homologyFunctor C (ComplexShape.up ℤ) n
  isoZero := Iso.refl _
  shiftIso n a a' ha' := ShiftSequence.shiftIso C n a a' ha'
  shiftIso_zero a := by
    ext K
    dsimp [homologyMap]
    simp only [ShiftSequence.shiftIso_hom_app, comp_id,
      shiftShortComplexFunctorIso_zero_add_hom_app]
  shiftIso_add n m a a' a'' ha' ha'' := by
    ext K
    dsimp [homologyMap]
    simp only [ShiftSequence.shiftIso_hom_app, id_comp,
      ← ShortComplex.homologyMap_comp, shiftFunctorAdd'_eq_shiftFunctorAdd,
      shiftShortComplexFunctorIso_add'_hom_app n m _ rfl a a' a'' ha' ha'' K]

instance {K L : CochainComplex C ℤ} (φ : K ⟶ L) (n : ℤ) [QuasiIso φ] :
    QuasiIso (φ⟦n⟧') where
  quasiIsoAt a := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    apply (NatIso.isIso_map_iff
      ((homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso n a (n + a) rfl) φ).2 ?_
    change IsIso (homologyMap φ _)
    infer_instance

end CochainComplex

namespace HomotopyCategory

variable [CategoryWithHomology C]

noncomputable instance :
    (homologyFunctor C (ComplexShape.up ℤ) 0).ShiftSequence ℤ :=
  Functor.ShiftSequence.induced (homologyFunctorFactors C (ComplexShape.up ℤ) 0) ℤ
    (homologyFunctor C (ComplexShape.up ℤ))
    (homologyFunctorFactors C (ComplexShape.up ℤ))

variable {C}

lemma homologyShiftIso_hom_app (n a a' : ℤ) (ha' : n + a = a') (K : CochainComplex C ℤ) :
    ((homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso n a a' ha').hom.app
      ((quotient _ _).obj K) =
    (homologyFunctor _ _ a).map (((quotient _ _).commShiftIso n).inv.app K) ≫
      (homologyFunctorFactors _ _ a).hom.app (K⟦n⟧) ≫
      ((HomologicalComplex.homologyFunctor _ _ 0).shiftIso n a a' ha').hom.app K ≫
      (homologyFunctorFactors _ _ a').inv.app K := by
  apply Functor.ShiftSequence.induced_shiftIso_hom_app_obj

end HomotopyCategory
