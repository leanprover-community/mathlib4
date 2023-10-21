import Mathlib.Algebra.Homology.Single

namespace HomologicalComplex

open CategoryTheory Limits

variable {C ι : Type _} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
  {c : ComplexShape ι} [DecidableEq ι]

noncomputable def fromSingleEquiv (A : C) (K : HomologicalComplex C c) (i j : ι) (hij : c.Rel i j) :
    ((single C c i).obj A ⟶ K) ≃ { f : A ⟶ K.X i // f ≫ K.d i j = 0 } where
  toFun φ := ⟨(singleObjXSelf C c i A).inv ≫ φ.f i, by simp⟩
  invFun f :=
    { f := fun k =>
        if hk : k = i then
          (((single C c i).obj A).XIsoOfEq hk).hom ≫ (singleObjXSelf C c i A).hom ≫ f.1 ≫ (K.XIsoOfEq hk).inv
        else 0
      comm' := fun k l hkl => by
        by_cases hk : k = i
        · subst hk
          dsimp
          obtain rfl : l = j := (c.next_eq' hkl).symm.trans (c.next_eq' hij)
          simp only [Category.comp_id, Category.id_comp, ite_true, Category.assoc, zero_comp]
          rw [f.2, comp_zero]
        · dsimp
          rw [dif_neg hk, zero_comp, zero_comp] }
  left_inv φ := by
    ext k
    by_cases hk : k = i
    · subst hk
      dsimp
      simp
    · dsimp
      rw [dif_neg hk]
      apply IsZero.eq_of_src
      dsimp
      rw [if_neg hk]
      exact Limits.isZero_zero _
  right_inv f := by
    ext
    dsimp
    simp

noncomputable def toSingleEquiv (A : C) (K : HomologicalComplex C c) (i j : ι) (hij : c.Rel i j) :
    (K ⟶ (single C c j).obj A) ≃ { f : K.X j ⟶ A // K.d i j ≫ f = 0 } where
  toFun φ := ⟨φ.f j ≫ (singleObjXSelf C c j A).hom, by
    simp only [← φ.comm_assoc, single_obj_d, zero_comp, comp_zero]⟩
  invFun f :=
    { f := fun k =>
        if hk : k = j then
          (K.XIsoOfEq hk).hom ≫ f.1 ≫ (singleObjXSelf C c j A).inv ≫ (((single C c j).obj A).XIsoOfEq hk).inv
        else 0
      comm' := fun k l hkl => by
        by_cases hk : l = j
        · subst hk
          dsimp
          obtain rfl : k = i := (c.prev_eq' hkl).symm.trans (c.prev_eq' hij)
          simp
          rw [reassoc_of% f.2, zero_comp]
        · dsimp
          rw [dif_neg hk, comp_zero, comp_zero] }
  left_inv φ := by
    ext k
    by_cases hk : k = j
    · subst hk
      dsimp
      simp
    · dsimp
      rw [dif_neg hk]
      apply IsZero.eq_of_tgt
      dsimp
      rw [if_neg hk]
      exact Limits.isZero_zero _
  right_inv f := by
    ext
    dsimp
    simp

end HomologicalComplex
