/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Triangulated.TStructure.Basic

/-!
# The canonical t-structure on the derived category

In this file, we introduce the canonical t-structure on the
derived category of an abelian category.

-/

open CategoryTheory Category Pretriangulated Triangulated Limits Preadditive

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The canonical t-structure on `DerivedCategory C`. -/
def TStructure.t : TStructure (DerivedCategory C) where
  le n X := ∃ (K : CochainComplex C ℤ) (_ : X ≅ DerivedCategory.Q.obj K), K.IsStrictlyLE n
  ge n X := ∃ (K : CochainComplex C ℤ) (_ : X ≅ DerivedCategory.Q.obj K), K.IsStrictlyGE n
  le_isClosedUnderIsomorphisms n :=
    { of_iso := by
        rintro X Y e ⟨K, e', _⟩
        exact ⟨K, e.symm ≪≫ e', inferInstance⟩ }
  ge_isClosedUnderIsomorphisms n :=
    { of_iso := by
        rintro X Y e ⟨K, e', _⟩
        exact ⟨K, e.symm ≪≫ e', inferInstance⟩ }
  le_shift := by
    rintro n a n' h X ⟨K, e, _⟩
    exact ⟨(shiftFunctor (CochainComplex C ℤ) a).obj K,
      (shiftFunctor (DerivedCategory C) a).mapIso e ≪≫ (Q.commShiftIso a).symm.app K,
      K.isStrictlyLE_shift n a n' h⟩
  ge_shift := by
    rintro n a n' h X ⟨K, e, _⟩
    exact ⟨(shiftFunctor (CochainComplex C ℤ) a).obj K,
      (shiftFunctor (DerivedCategory C) a).mapIso e ≪≫ (Q.commShiftIso a).symm.app K,
      K.isStrictlyGE_shift n a n' h⟩
  zero' X Y f := by
    rintro ⟨K, e₁, _⟩ ⟨L, e₂, _⟩
    rw [← cancel_epi e₁.inv, ← cancel_mono e₂.hom, comp_zero, zero_comp]
    apply (subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE K L 0 1 (by simp)).elim
  le_zero_le := by
    rintro X ⟨K, e, _⟩
    exact ⟨K, e, K.isStrictlyLE_of_le 0 1 (by omega)⟩
  ge_one_le := by
    rintro X ⟨K, e, _⟩
    exact ⟨K, e, K.isStrictlyGE_of_ge 0 1 (by omega)⟩
  exists_triangle_zero_one X := by
    obtain ⟨K, ⟨e₂⟩⟩ : ∃ K, Nonempty (Q.obj K ≅ X) := ⟨_, ⟨Q.objObjPreimageIso X⟩⟩
    have h := K.shortComplexTruncLE_shortExact 0
    refine ⟨Q.obj (K.truncLE 0), Q.obj (K.truncGE 1),
      ⟨_, Iso.refl _, inferInstance⟩, ⟨_, Iso.refl _, inferInstance⟩,
      Q.map (K.ιTruncLE 0) ≫ e₂.hom, e₂.inv ≫ Q.map (K.πTruncGE 1),
      inv (Q.map (K.shortComplexTruncLEX₃ToTruncGE 0 1 (by omega))) ≫ (triangleOfSES h).mor₃,
      isomorphic_distinguished _ (triangleOfSES_distinguished h) _ (Iso.symm ?_)⟩
    refine Triangle.isoMk _ _ (Iso.refl _) e₂
      (asIso (Q.map (K.shortComplexTruncLEX₃ToTruncGE 0 1 (by omega)))) ?_ ?_ (by simp)
    · dsimp
      rw [id_comp]
      rfl
    · dsimp
      rw [← Q.map_comp, CochainComplex.g_shortComplexTruncLEX₃ToTruncGE,
        Iso.hom_inv_id_assoc]

/-- Given `X : DerivedCategory C` and `n : ℤ`, this property means
that `X` is `≤ n` for the canonical t-structure. -/
abbrev IsLE (X : DerivedCategory C) (n : ℤ) : Prop := TStructure.t.IsLE X n

/-- Given `X : DerivedCategory C` and `n : ℤ`, this property means
that `X` is `≥ n` for the canonical t-structure. -/
abbrev IsGE (X : DerivedCategory C) (n : ℤ) : Prop := TStructure.t.IsGE X n

lemma isGE_iff (X : DerivedCategory C) (n : ℤ) :
    X.IsGE n ↔ ∀ (i : ℤ) (_ : i < n), IsZero ((homologyFunctor C i).obj X) := by
  constructor
  · rintro ⟨K, e, _⟩ i hi
    apply ((K.exactAt_of_isGE n i hi).isZero_homology).of_iso
    exact (homologyFunctor C i).mapIso e ≪≫ (homologyFunctorFactors C i).app K
  · intro hX
    have : (Q.objPreimage X).IsGE n := by
      rw [CochainComplex.isGE_iff]
      intro i hi
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      apply (hX i hi).of_iso
      exact (homologyFunctorFactors C i).symm.app _ ≪≫
        (homologyFunctor C i).mapIso (Q.objObjPreimageIso X)
    exact ⟨(Q.objPreimage X).truncGE n, (Q.objObjPreimageIso X).symm ≪≫
      asIso (Q.map ((Q.objPreimage X).πTruncGE n)), inferInstance⟩

lemma isLE_iff (X : DerivedCategory C) (n : ℤ) :
    X.IsLE n ↔ ∀ (i : ℤ) (_ : n < i), IsZero ((homologyFunctor C i).obj X) := by
  constructor
  · rintro ⟨K, e, _⟩ i hi
    apply ((K.exactAt_of_isLE n i hi).isZero_homology).of_iso
    exact (homologyFunctor C i).mapIso e ≪≫ (homologyFunctorFactors C i).app K
  · intro hX
    have : (Q.objPreimage X).IsLE n := by
      rw [CochainComplex.isLE_iff]
      intro i hi
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      apply (hX i hi).of_iso
      exact (homologyFunctorFactors C i).symm.app _ ≪≫
        (homologyFunctor C i).mapIso (Q.objObjPreimageIso X)
    exact ⟨(Q.objPreimage X).truncLE n, (Q.objObjPreimageIso X).symm ≪≫
      (asIso (Q.map ((Q.objPreimage X).ιTruncLE n))).symm, inferInstance⟩

lemma isZero_of_isGE (X : DerivedCategory C) (n i : ℤ) (hi : i < n) [hX : X.IsGE n] :
    IsZero ((homologyFunctor _ i).obj X) := by
  rw [isGE_iff] at hX
  exact hX i hi

lemma isZero_of_isLE (X : DerivedCategory C) (n i : ℤ) (hi : n < i) [hX : X.IsLE n] :
    IsZero ((homologyFunctor _ i).obj X) := by
  rw [isLE_iff] at hX
  exact hX i hi

lemma isGE_Q_obj_iff (K : CochainComplex C ℤ) (n : ℤ) :
    (Q.obj K).IsGE n ↔ K.IsGE n := by
  have eq := fun i ↦ ((homologyFunctorFactors C i).app K).isZero_iff
  simp only [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj] at eq
  simp only [isGE_iff, CochainComplex.isGE_iff,
    HomologicalComplex.exactAt_iff_isZero_homology, eq]

lemma isLE_Q_obj_iff (K : CochainComplex C ℤ) (n : ℤ) :
    (Q.obj K).IsLE n ↔ K.IsLE n := by
  have eq := fun i ↦ ((homologyFunctorFactors C i).app K).isZero_iff
  simp only [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj] at eq
  simp only [isLE_iff, CochainComplex.isLE_iff,
    HomologicalComplex.exactAt_iff_isZero_homology, eq]

instance (K : CochainComplex C ℤ) (n : ℤ) [K.IsGE n] :
    (Q.obj K).IsGE n := by
  rw [isGE_Q_obj_iff]
  infer_instance

instance (K : CochainComplex C ℤ) (n : ℤ) [K.IsLE n] :
    (Q.obj K).IsLE n := by
  rw [isLE_Q_obj_iff]
  infer_instance

instance (X : C) (n : ℤ) : ((singleFunctor C n).obj X).IsGE n := by
  let e := (singleFunctorIsoCompQ C n).app X
  dsimp only [Functor.comp_obj] at e
  exact TStructure.t.isGE_of_iso e.symm n

instance (X : C) (n : ℤ) : ((singleFunctor C n).obj X).IsLE n := by
  let e := (singleFunctorIsoCompQ C n).app X
  dsimp only [Functor.comp_obj] at e
  exact TStructure.t.isLE_of_iso e.symm n

lemma exists_iso_Q_obj_of_isLE (X : DerivedCategory C) (n : ℤ) [hX : X.IsLE n] :
    ∃ (K : CochainComplex C ℤ) (_ : K.IsStrictlyLE n), Nonempty (X ≅ Q.obj K) := by
  obtain ⟨K, e, _⟩ := hX
  exact ⟨K, inferInstance, ⟨e⟩⟩

lemma exists_iso_Q_obj_of_isGE (X : DerivedCategory C) (n : ℤ) [hX : X.IsGE n] :
    ∃ (K : CochainComplex C ℤ) (_ : K.IsStrictlyGE n), Nonempty (X ≅ Q.obj K) := by
  obtain ⟨K, e, _⟩ := hX
  exact ⟨K, inferInstance, ⟨e⟩⟩

lemma exists_iso_Q_obj_of_isGE_of_isLE (X : DerivedCategory C) (a b : ℤ) [X.IsGE a] [X.IsLE b] :
    ∃ (K : CochainComplex C ℤ) (_ : K.IsStrictlyGE a) (_ : K.IsStrictlyLE b),
      Nonempty (X ≅ Q.obj K) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isLE b
  have : K.IsGE a := by
    rw [← isGE_Q_obj_iff]
    exact TStructure.t.isGE_of_iso e a
  exact ⟨K.truncGE a, inferInstance, inferInstance, ⟨e ≪≫ asIso (Q.map (K.πTruncGE a))⟩⟩

end DerivedCategory
