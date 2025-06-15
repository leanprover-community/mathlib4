/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Triangulated.TStructure.Homology

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
noncomputable def TStructure.t : TStructure (DerivedCategory C) where
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

lemma exists_iso_single (X : DerivedCategory C) (n : ℤ) [X.IsGE n] [X.IsLE n] :
    ∃ (A : C), Nonempty (X ≅ (singleFunctor C n).obj A) := by
  dsimp only [singleFunctor, Functor.comp_obj]
  obtain ⟨Y, _, _, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isGE_of_isLE n n
  obtain ⟨A, ⟨e'⟩⟩ := Y.exists_iso_single n
  exact ⟨A, ⟨e ≪≫ Q.mapIso e' ≪≫
    ((SingleFunctors.evaluation _ _ n).mapIso (singleFunctorsPostcompQIso C)).symm.app A⟩⟩

lemma singleFunctor_preimage {A B : C} {n : ℤ}
    (f : (singleFunctor C n).obj A ⟶  (singleFunctor C n).obj B) :
    (singleFunctor C n).preimage f = (singleFunctorCompHomologyFunctorIso C n).inv.app A ≫
        (homologyFunctor _ n).map f ≫ (singleFunctorCompHomologyFunctorIso C n).hom.app B := by
  obtain ⟨φ, rfl⟩ := (singleFunctor C n).map_surjective f
  erw [Functor.preimage_map, ← NatTrans.naturality_assoc, Iso.inv_hom_id_app,
    comp_id, Functor.id_map]

namespace TStructure

lemma singleFunctor_obj_mem_heart (X : C) :
    t.heart ((singleFunctor C 0).obj X) := by
  rw [TStructure.mem_heart_iff]
  constructor <;> infer_instance

@[simp]
lemma essImage_singleFunctor_eq_heart :
    (singleFunctor C 0).essImage = t.heart := by
  ext X
  constructor
  · rintro ⟨A, ⟨e⟩⟩
    exact t.heart.prop_of_iso e (singleFunctor_obj_mem_heart A)
  · intro (h : t.heart _)
    rw [TStructure.mem_heart_iff] at h
    have := h.1
    have := h.2
    obtain ⟨A, ⟨e⟩⟩ := exists_iso_single X 0
    exact ⟨A, ⟨e.symm⟩⟩

noncomputable instance : (t : TStructure (DerivedCategory C)).HasHeart where
  H := C
  ι := singleFunctor C 0

lemma isIso_homologyFunctor_map_truncLTι_app (X : DerivedCategory C) (a n : ℤ) (hn : n < a) :
    IsIso ((homologyFunctor C n).map ((t.truncLTι a).app X)) := by
  have : Mono ((homologyFunctor C n).map ((t.truncLTι a).app X)) :=
    ((homologyFunctor C 0).homologySequence_mono_shift_map_mor₁_iff _
      (t.triangleLTGE_distinguished a X) (n-1) n (by linarith)).2 (by
      apply IsZero.eq_of_src
      exact isZero_of_isGE ((t.truncGE a).obj X) a (n-1) (by linarith))
  have : Epi ((homologyFunctor C n).map ((t.truncLTι a).app X)) :=
    ((homologyFunctor C 0).homologySequence_epi_shift_map_mor₁_iff _
      (t.triangleLTGE_distinguished a X) n).2 (by
      apply IsZero.eq_of_tgt
      exact isZero_of_isGE ((t.truncGE a).obj X) a n (by linarith))
  apply isIso_of_mono_of_epi

lemma isIso_homologyFunctor_map_truncLEι_app (X : DerivedCategory C) (a n : ℤ) (hn : n ≤ a) :
    IsIso ((homologyFunctor C n).map ((t.truncLEι a).app X )) :=
  isIso_homologyFunctor_map_truncLTι_app X (a+1) n (by linarith)

lemma isIso_homologyFunctor_map_truncGEπ_app (X : DerivedCategory C) (a n : ℤ) (hn : a ≤ n) :
    IsIso ((homologyFunctor C n).map ((t.truncGEπ a).app X )) := by
  have : Mono ((homologyFunctor C n).map ((t.truncGEπ a).app X)) :=
    ((homologyFunctor C 0).homologySequence_mono_shift_map_mor₂_iff _
      (t.triangleLTGE_distinguished a X) n).2 (by
        apply IsZero.eq_of_src
        exact isZero_of_isLE ((t.truncLT a).obj X) (a-1) n (by linarith))
  have : Epi ((homologyFunctor C n).map ((t.truncGEπ a).app X)) :=
    ((homologyFunctor C 0).homologySequence_epi_shift_map_mor₂_iff _
      (t.triangleLTGE_distinguished a X) n (n+1) rfl).2 (by
        apply IsZero.eq_of_tgt
        exact isZero_of_isLE ((t.truncLT a).obj X) (a-1) (n+1) (by linarith))
  apply isIso_of_mono_of_epi

variable (C)

lemma isIso_whiskerRight_truncLEι_homologyFunctor (a n : ℤ) (hn : n ≤ a) :
    IsIso (whiskerRight (t.truncLEι a) (homologyFunctor C n)) :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
    (fun X => isIso_homologyFunctor_map_truncLEι_app X a n hn)

noncomputable def truncLECompHomologyFunctorIso (a n : ℤ) (hn : n ≤ a) :
    t.truncLE a ⋙ homologyFunctor C n ≅ homologyFunctor C n := by
  have := isIso_whiskerRight_truncLEι_homologyFunctor C a n hn
  exact asIso (whiskerRight (t.truncLEι a) (homologyFunctor C n))

lemma isIso_whiskerRight_truncGEπ_homologyFunctor (a n : ℤ) (hn : a ≤ n) :
  IsIso (whiskerRight (t.truncGEπ a) (homologyFunctor C n)) :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
    (fun X => isIso_homologyFunctor_map_truncGEπ_app X a n hn)

noncomputable def truncGECompHomologyFunctorIso (a n : ℤ) (hn : a ≤ n) :
    t.truncGE a ⋙ homologyFunctor C n ≅ homologyFunctor C n := by
  have := isIso_whiskerRight_truncGEπ_homologyFunctor C a n hn
  exact (asIso (whiskerRight (t.truncGEπ a) (homologyFunctor C n))).symm

noncomputable def truncGELECompHomologyFunctorIso (a b n : ℤ) (ha : a ≤ n) (hb : n ≤ b):
  t.truncGELE a b ⋙ homologyFunctor C n ≅ homologyFunctor C n :=
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (t.truncLE b) (truncGECompHomologyFunctorIso C a n ha) ≪≫
      truncLECompHomologyFunctorIso C b n hb

variable {C}

noncomputable def truncLE₀GE₀ToHeart : DerivedCategory C ⥤ C :=
  t.liftHeart (t.truncGELE 0 0) t.truncGE₀LE₀_mem_heart

noncomputable def truncLE₀GE₀ToHeartιHeart :
    (truncLE₀GE₀ToHeart : _ ⥤ C) ⋙ t.ιHeart ≅ t.truncGELE 0 0 :=
  t.liftHeartιHeart _ _

variable (C)

noncomputable def homologyFunctorIsotruncLE₀GE₀ToHeart :
    homologyFunctor C 0 ≅ truncLE₀GE₀ToHeart :=
  (truncGELECompHomologyFunctorIso C 0 0 0 (by rfl) (by rfl)).symm ≪≫
    isoWhiskerRight truncLE₀GE₀ToHeartιHeart.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (singleFunctorCompHomologyFunctorIso C 0) ≪≫
    truncLE₀GE₀ToHeart.rightUnitor

noncomputable instance : (t : TStructure (DerivedCategory C)).HasHomology₀ where
  homology₀ := homologyFunctor C 0
  iso := isoWhiskerRight (homologyFunctorIsotruncLE₀GE₀ToHeart C) _ ≪≫
    truncLE₀GE₀ToHeartιHeart

noncomputable instance : (t : TStructure (DerivedCategory C)).homology₀.ShiftSequence ℤ :=
  (inferInstance : (homologyFunctor C 0).ShiftSequence ℤ)

end TStructure

open DerivedCategory.TStructure

variable (C)

abbrev Minus := (t : TStructure (DerivedCategory C)).minus.FullSubcategory
abbrev Plus := (t : TStructure (DerivedCategory C)).plus.FullSubcategory
abbrev Bounded := (t : TStructure (DerivedCategory C)).bounded.FullSubcategory

variable {C}

abbrev Minus.ι : Minus C ⥤ DerivedCategory C := t.minus.ι
abbrev Plus.ι : Plus C ⥤ DerivedCategory C := t.plus.ι
abbrev Bounded.ι : Bounded C ⥤ DerivedCategory C := t.bounded.ι

end DerivedCategory
