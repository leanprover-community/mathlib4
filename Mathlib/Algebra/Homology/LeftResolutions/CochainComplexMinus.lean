/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.LeftResolutions.Basic
import Mathlib.Algebra.Homology.BicomplexRows
import Mathlib.Algebra.Homology.CochainComplexMinus
import Mathlib.Algebra.Homology.TotalComplexMap

/-!
# Resolutions of bounded above complexes

-/

namespace CategoryTheory

open Category Limits CochainComplex

namespace Abelian

namespace LeftResolutions

variable {A C : Type*} [Category C] [Category A] {ι : C ⥤ A}
  [ι.Full] [ι.Faithful] [Preadditive C] [HasZeroObject C]
  [Abelian A] (Λ : LeftResolutions ι)

variable [Λ.F.PreservesZeroMorphisms]

instance : Λ.chainComplexFunctor.PreservesZeroMorphisms where
  map_zero _ _ := by
    simp [chainComplexFunctor]

instance : Λ.cochainComplexFunctor.PreservesZeroMorphisms where
  map_zero _ _ := by
    simp [cochainComplexFunctor]

noncomputable def bicomplexFunctor :
    CochainComplex A ℤ ⥤ HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
      Λ.cochainComplexFunctor.mapHomologicalComplex (ComplexShape.up ℤ)

instance (K : CochainComplex A ℤ) (i : ℤ) :
    CochainComplex.IsStrictlyLE ((Λ.bicomplexFunctor.obj K).X i) 0 := by
  dsimp [bicomplexFunctor]
  infer_instance

instance (K : CochainComplex A ℤ) (i : ℤ) :
    IsStrictlyLE (((bicomplexFunctor Λ ⋙
      Functor.mapHomologicalComplex₂ ι (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).X i) 0 := by
  dsimp [Functor.mapHomologicalComplex₂]
  infer_instance

instance (K : CochainComplex A ℤ) (i : ℤ) [K.IsStrictlyLE i] :
    CochainComplex.IsStrictlyLE (Λ.bicomplexFunctor.obj K) i := by
  dsimp [bicomplexFunctor]
  infer_instance

instance (K : CochainComplex A ℤ) (i : ℤ) [K.IsStrictlyLE i] :
    CochainComplex.IsStrictlyLE ((ι.mapHomologicalComplex₂ _ _).obj
      (Λ.bicomplexFunctor.obj K)) i := by
  dsimp [bicomplexFunctor, Functor.mapHomologicalComplex₂]
  infer_instance

instance (K : CochainComplex A ℤ) (i : ℤ) [K.IsStrictlyLE i]:
    IsStrictlyLE ((bicomplexFunctor Λ ⋙
      Functor.mapHomologicalComplex₂ ι (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K) i := by
  dsimp
  infer_instance

instance (K : CochainComplex A ℤ) (i : ℤ)  :
    CochainComplex.IsStrictlyLE (((ι.mapHomologicalComplex₂ _ _).obj
      (Λ.bicomplexFunctor.obj K)).X i) 0 := by
  dsimp [bicomplexFunctor, Functor.mapHomologicalComplex₂]
  infer_instance

variable [HasFiniteCoproducts C]

instance (K : CochainComplex.Minus A) :
    (Λ.bicomplexFunctor.obj K.obj).HasTotal (ComplexShape.up ℤ) := by
  obtain ⟨i, hi⟩ := K.2
  exact HomologicalComplex₂.hasTotal_of_isStrictlyLE _ i 0

instance (K : CochainComplex.Minus A) :
    ((ι.mapHomologicalComplex₂ _ _).obj (Λ.bicomplexFunctor.obj K.obj)).HasTotal
      (ComplexShape.up ℤ) := by
  obtain ⟨i, hi⟩ := K.2
  exact HomologicalComplex₂.hasTotal_of_isStrictlyLE _ i 0

instance (K : CochainComplex.Minus A) :
    ((Λ.bicomplexFunctor ⋙ ι.mapHomologicalComplex₂ _ _).obj K.obj).HasTotal
      (ComplexShape.up ℤ) := by
  dsimp
  infer_instance

instance (K : CochainComplex C ℤ) (i : ℤ) :
    IsStrictlyLE (((HomologicalComplex₂.singleRow C
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) 0).obj K).X i) 0 := by
  dsimp [HomologicalComplex₂.singleRow]
  infer_instance

instance (K : CochainComplex C ℤ) (i : ℤ) [K.IsStrictlyLE i] :
    IsStrictlyLE ((HomologicalComplex₂.singleRow C (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) 0).obj K) i := by
  dsimp [HomologicalComplex₂.singleRow]
  infer_instance

instance (K : CochainComplex C ℤ) :
    ((HomologicalComplex₂.singleRow C (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) 0).obj K).HasTotal (ComplexShape.up ℤ) := fun i =>
  hasCoproduct_of_isZero_but_one _ ⟨⟨i, 0⟩, by simp⟩ (by
    rintro ⟨⟨p, q⟩, hpq⟩ h
    apply HomologicalComplex.isZero_single_obj_X
    rintro rfl
    obtain rfl : p = i := by simpa using hpq
    exact h rfl)

instance (K : CochainComplex A ℤ) (i : ℤ) [K.IsStrictlyLE i]
    [(Λ.bicomplexFunctor.obj K).HasTotal (ComplexShape.up ℤ)]:
    CochainComplex.IsStrictlyLE ((Λ.bicomplexFunctor.obj K).total (ComplexShape.up ℤ)) i where
  isZero n hn := by
    rw [IsZero.iff_id_eq_zero]
    ext i₁ i₂ h
    dsimp at h hn
    apply IsZero.eq_of_src
    by_cases hi₂ : 0 < i₂
    · exact CochainComplex.isZero_of_isStrictlyLE _ 0 _ hi₂
    · have : IsZero (((Λ.bicomplexFunctor).obj K).X i₁) := by
        apply CochainComplex.isZero_of_isStrictlyLE _ i
        by_contra!
        obtain ⟨k, hk⟩ := Int.le.dest (show n ≤ i by omega)
        exact hn k (by omega)
      exact (HomologicalComplex.eval _ _ i₂).map_isZero this

noncomputable abbrev bicomplexπ :
    Λ.bicomplexFunctor ⋙ ι.mapHomologicalComplex₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⟶
      HomologicalComplex₂.singleRow A (ComplexShape.up ℤ) (ComplexShape.up ℤ) 0 :=
  NatTrans.mapHomologicalComplex Λ.cochainComplexNatTransπ (ComplexShape.up ℤ)

section

variable (K L : CochainComplex.Minus A) (φ : K ⟶ L)

/-- totalπ' -/
noncomputable def totalπ'  :
    ((ι.mapHomologicalComplex₂ _ _).obj (Λ.bicomplexFunctor.obj K.obj)).total (ComplexShape.up ℤ) ⟶
      ((HomologicalComplex₂.singleRow A
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) 0).obj K.obj).total (ComplexShape.up ℤ) :=
  HomologicalComplex₂.total.map (Λ.bicomplexπ.app K.obj) (ComplexShape.up ℤ)

omit [HasFiniteCoproducts C] in
variable {K L} in
@[reassoc (attr := simp)]
lemma totalπ'_naturality :
    (HomologicalComplex₂.total.map
      ((ι.mapHomologicalComplex₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
        (Λ.bicomplexFunctor.map φ)) (ComplexShape.up ℤ)) ≫ Λ.totalπ' L =
      Λ.totalπ' K ≫ HomologicalComplex₂.total.map
        ((HomologicalComplex₂.singleRow A (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) 0).map φ) (ComplexShape.up ℤ) := by
  dsimp [totalπ']
  simp only [← HomologicalComplex₂.total.map_comp]
  congr 1
  ext x y
  by_cases hy : y = 0
  · subst hy
    have eq := Λ.π.naturality (φ.f x)
    dsimp at eq
    dsimp [cochainComplexπ, bicomplexFunctor, cochainComplexFunctor]
    simp only [HomologicalComplex.mkHomToSingle_f, Functor.mapHomologicalComplex_obj_X, assoc,
      HomologicalComplex.single_map_f_self, Iso.inv_hom_id_assoc, ← reassoc_of% eq,
      ← ι.map_comp_assoc]
    simp only [← assoc]
    congr 3
    rw [HomologicalComplex.extendMap_f (i := 0) (h := by rfl)]
    dsimp [cochainComplexXZeroIso, chainComplexFunctor]
    simp
  · apply IsZero.eq_of_tgt
    apply HomologicalComplex₂.isZero_singleRow_X_X
    exact hy

instance : QuasiIso (Λ.totalπ' K) := by
  obtain ⟨i, hi⟩ := K.2
  apply HomologicalComplex₂.total.quasiIso_map_of_isStrictlyGE_of_isStrictlyLE _ i 0
  dsimp [bicomplexπ]
  infer_instance

variable [ι.Additive]

noncomputable instance : ι.PreservesTotalComplex ((bicomplexFunctor Λ).obj K.obj)
    (ComplexShape.up ℤ) := by
  apply Nonempty.some
  have ⟨i, hi⟩ := K.2
  exact ⟨HomologicalComplex₂.preservesTotal_of_isStrictlyLE _ i 0 ι⟩

noncomputable def totalπ :
    (ι.mapHomologicalComplex _).obj ((Λ.bicomplexFunctor.obj K.obj).total
      (ComplexShape.up ℤ)) ⟶ K.obj :=
  (HomologicalComplex₂.mapTotalIso _ _ _).inv ≫ Λ.totalπ' K ≫
    (HomologicalComplex₂.singleRow₀ObjTotal K.obj).hom

instance : QuasiIso (Λ.totalπ K) := by
  dsimp only [totalπ]
  infer_instance

noncomputable def resolutionFunctor : CochainComplex.Minus A ⥤ CochainComplex.Minus C where
  obj K := ⟨((Λ.bicomplexFunctor.obj K.obj).total (ComplexShape.up ℤ)), by
    obtain ⟨i, hi⟩ := K.2
    exact ⟨i, inferInstance⟩⟩
  map {K L} φ := HomologicalComplex₂.total.map (Λ.bicomplexFunctor.map φ) (ComplexShape.up ℤ)
  map_id K := by
    dsimp
    erw [Λ.bicomplexFunctor.map_id, HomologicalComplex₂.total.map_id]
    rfl
  map_comp φ ψ := by
    dsimp
    erw [Λ.bicomplexFunctor.map_comp, HomologicalComplex₂.total.map_comp]
    rfl

noncomputable def resolutionNatTrans : Λ.resolutionFunctor ⋙ ι.mapCochainComplexMinus ⟶ 𝟭 _ where
  app _ := Λ.totalπ _
  naturality {K L} f := by
    dsimp [resolutionFunctor, totalπ]
    erw [HomologicalComplex₂.mapTotalIso_inv_naturality_assoc]
    rw [totalπ'_naturality_assoc]
    erw [assoc ((HomologicalComplex₂.mapTotalIso ι _ (ComplexShape.up ℤ)).inv), assoc]
    rw [HomologicalComplex₂.singleRow₀ObjTotal_hom_naturality]

lemma quasiIso_resolutionNatTrans_app (K : CochainComplex.Minus A) :
    Minus.quasiIso (Λ.resolutionNatTrans.app K) :=
  inferInstanceAs (QuasiIso (Λ.totalπ K))

instance (K : CochainComplex.Minus A) : QuasiIso ((Minus.ι A).map (Λ.resolutionNatTrans.app K)) :=
  Λ.quasiIso_resolutionNatTrans_app K

lemma quasiIso_resolutionFunctor_map {K L : CochainComplex.Minus A} (f : K ⟶ L)
    (hf : Minus.quasiIso f) :
    Minus.quasiIso (ι.mapCochainComplexMinus.map (Λ.resolutionFunctor.map f)) := by
  have eq := (CochainComplex.Minus.ι _).congr_map (Λ.resolutionNatTrans.naturality f)
  dsimp at eq
  simp only [Functor.map_comp] at eq
  change QuasiIso _
  rw [← quasiIso_iff_comp_right _ ((Minus.ι A).map (Λ.resolutionNatTrans.app L)), eq]
  have : QuasiIso ((Minus.ι A).map f) := hf
  infer_instance

end

end LeftResolutions

end Abelian

end CategoryTheory
