/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.LeftResolution.Basic
public import Mathlib.Algebra.Homology.BicomplexRows
public import Mathlib.Algebra.Homology.CochainComplexMinus
public import Mathlib.Algebra.Homology.TotalComplexMap

/-!
# Resolutions of bounded above complexes

-/

@[expose] public section

namespace CategoryTheory

open Category Limits CochainComplex

namespace Abelian

namespace LeftResolution

variable {A C : Type*} [Category C] [Category A] {ι : C ⥤ A}
  [ι.Full] [ι.Faithful] [Preadditive C] [HasZeroObject C]
  [Abelian A] (Λ : LeftResolution ι)

variable [Λ.F.PreservesZeroMorphisms]

set_option backward.isDefEq.respectTransparency false in
instance : Λ.chainComplexFunctor.PreservesZeroMorphisms where
  map_zero _ _ := by
    simp [chainComplexFunctor]

set_option backward.isDefEq.respectTransparency false in
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

instance (K : CochainComplex A ℤ) (i : ℤ) [K.IsStrictlyLE i] :
    IsStrictlyLE ((bicomplexFunctor Λ ⋙
      Functor.mapHomologicalComplex₂ ι (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K) i := by
  dsimp
  infer_instance

instance (K : CochainComplex A ℤ) (i : ℤ) :
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
    [(Λ.bicomplexFunctor.obj K).HasTotal (ComplexShape.up ℤ)] :
    CochainComplex.IsStrictlyLE ((Λ.bicomplexFunctor.obj K).total (ComplexShape.up ℤ)) i where
  isZero n hn := by
    rw [IsZero.iff_id_eq_zero]
    ext i₁ i₂ h
    dsimp at h hn
    apply IsZero.eq_of_src
    by_cases hi₂ : 0 < i₂
    · exact CochainComplex.isZero_of_isStrictlyLE _ 0 _ hi₂
    · have : IsZero (((Λ.bicomplexFunctor).obj K).X i₁) := by
        refine CochainComplex.isZero_of_isStrictlyLE _ i _ ?_
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
noncomputable def totalπ' :
    ((ι.mapHomologicalComplex₂ _ _).obj (Λ.bicomplexFunctor.obj K.obj)).total (ComplexShape.up ℤ) ⟶
      ((HomologicalComplex₂.singleRow A
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) 0).obj K.obj).total (ComplexShape.up ℤ) :=
  HomologicalComplex₂.total.map (Λ.bicomplexπ.app K.obj) (ComplexShape.up ℤ)

set_option backward.isDefEq.respectTransparency false in
omit [HasFiniteCoproducts C] in
variable {K L} in
@[reassoc (attr := simp)]
lemma totalπ'_naturality :
    (HomologicalComplex₂.total.map
      ((ι.mapHomologicalComplex₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
        (Λ.bicomplexFunctor.map φ.hom)) (ComplexShape.up ℤ)) ≫ Λ.totalπ' L =
      Λ.totalπ' K ≫ HomologicalComplex₂.total.map
        ((HomologicalComplex₂.singleRow A (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) 0).map φ.hom) (ComplexShape.up ℤ) := by
  dsimp [totalπ']
  simp only [← HomologicalComplex₂.total.map_comp]
  congr 1
  ext x y
  by_cases hy : y = 0
  · subst hy
    have eq := Λ.π.naturality (φ.hom.f x)
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

set_option backward.isDefEq.respectTransparency false in
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

noncomputable def minusResolutionFunctor : CochainComplex.Minus A ⥤ CochainComplex.Minus C where
  obj K := ⟨((Λ.bicomplexFunctor.obj K.obj).total (ComplexShape.up ℤ)), by
    obtain ⟨i, hi⟩ := K.2
    exact ⟨i, inferInstance⟩⟩
  map {K L} φ := ObjectProperty.homMk
    (HomologicalComplex₂.total.map (Λ.bicomplexFunctor.map φ.hom) (ComplexShape.up ℤ))
  map_id K := by
    erw [Λ.bicomplexFunctor.map_id, HomologicalComplex₂.total.map_id]
    rfl
  map_comp φ ψ := by
    erw [Λ.bicomplexFunctor.map_comp, HomologicalComplex₂.total.map_comp]
    rfl

noncomputable def minusResolutionNatTrans :
    Λ.minusResolutionFunctor ⋙ ι.mapCochainComplexMinus ⟶ 𝟭 _ where
  app _ := ObjectProperty.homMk (Λ.totalπ _)
  naturality {K L} f := by
    ext : 1
    dsimp [minusResolutionFunctor, totalπ]
    erw [HomologicalComplex₂.mapTotalIso_inv_naturality_assoc]
    rw [totalπ'_naturality_assoc]
    erw [assoc ((HomologicalComplex₂.mapTotalIso ι _ (ComplexShape.up ℤ)).inv), assoc]
    rw [HomologicalComplex₂.singleRow₀ObjTotal_hom_naturality]

lemma quasiIso_minusResolutionNatTrans_app (K : CochainComplex.Minus A) :
    Minus.quasiIso _ (Λ.minusResolutionNatTrans.app K) :=
  inferInstanceAs (QuasiIso (Λ.totalπ K))

instance (K : CochainComplex.Minus A) :
    QuasiIso (Λ.minusResolutionNatTrans.app K).hom :=
  Λ.quasiIso_minusResolutionNatTrans_app K

set_option backward.isDefEq.respectTransparency false in
instance (K : Minus A) :
    QuasiIso ((Functor.whiskerRight Λ.minusResolutionNatTrans (Minus.ι A)).app K) := by
  dsimp; infer_instance

set_option backward.isDefEq.respectTransparency false in
lemma quasiIso_minusResolutionFunctor_map {K L : CochainComplex.Minus A} (f : K ⟶ L)
    (hf : Minus.quasiIso _ f) :
    Minus.quasiIso _ (ι.mapCochainComplexMinus.map (Λ.minusResolutionFunctor.map f)) := by
  have : QuasiIso f.hom := hf
  have eq := (CochainComplex.Minus.ι _).congr_map (Λ.minusResolutionNatTrans.naturality f)
  dsimp at eq
  change QuasiIso _
  rw [← quasiIso_iff_comp_right _ (Λ.minusResolutionNatTrans.app L).hom]
  dsimp
  rw [eq]
  infer_instance

end

end LeftResolution

end Abelian

end CategoryTheory
