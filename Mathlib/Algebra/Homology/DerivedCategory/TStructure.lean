import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Triangulated.TStructure.Homology

open CategoryTheory Category Pretriangulated Triangulated Limits Preadditive

universe w

namespace CategoryTheory

lemma Full.ofCompLeft {C D E : Type _} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) (hFG : Full (F ⋙ G)) (hF : EssSurj F) :
    Full G := Functor.fullOfSurjective _ (fun X' Y' f => by
  let φ : (F ⋙ G).obj _ ⟶ (F ⋙ G).obj _ :=
    G.map (F.objObjPreimageIso X').hom ≫ f ≫ G.map (F.objObjPreimageIso Y').inv
  let f' := (F ⋙ G).preimage φ
  have hf' : G.map (F.map f') = _ := (F ⋙ G).image_preimage φ
  refine' ⟨(F.objObjPreimageIso X').inv ≫ F.map f' ≫ (F.objObjPreimageIso Y').hom, _⟩
  rw [G.map_comp, G.map_comp, hf']
  simp only [φ, Functor.comp_obj, assoc, ← G.map_comp, ← G.map_comp_assoc,
    Iso.inv_hom_id, G.map_id, id_comp, comp_id])

lemma Faithful.ofCompLeft {C D E : Type _} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) (hFG : Faithful (F ⋙ G)) (hF : EssSurj F) (hF' : Full F) :
    Faithful G where
  map_injective {X' Y'} := fun f₁ f₂ hf => by
    obtain ⟨g₁, hg₁⟩ := F.map_surjective
      ((Functor.objObjPreimageIso F X').hom ≫ f₁ ≫ (Functor.objObjPreimageIso F Y').inv)
    obtain ⟨g₂, hg₂⟩ := F.map_surjective
      ((Functor.objObjPreimageIso F X').hom ≫ f₂ ≫ (Functor.objObjPreimageIso F Y').inv)
    suffices g₁ = g₂ by
      rw [← cancel_mono (F.objObjPreimageIso Y').inv,
        ← cancel_epi (F.objObjPreimageIso X').hom, ← hg₁, ← hg₂, this]
    apply (F ⋙ G).map_injective
    dsimp
    simp only [hg₁, hg₂, G.map_comp, hf]

end CategoryTheory

namespace DerivedCategory

variable {C : Type _} [Category C] [Abelian C] [HasDerivedCategory.{w} C]

namespace TStructure

namespace t_aux

variable {K L : CochainComplex C ℤ} [K.IsStrictlyLE 0]

lemma zero₁ (f : K ⟶ L) [L.IsGE 1] : Q.map f = 0 := by
  have : QuasiIso (L.πTruncGE 1) := by
    rw [CochainComplex.quasiIso_πTruncGE_iff]
    infer_instance
  have hK : IsZero (K.truncGE 1) := by
    rw [IsZero.iff_id_eq_zero]
    ext n
    by_cases hn : 0 < n
    · apply (CochainComplex.isZero_of_isStrictlyLE _ 0 _ hn).eq_of_src
    · simp only [not_lt] at hn
      apply (CochainComplex.isZero_of_isStrictlyGE _ 1 _ (by omega)).eq_of_tgt
  rw [← cancel_mono (Q.map (L.πTruncGE 1)), zero_comp, ← Q.map_comp,
    ← CochainComplex.πTruncGE_naturality, hK.eq_of_tgt (K.πTruncGE 1) 0,
    zero_comp, Q.map_zero]

lemma zero (f : Q.obj K ⟶ Q.obj L) [L.IsGE 1] : f = 0 := by
  obtain ⟨L', g, s, hs, fac⟩ := left_fac _ _ f
  rw [← cancel_mono (Q.map s), zero_comp, fac, assoc, IsIso.inv_hom_id, comp_id]
  have : L'.IsGE 1 := by
    rw [CochainComplex.isGE_iff]
    intro i hi
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    apply ((L.exactAt_of_isGE 1 i hi).isZero_homology).of_iso
    rw [isIso_Q_map_iff_quasiIso] at hs
    exact (asIso (HomologicalComplex.homologyMap s i)).symm
  exact zero₁ g

end t_aux

def t : TStructure (DerivedCategory C) where
  setLE n X := ∃ (K : CochainComplex C ℤ) (_ : X ≅ DerivedCategory.Q.obj K), K.IsStrictlyLE n
  setGE n X := ∃ (K : CochainComplex C ℤ) (_ : X ≅ DerivedCategory.Q.obj K), K.IsStrictlyGE n
  setLE_respectsIso n :=
    { mem_of_iso := by
        rintro X Y e ⟨K, e', _⟩
        exact ⟨K, e.symm ≪≫ e', inferInstance⟩ }
  setGE_respectsIso n :=
    { mem_of_iso := by
        rintro X Y e ⟨K, e', _⟩
        exact ⟨K, e.symm ≪≫ e', inferInstance⟩ }
  shift_mem_setLE := by
    rintro n a n' h X ⟨K, e, _⟩
    exact ⟨(shiftFunctor (CochainComplex C ℤ) a).obj K,
      (shiftFunctor (DerivedCategory C) a).mapIso e ≪≫ (Q.commShiftIso a).symm.app K,
      K.isStrictlyLE_shift n a n' h⟩
  shift_mem_setGE := by
    rintro n a n' h X ⟨K, e, _⟩
    exact ⟨(shiftFunctor (CochainComplex C ℤ) a).obj K,
      (shiftFunctor (DerivedCategory C) a).mapIso e ≪≫ (Q.commShiftIso a).symm.app K,
      K.isStrictlyGE_shift n a n' h⟩
  zero' X Y f := by
    rintro ⟨K, e₁, _⟩ ⟨L, e₂, _⟩
    rw [← cancel_epi e₁.inv, ← cancel_mono e₂.hom, comp_zero, zero_comp]
    apply t_aux.zero
  setLE_zero_subset := by
    rintro X ⟨K, e, _⟩
    exact ⟨K, e, K.isStrictlyLE_of_LE 0 1 (by omega)⟩
  setGE_one_subset := by
    rintro X ⟨K, e, _⟩
    exact ⟨K, e, K.isStrictlyGE_of_GE 0 1 (by omega)⟩
  exists_triangle_zero_one X := by
    obtain ⟨K, ⟨e₂⟩⟩ : ∃ K, Nonempty (Q.obj K ≅ X) := ⟨_, ⟨Q.objObjPreimageIso X⟩⟩
    have h := K.shortComplexTruncLE_shortExact 0
    refine' ⟨Q.obj (K.truncLE 0), Q.obj (K.truncGE 1),
      ⟨_, Iso.refl _, inferInstance⟩, ⟨_, Iso.refl _, inferInstance⟩,
      Q.map (K.ιTruncLE 0) ≫ e₂.hom, e₂.inv ≫ Q.map (K.πTruncGE 1),
      inv (Q.map (K.shortComplexTruncLEX₃ToTruncGE 0 1 (by omega))) ≫ (triangleOfSES h).mor₃,
      isomorphic_distinguished _ (triangleOfSES_distinguished h) _ (Iso.symm _)⟩
    refine' Triangle.isoMk _ _ (Iso.refl _) e₂
      (asIso (Q.map (K.shortComplexTruncLEX₃ToTruncGE 0 1 (by omega)))) _ _ (by simp)
    · dsimp
      rw [id_comp]
      rfl
    · dsimp
      rw [← Q.map_comp, CochainComplex.g_shortComplexTruncLEX₃ToTruncGE,
        Iso.hom_inv_id_assoc]

end TStructure

abbrev IsLE (X : DerivedCategory C) (n : ℤ) : Prop := TStructure.t.IsLE X n
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
  have eq := fun i => ((homologyFunctorFactors C i).app K).isZero_iff
  simp only [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj] at eq
  simp only [isGE_iff, CochainComplex.isGE_iff,
    HomologicalComplex.exactAt_iff_isZero_homology, eq]

lemma isLE_Q_obj_iff (K : CochainComplex C ℤ) (n : ℤ) :
    (Q.obj K).IsLE n ↔ K.IsLE n := by
  have eq := fun i => ((homologyFunctorFactors C i).app K).isZero_iff
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

lemma right_fac_of_isStrictlyLE (X Y : CochainComplex C ℤ) (f : Q.obj X ⟶ Q.obj Y) (n : ℤ)
    [X.IsStrictlyLE n] :
    ∃ (X' : CochainComplex C ℤ) (_ : X'.IsStrictlyLE n) (s : X' ⟶ X) (hs : IsIso (Q.map s))
      (g : X' ⟶ Y), f = inv (Q.map s) ≫ Q.map g := by
  obtain ⟨X', s, hs, g, rfl⟩ := right_fac X Y f
  have : IsIso (Q.map (CochainComplex.truncLEMap s n)) := by
    rw [isIso_Q_map_iff_quasiIso, CochainComplex.quasiIso_truncLEMap_iff]
    rw [isIso_Q_map_iff_quasiIso] at hs
    infer_instance
  refine' ⟨X'.truncLE n, inferInstance, CochainComplex.truncLEMap s n ≫ X.ιTruncLE n, _,
      CochainComplex.truncLEMap g n ≫ Y.ιTruncLE n, _⟩
  · rw [Q.map_comp]
    infer_instance
  · have eq := Q.congr_map (CochainComplex.ιTruncLE_naturality s n)
    have eq' := Q.congr_map (CochainComplex.ιTruncLE_naturality g n)
    simp only [Functor.map_comp] at eq eq'
    simp only [Functor.map_comp, ← cancel_epi (Q.map (CochainComplex.truncLEMap s n) ≫
      Q.map (CochainComplex.ιTruncLE X n)), IsIso.hom_inv_id_assoc, assoc, reassoc_of% eq, eq']

lemma left_fac_of_isStrictlyGE (X Y : CochainComplex C ℤ) (f : Q.obj X ⟶ Q.obj Y) (n : ℤ)
    [Y.IsStrictlyGE n] :
    ∃ (Y' : CochainComplex C ℤ) (_ : Y'.IsStrictlyGE n) (g : X ⟶ Y') (s : Y ⟶ Y')
      (hs : IsIso (Q.map s)), f = Q.map g ≫ inv (Q.map s) := by
  obtain ⟨Y', g, s, hs, rfl⟩ := left_fac X Y f
  have : IsIso (Q.map (CochainComplex.truncGEMap s n)) := by
    rw [isIso_Q_map_iff_quasiIso, CochainComplex.quasiIso_truncGEMap_iff]
    rw [isIso_Q_map_iff_quasiIso] at hs
    infer_instance
  refine' ⟨Y'.truncGE n, inferInstance, X.πTruncGE n ≫ CochainComplex.truncGEMap g n,
    Y.πTruncGE n ≫ CochainComplex.truncGEMap s n, _, _⟩
  · rw [Q.map_comp]
    infer_instance
  · have eq := Q.congr_map (CochainComplex.πTruncGE_naturality s n)
    have eq' := Q.congr_map (CochainComplex.πTruncGE_naturality g n)
    simp only [Functor.map_comp] at eq eq'
    simp only [Functor.map_comp, ← cancel_mono (Q.map (CochainComplex.πTruncGE Y n)
      ≫ Q.map (CochainComplex.truncGEMap s n)), assoc, IsIso.inv_hom_id, comp_id]
    simp only [eq, IsIso.inv_hom_id_assoc, eq']

lemma right_fac_of_isStrictlyLE_of_isStrictlyGE
    (X Y : CochainComplex C ℤ) (a b : ℤ) [X.IsStrictlyGE a] [X.IsStrictlyLE b]
    [Y.IsStrictlyGE a] (f : Q.obj X ⟶ Q.obj Y) :
    ∃ (X' : CochainComplex C ℤ) ( _ : X'.IsStrictlyGE a) (_ : X'.IsStrictlyLE b)
    (s : X' ⟶ X) (hs : IsIso (Q.map s)) (g : X' ⟶ Y), f = inv (Q.map s) ≫ Q.map g := by
  obtain ⟨X', hX', s, hs, g, fac⟩ := right_fac_of_isStrictlyLE _ _ f b
  have : IsIso (Q.map (CochainComplex.truncGEMap s a)) := by
    rw [isIso_Q_map_iff_quasiIso] at hs
    rw [isIso_Q_map_iff_quasiIso, CochainComplex.quasiIso_truncGEMap_iff]
    infer_instance
  refine' ⟨X'.truncGE a, inferInstance, inferInstance,
    CochainComplex.truncGEMap s a ≫ inv (X.πTruncGE a), _,
      CochainComplex.truncGEMap g a ≫ inv (Y.πTruncGE a), _⟩
  · rw [Q.map_comp]
    infer_instance
  · simp only [Functor.map_comp, Functor.map_inv, IsIso.inv_comp, IsIso.inv_inv, assoc, fac,
      ← cancel_epi (Q.map s), IsIso.hom_inv_id_assoc]
    simp only [← Functor.map_comp_assoc, ← CochainComplex.πTruncGE_naturality s a]
    simp only [Functor.map_comp, assoc, IsIso.hom_inv_id_assoc]
    simp only [← Functor.map_comp_assoc, CochainComplex.πTruncGE_naturality g a]
    simp only [Functor.map_comp, assoc, IsIso.hom_inv_id, comp_id]

lemma left_fac_of_isStrictlyLE_of_isStrictlyGE
    (X Y : CochainComplex C ℤ) (a b : ℤ)
    [X.IsStrictlyLE b] [Y.IsStrictlyGE a] [Y.IsStrictlyLE b] (f : Q.obj X ⟶ Q.obj Y) :
    ∃ (Y' : CochainComplex C ℤ) ( _ : Y'.IsStrictlyGE a) (_ : Y'.IsStrictlyLE b)
    (g : X ⟶ Y') (s : Y ⟶ Y') (hs : IsIso (Q.map s)) , f = Q.map g ≫ inv (Q.map s) := by
  obtain ⟨Y', hY', g, s, hs, fac⟩ := left_fac_of_isStrictlyGE _ _ f a
  have : IsIso (Q.map (CochainComplex.truncLEMap s b)) := by
    rw [isIso_Q_map_iff_quasiIso] at hs
    rw [isIso_Q_map_iff_quasiIso, CochainComplex.quasiIso_truncLEMap_iff]
    infer_instance
  refine' ⟨Y'.truncLE b, inferInstance, inferInstance,
    inv (X.ιTruncLE b) ≫ CochainComplex.truncLEMap g b,
    inv (Y.ιTruncLE b) ≫ CochainComplex.truncLEMap s b, _, _⟩
  · rw [Q.map_comp]
    infer_instance
  · simp only [Functor.map_comp, Functor.map_inv, IsIso.inv_comp, IsIso.inv_inv, assoc, fac,
      ← cancel_mono (Q.map s), IsIso.inv_hom_id, comp_id]
    simp only [← Functor.map_comp, ← CochainComplex.ιTruncLE_naturality s b]
    simp only [Functor.map_comp, IsIso.inv_hom_id_assoc]
    simp only [← Functor.map_comp, CochainComplex.ιTruncLE_naturality g b]
    simp only [Functor.map_comp, IsIso.inv_hom_id_assoc]

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
    ((SingleFunctors.evaluation _ _ n).mapIso (singleFunctorsPostCompQIso C)).symm.app A⟩⟩

instance (n : ℤ) : Faithful (singleFunctor C n) := ⟨fun {A B} f₁ f₂ h => by
  have eq₁ := NatIso.naturality_1 (singleFunctorCompHomologyFunctorIso C n) f₁
  have eq₂ := NatIso.naturality_1 (singleFunctorCompHomologyFunctorIso C n) f₂
  dsimp at eq₁ eq₂
  rw [← eq₁, ← eq₂, h]⟩

noncomputable instance (n : ℤ) : Full (CochainComplex.singleFunctor C n) :=
  (inferInstance : Full (HomologicalComplex.single _ _ _))

noncomputable instance (n : ℤ) : Full (CochainComplex.singleFunctor C n ⋙ Q) := by
  apply Functor.fullOfSurjective
  intro A B f
  suffices ∃ (f' : (CochainComplex.singleFunctor C n).obj A ⟶
    (CochainComplex.singleFunctor C n).obj B), f = Q.map f' by
    obtain ⟨f', rfl⟩ := this
    obtain ⟨g, hg⟩ := (CochainComplex.singleFunctor C n).map_surjective f'
    refine' ⟨g, _⟩
    dsimp
    rw [hg]
  obtain ⟨X, _, _, s, hs, g, fac⟩ := right_fac_of_isStrictlyLE_of_isStrictlyGE _ _ n n f
  have : IsIso s := by
    obtain ⟨A', ⟨e⟩⟩ := X.exists_iso_single n
    have ⟨φ, hφ⟩ := (CochainComplex.singleFunctor C n).map_surjective (e.inv ≫ s)
    suffices IsIso φ by
      have : IsIso (e.inv ≫ s) := by
        rw [← hφ]
        infer_instance
      exact IsIso.of_isIso_comp_left e.inv s
    apply (NatIso.isIso_map_iff (singleFunctorCompHomologyFunctorIso C n) φ).1
    have : IsIso (Q.map ((CochainComplex.singleFunctor C n).map φ)) := by
      rw [hφ]
      rw [Q.map_comp]
      infer_instance
    have : IsIso ((singleFunctor C n).map φ) :=
      (NatIso.isIso_map_iff ((SingleFunctors.evaluation _ _ n).mapIso
        (singleFunctorsPostCompQIso C)) φ).2 this
    dsimp
    infer_instance
  exact ⟨inv s ≫ g, by rw [Q.map_comp, fac, Q.map_inv]⟩

noncomputable instance (n : ℤ) : Full (singleFunctor C n) := by
  have : _ ≅ (CochainComplex.singleFunctor C n ⋙ Q) := ((SingleFunctors.evaluation _ _ n).mapIso (singleFunctorsPostCompQIso C))
  exact Full.ofIso this.symm

lemma singleFunctor_preimage {A B : C} {n : ℤ}
    (f : (singleFunctor C n).obj A ⟶  (singleFunctor C n).obj B) :
    (singleFunctor C n).preimage f = (singleFunctorCompHomologyFunctorIso C n).inv.app A ≫
        (homologyFunctor _ n).map f ≫ (singleFunctorCompHomologyFunctorIso C n).hom.app B := by
  obtain ⟨φ, rfl⟩ := (singleFunctor C n).map_surjective f
  erw [preimage_map, ← NatTrans.naturality_assoc, Iso.inv_hom_id_app, comp_id, Functor.id_map]

namespace TStructure

lemma singleFunctor_obj_mem_heart (X : C) :
    t.heart ((singleFunctor C 0).obj X) := by
  rw [TStructure.mem_heart_iff]
  constructor <;> infer_instance

@[simp]
lemma essImage_singleFunctor_eq_heart :
    (singleFunctor C 0).essImage = setOf t.heart := by
  ext X
  constructor
  · rintro ⟨A, ⟨e⟩⟩
    exact mem_of_iso t.heart e (singleFunctor_obj_mem_heart A)
  · intro (h : t.heart _)
    rw [TStructure.mem_heart_iff] at h
    have := h.1
    have := h.2
    obtain ⟨A, ⟨e⟩⟩ := exists_iso_single X 0
    exact ⟨A, ⟨e.symm⟩⟩

noncomputable instance : (t : TStructure (DerivedCategory C)).HasHeart where
  ι := singleFunctor C 0

variable (C)

/-namespace HeartEquivalence

variable {C}

noncomputable def functor : (t : TStructure (DerivedCategory C)).Heart' ⥤ C :=
  t.ιHeart' ⋙ homologyFunctor C 0

noncomputable def inverse : C ⥤ (t : TStructure (DerivedCategory C)).Heart' :=
  FullSubcategory.lift _ (singleFunctor C 0) singleFunctor_obj_mem_heart

noncomputable def inverseCompιHeart : (inverse : C ⥤ _) ⋙ t.ιHeart' ≅ singleFunctor C 0 :=
  FullSubcategory.lift_comp_inclusion _ _ _

noncomputable instance : Full (inverse : C ⥤ _) := Functor.fullOfSurjective  _ (by
  intro A B (φ : (singleFunctor C 0).obj A ⟶ (singleFunctor C 0).obj B)
  obtain ⟨f, rfl⟩ := (singleFunctor C 0).map_surjective φ
  exact ⟨_, rfl⟩)

instance : Faithful (inverse : C ⥤ _) := ⟨by
  intro A B f₁ f₂ h
  exact (singleFunctor C 0).map_injective h⟩

instance : EssSurj (inverse : C ⥤ _) := ⟨fun X => by
  have : X.obj.IsLE 0 := X.2.1
  have : X.obj.IsGE 0 := X.2.2
  obtain ⟨A, ⟨e⟩⟩ := exists_iso_single X.obj 0
  exact ⟨A, ⟨t.ιHeart'.preimageIso e.symm⟩⟩⟩

noncomputable def counitIso : inverse ⋙ functor ≅ 𝟭 C :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight inverseCompιHeart _ ≪≫ singleFunctorCompHomologyFunctorIso C 0

noncomputable instance : Full (functor : _ ⥤ C) :=
  Full.ofCompLeft (inverse : C ⥤ _) functor (Full.ofIso counitIso.symm) inferInstance

instance : Faithful (functor : _ ⥤ C) :=
  Faithful.ofCompLeft (inverse : C ⥤ _) functor (Faithful.of_iso counitIso.symm)
    inferInstance inferInstance

noncomputable def unitIso :
    𝟭 (t : TStructure (DerivedCategory C)).Heart' ≅ functor ⋙ inverse :=
  natIsoOfCompFullyFaithful functor
    (Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm ≪≫
    isoWhiskerLeft _ counitIso.symm ≪≫ (Functor.associator _ _ _).symm)

@[simp]
lemma functor_map_unitIso_hom_app (X : (t : TStructure (DerivedCategory C)).Heart') :
    functor.map (unitIso.hom.app X) = counitIso.inv.app (functor.obj X) := by
  simp [unitIso]

@[simp]
lemma functor_map_unitIso_inv_app (X : (t : TStructure (DerivedCategory C)).Heart') :
    functor.map (unitIso.inv.app X) = counitIso.hom.app (functor.obj X) := by
  simp [unitIso]

end HeartEquivalence

@[simps]
noncomputable def heartEquivalence :
    (t : TStructure (DerivedCategory C)).Heart' ≌ C where
  functor := HeartEquivalence.functor
  inverse := HeartEquivalence.inverse
  unitIso := HeartEquivalence.unitIso
  counitIso := HeartEquivalence.counitIso

noncomputable def heartEquivalenceInverseCompιHeart :
    (heartEquivalence C).inverse ⋙ t.ιHeart' ≅ singleFunctor C 0 :=
  HeartEquivalence.inverseCompιHeart-/

variable {C}

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

/-noncomputable def homologyCompFunctorIso (q : ℤ) :
    t.homology' q ⋙ (heartEquivalence C).functor ≅
      homologyFunctor C q := by
  refine' (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (t.homologyCompιHeart' q) _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ ((homologyFunctor C 0).shiftIso q 0 q (add_zero q)) ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (truncGECompHomologyFunctorIso C q q (by rfl)) ≪≫
    truncLECompHomologyFunctorIso C q q (by rfl)

noncomputable def homologyIsoHomologyFunctorCompInverse (q : ℤ) :
    t.homology' q ≅ homologyFunctor C q ⋙ (heartEquivalence C).inverse :=
  natIsoOfCompFullyFaithful (heartEquivalence C).functor
    (homologyCompFunctorIso C q ≪≫ (Functor.rightUnitor _).symm ≪≫
    isoWhiskerLeft _ (heartEquivalence C).counitIso.symm ≪≫ (Functor.associator _ _ _).symm)

noncomputable def homologyιHeart (q : ℤ) :
    t.homology' q ⋙ t.ιHeart' ≅ homologyFunctor C q ⋙ singleFunctor C 0 :=
  isoWhiskerRight (homologyIsoHomologyFunctorCompInverse C q) _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (heartEquivalenceInverseCompιHeart C).symm-/

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

abbrev Minus := (t : TStructure (DerivedCategory C)).minus.category
abbrev Plus := (t : TStructure (DerivedCategory C)).plus.category
--abbrev Bounded := (t : TStructure (DerivedCategory C)).bounded.category

variable {C}

abbrev Minus.ι : Minus C ⥤ DerivedCategory C := t.minus.ι
abbrev Plus.ι : Plus C ⥤ DerivedCategory C := t.plus.ι
--abbrev ιBounded : Bounded C ⥤ DerivedCategory C := t.bounded.ι

end DerivedCategory
