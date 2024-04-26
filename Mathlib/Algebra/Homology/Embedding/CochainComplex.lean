import Mathlib.Algebra.Homology.Embedding.ComplementaryTrunc
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

open CategoryTheory Category Limits ComplexShape ZeroObject

namespace CochainComplex

variable {C : Type*} [Category C]

open HomologicalComplex

section HasZeroMorphisms

variable [HasZeroMorphisms C]

variable (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

section

variable [HasZeroObject C] [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]

noncomputable abbrev truncLE (n : ℤ) : CochainComplex C ℤ :=
  HomologicalComplex.truncLE K (embeddingUpIntLE n)

noncomputable abbrev truncGE (n : ℤ) : CochainComplex C ℤ :=
  HomologicalComplex.truncGE K (embeddingUpIntGE n)

noncomputable def ιTruncLE (n : ℤ) : K.truncLE n ⟶ K :=
  HomologicalComplex.ιTruncLE K (embeddingUpIntLE n)

noncomputable def πTruncGE (n : ℤ) : K ⟶ K.truncGE n :=
  HomologicalComplex.πTruncGE K (embeddingUpIntGE n)

section

variable {K L}

noncomputable def truncLEMap (n : ℤ) : K.truncLE n ⟶ L.truncLE n :=
  HomologicalComplex.truncLEMap φ (embeddingUpIntLE n)

noncomputable def truncGEMap (n : ℤ) : K.truncGE n ⟶ L.truncGE n :=
  HomologicalComplex.truncGEMap φ (embeddingUpIntGE n)

@[reassoc (attr := simp)]
lemma ιTruncLE_naturality (n : ℤ) :
    truncLEMap φ n ≫ L.ιTruncLE n = K.ιTruncLE n ≫ φ := by
  apply HomologicalComplex.ιTruncLE_naturality

@[reassoc (attr := simp)]
lemma πTruncGE_naturality (n : ℤ) :
    K.πTruncGE n ≫ truncGEMap φ n = φ ≫ L.πTruncGE n := by
  apply HomologicalComplex.πTruncGE_naturality

end

end

abbrev IsStrictlyGE (n : ℤ) := K.IsStrictlySupported (embeddingUpIntGE n)
abbrev IsStrictlyLE (n : ℤ) := K.IsStrictlySupported (embeddingUpIntLE n)
abbrev IsGE (n : ℤ) := K.IsSupported (embeddingUpIntGE n)
abbrev IsLE (n : ℤ) := K.IsSupported (embeddingUpIntLE n)

lemma isZero_of_isStrictlyGE (n i : ℤ) (hi : i < n) [K.IsStrictlyGE n] :
    IsZero (K.X i) :=
  isZero_X_of_isStrictlySupported K (embeddingUpIntGE n) i
    (by simpa only [not_mem_range_embeddingUpIntGE_iff] using hi)

lemma isZero_of_isStrictlyLE (n i : ℤ) (hi : n < i) [K.IsStrictlyLE n] :
    IsZero (K.X i) :=
  isZero_X_of_isStrictlySupported K (embeddingUpIntLE n) i
    (by simpa only [not_mem_range_embeddingUpIntLE_iff] using hi)

lemma exactAt_of_isGE (n i : ℤ) (hi : i < n) [K.IsGE n] :
    K.ExactAt i :=
  exactAt_of_isSupported K (embeddingUpIntGE n) i
    (by simpa only [not_mem_range_embeddingUpIntGE_iff] using hi)

lemma exactAt_of_isLE (n i : ℤ) (hi : n < i) [K.IsLE n] :
    K.ExactAt i :=
  exactAt_of_isSupported K (embeddingUpIntLE n) i
    (by simpa only [not_mem_range_embeddingUpIntLE_iff] using hi)

lemma isZero_of_isGE (n i : ℤ) (hi : i < n) [K.IsGE n] [K.HasHomology i]:
    IsZero (K.homology i) :=
  (K.exactAt_of_isGE n i hi).isZero_homology

lemma isZero_of_isLE (n i : ℤ) (hi : n < i) [K.IsLE n] [K.HasHomology i]:
    IsZero (K.homology i) :=
  (K.exactAt_of_isLE n i hi).isZero_homology

lemma isStrictlyGE_iff (n : ℤ) :
    K.IsStrictlyGE n ↔ ∀ (i : ℤ) (_ : i < n), IsZero (K.X i) := by
  constructor
  · intro _ i hi
    exact K.isZero_of_isStrictlyGE n i hi
  · intro h
    refine' IsStrictlySupported.mk (fun i hi => _)
    rw [not_mem_range_embeddingUpIntGE_iff] at hi
    exact h i hi

lemma isStrictlyLE_iff (n : ℤ) :
    K.IsStrictlyLE n ↔ ∀ (i : ℤ) (_ : n < i), IsZero (K.X i) := by
  constructor
  · intro _ i hi
    exact K.isZero_of_isStrictlyLE n i hi
  · intro h
    refine' IsStrictlySupported.mk (fun i hi => _)
    rw [not_mem_range_embeddingUpIntLE_iff] at hi
    exact h i hi

lemma isGE_iff (n : ℤ) :
    K.IsGE n ↔ ∀ (i : ℤ) (_ : i < n), K.ExactAt i := by
  constructor
  · intro _ i hi
    exact K.exactAt_of_isGE n i hi
  · intro h
    refine' IsSupported.mk (fun i hi => _)
    rw [not_mem_range_embeddingUpIntGE_iff] at hi
    exact h i hi

lemma isLE_iff (n : ℤ) :
    K.IsLE n ↔ ∀ (i : ℤ) (_ : n < i), K.ExactAt i := by
  constructor
  · intro _ i hi
    exact K.exactAt_of_isLE n i hi
  · intro h
    refine' IsSupported.mk (fun i hi => _)
    rw [not_mem_range_embeddingUpIntLE_iff] at hi
    exact h i hi

lemma isStrictlyLE_of_LE (p q : ℤ) (hpq : p ≤ q) [K.IsStrictlyLE p] :
    K.IsStrictlyLE q := by
  rw [isStrictlyLE_iff]
  intro i hi
  apply K.isZero_of_isStrictlyLE p
  omega

lemma isStrictlyGE_of_GE (p q : ℤ) (hpq : p ≤ q) [K.IsStrictlyGE q] :
    K.IsStrictlyGE p := by
  rw [isStrictlyGE_iff]
  intro i hi
  apply K.isZero_of_isStrictlyGE q
  omega

lemma isLE_of_LE (p q : ℤ) (hpq : p ≤ q) [K.IsLE p] :
    K.IsLE q := by
  rw [isLE_iff]
  intro i hi
  apply K.exactAt_of_isLE p
  omega

lemma isGE_of_GE (p q : ℤ) (hpq : p ≤ q) [K.IsGE q] :
    K.IsGE p := by
  rw [isGE_iff]
  intro i hi
  apply K.exactAt_of_isGE q
  omega

variable {K L}

lemma isStrictlyLE_of_iso (n : ℤ) [K.IsStrictlyLE n] : L.IsStrictlyLE n := by
  apply isStrictlySupported_of_iso e

lemma isStrictlyGE_of_iso (n : ℤ) [K.IsStrictlyGE n] : L.IsStrictlyGE n := by
  apply isStrictlySupported_of_iso e

lemma isLE_of_iso (n : ℤ) [K.IsLE n] : L.IsLE n := by
  apply isSupported_of_iso e

lemma isGE_of_iso (n : ℤ) [K.IsGE n] : L.IsGE n := by
  apply isSupported_of_iso e

lemma exists_iso_single [HasZeroObject C] (n : ℤ) [K.IsStrictlyGE n] [K.IsStrictlyLE n] :
    ∃ (M : C), Nonempty (K ≅ (single _ _ n).obj M) := by
  refine' ⟨K.X n, ⟨_⟩⟩
  refine' HomologicalComplex.Hom.isoOfComponents _ _
  · intro i
    by_cases h : i = n
    · subst h
      exact (singleObjXSelf _ _ _).symm
    · refine' IsZero.isoZero _ ≪≫ (IsZero.isoZero _).symm
      · by_cases hi' : i ≤ n
        · refine' K.isZero_of_isStrictlyGE n i _
          cases hi'.lt_or_eq <;> tauto
        · exact K.isZero_of_isStrictlyLE n i (by linarith)
      · exact isZero_single_obj_X _ _ _ _ h
  · intro i j (hij : i + 1 = j)
    simp only [single_obj_d, comp_zero]
    by_cases h : i < n
    · apply (K.isZero_of_isStrictlyGE n i h).eq_of_src
    · apply IsZero.eq_of_tgt
      apply isZero_single_obj_X
      linarith

variable [HasZeroObject C]
instance (A : C) (n : ℤ) :
    IsStrictlyGE ((single C (ComplexShape.up ℤ) n).obj A) n := by
  rw [isStrictlyGE_iff]
  intro i hi
  apply isZero_single_obj_X
  omega

instance (A : C) (n : ℤ) :
    IsStrictlyLE ((single C (ComplexShape.up ℤ) n).obj A) n := by
  rw [isStrictlyLE_iff]
  intro i hi
  apply isZero_single_obj_X
  omega

section

variable [∀ (i : ℤ), K.HasHomology i] [∀ (i : ℤ), L.HasHomology i] (n : ℤ)

lemma quasiIso_πTruncGE_iff : QuasiIso (K.πTruncGE n) ↔ K.IsGE n :=
  quasiIso_πTruncGE_iff_isSupported K (embeddingUpIntGE n)

instance [K.IsStrictlyGE n] : IsIso (K.πTruncGE n) := by dsimp [πTruncGE]; infer_instance
instance [K.IsStrictlyLE n] : IsIso (K.ιTruncLE n) := by dsimp [ιTruncLE]; infer_instance

lemma isIso_πTruncGE_iff :
    IsIso (K.πTruncGE n) ↔ K.IsStrictlyGE n := by
  constructor
  · intro
    apply isStrictlyGE_of_iso (asIso (K.πTruncGE n)).symm
  · intro
    infer_instance

lemma isIso_ιTruncLE_iff :
    IsIso (K.ιTruncLE n) ↔ K.IsStrictlyLE n := by
  constructor
  · intro
    apply isStrictlyLE_of_iso (asIso (K.ιTruncLE n))
  · intro
    infer_instance

-- the dual statements of this lemma and the instance below are proven
-- below in the case `C` is abelian
lemma quasiIso_truncGEMap_iff (n : ℤ) :
    QuasiIso (truncGEMap φ n) ↔ ∀ (i : ℤ) (_ : n ≤ i), QuasiIsoAt φ i := by
  dsimp [truncGEMap]
  rw [HomologicalComplex.quasiIso_truncGEMap_iff]
  constructor
  · intro h i hi
    obtain ⟨k, rfl⟩ := Int.eq_add_ofNat_of_le hi
    exact h k _ rfl
  · rintro h i _ rfl
    exact h _ (by simp)

instance [K.IsGE n] : QuasiIso (K.πTruncGE n) := by
  dsimp [πTruncGE]
  rw [quasiIso_πTruncGE_iff_isSupported]
  infer_instance

instance : QuasiIsoAt (K.πTruncGE n) n :=
  K.quasiIsoAt_πTruncGE (embeddingUpIntGE n) (j := 0) (by simp)

noncomputable def truncGEXIso (n : ℤ) (i : ℤ) (hi : n < i) :
    (K.truncGE n).X i ≅ K.X i :=
  HomologicalComplex.truncGEXIso K (embeddingUpIntGE n) (i := (i - n).natAbs) (by
      dsimp
      rw [Int.natAbs_of_nonneg (by omega), add_sub_cancel])
    (fun h => by
      rw [boundaryGE_embeddingUpIntGE_iff, Int.natAbs_eq_zero] at h
      linarith)

noncomputable def truncGEXIsoOpcycles (n : ℤ) :
    (K.truncGE n).X n ≅ K.opcycles n :=
  HomologicalComplex.truncGEXIsoOpcycles K (embeddingUpIntGE n) (i := 0) (by simp)
    (by rw [boundaryGE_embeddingUpIntGE_iff])

lemma acyclic_truncGE_iff (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (K.truncGE n₁).Acyclic ↔ K.IsLE n₀ := by
  dsimp [truncGE]
  rw [acyclic_truncGE_iff_isSupportedOutside,
    (Embedding.embeddingUpInt_areComplementary n₀ n₁ h).isSupportedOutside₂_iff]

end

end HasZeroMorphisms

section Preadditive

variable [Preadditive C] (K : CochainComplex C ℤ)

instance [HasZeroObject C] (A : C) (n : ℤ) : ((singleFunctor C n).obj A).IsStrictlyGE n := by
  dsimp [singleFunctor, singleFunctors]
  infer_instance

instance [HasZeroObject C] (A : C) (n : ℤ) : ((singleFunctor C n).obj A).IsStrictlyLE n := by
  dsimp [singleFunctor, singleFunctors]
  infer_instance

lemma isStrictlyLE_shift (n : ℤ) [K.IsStrictlyLE n] (a n' : ℤ) (h : a + n' = n) :
    (K⟦a⟧).IsStrictlyLE n' := by
  rw [isStrictlyLE_iff]
  intro i hi
  exact IsZero.of_iso (K.isZero_of_isStrictlyLE n _ (by omega)) (K.shiftFunctorObjXIso a i _ rfl)

lemma isStrictlyGE_shift (n : ℤ) [K.IsStrictlyGE n] (a n' : ℤ) (h : a + n' = n) :
    (K⟦a⟧).IsStrictlyGE n' := by
  rw [isStrictlyGE_iff]
  intro i hi
  exact IsZero.of_iso (K.isZero_of_isStrictlyGE n _ (by omega)) (K.shiftFunctorObjXIso a i _ rfl)

section

variable [CategoryWithHomology C]

lemma isLE_shift (n : ℤ) [K.IsLE n] (a n' : ℤ) (h : a + n' = n) : (K⟦a⟧).IsLE n' := by
  rw [isLE_iff]
  intro i hi
  rw [exactAt_iff_isZero_homology]
  exact IsZero.of_iso (K.isZero_of_isLE n (a+i) (by linarith))
    (((homologyFunctor C _ (0 : ℤ)).shiftIso a i _ rfl).app K)

lemma isGE_shift (n : ℤ) [K.IsGE n] (a n' : ℤ) (h : a + n' = n) : (K⟦a⟧).IsGE n' := by
  rw [isGE_iff]
  intro i hi
  rw [exactAt_iff_isZero_homology]
  exact IsZero.of_iso (K.isZero_of_isGE n (a+i) (by linarith))
    (((homologyFunctor C _ (0 : ℤ)).shiftIso a i _ rfl).app K)

end

end Preadditive

section Abelian

variable [Abelian C] (K L : CochainComplex C ℤ)

instance (n : ℤ) [K.IsLE n] : QuasiIso (K.ιTruncLE n) := by
  dsimp [ιTruncLE]
  rw [quasiIso_ιTruncLE_iff_isSupported]
  infer_instance

variable {K L} in
lemma quasiIso_truncLEMap_iff (φ : K ⟶ L) (n : ℤ) :
    QuasiIso (truncLEMap φ n) ↔ ∀ (i : ℤ) (_ : i ≤ n), QuasiIsoAt φ i := by
  dsimp [truncLEMap]
  rw [HomologicalComplex.quasiIso_truncLEMap_iff]
  constructor
  · intro h i hi
    obtain ⟨k, rfl⟩ := Int.eq_add_ofNat_of_le hi
    exact h k _ (by dsimp; omega)
  · rintro h i _ rfl
    exact h _ (by simp)

noncomputable abbrev shortComplexTruncLE (n : ℤ) : ShortComplex (CochainComplex C ℤ) :=
  HomologicalComplex.shortComplexTruncLE K (embeddingUpIntLE n)

lemma shortComplexTruncLE_shortExact (n : ℤ) :
    (K.shortComplexTruncLE n).ShortExact := by
  apply HomologicalComplex.shortComplexTruncLE_shortExact

variable (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)

noncomputable abbrev shortComplexTruncLEX₃ToTruncGE :
    (K.shortComplexTruncLE n₀).X₃ ⟶ K.truncGE n₁ :=
  HomologicalComplex.shortComplexTruncLEX₃ToTruncGE K
    (Embedding.embeddingUpInt_areComplementary n₀ n₁ h)

@[reassoc (attr := simp)]
lemma g_shortComplexTruncLEX₃ToTruncGE :
    (K.shortComplexTruncLE n₀).g ≫ K.shortComplexTruncLEX₃ToTruncGE n₀ n₁ h = K.πTruncGE n₁ := by
  apply HomologicalComplex.g_shortComplexTruncLEX₃ToTruncGE

lemma acyclic_truncLE_iff (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (K.truncLE n₀).Acyclic ↔ K.IsGE n₁ := by
  dsimp [truncLE]
  rw [acyclic_truncLE_iff_isSupportedOutside,
    (Embedding.embeddingUpInt_areComplementary n₀ n₁ h).isSupportedOutside₁_iff K]

end Abelian

end CochainComplex
