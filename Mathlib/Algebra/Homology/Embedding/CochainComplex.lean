/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Embedding.AreComplementary
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
# Truncations on cochain complexes indexed by the integers.

In this file, we introduce abbreviations for the canonical truncations
`CochainComplex.truncLE`, `CochainComplex.truncGE` of cochain
complexes indexed by `ℤ`, as well as the conditions
`CochainComplex.IsStrictlyLE`, `CochainComplex.IsStrictlyGE`,
`CochainComplex.IsLE`, and `CochainComplex.IsGE`.

-/

open CategoryTheory Category Limits ComplexShape ZeroObject

namespace CochainComplex

variable {C : Type*} [Category C]

open HomologicalComplex

section HasZeroMorphisms

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

section

variable [HasZeroObject C] [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]

/-- If `K : CochainComplex C ℤ`, this is the canonical truncation `≤ n` of `K`. -/
noncomputable abbrev truncLE (n : ℤ) : CochainComplex C ℤ :=
  HomologicalComplex.truncLE K (embeddingUpIntLE n)

/-- If `K : CochainComplex C ℤ`, this is the canonical truncation `≥ n` of `K`. -/
noncomputable abbrev truncGE (n : ℤ) : CochainComplex C ℤ :=
  HomologicalComplex.truncGE K (embeddingUpIntGE n)

/-- The canonical map `K.truncLE n ⟶ K` for `K : CochainComplex C ℤ`. -/
noncomputable def ιTruncLE (n : ℤ) : K.truncLE n ⟶ K :=
  HomologicalComplex.ιTruncLE K (embeddingUpIntLE n)

/-- The canonical map `K ⟶ K.truncGE n` for `K : CochainComplex C ℤ`. -/
noncomputable def πTruncGE (n : ℤ) : K ⟶ K.truncGE n :=
  HomologicalComplex.πTruncGE K (embeddingUpIntGE n)

section

variable {K L}

/-- The morphism `K.truncLE n ⟶ L.truncLE n` induced by a morphism `K ⟶ L`. -/
noncomputable abbrev truncLEMap (n : ℤ) : K.truncLE n ⟶ L.truncLE n :=
  HomologicalComplex.truncLEMap φ (embeddingUpIntLE n)

/-- The morphism `K.truncGE n ⟶ L.truncGE n` induced by a morphism `K ⟶ L`. -/
noncomputable abbrev truncGEMap (n : ℤ) : K.truncGE n ⟶ L.truncGE n :=
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

/-- The condition that a cochain complex `K` is strictly `≥ n`. -/
abbrev IsStrictlyGE (n : ℤ) := K.IsStrictlySupported (embeddingUpIntGE n)

/-- The condition that a cochain complex `K` is strictly `≤ n`. -/
abbrev IsStrictlyLE (n : ℤ) := K.IsStrictlySupported (embeddingUpIntLE n)

/-- The condition that a cochain complex `K` is (cohomologically) `≥ n`. -/
abbrev IsGE (n : ℤ) := K.IsSupported (embeddingUpIntGE n)

/-- The condition that a cochain complex `K` is (cohomologically) `≤ n`. -/
abbrev IsLE (n : ℤ) := K.IsSupported (embeddingUpIntLE n)

lemma isZero_of_isStrictlyGE (n i : ℤ) (hi : i < n) [K.IsStrictlyGE n] :
    IsZero (K.X i) :=
  isZero_X_of_isStrictlySupported K (embeddingUpIntGE n) i
    (by simpa only [notMem_range_embeddingUpIntGE_iff] using hi)

lemma isZero_of_isStrictlyLE (n i : ℤ) (hi : n < i) [K.IsStrictlyLE n] :
    IsZero (K.X i) :=
  isZero_X_of_isStrictlySupported K (embeddingUpIntLE n) i
    (by simpa only [notMem_range_embeddingUpIntLE_iff] using hi)

lemma exactAt_of_isGE (n i : ℤ) (hi : i < n) [K.IsGE n] :
    K.ExactAt i :=
  exactAt_of_isSupported K (embeddingUpIntGE n) i
    (by simpa only [notMem_range_embeddingUpIntGE_iff] using hi)

lemma exactAt_of_isLE (n i : ℤ) (hi : n < i) [K.IsLE n] :
    K.ExactAt i :=
  exactAt_of_isSupported K (embeddingUpIntLE n) i
    (by simpa only [notMem_range_embeddingUpIntLE_iff] using hi)

lemma isZero_of_isGE (n i : ℤ) (hi : i < n) [K.IsGE n] [K.HasHomology i] :
    IsZero (K.homology i) :=
  (K.exactAt_of_isGE n i hi).isZero_homology

lemma isZero_of_isLE (n i : ℤ) (hi : n < i) [K.IsLE n] [K.HasHomology i] :
    IsZero (K.homology i) :=
  (K.exactAt_of_isLE n i hi).isZero_homology

lemma isStrictlyGE_iff (n : ℤ) :
    K.IsStrictlyGE n ↔ ∀ (i : ℤ) (_ : i < n), IsZero (K.X i) := by
  constructor
  · intro _ i hi
    exact K.isZero_of_isStrictlyGE n i hi
  · intro h
    refine IsStrictlySupported.mk (fun i hi ↦ ?_)
    rw [notMem_range_embeddingUpIntGE_iff] at hi
    exact h i hi

lemma isStrictlyLE_iff (n : ℤ) :
    K.IsStrictlyLE n ↔ ∀ (i : ℤ) (_ : n < i), IsZero (K.X i) := by
  constructor
  · intro _ i hi
    exact K.isZero_of_isStrictlyLE n i hi
  · intro h
    refine IsStrictlySupported.mk (fun i hi ↦ ?_)
    rw [notMem_range_embeddingUpIntLE_iff] at hi
    exact h i hi

lemma isGE_iff (n : ℤ) :
    K.IsGE n ↔ ∀ (i : ℤ) (_ : i < n), K.ExactAt i := by
  constructor
  · intro _ i hi
    exact K.exactAt_of_isGE n i hi
  · intro h
    refine IsSupported.mk (fun i hi ↦ ?_)
    rw [notMem_range_embeddingUpIntGE_iff] at hi
    exact h i hi

lemma isLE_iff (n : ℤ) :
    K.IsLE n ↔ ∀ (i : ℤ) (_ : n < i), K.ExactAt i := by
  constructor
  · intro _ i hi
    exact K.exactAt_of_isLE n i hi
  · intro h
    refine IsSupported.mk (fun i hi ↦ ?_)
    rw [notMem_range_embeddingUpIntLE_iff] at hi
    exact h i hi

lemma isStrictlyLE_of_le (p q : ℤ) (hpq : p ≤ q) [K.IsStrictlyLE p] :
    K.IsStrictlyLE q := by
  rw [isStrictlyLE_iff]
  intro i hi
  apply K.isZero_of_isStrictlyLE p
  cutsat

lemma isStrictlyGE_of_ge (p q : ℤ) (hpq : p ≤ q) [K.IsStrictlyGE q] :
    K.IsStrictlyGE p := by
  rw [isStrictlyGE_iff]
  intro i hi
  apply K.isZero_of_isStrictlyGE q
  cutsat

lemma isLE_of_le (p q : ℤ) (hpq : p ≤ q) [K.IsLE p] :
    K.IsLE q := by
  rw [isLE_iff]
  intro i hi
  apply K.exactAt_of_isLE p
  cutsat

lemma isGE_of_ge (p q : ℤ) (hpq : p ≤ q) [K.IsGE q] :
    K.IsGE p := by
  rw [isGE_iff]
  intro i hi
  apply K.exactAt_of_isGE q
  cutsat

section

variable {K L}

include e

lemma isStrictlyLE_of_iso (n : ℤ) [K.IsStrictlyLE n] : L.IsStrictlyLE n := by
  apply isStrictlySupported_of_iso e

lemma isStrictlyGE_of_iso (n : ℤ) [K.IsStrictlyGE n] : L.IsStrictlyGE n := by
  apply isStrictlySupported_of_iso e

lemma isLE_of_iso (n : ℤ) [K.IsLE n] : L.IsLE n := by
  apply isSupported_of_iso e

lemma isGE_of_iso (n : ℤ) [K.IsGE n] : L.IsGE n := by
  apply isSupported_of_iso e

end

section

variable [HasZeroObject C]

/-- A cochain complex that is both strictly `≤ n` and `≥ n` is isomorphic to
a complex `(single _ _ n).obj M` for some object `M`. -/
lemma exists_iso_single (n : ℤ) [K.IsStrictlyGE n] [K.IsStrictlyLE n] :
    ∃ (M : C), Nonempty (K ≅ (single _ _ n).obj M) :=
  ⟨K.X n, ⟨{
      hom := mkHomToSingle (𝟙 _) (fun i (hi : i + 1 = n) ↦
        (K.isZero_of_isStrictlyGE n i (by cutsat)).eq_of_src _ _)
      inv := mkHomFromSingle (𝟙 _) (fun i (hi : n + 1 = i) ↦
        (K.isZero_of_isStrictlyLE n i (by cutsat)).eq_of_tgt _ _)
      hom_inv_id := by
        ext i
        obtain hi | rfl | hi := lt_trichotomy i n
        · apply (K.isZero_of_isStrictlyGE n i (by cutsat)).eq_of_src
        · simp
        · apply (K.isZero_of_isStrictlyLE n i (by cutsat)).eq_of_tgt
      inv_hom_id := by aesop }⟩⟩

instance (A : C) (n : ℤ) :
    IsStrictlyGE ((single C (ComplexShape.up ℤ) n).obj A) n := by
  rw [isStrictlyGE_iff]
  intro i hi
  exact isZero_single_obj_X _ _ _ _ (by cutsat)

instance (A : C) (n : ℤ) :
    IsStrictlyLE ((single C (ComplexShape.up ℤ) n).obj A) n := by
  rw [isStrictlyLE_iff]
  intro i hi
  exact isZero_single_obj_X _ _ _ _ (by cutsat)

variable [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] (n : ℤ)

instance [K.IsStrictlyGE n] : IsIso (K.πTruncGE n) := by dsimp [πTruncGE]; infer_instance

instance [K.IsStrictlyLE n] : IsIso (K.ιTruncLE n) := by dsimp [ιTruncLE]; infer_instance

lemma isIso_πTruncGE_iff : IsIso (K.πTruncGE n) ↔ K.IsStrictlyGE n := by
  apply HomologicalComplex.isIso_πTruncGE_iff

lemma isIso_ιTruncLE_iff : IsIso (K.ιTruncLE n) ↔ K.IsStrictlyLE n := by
  apply HomologicalComplex.isIso_ιTruncLE_iff

lemma quasiIso_πTruncGE_iff : QuasiIso (K.πTruncGE n) ↔ K.IsGE n :=
  quasiIso_πTruncGE_iff_isSupported K (embeddingUpIntGE n)

lemma quasiIso_ιTruncLE_iff : QuasiIso (K.ιTruncLE n) ↔ K.IsLE n :=
  quasiIso_ιTruncLE_iff_isSupported K (embeddingUpIntLE n)

instance [K.IsGE n] : QuasiIso (K.πTruncGE n) := by
  rw [quasiIso_πTruncGE_iff]
  infer_instance

instance [K.IsLE n] : QuasiIso (K.ιTruncLE n) := by
  rw [quasiIso_ιTruncLE_iff]
  infer_instance

variable {K L}

lemma quasiIso_truncGEMap_iff :
    QuasiIso (truncGEMap φ n) ↔ ∀ (i : ℤ) (_ : n ≤ i), QuasiIsoAt φ i := by
  rw [HomologicalComplex.quasiIso_truncGEMap_iff]
  constructor
  · intro h i hi
    obtain ⟨k, rfl⟩ := Int.le.dest hi
    exact h k _ rfl
  · rintro h i i' rfl
    exact h _ (by dsimp; cutsat)

lemma quasiIso_truncLEMap_iff :
    QuasiIso (truncLEMap φ n) ↔ ∀ (i : ℤ) (_ : i ≤ n), QuasiIsoAt φ i := by
  rw [HomologicalComplex.quasiIso_truncLEMap_iff]
  constructor
  · intro h i hi
    obtain ⟨k, rfl⟩ := Int.le.dest hi
    exact h k _ (by dsimp; cutsat)
  · rintro h i i' rfl
    exact h _ (by dsimp; cutsat)

end

end HasZeroMorphisms

section Preadditive

variable [Preadditive C]

instance [HasZeroObject C] (A : C) (n : ℤ) : ((singleFunctor C n).obj A).IsStrictlyGE n :=
  inferInstanceAs (IsStrictlyGE ((single C (ComplexShape.up ℤ) n).obj A) n)

instance [HasZeroObject C] (A : C) (n : ℤ) : ((singleFunctor C n).obj A).IsStrictlyLE n :=
  inferInstanceAs (IsStrictlyLE ((single C (ComplexShape.up ℤ) n).obj A) n)

variable (K : CochainComplex C ℤ)

lemma isStrictlyLE_shift (n : ℤ) [K.IsStrictlyLE n] (a n' : ℤ) (h : a + n' = n) :
    (K⟦a⟧).IsStrictlyLE n' := by
  rw [isStrictlyLE_iff]
  intro i hi
  exact IsZero.of_iso (K.isZero_of_isStrictlyLE n _ (by cutsat)) (K.shiftFunctorObjXIso a i _ rfl)

lemma isStrictlyGE_shift (n : ℤ) [K.IsStrictlyGE n] (a n' : ℤ) (h : a + n' = n) :
    (K⟦a⟧).IsStrictlyGE n' := by
  rw [isStrictlyGE_iff]
  intro i hi
  exact IsZero.of_iso (K.isZero_of_isStrictlyGE n _ (by cutsat)) (K.shiftFunctorObjXIso a i _ rfl)

section

variable [CategoryWithHomology C]

lemma isLE_shift (n : ℤ) [K.IsLE n] (a n' : ℤ) (h : a + n' = n) : (K⟦a⟧).IsLE n' := by
  rw [isLE_iff]
  intro i hi
  rw [exactAt_iff_isZero_homology]
  exact IsZero.of_iso (K.isZero_of_isLE n (a + i) (by cutsat))
    (((homologyFunctor C _ (0 : ℤ)).shiftIso a i _ rfl).app K)

lemma isGE_shift (n : ℤ) [K.IsGE n] (a n' : ℤ) (h : a + n' = n) : (K⟦a⟧).IsGE n' := by
  rw [isGE_iff]
  intro i hi
  rw [exactAt_iff_isZero_homology]
  exact IsZero.of_iso (K.isZero_of_isGE n (a + i) (by cutsat))
    (((homologyFunctor C _ (0 : ℤ)).shiftIso a i _ rfl).app K)

end

end Preadditive


section Abelian

variable [Abelian C] (K L : CochainComplex C ℤ)

/-- The cokernel sequence of the monomorphism `K.ιTruncLE n`. -/
noncomputable abbrev shortComplexTruncLE (n : ℤ) : ShortComplex (CochainComplex C ℤ) :=
  HomologicalComplex.shortComplexTruncLE K (embeddingUpIntLE n)

lemma shortComplexTruncLE_shortExact (n : ℤ) :
    (K.shortComplexTruncLE n).ShortExact := by
  apply HomologicalComplex.shortComplexTruncLE_shortExact

variable (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)

/-- The canonical morphism `(K.shortComplexTruncLE n₀).X₃ ⟶ K.truncGE n₁`. -/
noncomputable abbrev shortComplexTruncLEX₃ToTruncGE :
    (K.shortComplexTruncLE n₀).X₃ ⟶ K.truncGE n₁ :=
  HomologicalComplex.shortComplexTruncLEX₃ToTruncGE K
    (Embedding.embeddingUpInt_areComplementary n₀ n₁ h)

@[reassoc]
lemma g_shortComplexTruncLEX₃ToTruncGE :
    (K.shortComplexTruncLE n₀).g ≫ K.shortComplexTruncLEX₃ToTruncGE n₀ n₁ h = K.πTruncGE n₁ := by
  apply HomologicalComplex.g_shortComplexTruncLEX₃ToTruncGE

end Abelian

end CochainComplex
