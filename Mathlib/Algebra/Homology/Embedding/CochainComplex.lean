/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Embedding.TruncLE

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

/-- The condition that a cochain complex `K` is strictly `≤ n`. -/
abbrev IsStrictlyGE (n : ℤ) := K.IsStrictlySupported (embeddingUpIntGE n)

/-- The condition that a cochain complex `K` is strictly `≥ n`. -/
abbrev IsStrictlyLE (n : ℤ) := K.IsStrictlySupported (embeddingUpIntLE n)

/-- The condition that a cochain complex `K` is (cohomologically) `≤ n`. -/
abbrev IsGE (n : ℤ) := K.IsSupported (embeddingUpIntGE n)

/-- The condition that a cochain complex `K` is (cohomologically) `≥ n`. -/
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
    rw [not_mem_range_embeddingUpIntGE_iff] at hi
    exact h i hi

lemma isStrictlyLE_iff (n : ℤ) :
    K.IsStrictlyLE n ↔ ∀ (i : ℤ) (_ : n < i), IsZero (K.X i) := by
  constructor
  · intro _ i hi
    exact K.isZero_of_isStrictlyLE n i hi
  · intro h
    refine IsStrictlySupported.mk (fun i hi ↦ ?_)
    rw [not_mem_range_embeddingUpIntLE_iff] at hi
    exact h i hi

lemma isGE_iff (n : ℤ) :
    K.IsGE n ↔ ∀ (i : ℤ) (_ : i < n), K.ExactAt i := by
  constructor
  · intro _ i hi
    exact K.exactAt_of_isGE n i hi
  · intro h
    refine IsSupported.mk (fun i hi ↦ ?_)
    rw [not_mem_range_embeddingUpIntGE_iff] at hi
    exact h i hi

lemma isLE_iff (n : ℤ) :
    K.IsLE n ↔ ∀ (i : ℤ) (_ : n < i), K.ExactAt i := by
  constructor
  · intro _ i hi
    exact K.exactAt_of_isLE n i hi
  · intro h
    refine IsSupported.mk (fun i hi ↦ ?_)
    rw [not_mem_range_embeddingUpIntLE_iff] at hi
    exact h i hi

lemma isStrictlyLE_of_le (p q : ℤ) (hpq : p ≤ q) [K.IsStrictlyLE p] :
    K.IsStrictlyLE q := by
  rw [isStrictlyLE_iff]
  intro i hi
  apply K.isZero_of_isStrictlyLE p
  omega

lemma isStrictlyGE_of_ge (p q : ℤ) (hpq : p ≤ q) [K.IsStrictlyGE q] :
    K.IsStrictlyGE p := by
  rw [isStrictlyGE_iff]
  intro i hi
  apply K.isZero_of_isStrictlyGE q
  omega

lemma isLE_of_le (p q : ℤ) (hpq : p ≤ q) [K.IsLE p] :
    K.IsLE q := by
  rw [isLE_iff]
  intro i hi
  apply K.exactAt_of_isLE p
  omega

lemma isGE_of_ge (p q : ℤ) (hpq : p ≤ q) [K.IsGE q] :
    K.IsGE p := by
  rw [isGE_iff]
  intro i hi
  apply K.exactAt_of_isGE q
  omega

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

/-- A cochain complex that is both strictly `≤ n` and `≥ n` is isomorphic to
a complex `(single _ _ n).obj M` for some object `M`. -/
lemma exists_iso_single [HasZeroObject C] (n : ℤ) [K.IsStrictlyGE n] [K.IsStrictlyLE n] :
    ∃ (M : C), Nonempty (K ≅ (single _ _ n).obj M) :=
  ⟨K.X n, ⟨{
      hom := mkHomToSingle (𝟙 _) (fun i (hi : i + 1 = n) ↦
        (K.isZero_of_isStrictlyGE n i (by omega)).eq_of_src _ _)
      inv := mkHomFromSingle (𝟙 _) (fun i (hi : n + 1 = i) ↦
        (K.isZero_of_isStrictlyLE n i (by omega)).eq_of_tgt _ _)
      hom_inv_id := by
        ext i
        obtain hi | rfl | hi := lt_trichotomy i n
        · apply (K.isZero_of_isStrictlyGE n i (by omega)).eq_of_src
        · simp
        · apply (K.isZero_of_isStrictlyLE n i (by omega)).eq_of_tgt
      inv_hom_id := by aesop }⟩⟩

end HasZeroMorphisms

end CochainComplex
