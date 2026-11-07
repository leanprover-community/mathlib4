/-
Copyright (c) 2026 Nicola Falciola. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Falciola
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Updating a submatrix along embeddings

Given embeddings `eₙ : n ↪ o` and `eₘ : m ↪ p`, a matrix `A : Matrix n m α` and a matrix
`B : Matrix o p α`, this file provides the machinery to build the matrix that replaces in
`B` the entries at positions `(eₙ i, eₘ j)` with `A i j`. It generalizes `Matrix.updateRow` and
`Matrix.updateCol` .
It also provides the special case of a square matrix extended by the identity with the
corresponding `MonoidHom` `Matrix n n R →* Matrix m m R` for any embedding `n ↪ m`.

## Main definitions

* `Matrix.updateSubmatrix eₙ eₘ A B`: replace the submatrix of `B` indexed by `eₙ` and `eₘ`
  with `A`.
* `Matrix.updateSubmatrixAddMonoidHom eₙ eₘ`, `Matrix.updateSubmatrixLinearMap R eₙ eₘ`:
  `updateSubmatrix` as an additive monoid homomorphism, resp. a linear map,
  `Matrix n m α × Matrix o p α → Matrix o p α`.
* `Matrix.extendedByOne e A`: the square matrix `A` extended along `e : n ↪ m` by the identity.
* `Matrix.extendedByOneMonoidHom e`: `extendedByOne e` as a monoid homomorphism.
-/

@[expose] public section

namespace Matrix

open Function

variable {k l m n o p q r α R : Type*}

section UpdateSubmatrix

variable (eₙ : n ↪ o) (eₘ : m ↪ p) (A : Matrix n m α) (B : Matrix o p α)

/-- Update the submatrix of `B` indexed by the embeddings `eₙ` and `eₘ` with the matrix `A`: the
entry at `(eₙ i, eₘ j)` is `A i j`, and every other entry is that of `B`. -/
noncomputable def updateSubmatrix : Matrix o p α :=
  of <| extend eₙ (fun i ↦ extend eₘ (A i) (B (eₙ i))) (of.symm B)

@[simp]
theorem updateSubmatrix_apply_embedding {i : n} {j : m} :
    updateSubmatrix eₙ eₘ A B (eₙ i) (eₘ j) = A i j := by
  simp [updateSubmatrix, eₙ.injective, eₘ.injective]

@[simp]
theorem updateSubmatrix_submatrix : (updateSubmatrix eₙ eₘ A B).submatrix eₙ eₘ = A := by
  ext
  simp

@[simp]
theorem updateSubmatrix_apply_of_notMem_left {i : o} {j : p} (hi : i ∉ Set.range eₙ) :
    updateSubmatrix eₙ eₘ A B i j = B i j := by
  simp [updateSubmatrix, extend_apply' _ _ _ fun i ↦ hi i]

@[simp]
theorem updateSubmatrix_apply_of_notMem_right {i : o} {j : p} (hj : j ∉ Set.range eₘ) :
    updateSubmatrix eₙ eₘ A B i j = B i j := by
  by_cases hi : i ∈ Set.range eₙ
  · obtain ⟨-, rfl⟩ := hi
    simp [updateSubmatrix, extend_apply' _ _ _ hj, eₙ.injective]
  · exact updateSubmatrix_apply_of_notMem_left _ _ _ _ hi

theorem updateSubmatrix_apply_congr {X Y : Matrix o p α} {i : o} {j : p} (h : X i j = Y i j) :
    updateSubmatrix eₙ eₘ A X i j = updateSubmatrix eₙ eₘ A Y i j := by
  by_cases hij : i ∈ Set.range eₙ ∧ j ∈ Set.range eₘ
  · obtain ⟨⟨-, rfl⟩, -, rfl⟩ := hij
    simp
  · rcases not_and_or.mp hij with h' | h' <;> simp [h', h]

theorem ext_updateSubmatrix_iff {C : Matrix o p α} :
    C = updateSubmatrix eₙ eₘ A B ↔ C.submatrix eₙ eₘ = A ∧
      ∀ i j, (i ∉ Set.range eₙ ∨ j ∉ Set.range eₘ) → C i j = B i j := by
  refine ⟨?_, fun ⟨h1, h2⟩ ↦ ?_⟩
  · rintro rfl
    exact ⟨by simp, fun _ _ h ↦ h.elim (updateSubmatrix_apply_of_notMem_left _ _ _ _ ·)
      (updateSubmatrix_apply_of_notMem_right _ _ _ _ ·)⟩
  · ext i j
    by_cases h : i ∈ Set.range eₙ ∧ j ∈ Set.range eₘ
    · obtain ⟨⟨-, rfl⟩, ⟨-, rfl⟩⟩ := h
      simpa using congr_fun (congr_fun h1 _) _
    · rcases not_and_or.mp h with h' | h' <;> simp [h2, h']

@[simp]
theorem updateSubmatrix_submatrix_self : updateSubmatrix eₙ eₘ (B.submatrix eₙ eₘ) B = B :=
  ((ext_updateSubmatrix_iff eₙ eₘ _ B).mpr ⟨rfl, fun _ _ _ ↦ rfl⟩).symm

@[simp]
theorem updateSubmatrix_idem (C : Matrix n m α) :
    updateSubmatrix eₙ eₘ C (updateSubmatrix eₙ eₘ A B) = updateSubmatrix eₙ eₘ C B :=
  (ext_updateSubmatrix_iff eₙ eₘ C B).mpr ⟨by simp, fun _ _ h ↦ by rcases h with h | h <;> simp [h]⟩

theorem updateSubmatrix_comm_of_disjoint_left (eₖ : k ↪ o) (eₗ : l ↪ p) (C : Matrix k l α)
    (h : Disjoint (Set.range eₙ) (Set.range eₖ)) :
    updateSubmatrix eₙ eₘ A (updateSubmatrix eₖ eₗ C B) =
      updateSubmatrix eₖ eₗ C (updateSubmatrix eₙ eₘ A B) := by
  rw [ext_updateSubmatrix_iff]
  refine ⟨?_, fun _ _ hij ↦ updateSubmatrix_apply_congr _ _ _ ?_⟩
  · ext
    simp [Set.disjoint_right.mp h]
  · rcases hij with hi | hj
    · exact updateSubmatrix_apply_of_notMem_left _ _ _ _ hi
    · exact updateSubmatrix_apply_of_notMem_right _ _ _ _ hj

theorem updateSubmatrix_comm_of_disjoint_right (eₖ : k ↪ o) (eₗ : l ↪ p) (C : Matrix k l α)
    (h : Disjoint (Set.range eₘ) (Set.range eₗ)) :
    updateSubmatrix eₙ eₘ A (updateSubmatrix eₖ eₗ C B) =
      updateSubmatrix eₖ eₗ C (updateSubmatrix eₙ eₘ A B) := by
  rw [ext_updateSubmatrix_iff]
  refine ⟨?_, fun _ _ hij ↦ updateSubmatrix_apply_congr _ _ _ ?_⟩
  · ext
    simp [Set.disjoint_right.mp h]
  · rcases hij with hi | hj
    · exact updateSubmatrix_apply_of_notMem_left _ _ _ _ hi
    · exact updateSubmatrix_apply_of_notMem_right _ _ _ _ hj

theorem updateSubmatrix_eq_self_iff : updateSubmatrix eₙ eₘ A B = B ↔ A = B.submatrix eₙ eₘ :=
  ⟨fun h ↦ by simpa using congr_arg (·.submatrix eₙ eₘ) h,
    fun h ↦ h ▸ updateSubmatrix_submatrix_self eₙ eₘ B⟩

theorem updateSubmatrix_equiv_equiv (e : n ≃ o) (f : m ≃ p) :
    updateSubmatrix e.toEmbedding f.toEmbedding A B = reindex e f A := by
  rw [eq_comm, ext_updateSubmatrix_iff]
  refine ⟨by simp, fun i j h ↦ ?_⟩
  rcases h with h | h
  · exact absurd (e.surjective i) h
  · exact absurd (f.surjective j) h

@[simp]
theorem updateSubmatrix_refl_refl (C : Matrix n m α) :
    updateSubmatrix (Embedding.refl n) (Embedding.refl m) A C = A := by
  ext
  exact updateSubmatrix_apply_embedding ..

theorem updateSubmatrix_left_injective : Function.Injective (updateSubmatrix eₙ eₘ · B) := by
  intro _ _ h
  ext
  simpa using congr_fun (congr_fun h (eₙ _)) (eₘ _)

theorem updateSubmatrix_trans (eₒ : o ↪ q) (eₚ : p ↪ r) (B : Matrix q r α) :
    updateSubmatrix (eₙ.trans eₒ) (eₘ.trans eₚ) A B =
      updateSubmatrix eₒ eₚ (updateSubmatrix eₙ eₘ A (B.submatrix eₒ eₚ)) B := by
  rw [ext_updateSubmatrix_iff]
  refine ⟨?_, fun _ _ h ↦ ?_⟩
  · rw [ext_updateSubmatrix_iff]
    refine ⟨?_, fun x y h ↦ ?_⟩
    · ext
      simpa using updateSubmatrix_apply_embedding (eₙ.trans eₒ) (eₘ.trans eₚ) A B (i := _) (j := _)
    · have hx (x) (hx : x ∉ Set.range eₙ) : eₒ x ∉ Set.range (eₙ.trans eₒ) :=
        fun ⟨a, ha⟩ ↦ hx ⟨a, eₒ.injective ha⟩
      have hy (y) (hy : y ∉ Set.range eₘ) : eₚ y ∉ Set.range (eₘ.trans eₚ) :=
        fun ⟨a, ha⟩ ↦ hy ⟨a, eₚ.injective ha⟩
      rcases h with h | h
      · simpa using updateSubmatrix_apply_of_notMem_left _ _ _ _ (hx x h) (j := _)
      · simpa using updateSubmatrix_apply_of_notMem_right _ _ _ _ (hy y h) (i := _)
  · rcases h with h | h
    · exact updateSubmatrix_apply_of_notMem_left _ _ _ _
        (Set.notMem_subset (Set.range_comp_subset_range eₙ eₒ) h)
    · exact updateSubmatrix_apply_of_notMem_right _ _ _ _
        (Set.notMem_subset (Set.range_comp_subset_range eₘ eₚ) h)

theorem transpose_updateSubmatrix : (updateSubmatrix eₙ eₘ A B)ᵀ = updateSubmatrix eₘ eₙ Aᵀ Bᵀ := by
  refine (ext_updateSubmatrix_iff eₘ eₙ Aᵀ Bᵀ).mpr ⟨by ext; simp, fun _ _ h ↦ ?_⟩
  rcases h with h | h
  · exact updateSubmatrix_apply_of_notMem_right _ _ _ _ h
  · exact updateSubmatrix_apply_of_notMem_left _ _ _ _ h

theorem conjTranspose_updateSubmatrix [Star α] :
    (updateSubmatrix eₙ eₘ A B)ᴴ = updateSubmatrix eₘ eₙ Aᴴ Bᴴ := by
  rw [ext_updateSubmatrix_iff]
  exact ⟨by ext; simp, fun _ _ h ↦ by rcases h with h | h <;> simp [h]⟩

theorem updateSubmatrix_diagonal [Zero α] [DecidableEq n] [DecidableEq o] (d : n → α)
    (d' : o → α) :
    updateSubmatrix eₙ eₙ (diagonal d) (diagonal d') = diagonal (extend eₙ d d') := by
  rw [eq_comm, ext_updateSubmatrix_iff]
  refine ⟨by ext; simp [diagonal_apply, eₙ.injective.eq_iff, eₙ.injective.extend_apply],
    fun i j h ↦ ?_⟩
  obtain rfl | hij := eq_or_ne i j
  · rcases h with h | h <;> simp [extend_apply' _ _ _ h]
  · simp [hij]

theorem updateSubmatrix_map {β : Type*} (f : α → β) :
    (updateSubmatrix eₙ eₘ A B).map f = updateSubmatrix eₙ eₘ (A.map f) (B.map f) :=
  (ext_updateSubmatrix_iff eₙ eₘ (A.map f) (B.map f)).mpr
    ⟨by ext; simp, fun _ _ h ↦ by rcases h with h | h <;> simp [h]⟩

theorem updateSubmatrix_reindex_reindex (σ : n ≃ k) (τ : m ≃ l) (eₖ : k ↪ o) (eₗ : l ↪ p) :
    updateSubmatrix eₖ eₗ (reindex σ τ A) B =
      updateSubmatrix (σ.toEmbedding.trans eₖ) (τ.toEmbedding.trans eₗ) A B := by
  refine (ext_updateSubmatrix_iff (σ.toEmbedding.trans eₖ)
      (τ.toEmbedding.trans eₗ) A B).mpr ⟨by ext; simp, fun _ _ h ↦ ?_⟩
  rcases h with h | h
  · exact updateSubmatrix_apply_of_notMem_left _ _ _ _ (by simpa using h)
  · exact updateSubmatrix_apply_of_notMem_right _ _ _ _ (by simpa using h)

theorem reindex_reindex_updateSubmatrix (ρ : o ≃ q) (π : p ≃ r) :
    reindex ρ π (updateSubmatrix eₙ eₘ A B) =
      updateSubmatrix (eₙ.trans ρ.toEmbedding) (eₘ.trans π.toEmbedding) A (reindex ρ π B) := by
  refine (ext_updateSubmatrix_iff (eₙ.trans ρ.toEmbedding) (eₘ.trans π.toEmbedding) A
    ((reindex ρ π) B)).mpr ⟨by ext; simp, fun _ _ h ↦ ?_⟩
  simp only [reindex_apply, submatrix_apply]
  rcases h with h | h
  · exact updateSubmatrix_apply_of_notMem_left _ _ _ _ fun ⟨a, ha⟩ ↦ h ⟨a, by simp [ha]⟩
  · exact updateSubmatrix_apply_of_notMem_right _ _ _ _ fun ⟨a, ha⟩ ↦ h ⟨a, by simp [ha]⟩

theorem updateSubmatrix_inl_inl (B : Matrix (n ⊕ o) (m ⊕ p) α) :
    updateSubmatrix Embedding.inl Embedding.inl A B =
      fromBlocks A B.toBlocks₁₂ B.toBlocks₂₁ B.toBlocks₂₂ := by
  ext (i | i) (j | j) <;>
  first
  | exact updateSubmatrix_apply_embedding ..
  | simp [toBlocks₁₂, toBlocks₂₁, toBlocks₂₂]

theorem updateSubmatrix_inr_inr (B : Matrix (o ⊕ n) (p ⊕ m) α) :
    updateSubmatrix Embedding.inr Embedding.inr A B =
      fromBlocks B.toBlocks₁₁ B.toBlocks₁₂ B.toBlocks₂₁ A := by
  ext (i | i) (j | j) <;>
  first
  | exact updateSubmatrix_apply_embedding ..
  | simp [toBlocks₁₁, toBlocks₁₂, toBlocks₂₁]

theorem submatrix_toSquareBlockProp_updateSubmatrix (M : Matrix n n α) (N : Matrix o o α) :
    ((updateSubmatrix eₙ eₙ M N).toSquareBlockProp (· ∈ Set.range eₙ)).submatrix
      (Equiv.ofInjective eₙ eₙ.injective) (Equiv.ofInjective eₙ eₙ.injective) = M := by
  ext
  simp [toSquareBlockProp_def]

theorem toSquareBlockProp_updateSubmatrix_compl (M : Matrix n n α) (N : Matrix o o α) :
    (updateSubmatrix eₙ eₙ M N).toSquareBlockProp (fun i ↦ i ∉ Set.range eₙ) =
      N.toSquareBlockProp (fun i ↦ i ∉ Set.range eₙ) := by
  ext ⟨-, hi⟩ ⟨-, hj⟩
  simp [toSquareBlockProp_def, hi]

theorem updateRow_eq_updateSubmatrix [DecidableEq o] (i : o) (b : p → α) :
    B.updateRow i b = updateSubmatrix (Embedding.punit i) (Embedding.refl p) (of fun _ ↦ b) B := by
  refine (ext_updateSubmatrix_iff (Embedding.punit i) (Embedding.refl p)
    (of fun _ ↦ b) B).mpr ⟨by ext; simp [Embedding.punit], fun _ _ h ↦ ?_⟩
  rcases h with h | h
  · simp_all [updateRow_apply, Embedding.punit]
  · exact (h ⟨_, rfl⟩).elim

theorem updateCol_eq_updateSubmatrix [DecidableEq p] (j : p) (b : o → α) :
    B.updateCol j b =
      updateSubmatrix (Embedding.refl o) (Embedding.punit j) (of fun i _ ↦ b i) B := by
  refine (ext_updateSubmatrix_iff (Embedding.refl o) (Embedding.punit j)
    (of fun i _ ↦ b i) B).mpr ⟨by ext; simp [Embedding.punit], fun _ _ h ↦ ?_⟩
  rcases h with h | h
  · exact (h ⟨_, rfl⟩).elim
  · simp_all [Embedding.punit]

theorem updateSubmatrix_updateRow_of_notMem [DecidableEq o] {i : o} (hi : i ∉ Set.range eₙ)
    (b : p → α) :
    updateSubmatrix eₙ eₘ A (B.updateRow i b) = (updateSubmatrix eₙ eₘ A B).updateRow i b := by
  rw [eq_comm, ext_updateSubmatrix_iff]
  exact ⟨by ext; simp [updateRow_apply, ne_of_mem_of_not_mem _ hi],
    fun _ _ h ↦ by rcases h with h | h <;> simp [updateRow_apply, h]⟩

theorem updateSubmatrix_updateCol_of_notMem [DecidableEq p] {j : p} (hj : j ∉ Set.range eₘ)
    (b : o → α) :
    updateSubmatrix eₙ eₘ A (B.updateCol j b) = (updateSubmatrix eₙ eₘ A B).updateCol j b := by
  rw [eq_comm, ext_updateSubmatrix_iff]
  exact ⟨by ext; simp [ne_of_mem_of_not_mem _ hj],
    fun _ _ h ↦ by rcases h with h | h <;> simp [updateCol_apply, h]⟩

theorem updateRow_updateSubmatrix [DecidableEq n] [DecidableEq o] (a : n) (b : p → α) :
    (updateSubmatrix eₙ eₘ A B).updateRow (eₙ a) b =
      updateSubmatrix eₙ eₘ (A.updateRow a (b ∘ eₘ)) (B.updateRow (eₙ a) b) := by
  rw [ext_updateSubmatrix_iff]
  exact ⟨by ext; simp [updateRow_apply, eₙ.injective.eq_iff],
    fun _ _ h ↦ by rcases h with h | h <;> simp [updateRow_apply, h]⟩

theorem updateCol_updateSubmatrix [DecidableEq m] [DecidableEq p] (a : m) (b : o → α) :
    (updateSubmatrix eₙ eₘ A B).updateCol (eₘ a) b =
      updateSubmatrix eₙ eₘ (A.updateCol a (b ∘ eₙ)) (B.updateCol (eₘ a) b) := by
  rw [ext_updateSubmatrix_iff]
  exact ⟨by ext; simp [updateCol_apply, eₘ.injective.eq_iff],
    fun _ _ h ↦ by rcases h with h | h <;> simp [updateCol_apply, h]⟩

theorem updateSubmatrix_add [Add α] (C : Matrix n m α) (D : Matrix o p α) :
    updateSubmatrix eₙ eₘ (A + C) (B + D) =
      updateSubmatrix eₙ eₘ A B + updateSubmatrix eₙ eₘ C D := by
  rw [eq_comm, ext_updateSubmatrix_iff]
  exact ⟨by ext; simp, fun _ _ h ↦ by rcases h with h | h <;> simp [h]⟩

@[simp]
theorem updateSubmatrix_zero [Zero α] :
    updateSubmatrix eₙ eₘ (0 : Matrix n m α) (0 : Matrix o p α) = 0 := by
  rw [eq_comm, ext_updateSubmatrix_iff]
  exact ⟨by ext; simp, fun _ _ _ ↦ rfl⟩

theorem updateSubmatrix_neg [Neg α] :
    updateSubmatrix eₙ eₘ (-A) (-B) = -updateSubmatrix eₙ eₘ A B := by
  rw [eq_comm, ext_updateSubmatrix_iff]
  exact ⟨by ext; simp, fun _ _ h ↦ by rcases h with h | h <;> simp [h]⟩

theorem updateSubmatrix_sub [Sub α] (C : Matrix n m α) (D : Matrix o p α) :
    updateSubmatrix eₙ eₘ (A - C) (B - D) =
      updateSubmatrix eₙ eₘ A B - updateSubmatrix eₙ eₘ C D := by
  rw [eq_comm, ext_updateSubmatrix_iff]
  exact ⟨by ext; simp, fun _ _ h ↦ by rcases h with h | h <;> simp [h]⟩

theorem updateSubmatrix_smul [SMul R α] (r : R) :
    updateSubmatrix eₙ eₘ (r • A) (r • B) = r • updateSubmatrix eₙ eₘ A B := by
  rw [eq_comm, ext_updateSubmatrix_iff]
  exact ⟨by ext; simp, fun _ _ h ↦ by rcases h with h | h <;> simp [h]⟩

/-- `updateSubmatrix eₙ eₘ` as an additive monoid homomorphism in the pair `(A, B)`. -/
@[simps]
noncomputable def updateSubmatrixAddMonoidHom [AddZeroClass α] :
    Matrix n m α × Matrix o p α →+ Matrix o p α where
  toFun M := updateSubmatrix eₙ eₘ M.fst M.snd
  map_zero' := updateSubmatrix_zero eₙ eₘ
  map_add' _ _ := updateSubmatrix_add ..

variable (R) in
/-- `updateSubmatrix eₙ eₘ` as an `R`-linear map in the pair `(A, B)`. -/
@[simps!]
noncomputable def updateSubmatrixLinearMap [Semiring R] [AddCommMonoid α] [Module R α] :
    Matrix n m α × Matrix o p α →ₗ[R] Matrix o p α where
  __ := updateSubmatrixAddMonoidHom eₙ eₘ
  map_smul' _ _ := updateSubmatrix_smul ..

@[simp]
theorem updateSubmatrixLinearMap_toAddMonoidHom [Semiring R] [AddCommMonoid α] [Module R α] :
    (updateSubmatrixLinearMap R eₙ eₘ (α := α)).toAddMonoidHom =
      updateSubmatrixAddMonoidHom eₙ eₘ :=
  rfl

end UpdateSubmatrix

section ExtendByOne

variable {n' m' S : Type*} [DecidableEq l] [DecidableEq m] [Semiring R] [Semiring S] (e : n ↪ m)

/-- Extend a matrix `A : Matrix n n R` along an embedding `e : n ↪ m`: the entry at `(e i, e j)`
is `A i j`, and every other entry is that of the identity matrix. -/
noncomputable abbrev extendedByOne (A : Matrix n n R) : Matrix m m R :=
  updateSubmatrix e e A (1 : Matrix m m R)

theorem ext_extendedByOne_iff {B : Matrix m m R} {A : Matrix n n R} :
    B = A.extendedByOne e ↔ B.submatrix e e = A ∧
      ∀ i j, (i ∉ Set.range e ∨ j ∉ Set.range e) → B i j = (1 : Matrix m m R) i j :=
  ext_updateSubmatrix_iff ..

theorem extendedByOne_trans (f : m ↪ l) (A : Matrix n n R) :
    A.extendedByOne (e.trans f) = (A.extendedByOne e).extendedByOne f := by
  rw [extendedByOne, updateSubmatrix_trans, submatrix_one_embedding]

theorem extendedByOne_equiv (σ : n ≃ m) (A : Matrix n n R) :
    A.extendedByOne σ.toEmbedding = reindex σ σ A :=
  updateSubmatrix_equiv_equiv ..

theorem extendedByOne_reindex_reindex (σ : n ≃ n') (f : n' ↪ m) (A : Matrix n n R) :
    (reindex σ σ A).extendedByOne f = A.extendedByOne (σ.toEmbedding.trans f) :=
  updateSubmatrix_reindex_reindex ..

theorem reindex_reindex_extendedByOne [DecidableEq m'] (ρ : m ≃ m') (A : Matrix n n R) :
    reindex ρ ρ (A.extendedByOne e) = A.extendedByOne (e.trans ρ.toEmbedding) := by
  rw [extendedByOne, reindex_reindex_updateSubmatrix, reindex_apply, submatrix_one_equiv]

theorem transpose_extendedByOne (A : Matrix n n R) :
    (A.extendedByOne e)ᵀ = Aᵀ.extendedByOne e := by
  rw [extendedByOne, transpose_updateSubmatrix, transpose_one]

theorem conjTranspose_extendedByOne [StarRing R] (A : Matrix n n R) :
    (A.extendedByOne e)ᴴ = Aᴴ.extendedByOne e := by
  rw [extendedByOne, conjTranspose_updateSubmatrix, conjTranspose_one]

theorem extendedByOne_map (f : R →+* S) (A : Matrix n n R) :
    (A.extendedByOne e).map f = (A.map f).extendedByOne e := by
  simp [extendedByOne, updateSubmatrix_map]

theorem toSquareBlockProp_extendedByOne_compl (M : Matrix n n R) :
    (M.extendedByOne e).toSquareBlockProp (fun i ↦ i ∉ Set.range e) = 1 := by
  ext ⟨-, hi⟩ ⟨-, hj⟩
  simp [toSquareBlockProp_def, hi, Matrix.one_apply]

theorem extendedByOne_one [DecidableEq n] : extendedByOne e (1 : Matrix n n R) = 1 := by
  rw [extendedByOne, updateSubmatrix_eq_self_iff, submatrix_one_embedding]

theorem extendedByOne_diagonal [DecidableEq n] (d : n → R) :
    (diagonal d).extendedByOne e = diagonal (extend e d 1) := by
  rw [extendedByOne, ← diagonal_one, updateSubmatrix_diagonal]
  rfl

theorem extendedByOne_eq_one_iff [DecidableEq n] {A : Matrix n n R} :
    A.extendedByOne e = 1 ↔ A = 1 := by
  rw [extendedByOne, updateSubmatrix_eq_self_iff, submatrix_one_embedding]

theorem extendedByOne_mul [Fintype n] [Fintype m] (A B : Matrix n n R) :
    (A * B).extendedByOne e = A.extendedByOne e * B.extendedByOne e := by
  rw [eq_comm, ext_updateSubmatrix_iff]
  refine ⟨?_, fun i j h ↦ ?_⟩
  · ext
    rw [submatrix_apply, Matrix.mul_apply]
    exact (Fintype.sum_of_injective e e.injective _ _
      (fun k hk ↦ by simp [ne_of_mem_of_not_mem _ hk]) (by simp)).symm
  · rcases h with h | h <;> simp [Matrix.mul_apply, h, Matrix.one_apply]

section MonoidHom

variable [DecidableEq n] [Fintype n] [Fintype m] [Fintype l]

/-- The `MonoidHom` induced by `extendedByOne`. -/
@[simps!]
noncomputable def extendedByOneMonoidHom : Matrix n n R →* Matrix m m R where
  toFun := extendedByOne e
  map_mul' := extendedByOne_mul _
  map_one' := extendedByOne_one _

theorem extendedByOneMonoidHom_map (f : R →+* S) (A : Matrix n n R) :
    (extendedByOneMonoidHom e A).map f = extendedByOneMonoidHom e (A.map f) :=
  extendedByOne_map ..

theorem extendedByOneMonoidHom_comp_map (f : R →+* S) :
    (extendedByOneMonoidHom e).comp (RingHom.mapMatrix f).toMonoidHom =
      (RingHom.mapMatrix f).toMonoidHom.comp (extendedByOneMonoidHom e) :=
  MonoidHom.ext fun _ ↦ (extendedByOne_map ..).symm

theorem extendedByOneMonoidHom_refl :
    extendedByOneMonoidHom (Embedding.refl n) = MonoidHom.id (Matrix n n R) := by
  ext
  simp

theorem extendedByOneMonoidHom_trans (f : m ↪ l) :
    extendedByOneMonoidHom (e.trans f) =
      (extendedByOneMonoidHom (R := R) f).comp (extendedByOneMonoidHom e) :=
  MonoidHom.ext fun _ ↦ extendedByOne_trans ..

theorem extendedByOneMonoidHom_equiv (σ : n ≃ m) :
    extendedByOneMonoidHom σ.toEmbedding = (reindexRingEquiv R σ).toRingHom.toMonoidHom :=
  MonoidHom.ext fun _ ↦ extendedByOne_equiv ..

theorem extendedByOneMonoidHom_reindex [DecidableEq n'] [Fintype n']
    (σ : n ≃ n') (f : n' ↪ m) (A : Matrix n n R) :
    extendedByOneMonoidHom f (reindex σ σ A) = extendedByOneMonoidHom (σ.toEmbedding.trans f) A :=
  extendedByOne_reindex_reindex ..

theorem reindex_extendedByOneMonoidHom [DecidableEq m'] [Fintype m']
    (ρ : m ≃ m') (A : Matrix n n R) :
    reindex ρ ρ (extendedByOneMonoidHom e A) = extendedByOneMonoidHom (e.trans ρ.toEmbedding) A :=
  reindex_reindex_extendedByOne ..

theorem extendedByOneMonoidHom_comp_reindexRingEquiv [DecidableEq n'] [Fintype n']
    (σ : n ≃ n') (f : n' ↪ m) :
    (extendedByOneMonoidHom f).comp (reindexRingEquiv R σ).toRingHom.toMonoidHom =
      extendedByOneMonoidHom (σ.toEmbedding.trans f) :=
  MonoidHom.ext fun _ ↦ extendedByOne_reindex_reindex ..

theorem reindexRingEquiv_comp_extendedByOneMonoidHom [DecidableEq m'] [Fintype m']
    (ρ : m ≃ m') :
    (reindexRingEquiv R ρ).toRingHom.toMonoidHom.comp (extendedByOneMonoidHom e) =
      extendedByOneMonoidHom (e.trans ρ.toEmbedding) :=
  MonoidHom.ext fun _ ↦ reindex_reindex_extendedByOne ..

theorem extendedByOneMonoidHom_submatrix (A : Matrix n n R) :
    (extendedByOneMonoidHom e A).submatrix e e = A := by
  simp

theorem extendedByOneMonoidHom_injective :
    Function.Injective (extendedByOneMonoidHom (R := R) e) :=
  fun _ _ h ↦ updateSubmatrix_left_injective _ _ _ h

end MonoidHom

end ExtendByOne

section Inv

variable [CommRing R] [DecidableEq n] [DecidableEq m] [Fintype n] [Fintype m] (e : n ↪ m)

theorem inv_extendedByOne {A : Matrix n n R} (h : IsUnit A.det) :
    (A.extendedByOne e)⁻¹ = A⁻¹.extendedByOne e :=
  inv_eq_right_inv (by rw [← extendedByOne_mul, mul_nonsing_inv _ h, extendedByOne_one])

end Inv

end Matrix
