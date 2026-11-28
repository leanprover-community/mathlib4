/-
Copyright (c) 2026 Nicola Falciola. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Falciola
-/
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.RowCol

/-!
# Extending a matrix into a submatrix of another one

Given maps `eₙ : n → o` and `eₘ : m → p`, a matrix `A : Matrix n m α` and a matrix
`B : Matrix o p α`, this file provides the machinery to build the matrix that replaces in
`B` the entries at positions `(eₙ i, eₘ j)` with `A i j`. It generalizes `Matrix.updateRow` and
`Matrix.updateCol`.

The construction is defined for arbitrary maps via `Function.extend`, and is mathematically
meaningful when `eₙ` and `eₘ` are injective. Lemmas only assume injectivity when they need it.

## Main definitions

* `Matrix.extendSubmatrix eₙ eₘ A B`: replace the submatrix of `B` indexed by `eₙ` and `eₘ`
  with `A`.
* `Matrix.extendSubmatrixAddMonoidHom eₙ eₘ`, `Matrix.extendSubmatrixLinearMap R eₙ eₘ`:
  `extendSubmatrix` as an additive monoid homomorphism, resp. a linear map,
  `Matrix n m α × Matrix o p α → Matrix o p α`.
-/

@[expose] public section

namespace Matrix

open Function

variable {k l m n o p q r α R : Type*}

section ExtendSubmatrix

variable (eₙ : n → o) (eₘ : m → p) (A : Matrix n m α) (B : Matrix o p α)

/-- Replace the submatrix of `B` indexed by the maps `eₙ` and `eₘ` with the matrix `A`: when `eₙ`
and `eₘ` are injective, the entry at `(eₙ i, eₘ j)` is `A i j`, and every other entry is that
of `B`. -/
noncomputable def extendSubmatrix : Matrix o p α :=
  of <| extend eₙ (fun i ↦ extend eₘ (A i) (B (eₙ i))) (of.symm B)

@[simp]
theorem extendSubmatrix_apply_apply (hₙ : Injective eₙ) (hₘ : Injective eₘ) (i : n) (j : m) :
    extendSubmatrix eₙ eₘ A B (eₙ i) (eₘ j) = A i j := by
  simp [extendSubmatrix, hₙ, hₘ]

@[simp]
theorem extendSubmatrix_submatrix (hₙ : Injective eₙ) (hₘ : Injective eₘ) :
    (extendSubmatrix eₙ eₘ A B).submatrix eₙ eₘ = A := by
  ext
  simp [hₙ, hₘ]

@[simp]
theorem extendSubmatrix_apply_of_notMem_left {i : o} {j : p} (hi : i ∉ Set.range eₙ) :
    extendSubmatrix eₙ eₘ A B i j = B i j := by
  simp [extendSubmatrix, extend_apply' _ _ _ hi]

@[simp]
theorem extendSubmatrix_apply_of_notMem_right {i : o} {j : p} (hj : j ∉ Set.range eₘ) :
    extendSubmatrix eₙ eₘ A B i j = B i j := by
  simp only [extendSubmatrix, of_apply, of_symm_apply, comp_def,
    apply_extend fun r : p → α ↦ r j, extend_apply' _ _ _ hj]
  exact congrFun (extend_comp_self eₙ (B · j)) i

/-- If `X` and `Y` have the same `i`-th row, so do `extendSubmatrix eₙ eₘ A X` and
`extendSubmatrix eₙ eₘ A Y`. -/
theorem extendSubmatrix_apply_congr_left (hₙ : Injective eₙ) {X Y : Matrix o p α} {i : o}
    (h : X i = Y i) (j : p) :
    extendSubmatrix eₙ eₘ A X i j = extendSubmatrix eₙ eₘ A Y i j := by
  by_cases hi : i ∈ Set.range eₙ
  · obtain ⟨a, rfl⟩ := hi
    simp [extendSubmatrix, hₙ, h]
  · simp [hi, congr_fun h j]

/-- If `X` and `Y` have the same `j`-th column, so do `extendSubmatrix eₙ eₘ A X` and
`extendSubmatrix eₙ eₘ A Y`. -/
theorem extendSubmatrix_apply_congr_right (hₘ : Injective eₘ) {X Y : Matrix o p α} {j : p}
    (h : ∀ i, X i j = Y i j) (i : o) :
    extendSubmatrix eₙ eₘ A X i j = extendSubmatrix eₙ eₘ A Y i j := by
  simp only [extendSubmatrix, of_apply, of_symm_apply, comp_def,
    apply_extend fun r : p → α ↦ r j]
  by_cases hj : j ∈ Set.range eₘ
  · obtain ⟨b, rfl⟩ := hj
    simp [hₘ, h]
  · simp [extend_apply' _ _ _ hj, h]

theorem extendSubmatrix_apply_congr (hₙ : Injective eₙ) (hₘ : Injective eₘ) {X Y : Matrix o p α}
    {i : o} {j : p} (h : X i j = Y i j) :
    extendSubmatrix eₙ eₘ A X i j = extendSubmatrix eₙ eₘ A Y i j := by
  by_cases hij : i ∈ Set.range eₙ ∧ j ∈ Set.range eₘ
  · obtain ⟨⟨a, rfl⟩, b, rfl⟩ := hij
    simp [hₙ, hₘ]
  · rcases not_and_or.mp hij with h' | h' <;> simp [h', h]

theorem extendSubmatrix_map {β : Type*} (f : α → β) :
    (extendSubmatrix eₙ eₘ A B).map f = extendSubmatrix eₙ eₘ (A.map f) (B.map f) := by
  ext i j
  simp only [extendSubmatrix, map_apply, of_apply, apply_extend fun r : p → α ↦ r j, comp_def,
    of_symm_apply, apply_extend f, apply_extend fun r : p → β ↦ r j]
  rfl

theorem eq_extendSubmatrix_iff (hₙ : Injective eₙ) (hₘ : Injective eₘ) {C : Matrix o p α} :
    C = extendSubmatrix eₙ eₘ A B ↔ C.submatrix eₙ eₘ = A ∧
      ∀ i j, (i ∉ Set.range eₙ ∨ j ∉ Set.range eₘ) → C i j = B i j := by
  refine ⟨?_, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · rintro rfl
    exact ⟨extendSubmatrix_submatrix eₙ eₘ A B hₙ hₘ, fun _ _ h ↦
      h.elim (extendSubmatrix_apply_of_notMem_left _ _ _ _ ·)
        (extendSubmatrix_apply_of_notMem_right _ _ _ _ ·)⟩
  · subst h₁
    ext i j
    by_cases hij : i ∈ Set.range eₙ ∧ j ∈ Set.range eₘ
    · obtain ⟨⟨a, rfl⟩, b, rfl⟩ := hij
      simp [hₙ, hₘ]
    · rcases not_and_or.mp hij with h | h <;> simp [h, h₂]

@[simp]
theorem extendSubmatrix_submatrix_self : extendSubmatrix eₙ eₘ (B.submatrix eₙ eₘ) B = B := by
  have h (a : n) : extend eₘ (B.submatrix eₙ eₘ a) (B (eₙ a)) = B (eₙ a) :=
    extend_comp_self eₘ (B (eₙ a))
  simp only [extendSubmatrix, h]
  exact extend_comp_self eₙ B

@[simp]
theorem extendSubmatrix_extendSubmatrix (hₙ : Injective eₙ) (hₘ : Injective eₘ)
    (C : Matrix n m α) :
    extendSubmatrix eₙ eₘ C (extendSubmatrix eₙ eₘ A B) = extendSubmatrix eₙ eₘ C B := by
  ext i j
  by_cases hij : i ∈ Set.range eₙ ∧ j ∈ Set.range eₘ
  · obtain ⟨⟨-, rfl⟩, -, rfl⟩ := hij
    simp [hₙ, hₘ]
  · rcases not_and_or.mp hij with h | h <;> simp [h]

theorem extendSubmatrix_comm_of_disjoint_left (eₖ : k → o) (eₗ : l → p) (C : Matrix k l α)
    (hₙ : Injective eₙ) (hₖ : Injective eₖ) (h : Disjoint (Set.range eₙ) (Set.range eₖ)) :
    extendSubmatrix eₙ eₘ A (extendSubmatrix eₖ eₗ C B) =
      extendSubmatrix eₖ eₗ C (extendSubmatrix eₙ eₘ A B) := by
  ext i j
  by_cases hi : i ∈ Set.range eₙ
  · have hk : i ∉ Set.range eₖ := Set.disjoint_left.mp h hi
    rw [extendSubmatrix_apply_of_notMem_left _ _ _ _ hk]
    exact extendSubmatrix_apply_congr_left _ _ _ hₙ
      (funext fun _ ↦ extendSubmatrix_apply_of_notMem_left _ _ _ _ hk) _
  · rw [extendSubmatrix_apply_of_notMem_left _ _ _ _ hi]
    exact extendSubmatrix_apply_congr_left _ _ _ hₖ
      (funext fun _ ↦ (extendSubmatrix_apply_of_notMem_left _ _ _ _ hi).symm) _

theorem extendSubmatrix_comm_of_disjoint_right (eₖ : k → o) (eₗ : l → p) (C : Matrix k l α)
    (hₘ : Injective eₘ) (hₗ : Injective eₗ) (h : Disjoint (Set.range eₘ) (Set.range eₗ)) :
    extendSubmatrix eₙ eₘ A (extendSubmatrix eₖ eₗ C B) =
      extendSubmatrix eₖ eₗ C (extendSubmatrix eₙ eₘ A B) := by
  ext i j
  by_cases hj : j ∈ Set.range eₘ
  · have hl : j ∉ Set.range eₗ := Set.disjoint_left.mp h hj
    rw [extendSubmatrix_apply_of_notMem_right _ _ _ _ hl]
    exact extendSubmatrix_apply_congr_right _ _ _ hₘ
      (fun _ ↦ extendSubmatrix_apply_of_notMem_right _ _ _ _ hl) _
  · rw [extendSubmatrix_apply_of_notMem_right _ _ _ _ hj]
    exact extendSubmatrix_apply_congr_right _ _ _ hₗ
      (fun _ ↦ (extendSubmatrix_apply_of_notMem_right _ _ _ _ hj).symm) _

theorem extendSubmatrix_eq_self_iff (hₙ : Injective eₙ) (hₘ : Injective eₘ) :
    extendSubmatrix eₙ eₘ A B = B ↔ A = B.submatrix eₙ eₘ :=
  ⟨fun h ↦ by rw [← extendSubmatrix_submatrix eₙ eₘ A B hₙ hₘ, h],
    fun h ↦ h ▸ extendSubmatrix_submatrix_self eₙ eₘ B⟩

theorem extendSubmatrix_equiv_equiv (e : n ≃ o) (f : m ≃ p) :
    extendSubmatrix e f A B = reindex e f A := by
  rw [eq_comm, eq_extendSubmatrix_iff _ _ _ _ e.injective f.injective]
  refine ⟨by simp, fun i j h ↦ ?_⟩
  rcases h with h | h
  · exact absurd (e.surjective i) h
  · exact absurd (f.surjective j) h

@[simp]
theorem extendSubmatrix_id_id (C : Matrix n m α) :
    extendSubmatrix id id A C = A := by
  ext
  exact extendSubmatrix_apply_apply _ _ _ _ injective_id injective_id ..

theorem extendSubmatrix_left_injective (hₙ : Injective eₙ) (hₘ : Injective eₘ) :
    Injective (extendSubmatrix eₙ eₘ · B) := by
  intro _ _ h
  ext
  simpa [hₙ, hₘ] using congr_fun (congr_fun h (eₙ _)) (eₘ _)

theorem extendSubmatrix_trans (eₒ : o → q) (eₚ : p → r) (hₙ : Injective eₙ) (hₘ : Injective eₘ)
    (hₒ : Injective eₒ) (hₚ : Injective eₚ) (B : Matrix q r α) :
    extendSubmatrix (eₒ ∘ eₙ) (eₚ ∘ eₘ) A B =
      extendSubmatrix eₒ eₚ (extendSubmatrix eₙ eₘ A (B.submatrix eₒ eₚ)) B := by
  rw [eq_extendSubmatrix_iff _ _ _ _ hₒ hₚ]
  refine ⟨?_, fun _ _ h ↦ ?_⟩
  · rw [eq_extendSubmatrix_iff _ _ _ _ hₙ hₘ]
    refine ⟨?_, fun x y h ↦ ?_⟩
    · ext
      simpa using extendSubmatrix_apply_apply (eₒ ∘ eₙ) (eₚ ∘ eₘ) A B (hₒ.comp hₙ) (hₚ.comp hₘ)
        _ _
    · have hx (x) (hx : x ∉ Set.range eₙ) : eₒ x ∉ Set.range (eₒ ∘ eₙ) :=
        fun ⟨a, ha⟩ ↦ hx ⟨a, hₒ ha⟩
      have hy (y) (hy : y ∉ Set.range eₘ) : eₚ y ∉ Set.range (eₚ ∘ eₘ) :=
        fun ⟨a, ha⟩ ↦ hy ⟨a, hₚ ha⟩
      rcases h with h | h
      · simpa using extendSubmatrix_apply_of_notMem_left _ _ _ _ (hx x h) (j := _)
      · simpa using extendSubmatrix_apply_of_notMem_right _ _ _ _ (hy y h) (i := _)
  · rcases h with h | h
    · exact extendSubmatrix_apply_of_notMem_left _ _ _ _
        (Set.notMem_subset (Set.range_comp_subset_range eₙ eₒ) h)
    · exact extendSubmatrix_apply_of_notMem_right _ _ _ _
        (Set.notMem_subset (Set.range_comp_subset_range eₘ eₚ) h)

theorem transpose_extendSubmatrix (hₙ : Injective eₙ) (hₘ : Injective eₘ) :
    (extendSubmatrix eₙ eₘ A B)ᵀ = extendSubmatrix eₘ eₙ Aᵀ Bᵀ := by
  refine (eq_extendSubmatrix_iff eₘ eₙ Aᵀ Bᵀ hₘ hₙ).mpr ⟨by ext; simp [hₙ, hₘ], fun _ _ h ↦ ?_⟩
  rcases h with h | h
  · exact extendSubmatrix_apply_of_notMem_right _ _ _ _ h
  · exact extendSubmatrix_apply_of_notMem_left _ _ _ _ h

theorem conjTranspose_extendSubmatrix [Star α] (hₙ : Injective eₙ) (hₘ : Injective eₘ) :
    (extendSubmatrix eₙ eₘ A B)ᴴ = extendSubmatrix eₘ eₙ Aᴴ Bᴴ := by
  simp [conjTranspose, transpose_extendSubmatrix _ _ _ _ hₙ hₘ, extendSubmatrix_map]

theorem extendSubmatrix_diagonal [Zero α] [DecidableEq n] [DecidableEq o] (hₙ : Injective eₙ)
    (d : n → α) (d' : o → α) :
    extendSubmatrix eₙ eₙ (diagonal d) (diagonal d') = diagonal (extend eₙ d d') := by
  rw [eq_comm, eq_extendSubmatrix_iff _ _ _ _ hₙ hₙ]
  refine ⟨by ext; simp [diagonal_apply, hₙ.eq_iff, hₙ.extend_apply], fun i j h ↦ ?_⟩
  obtain rfl | hij := eq_or_ne i j
  · rcases h with h | h <;> simp [extend_apply' _ _ _ h]
  · simp [hij]

theorem extendSubmatrix_reindex (σ : n ≃ k) (τ : m ≃ l) (eₖ : k → o) (eₗ : l → p)
    (hₖ : Injective eₖ) (hₗ : Injective eₗ) :
    extendSubmatrix eₖ eₗ (reindex σ τ A) B = extendSubmatrix (eₖ ∘ σ) (eₗ ∘ τ) A B := by
  rw [← extendSubmatrix_equiv_equiv,
    extendSubmatrix_trans _ _ _ _ _ σ.injective τ.injective hₖ hₗ]

theorem reindex_extendSubmatrix (hₙ : Injective eₙ) (hₘ : Injective eₘ) (ρ : o ≃ q)
    (π : p ≃ r) :
    reindex ρ π (extendSubmatrix eₙ eₘ A B) =
      extendSubmatrix (ρ ∘ eₙ) (π ∘ eₘ) A (reindex ρ π B) := by
  rw [← extendSubmatrix_equiv_equiv _ ((reindex ρ π) B),
    extendSubmatrix_trans eₙ eₘ A ρ π hₙ hₘ ρ.injective π.injective]
  simp

theorem extendSubmatrix_inl_inl (B : Matrix (n ⊕ o) (m ⊕ p) α) :
    extendSubmatrix Sum.inl Sum.inl A B =
      fromBlocks A B.toBlocks₁₂ B.toBlocks₂₁ B.toBlocks₂₂ := by
  ext (i | i) (j | j) <;>
  first
  | exact extendSubmatrix_apply_apply _ _ _ _ Sum.inl_injective Sum.inl_injective ..
  | simp [toBlocks₁₂, toBlocks₂₁, toBlocks₂₂]

theorem extendSubmatrix_inr_inr (B : Matrix (o ⊕ n) (p ⊕ m) α) :
    extendSubmatrix Sum.inr Sum.inr A B =
      fromBlocks B.toBlocks₁₁ B.toBlocks₁₂ B.toBlocks₂₁ A := by
  ext (i | i) (j | j) <;>
  first
  | exact extendSubmatrix_apply_apply _ _ _ _ Sum.inr_injective Sum.inr_injective ..
  | simp [toBlocks₁₁, toBlocks₁₂, toBlocks₂₁]

theorem extendSubmatrix_inl_inr (B : Matrix (n ⊕ o) (p ⊕ m) α) :
    extendSubmatrix Sum.inl Sum.inr A B =
      fromBlocks B.toBlocks₁₁ A B.toBlocks₂₁ B.toBlocks₂₂ := by
  ext (i | i) (j | j) <;>
  first
  | exact extendSubmatrix_apply_apply _ _ _ _ Sum.inl_injective Sum.inr_injective ..
  | simp [toBlocks₁₁, toBlocks₂₁, toBlocks₂₂]

theorem extendSubmatrix_inr_inl (B : Matrix (o ⊕ n) (m ⊕ p) α) :
    extendSubmatrix Sum.inr Sum.inl A B =
      fromBlocks B.toBlocks₁₁ B.toBlocks₁₂ A B.toBlocks₂₂ := by
  ext (i | i) (j | j) <;>
  first
  | exact extendSubmatrix_apply_apply _ _ _ _ Sum.inr_injective Sum.inl_injective ..
  | simp [toBlocks₁₁, toBlocks₁₂, toBlocks₂₂]

theorem submatrix_toSquareBlockProp_extendSubmatrix (hₙ : Injective eₙ) (M : Matrix n n α)
    (N : Matrix o o α) :
    ((extendSubmatrix eₙ eₙ M N).toSquareBlockProp (· ∈ Set.range eₙ)).submatrix
      (Equiv.ofInjective eₙ hₙ) (Equiv.ofInjective eₙ hₙ) = M := by
  ext
  simp [toSquareBlockProp_def, hₙ]

theorem toSquareBlockProp_extendSubmatrix_compl (M : Matrix n n α) (N : Matrix o o α) :
    (extendSubmatrix eₙ eₙ M N).toSquareBlockProp (fun i ↦ i ∉ Set.range eₙ) =
      N.toSquareBlockProp (fun i ↦ i ∉ Set.range eₙ) := by
  ext ⟨-, hi⟩ ⟨-, hj⟩
  simp [toSquareBlockProp_def, hi]

theorem updateRow_eq_extendSubmatrix [DecidableEq o] (i : o) (b : p → α) :
    B.updateRow i b = extendSubmatrix (fun _ : Unit ↦ i) id (of fun _ ↦ b) B := by
  rw [eq_extendSubmatrix_iff _ _ _ _ (injective_of_subsingleton _) injective_id]
  refine ⟨by ext; simp, fun _ _ h ↦ ?_⟩
  rcases h with h | h
  · simp_all
  · exact (h ⟨_, rfl⟩).elim

theorem updateCol_eq_extendSubmatrix [DecidableEq p] (j : p) (b : o → α) :
    B.updateCol j b = extendSubmatrix id (fun _ : Unit ↦ j) (of fun i _ ↦ b i) B := by
  rw [eq_extendSubmatrix_iff _ _ _ _ injective_id (injective_of_subsingleton _)]
  refine ⟨by ext; simp, fun _ _ h ↦ ?_⟩
  rcases h with h | h
  · exact (h ⟨_, rfl⟩).elim
  · simp_all

theorem extendSubmatrix_updateRow_of_notMem [DecidableEq o] (hₙ : Injective eₙ) {i : o}
    (hi : i ∉ Set.range eₙ) (b : p → α) :
    extendSubmatrix eₙ eₘ A (B.updateRow i b) = (extendSubmatrix eₙ eₘ A B).updateRow i b := by
  ext x y
  by_cases hx : x = i
  · simp [hx, hi]
  · simp [hx, extendSubmatrix_apply_congr_left _ _ _ hₙ]

theorem extendSubmatrix_updateCol_of_notMem [DecidableEq p] (hₘ : Injective eₘ) {j : p}
    (hj : j ∉ Set.range eₘ) (b : o → α) :
    extendSubmatrix eₙ eₘ A (B.updateCol j b) = (extendSubmatrix eₙ eₘ A B).updateCol j b := by
  ext x y
  by_cases hy : y = j
  · subst hy
    simp [hj]
  · simp [hy, extendSubmatrix_apply_congr_right _ _ _ hₘ]

theorem updateRow_extendSubmatrix [DecidableEq n] [DecidableEq o] (hₙ : Injective eₙ) (a : n)
    (b : p → α) :
    (extendSubmatrix eₙ eₘ A B).updateRow (eₙ a) b =
      extendSubmatrix eₙ eₘ (A.updateRow a (b ∘ eₘ)) (B.updateRow (eₙ a) b) := by
  ext x y
  by_cases hx : x = eₙ a
  · subst hx
    rw [updateRow_self]
    simp [extendSubmatrix, of_apply, hₙ.extend_apply, updateRow_self]
  · rw [updateRow_ne hx]
    by_cases hx' : x ∈ Set.range eₙ
    · obtain ⟨c, rfl⟩ := hx'
      have hc : c ≠ a := fun h ↦ hx (h ▸ rfl)
      simp [extendSubmatrix, hₙ, hc, hx]
    · simp [hx', hx]

theorem updateCol_extendSubmatrix [DecidableEq m] [DecidableEq p] (hₘ : Injective eₘ) (a : m)
    (b : o → α) :
    (extendSubmatrix eₙ eₘ A B).updateCol (eₘ a) b =
      extendSubmatrix eₙ eₘ (A.updateCol a (b ∘ eₙ)) (B.updateCol (eₘ a) b) := by
  ext x y
  by_cases hy : y = eₘ a
  · simp [hy, updateCol_self, extendSubmatrix, comp_def, apply_extend fun r : p → α ↦ r (eₘ a), hₘ,
      (congrFun (extend_comp_self eₙ b) x).symm]
  · by_cases hy' : y ∈ Set.range eₘ
    · obtain ⟨c, rfl⟩ := hy'
      have hc : c ≠ a := fun h ↦ hy (h ▸ rfl)
      simp [extendSubmatrix, comp_def, apply_extend fun r : p → α ↦ r (eₘ c), hₘ, hc, hy]
    · simp [hy', hy]

theorem extendSubmatrix_add [Add α] (C : Matrix n m α) (D : Matrix o p α) :
    extendSubmatrix eₙ eₘ (A + C) (B + D) =
      extendSubmatrix eₙ eₘ A B + extendSubmatrix eₙ eₘ C D := by
  have h : (fun i ↦ extend eₘ ((A + C) i) ((B + D) (eₙ i))) =
      (fun i ↦ extend eₘ (A i) (B (eₙ i))) + fun i ↦ extend eₘ (C i) (D (eₙ i)) :=
    funext fun i ↦ extend_add eₘ (A i) (C i) (B (eₙ i)) (D (eₙ i))
  simp only [extendSubmatrix, h, of_add_of, ← extend_add]
  rfl

@[simp]
theorem extendSubmatrix_zero [Zero α] :
    extendSubmatrix eₙ eₘ (0 : Matrix n m α) (0 : Matrix o p α) = 0 :=
  (extendSubmatrix_map eₙ eₘ (0 : Matrix n m α) 0 fun _ ↦ (0 : α)).symm

theorem extendSubmatrix_neg [Neg α] :
    extendSubmatrix eₙ eₘ (-A) (-B) = -extendSubmatrix eₙ eₘ A B :=
  (extendSubmatrix_map eₙ eₘ A B (-·)).symm

theorem extendSubmatrix_sub [Sub α] (C : Matrix n m α) (D : Matrix o p α) :
    extendSubmatrix eₙ eₘ (A - C) (B - D) =
      extendSubmatrix eₙ eₘ A B - extendSubmatrix eₙ eₘ C D := by
  have h : (fun i ↦ extend eₘ ((A - C) i) ((B - D) (eₙ i))) =
      (fun i ↦ extend eₘ (A i) (B (eₙ i))) - fun i ↦ extend eₘ (C i) (D (eₙ i)) :=
    funext fun i ↦ extend_sub eₘ (A i) (C i) (B (eₙ i)) (D (eₙ i))
  simp only [extendSubmatrix, h, of_sub_of, ← extend_sub]
  rfl

theorem extendSubmatrix_smul [SMul R α] (r : R) :
    extendSubmatrix eₙ eₘ (r • A) (r • B) = r • extendSubmatrix eₙ eₘ A B :=
  (extendSubmatrix_map eₙ eₘ A B (r • ·)).symm

/-- `extendSubmatrix eₙ eₘ` as an additive monoid homomorphism in the pair `(A, B)`. -/
@[simps]
noncomputable def extendSubmatrixAddMonoidHom [AddZeroClass α] :
    Matrix n m α × Matrix o p α →+ Matrix o p α where
  toFun M := extendSubmatrix eₙ eₘ M.fst M.snd
  map_zero' := extendSubmatrix_zero eₙ eₘ
  map_add' _ _ := extendSubmatrix_add ..

variable (R) in
/-- `extendSubmatrix eₙ eₘ` as an `R`-linear map in the pair `(A, B)`. -/
@[simps!]
noncomputable def extendSubmatrixLinearMap [Semiring R] [AddCommMonoid α] [Module R α] :
    Matrix n m α × Matrix o p α →ₗ[R] Matrix o p α where
  __ := extendSubmatrixAddMonoidHom eₙ eₘ
  map_smul' _ _ := extendSubmatrix_smul ..

@[simp]
theorem extendSubmatrixLinearMap_toAddMonoidHom [Semiring R] [AddCommMonoid α] [Module R α] :
    (extendSubmatrixLinearMap R eₙ eₘ (α := α)).toAddMonoidHom =
      extendSubmatrixAddMonoidHom eₙ eₘ :=
  rfl

end ExtendSubmatrix

end Matrix
