/-
Copyright (c) 2026 Ambrose Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ambrose Tang
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Admissible

/-!
# Attaching a leaf to a Cartan matrix

Infrastructure for the classification of finite Cartan matrices
(`Mathlib.LinearAlgebra.Matrix.Cartan.Classification`). The classification attaches one index at
a time to a matrix that is already known to be one of `Aₙ, Bₙ, Cₙ, Dₙ, E₆, E₇, E₈, F₄, G₂`; this
file defines the operation and the tests used to decide the outcome.

## Main definitions

* `Matrix.HasDynkinType`: `M` is a relabelling of one of `Aₙ, Bₙ, Cₙ, Dₙ, E₆, E₇, E₈, F₄, G₂`.
* `Matrix.addLeaf`: attach a new index to a matrix indexed by `Fin n`.

## Main results

* `Matrix.HasDynkinType.submatrix_iff`, `Matrix.HasDynkinType.transpose`: invariance under
  relabelling and transposition.
* `Matrix.hasDynkinType_addLeaf_iff_of_submatrix_eq`,
  `Matrix.isFiniteCartan_addLeaf_iff_of_submatrix_eq`: a symmetry of `X` moves the leaf.
* `Matrix.IsFiniteCartan.bonds_lt_four`: fewer than four bonds meet at an index.
* `Matrix.IsFiniteCartan.path_bonds_lt_four`: fewer than four bonds leave a path.
* `Matrix.IsFiniteCartan.mulVec_ne_zero`: no principal submatrix has a non-zero null vector.
-/

@[expose] public section

open Finset CartanMatrix

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-! ### Matrices of Dynkin type -/

/-- `M` is, after relabelling, one of the Cartan matrices `Aₙ, Bₙ, Cₙ, Dₙ, E₆, E₇, E₈, F₄, G₂`. -/
def HasDynkinType (M : Matrix ι ι ℤ) : Prop :=
  (∃ n e, M.reindex e e = A n) ∨ (∃ n e, M.reindex e e = B n) ∨
    (∃ n e, M.reindex e e = C n) ∨ (∃ n e, M.reindex e e = D n) ∨
    (∃ e, M.reindex e e = E 6) ∨ (∃ e, M.reindex e e = E 7) ∨ (∃ e, M.reindex e e = E 8) ∨
    (∃ e, M.reindex e e = F₄) ∨ (∃ e, M.reindex e e = G₂)

namespace HasDynkinType

variable {M : Matrix ι ι ℤ}

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma of_reindex (e : ι ≃ κ) (h : (M.reindex e e).HasDynkinType) : M.HasDynkinType := by
  have key {n : ℕ} (e' : κ ≃ Fin n) :
      (M.reindex e e).reindex e' e' = M.reindex (e.trans e') (e.trans e') := by
    ext; simp
  unfold HasDynkinType at h ⊢
  simp only [key] at h
  rcases h with ⟨n, e', h⟩ | ⟨n, e', h⟩ | ⟨n, e', h⟩ | ⟨n, e', h⟩ | ⟨e', h⟩ | ⟨e', h⟩ | ⟨e', h⟩ |
    ⟨e', h⟩ | ⟨e', h⟩
  exacts [.inl ⟨n, _, h⟩, .inr <| .inl ⟨n, _, h⟩, .inr <| .inr <| .inl ⟨n, _, h⟩,
    .inr <| .inr <| .inr <| .inl ⟨n, _, h⟩, .inr <| .inr <| .inr <| .inr <| .inl ⟨_, h⟩,
    .inr <| .inr <| .inr <| .inr <| .inr <| .inl ⟨_, h⟩,
    .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl ⟨_, h⟩,
    .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl ⟨_, h⟩,
    .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr ⟨_, h⟩]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
@[simp] lemma submatrix_iff (σ : κ ≃ ι) :
    (M.submatrix σ σ).HasDynkinType ↔ M.HasDynkinType := by
  refine ⟨fun h ↦ of_reindex σ.symm h, fun h ↦ of_reindex σ ?_⟩
  convert h using 2
  ext; simp

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- To show that `M` has Dynkin type, exhibit it as a relabelling of a matrix of Dynkin type. -/
lemma of_eq_submatrix {K : Matrix κ κ ℤ} (σ : ι ≃ κ) (h : M = K.submatrix σ σ)
    (hK : K.HasDynkinType) : M.HasDynkinType :=
  h ▸ (submatrix_iff σ).mpr hK

omit [Fintype ι] [DecidableEq ι] in
lemma transpose (h : M.HasDynkinType) : Mᵀ.HasDynkinType := by
  have hF : F₄ᵀ.reindex Fin.revPerm Fin.revPerm = F₄ := by decide
  have hG : G₂ᵀ.reindex Fin.revPerm Fin.revPerm = G₂ := by decide
  have key {n : ℕ} (e : ι ≃ Fin n) (e' : Fin n ≃ Fin n) :
      (M.reindex (e.trans e') (e.trans e'))ᵀ = ((M.reindex e e)ᵀ).reindex e' e' := by
    ext; simp
  unfold HasDynkinType at h ⊢
  simp only [← transpose_reindex]
  rcases h with ⟨n, e, h⟩ | ⟨n, e, h⟩ | ⟨n, e, h⟩ | ⟨n, e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ |
    ⟨e, h⟩ | ⟨e, h⟩
  · exact .inl ⟨n, e, by rw [h, A_transpose]⟩
  · exact .inr <| .inr <| .inl ⟨n, e, by rw [h, B_transpose]⟩
  · exact .inr <| .inl ⟨n, e, by rw [h, C_transpose]⟩
  · exact .inr <| .inr <| .inr <| .inl ⟨n, e, by rw [h, D_transpose]⟩
  · exact .inr <| .inr <| .inr <| .inr <| .inl ⟨e, by rw [h, E_transpose]⟩
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inl ⟨e, by rw [h, E_transpose]⟩
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl ⟨e, by rw [h, E_transpose]⟩
  · refine .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl
      ⟨e.trans Fin.revPerm, ?_⟩
    rw [key, h, hF]
  · refine .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr
      ⟨e.trans Fin.revPerm, ?_⟩
    rw [key, h, hG]

end HasDynkinType

/-! The listed matrices have Dynkin type. -/

lemma hasDynkinType_A (n : ℕ) : (A n).HasDynkinType := .inl ⟨n, .refl _, by simp⟩

lemma hasDynkinType_B (n : ℕ) : (B n).HasDynkinType := .inr <| .inl ⟨n, .refl _, by simp⟩

lemma hasDynkinType_C (n : ℕ) : (C n).HasDynkinType := .inr <| .inr <| .inl ⟨n, .refl _, by simp⟩

lemma hasDynkinType_D (n : ℕ) : (D n).HasDynkinType :=
  .inr <| .inr <| .inr <| .inl ⟨n, .refl _, by simp⟩

lemma hasDynkinType_E_six : (E 6).HasDynkinType :=
  .inr <| .inr <| .inr <| .inr <| .inl ⟨.refl _, by simp⟩

lemma hasDynkinType_E_seven : (E 7).HasDynkinType :=
  .inr <| .inr <| .inr <| .inr <| .inr <| .inl ⟨.refl _, by simp⟩

lemma hasDynkinType_E_eight : (E 8).HasDynkinType :=
  .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl ⟨.refl _, by simp⟩

lemma hasDynkinType_F₄ : F₄.HasDynkinType :=
  .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl ⟨.refl _, by simp⟩

lemma hasDynkinType_G₂ : G₂.HasDynkinType :=
  .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr ⟨.refl _, by simp⟩

/-! ### Attaching a leaf -/

/-- Attach a new node `Fin.last n` to the node `u` of `X`, with `a` in position `(u, last)` and `b`
in position `(last, u)`. -/
def addLeaf {n : ℕ} (X : Matrix (Fin n) (Fin n) ℤ) (u : Fin n) (a b : ℤ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  of fun i j ↦
    if hi : (i : ℕ) < n then
      if hj : (j : ℕ) < n then X ⟨i, hi⟩ ⟨j, hj⟩ else if (i : ℕ) = u then a else 0
    else if (j : ℕ) < n then (if (j : ℕ) = u then b else 0) else 2

section addLeaf

variable {n : ℕ} (X : Matrix (Fin n) (Fin n) ℤ) (u : Fin n) (a b : ℤ)

@[simp] lemma addLeaf_castSucc_castSucc (i j : Fin n) :
    addLeaf X u a b i.castSucc j.castSucc = X i j := by
  simp [addLeaf]

@[simp] lemma addLeaf_castSucc_last (i : Fin n) :
    addLeaf X u a b i.castSucc (Fin.last n) = if i = u then a else 0 := by
  simp [addLeaf, Fin.ext_iff]

@[simp] lemma addLeaf_last_castSucc (j : Fin n) :
    addLeaf X u a b (Fin.last n) j.castSucc = if j = u then b else 0 := by
  simp [addLeaf, Fin.ext_iff]

@[simp] lemma addLeaf_last_last : addLeaf X u a b (Fin.last n) (Fin.last n) = 2 := by
  simp [addLeaf]

lemma addLeaf_transpose : (addLeaf X u a b)ᵀ = addLeaf Xᵀ u b a := by
  ext i j
  simp only [addLeaf, transpose_apply, of_apply]
  split_ifs <;> rfl

lemma addLeaf_submatrix (σ : Equiv.Perm (Fin n)) :
    addLeaf (X.submatrix σ σ) u a b =
      (addLeaf X (σ u) a b).submatrix (finSuccEquivLast.symm.permCongr σ.optionCongr)
        (finSuccEquivLast.symm.permCongr σ.optionCongr) := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Equiv.permCongr_apply, finSuccEquivLast_castSucc, σ.injective.eq_iff]

/-- If a permutation `σ` fixes `X`, then attaching a leaf at `u` or at `σ u` gives the same matrix
up to relabelling; this is the form in which symmetries of `Aₙ` and `Dₙ` are used. -/
lemma isFiniteCartan_addLeaf_iff_of_submatrix_eq {σ : Equiv.Perm (Fin n)}
    (hσ : X.submatrix σ σ = X) :
    (addLeaf X (σ u) a b).IsFiniteCartan ↔ (addLeaf X u a b).IsFiniteCartan := by
  conv_rhs => rw [← hσ, addLeaf_submatrix]
  simp

/-- See `Matrix.isFiniteCartan_addLeaf_iff_of_submatrix_eq`. -/
lemma hasDynkinType_addLeaf_iff_of_submatrix_eq {σ : Equiv.Perm (Fin n)}
    (hσ : X.submatrix σ σ = X) :
    (addLeaf X (σ u) a b).HasDynkinType ↔ (addLeaf X u a b).HasDynkinType := by
  conv_rhs => rw [← hσ, addLeaf_submatrix]
  simp

end addLeaf

/-! ### Three tests ruling out a configuration -/

namespace IsFiniteCartan

variable {M : Matrix ι ι ℤ} (hM : M.IsFiniteCartan)
include hM

/-- Fewer than four bonds at a node, stated for an explicit list of distinct neighbours. -/
lemma bonds_lt_four (i : ι) (l : List ι) (hl : (i :: l).Nodup) :
    (l.map fun j ↦ M i j * M j i).sum < 4 := by
  rw [List.nodup_cons] at hl
  rw [← List.sum_toFinset _ hl.2]
  exact hM.sum_mul_lt_four_of_notMem (by simpa using hl.1)

/-- Fewer than four bonds leave the path `f 0, …, f k`. Each entry `(t, j)` of `l` is an index `j`
off the path together with the position `t` of the path index it is joined to. -/
lemma path_bonds_lt_four {k : ℕ} (f : Fin (k + 1) → ι) (hf : Function.Injective f)
    (hadj : ∀ i : Fin k, M (f i.castSucc) (f i.succ) ≠ 0) (l : List (Fin (k + 1) × ι))
    (hl : (l.map Prod.snd).Nodup) (hoff : ∀ p ∈ l, p.2 ∉ Set.range f) :
    (l.map fun p ↦ M (f p.1) p.2 * M p.2 (f p.1)).sum < 4 := by
  set S := univ.image f
  set T : ι → ℤ := fun j ↦ ∑ s ∈ S, M s j * M j s
  have hSN : Disjoint S (l.map Prod.snd).toFinset := by
    simp only [S, disjoint_left, mem_image, mem_univ, true_and, List.mem_toFinset, List.mem_map]
    rintro _ ⟨i, rfl⟩ ⟨p, hp, h⟩
    exact hoff p hp ⟨i, h.symm⟩
  have hle : ∀ p ∈ l, M (f p.1) p.2 * M p.2 (f p.1) ≤ T p.2 := fun p hp ↦
    single_le_sum (f := fun s ↦ M s p.2 * M p.2 s)
      (fun s hs ↦ hM.mul_nonneg_of_ne fun h ↦ disjoint_left.mp hSN hs
        (List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, h.symm⟩)))
      (mem_image_of_mem f (mem_univ _))
  calc (l.map fun p ↦ M (f p.1) p.2 * M p.2 (f p.1)).sum
      ≤ (l.map fun p ↦ T p.2).sum := List.sum_le_sum hle
    _ = ∑ j ∈ (l.map Prod.snd).toFinset, T j := by
        rw [List.sum_toFinset _ hl, List.map_map]; rfl
    _ < 4 := hM.sum_mul_lt_four (by simp [S]) (hM.cartanGram_sum_path_le f hf hadj) hSN

/-- A principal submatrix of a finite Cartan matrix has no non-zero null vector, since its
determinant is positive. This rules out the affine diagrams. -/
lemma mulVec_ne_zero {k : ℕ} {f : Fin k → ι} (hf : Function.Injective f) {x : Fin k → ℤ}
    (hx : x ≠ 0) : M.submatrix f f *ᵥ x ≠ 0 :=
  fun h ↦ hx (eq_zero_of_mulVec_eq_zero (hM.submatrix hf).det_pos.ne' h)

end IsFiniteCartan

end Matrix
