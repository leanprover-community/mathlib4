/-
Copyright (c) 2026 Ambrose Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ambrose Tang
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.LinearAlgebra.Matrix.Cartan.Classification.Leaf

import Mathlib.LinearAlgebra.Matrix.Cartan.Classification.Exceptional
import Mathlib.LinearAlgebra.Matrix.Cartan.Classification.TypeA
import Mathlib.LinearAlgebra.Matrix.Cartan.Classification.TypeB
import Mathlib.LinearAlgebra.Matrix.Cartan.Classification.TypeD
import Mathlib.LinearAlgebra.Matrix.Cartan.Classification.TypeE

/-!
# Classification of finite Cartan matrices

We prove that every indecomposable finite Cartan matrix is, after relabelling its index set, one
of `Aₙ, Bₙ, Cₙ, Dₙ, E₆, E₇, E₈, F₄, G₂`.

## Strategy

We induct on the number of indices and remove one index at a time.

1. The Dynkin diagram is connected, so some index `v` can be removed without disconnecting it
   (`SimpleGraph.Connected.exists_connected_induce_compl_singleton_of_finite_nontrivial`). By
   induction the rest of the matrix is one of the listed matrices `K`.
2. The index `v` is a *leaf*: it has exactly one neighbour `u`. Indeed, along the induction we also
   carry the fact that the unit vector `∑ εᵢ` has length at most `1`; a second neighbour would make
   the vector `∑ εᵢ + ε_v` have length at most `0`. So our matrix is `addLeaf K u a b`, where
   `a = M u v` and `b = M v u`.
3. For each listed `K` we go through the possible positions `u` and bonds `(a, b)` (files
   `Classification/TypeA.lean`, …, `Classification/Exceptional.lean`). Each result is either
   again in the list, or it is ruled out by one of two tests:
   * the *master inequality* (`Matrix.IsFiniteCartan.sum_mul_lt_four`, used through
     `Matrix.IsFiniteCartan.bonds_lt_four` and `Matrix.IsFiniteCartan.path_bonds_lt_four`): the
     bonds leaving a path number fewer than four (this handles too many bonds at an index, two
     branch points, two double bonds, and a branch point together with a double bond, whatever
     their distance);
   * a *null vector*: a principal submatrix with a non-zero kernel vector has determinant zero,
     contradicting `Matrix.IsFiniteCartan.det_pos` (this handles the affine diagrams of type
     `E₆`, `E₇`, `E₈` and `F₄`, which occur when an arm becomes too long).

Compared with Humphreys §11.4, step 3 replaces the shape theorem and the recognition of the shape:
since the new index is always attached to a matrix that we already know explicitly, the
relabelling `e : ι ≃ Fin n` is built one index at a time.

## Main results

* `Matrix.IsFiniteCartan.hasDynkinType_and_sum_le_one`: the induction.
* `Matrix.IsFiniteCartan.exists_A_or_B_or_C_or_D_or_E_or_F_or_G`: the classification.

## References

* [J. Humphreys, *Introduction to Lie Algebras and Representation Theory*][humphreys1972]
  §11.4
-/

public section

open Finset CartanMatrix

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-! ### The induction -/

namespace IsFiniteCartan

variable {M : Matrix ι ι ℤ} (hM : M.IsFiniteCartan)
include hM

omit hM [Fintype ι] [DecidableEq ι] in
/-- The Dynkin diagram of an indecomposable finite Cartan matrix is connected. -/
lemma connected_fromRel [Finite ι] (hM' : M.IsIndecomposable) [Nonempty ι] :
    (SimpleGraph.fromRel fun i j ↦ M i j ≠ 0).Connected := by
  rw [isIndecomposable_iff_reflTransGen] at hM'
  refine { preconnected := fun i j ↦ ?_ }
  rw [SimpleGraph.reachable_iff_reflTransGen]
  induction hM' i j with
  | refl => rfl
  | @tail b c _ hbc ih =>
    by_cases h : b = c
    · exact h ▸ ih
    · exact ih.tail ((SimpleGraph.fromRel_adj _ _ _).mpr ⟨h, .inl hbc⟩)

/-- Removing a node that does not disconnect the Dynkin diagram leaves an indecomposable
matrix. -/
lemma isIndecomposable_submatrix {v : ι}
    (hv : ((SimpleGraph.fromRel fun i j ↦ M i j ≠ 0).induce {v}ᶜ).Connected) :
    (M.submatrix ((↑) : ({v}ᶜ : Set ι) → ι) (↑)).IsIndecomposable := by
  rw [isIndecomposable_iff_reflTransGen]
  intro i j
  refine Relation.ReflTransGen.mono (fun x y hxy ↦ ?_) _ _
    ((SimpleGraph.reachable_iff_reflTransGen i j).mp (hv.preconnected i j))
  simp only [SimpleGraph.induce_adj, SimpleGraph.fromRel_adj] at hxy
  obtain ⟨-, h | h⟩ := hxy
  · exact h
  · simpa [hM.zero_comm] using h

/-- If `v` is a leaf with neighbour `u` and the rest of the matrix is the listed matrix `K`, then
our matrix is `addLeaf K u a b` after relabelling. -/
lemma hasDynkinType_of_leaf {u v : ι} (huv : u ≠ v) (hu : M u v ≠ 0)
    (honly : ∀ w, w ≠ v → w ≠ u → M w v = 0) {k : ℕ} {K : Matrix (Fin k) (Fin k) ℤ}
    (e : ({v}ᶜ : Set ι) ≃ Fin k)
    (he : (M.submatrix ((↑) : ({v}ᶜ : Set ι) → ι) (↑)).reindex e e = K)
    (hstep : ∀ u' a b, IsBond a b → (addLeaf K u' a b).IsFiniteCartan →
      (addLeaf K u' a b).HasDynkinType) :
    M.HasDynkinType := by
  have hne (j : Fin k) : (e.symm j : ι) ≠ v := (e.symm j).2
  let E : ι ≃ Fin (k + 1) :=
    { toFun i := if h : i = v then Fin.last k else (e ⟨i, h⟩).castSucc
      invFun := Fin.lastCases v fun j ↦ e.symm j
      left_inv i := by by_cases h : i = v <;> simp [h]
      right_inv j := by induction j using Fin.lastCases <;> simp [hne] }
  have hE (j : Fin k) : E.symm j.castSucc = e.symm j := by simp [E]
  have hEv : E.symm (Fin.last k) = v := by simp [E]
  have hKe (i j : Fin k) : K i j = M (e.symm i) (e.symm j) := by rw [← he]; simp
  have hiff (j : Fin k) : (e.symm j : ι) = u ↔ j = e ⟨u, huv⟩ := by
    refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
    rw [← e.apply_symm_apply j]
    exact congrArg e (Subtype.ext h)
  have hME : M.reindex E E = addLeaf K (e ⟨u, huv⟩) (M u v) (M v u) := by
    ext i j
    induction i using Fin.lastCases <;> induction j using Fin.lastCases
    · simp [hEv, hM.diag]
    · rename_i j
      simp only [reindex_apply, submatrix_apply, hEv, hE, addLeaf_last_castSucc]
      split_ifs with h
      · rw [(hiff j).mpr h]
      · rw [hM.zero_comm, honly _ (hne j) (mt (hiff j).mp h)]
    · rename_i i
      simp only [reindex_apply, submatrix_apply, hEv, hE, addLeaf_castSucc_last]
      split_ifs with h
      · rw [(hiff i).mpr h]
      · rw [honly _ (hne i) (mt (hiff i).mp h)]
    · simp [hE, hKe]
  exact HasDynkinType.of_reindex E (hME ▸ hstep _ _ _
    ((hM.apply_cases huv).resolve_left fun h ↦ hu h.1) (hME ▸ hM.reindex E))

/-- An index `v` is joined to at most one other index, provided the rest has `‖∑ εᵢ‖ ≤ 1`: two
neighbours `u, w` would give `‖∑ εᵢ‖² ≤ 1 + 1 + 2 (εᵤ + ε_w, ε_v) ≤ 0`. -/
lemma eq_zero_of_cartanGram_sum_le_one {u v w : ι} (huv : u ≠ v) (hu : M u v ≠ 0) (hwv : w ≠ v)
    (hwu : w ≠ u) (hq : ∑ i ∈ univ.erase v, ∑ j ∈ univ.erase v, cartanGram M i j ≤ 1) :
    M w v = 0 := by
  have hA := hM.isAdmissible_cartanGram
  by_contra hw
  have hpos := hA.sum_pos (S := univ) ⟨v, mem_univ v⟩
  rw [← insert_erase (mem_univ v), hA.sum_insert_eq (notMem_erase v univ)] at hpos
  have hu' : u ∈ univ.erase v := by simp [huv]
  have hw' : w ∈ (univ.erase v).erase u := by simp [hwv, hwu]
  have h₃ : ∑ t ∈ ((univ.erase v).erase u).erase w, cartanGram M t v ≤ 0 :=
    sum_nonpos fun t ht ↦ hA.offDiag_nonpos t v (by simp at ht; tauto)
  have h₁ := hA.le_neg_half huv ((hM.cartanGram_eq_zero_iff huv).not.mpr hu)
  have h₂ := hA.le_neg_half hwv ((hM.cartanGram_eq_zero_iff hwv).not.mpr hw)
  have : ∑ t ∈ univ.erase v, cartanGram M t v ≤ -1 := by
    rw [← add_sum_erase _ _ hu', ← add_sum_erase _ _ hw']
    linarith
  linarith

omit hM [Fintype κ] [DecidableEq κ] in
lemma isIndecomposable_of_reindex {k : ℕ} {X : Matrix κ κ ℤ} {K : Matrix (Fin k) (Fin k) ℤ}
    (hX : X.IsIndecomposable) (e : κ ≃ Fin k) (he : X.reindex e e = K) : K.IsIndecomposable := by
  have := Finite.of_equiv _ e.symm
  rw [isIndecomposable_iff_reflTransGen] at hX ⊢
  intro i j
  have := Relation.ReflTransGen.lift e (p := fun i j ↦ K i j ≠ 0)
    (fun x y h ↦ by simpa [← he, Function.onFun] using h) _ _ (hX (e.symm i) (e.symm j))
  simpa [Function.onFun] using this

end IsFiniteCartan

universe u in
/-- The induction behind the classification. Along with the Dynkin type we keep track of
`‖∑ εᵢ‖ ≤ 1`, which is what forces each new node to be a leaf. -/
theorem IsFiniteCartan.hasDynkinType_and_sum_le_one (n : ℕ) :
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
    ∀ {M : Matrix ι ι ℤ}, M.IsFiniteCartan → M.IsIndecomposable →
      M.HasDynkinType ∧ ∑ i, ∑ j, cartanGram M i j ≤ 1 := by
  induction n using Nat.strong_induction_on with | _ n ih
  intro ι _ _ hn M hM hM'
  obtain rfl | rfl | hn₂ : n = 0 ∨ n = 1 ∨ 2 ≤ n := by lia
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hn
    exact ⟨.inl ⟨0, Fintype.equivFinOfCardEq hn, by ext i; exact i.elim0⟩, by simp⟩
  · obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp hn
    refine ⟨.inl ⟨1, Fintype.equivFinOfCardEq hn, ?_⟩, ?_⟩
    · ext i j
      fin_cases i; fin_cases j
      simp [A, hM.diag]
    · have h (f : ι → ℝ) : ∑ i, f i = f x :=
        Fintype.sum_eq_single x fun y hy ↦ (hy (hx y)).elim
      simp [h]
  -- Remove a node `v` that does not disconnect the diagram.
  have : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by lia)
  have hG := connected_fromRel hM'
  obtain ⟨v, hv⟩ := hG.exists_connected_induce_compl_singleton_of_finite_nontrivial
  have hX' := hM.isIndecomposable_submatrix hv
  have hL : Fintype.card ({v}ᶜ : Set ι) = n - 1 := by
    rw [Fintype.card_compl_set]
    simp [hn]
  obtain ⟨hXD, hXq⟩ := ih (n - 1) (by lia) hL (hM.submatrix Subtype.val_injective) hX'
  have hq : ∑ i ∈ univ.erase v, ∑ j ∈ univ.erase v, cartanGram M i j ≤ 1 := by
    have hmem (x : ι) : x ∈ univ.erase v ↔ x ∈ ({v}ᶜ : Set ι) := by simp
    rw [cartanGram_submatrix _ Subtype.val_injective] at hXq
    rw [sum_subtype _ hmem]
    convert hXq using 2 with i
    rw [sum_subtype _ hmem]
    rfl
  -- The node `v` has a neighbour `u`, and no other.
  obtain ⟨u, huv, hu⟩ : ∃ u, u ≠ v ∧ M u v ≠ 0 := by
    obtain ⟨w, hw⟩ := exists_ne v
    have := hG.preconnected w v
    rw [SimpleGraph.reachable_iff_reflTransGen] at this
    rcases this.cases_tail with h | ⟨c, -, hc⟩
    · exact absurd h.symm hw
    · rw [SimpleGraph.fromRel_adj] at hc
      exact ⟨c, hc.1, hc.2.elim id fun h ↦ by simpa [hM.zero_comm] using h⟩
  have honly (w : ι) (hwv : w ≠ v) (hwu : w ≠ u) : M w v = 0 :=
    hM.eq_zero_of_cartanGram_sum_le_one huv hu hwv hwu hq
  refine ⟨?_, ?_⟩
  · rcases hXD with ⟨k, e, he⟩ | ⟨k, e, he⟩ | ⟨k, e, he⟩ | ⟨k, e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩ |
      ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩
    · exact hM.hasDynkinType_of_leaf huv hu honly e he fun _ _ _ hab h ↦
        h.hasDynkinType_addLeaf_A hab
    · exact hM.hasDynkinType_of_leaf huv hu honly e he fun _ _ _ hab h ↦
        h.hasDynkinType_addLeaf_B hab
    · exact hM.hasDynkinType_of_leaf huv hu honly e he fun _ _ _ hab h ↦
        h.hasDynkinType_addLeaf_C hab
    · exact hM.hasDynkinType_of_leaf huv hu honly e he fun _ _ _ hab h ↦
        h.hasDynkinType_addLeaf_D hab (IsFiniteCartan.isIndecomposable_of_reindex hX' e he)
    · exact hM.hasDynkinType_of_leaf huv hu honly e he fun _ _ _ hab h ↦
        h.hasDynkinType_addLeaf_E hab (by simp)
    · exact hM.hasDynkinType_of_leaf huv hu honly e he fun _ _ _ hab h ↦
        h.hasDynkinType_addLeaf_E hab (by simp)
    · exact hM.hasDynkinType_of_leaf huv hu honly e he fun _ _ _ hab h ↦
        h.hasDynkinType_addLeaf_E hab (by simp)
    · exact hM.hasDynkinType_of_leaf huv hu honly e he fun u' _ _ hab h ↦
        (not_isFiniteCartan_addLeaf_F₄ u' hab h).elim
    · exact hM.hasDynkinType_of_leaf huv hu honly e he fun u' _ _ hab h ↦
        (not_isFiniteCartan_addLeaf_G₂ u' hab h).elim
  · rw [← insert_erase (mem_univ v)]
    exact (hM.cartanGram_sum_insert_le (notMem_erase v univ) (s := u) (by simp [huv]) hu).trans hq

/-- **Classification of finite Cartan matrices.** An indecomposable finite Cartan matrix is, after
relabelling, one of `Aₙ, Bₙ, Cₙ, Dₙ, E₆, E₇, E₈, F₄, G₂`. -/
theorem IsFiniteCartan.exists_A_or_B_or_C_or_D_or_E_or_F_or_G {l : Type*} [Fintype l]
    [DecidableEq l] {M : Matrix l l ℤ} (hM : M.IsFiniteCartan) (hM' : M.IsIndecomposable) :
    (∃ n e, M.reindex e e = CartanMatrix.A n) ∨
    (∃ n e, M.reindex e e = CartanMatrix.B n) ∨
    (∃ n e, M.reindex e e = CartanMatrix.C n) ∨
    (∃ n e, M.reindex e e = CartanMatrix.D n) ∨
    (∃ e, M.reindex e e = CartanMatrix.E 6) ∨
    (∃ e, M.reindex e e = CartanMatrix.E 7) ∨
    (∃ e, M.reindex e e = CartanMatrix.E 8) ∨
    (∃ e, M.reindex e e = CartanMatrix.F₄) ∨
    (∃ e, M.reindex e e = CartanMatrix.G₂) :=
  (hasDynkinType_and_sum_le_one _ rfl hM hM').1

end Matrix
