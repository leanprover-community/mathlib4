/-
Copyright (c) 2026 Ambrose Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ambrose Tang
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Classification.Leaf

import Mathlib.LinearAlgebra.Matrix.Cartan.Classification.TypeA
import Mathlib.Tactic.Simproc.IsIndecomposable

/-!
# The classification step for type `Dₙ`

Attaching a leaf to an indecomposable `Dₙ` gives a finite Cartan matrix only if the result has
Dynkin type: `Dₙ₊₁`, `E₆`, `E₇`, `E₈`, or (since `D₁ = A₁` and `D₃ ≅ A₃`) one of the types arising
from `A₁` and `A₃`.

In `Dₙ` (`n ≥ 4`) the nodes `0` and `1` are both joined to `2`, and the nodes `2, …, n-1` form a
path.

## Main results

* `Matrix.IsFiniteCartan.hasDynkinType_addLeaf_D`: attaching a leaf to an indecomposable `Dₙ`
  gives a matrix of Dynkin type whenever it gives a finite Cartan matrix.
-/

public section

open CartanMatrix

namespace Matrix

/-! ### The leaf at the long end or at an interior node -/

/-- Leaf at the long end `n-1`, simple bond: `Dₙ₊₁`. -/
private lemma addLeaf_D_last_eq {n : ℕ} (hn : 3 ≤ n) :
    addLeaf (D n) ⟨n - 1, by lia⟩ (-1) (-1) = D (n + 1) := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [-Fin.castSucc_mk, D, Fin.ext_iff] <;> split_ifs <;> lia

/-- Leaf at `n-1`, multiple bond: the path `2, …, n-1` has bonds to `0`, `1` and the leaf. -/
private lemma not_isFiniteCartan_addLeaf_D_last {n : ℕ} (hn : 4 ≤ n) {a b : ℤ}
    (hm : 2 ≤ a * b) : ¬ (addLeaf (D n) ⟨n - 1, by lia⟩ a b).IsFiniteCartan := fun h ↦ by
  have := h.path_bonds_lt_four (k := n - 3) (fun t ↦ (⟨t + 2, by lia⟩ : Fin n).castSucc)
    (fun x y hxy ↦ by simpa [Fin.ext_iff] using hxy)
    (fun i ↦ by
      simp (disch := lia) only [addLeaf_castSucc_castSucc, D, of_apply, Fin.ext_iff,
        Fin.val_castSucc, Fin.val_succ, ite_eq_right]
      lia)
    [(0, (⟨0, by lia⟩ : Fin n).castSucc), (0, (⟨1, by lia⟩ : Fin n).castSucc),
      (Fin.last _, Fin.last n)]
    (by simp [Fin.ext_iff]; lia)
    (fun p hp ⟨t, ht⟩ ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;>
        simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_last] at ht <;> lia)
  simp (disch := lia) only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    addLeaf_castSucc_castSucc, addLeaf_castSucc_last, addLeaf_last_castSucc, D, of_apply,
    Fin.ext_iff, Fin.val_last, Fin.val_zero, ite_eq_left, ite_eq_right] at this
  lia

/-- Leaf at `2 ≤ u ≤ n-2`: the path `2, …, u` has bonds to `0`, `1`, `u+1` and the leaf. -/
private lemma not_isFiniteCartan_addLeaf_D_mid {n u : ℕ} (hu2 : 2 ≤ u) (hu : u + 2 ≤ n)
    {a b : ℤ} (hm : 1 ≤ a * b) : ¬ (addLeaf (D n) ⟨u, by lia⟩ a b).IsFiniteCartan := fun h ↦ by
  have := h.path_bonds_lt_four (k := u - 2) (fun t ↦ (⟨t + 2, by lia⟩ : Fin n).castSucc)
    (fun x y hxy ↦ by simpa [Fin.ext_iff] using hxy)
    (fun i ↦ by
      simp (disch := lia) only [addLeaf_castSucc_castSucc, D, of_apply, Fin.ext_iff,
        Fin.val_castSucc, Fin.val_succ, ite_eq_right]
      lia)
    [(0, (⟨0, by lia⟩ : Fin n).castSucc), (0, (⟨1, by lia⟩ : Fin n).castSucc),
      (Fin.last _, (⟨u + 1, by lia⟩ : Fin n).castSucc), (Fin.last _, Fin.last n)]
    (by simp [Fin.ext_iff]; lia)
    (fun p hp ⟨t, ht⟩ ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;>
        simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_last] at ht <;> lia)
  simp (disch := lia) only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    addLeaf_castSucc_castSucc, addLeaf_castSucc_last, addLeaf_last_castSucc, D, of_apply,
    Fin.ext_iff, Fin.val_last, Fin.val_zero, add_zero, ite_eq_left, ite_eq_right] at this
  lia

/-! ### The leaf at a short arm -/

/-- Leaf at `1`, multiple bond: the path `1, 2` has bonds to the leaf, `0` and `3`. -/
private lemma not_isFiniteCartan_addLeaf_D_one_multiple {n : ℕ} (hn : 4 ≤ n) {a b : ℤ}
    (hm : 2 ≤ a * b) : ¬ (addLeaf (D n) ⟨1, by lia⟩ a b).IsFiniteCartan := fun h ↦ by
  have := h.path_bonds_lt_four
    ![(⟨1, by lia⟩ : Fin n).castSucc, (⟨2, by lia⟩ : Fin n).castSucc]
    (injective_pair_iff_ne.mpr (by simp [Fin.ext_iff]))
    (fun i ↦ by fin_cases i; simp [-Fin.castSucc_mk, D, Fin.ext_iff]; lia)
    [(0, Fin.last n), (1, (⟨0, by lia⟩ : Fin n).castSucc), (1, (⟨3, by lia⟩ : Fin n).castSucc)]
    (by simp [Fin.ext_iff]; lia) (by simp [Fin.ext_iff]; lia)
  simp (disch := lia) only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    addLeaf_castSucc_castSucc, addLeaf_castSucc_last, addLeaf_last_castSucc, D, of_apply,
    cons_val_zero, cons_val_one, Fin.ext_iff, ite_eq_left, ite_eq_right] at this
  lia

/-- The nodes `0, …, 7` of `Dₙ` together with a leaf at `1` form `D₈` with a leaf at `1`. -/
private lemma addLeaf_D_one_submatrix_eq {n : ℕ} (hn : 8 ≤ n) (a b : ℤ) :
    (addLeaf (D n) ⟨1, by lia⟩ a b).submatrix
      (Fin.lastCases (Fin.last n) fun i : Fin 8 ↦ (⟨i, by lia⟩ : Fin n).castSucc)
      (Fin.lastCases (Fin.last n) fun i : Fin 8 ↦ (⟨i, by lia⟩ : Fin n).castSucc) =
      addLeaf (D 8) 1 a b := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp only [submatrix_apply, Fin.lastCases_last, Fin.lastCases_castSucc, addLeaf_last_last,
      addLeaf_castSucc_castSucc, addLeaf_castSucc_last, addLeaf_last_castSucc] <;>
    simp [D, Fin.ext_iff]; lia

/-- Leaf at `1`, simple bond, `n ≥ 8`: the centre `2` with arms `0`; `1, leaf`; `3, …, 7` is
affine `E₈`. -/
private lemma not_isFiniteCartan_addLeaf_D_one_simple {n : ℕ} (hn : 8 ≤ n) :
    ¬ (addLeaf (D n) ⟨1, by lia⟩ (-1) (-1)).IsFiniteCartan := fun h ↦ by
  have hg : Function.Injective
      (Fin.lastCases (Fin.last n) fun i : Fin 8 ↦ (⟨i, by lia⟩ : Fin n).castSucc) := by
    intro i j hij
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hij <;>
      simp [Fin.ext_iff] at hij ⊢ <;> lia
  have h8 := h.submatrix hg
  rw [addLeaf_D_one_submatrix_eq hn] at h8
  exact h8.mulVec_ne_zero Function.injective_id (x := ![3, 4, 6, 5, 4, 3, 2, 1, 2]) (by decide)
    (by decide)

/-- Leaf at `1`: a multiple bond is excluded; a simple bond gives `D₅`, `E₆`, `E₇`, `E₈` for
`n = 4, 5, 6, 7` and contains affine `E₈` for `n ≥ 8`. -/
private lemma hasDynkinType_addLeaf_D_one {n : ℕ} (hn : 4 ≤ n) {u : Fin n} (hu : (u : ℕ) = 1)
    {a b : ℤ} (hab : IsBond a b) (h : (addLeaf (D n) u a b).IsFiniteCartan) :
    (addLeaf (D n) u a b).HasDynkinType := by
  obtain ⟨rfl, rfl⟩ | hm := hab.eq_neg_one_or_two_le_mul
  swap
  · obtain rfl : u = ⟨1, by lia⟩ := Fin.ext hu
    exact (not_isFiniteCartan_addLeaf_D_one_multiple hn hm h).elim
  obtain rfl | rfl | rfl | rfl | hn8 : n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ 8 ≤ n := by lia
  rotate_left 4
  -- arms `(1, 2, ≥ 5)` contain affine `E₈`
  · obtain rfl : u = ⟨1, by lia⟩ := Fin.ext hu
    exact (not_isFiniteCartan_addLeaf_D_one_simple hn8 h).elim
  all_goals obtain rfl : u = 1 := Fin.ext (by simp [hu])
  -- arms `(1, 1, 2)` from the centre: `D₅`
  · exact .of_eq_submatrix (.ofBijective ![0, 3, 2, 1, 4] (by decide)) (by decide)
      (hasDynkinType_D 5)
  -- arms `(1, 2, 2)`, `(1, 2, 3)`, `(1, 2, 4)`: `E₆`, `E₇`, `E₈`
  · exact .of_eq_submatrix (finRotate _) (by decide) hasDynkinType_E_six
  · exact .of_eq_submatrix (finRotate _) (by decide) hasDynkinType_E_seven
  · exact .of_eq_submatrix (finRotate _) (by decide) hasDynkinType_E_eight

/-! ### The classification step -/

/-- Attaching a leaf to an indecomposable `Dₙ` gives a matrix of Dynkin type whenever it gives a
finite Cartan matrix. The hypothesis `hD` only serves to exclude `D₂`, which is two isolated
nodes. -/
theorem IsFiniteCartan.hasDynkinType_addLeaf_D {n : ℕ} {u : Fin n} {a b : ℤ}
    (h : (addLeaf (D n) u a b).IsFiniteCartan) (hab : IsBond a b) (hD : (D n).IsIndecomposable) :
    (addLeaf (D n) u a b).HasDynkinType := by
  obtain rfl | rfl | rfl | rfl | hn : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n := by lia
  -- `D₀` has no node to attach to
  · exact u.elim0
  -- `D₁ = A₁`
  · rw [D_one] at h ⊢
    exact h.hasDynkinType_addLeaf_A hab
  -- `D₂ = A₁ × A₁` is not indecomposable
  · simp only [D_two, reduceIsIndecomposable] at hD
  -- `D₃ ≅ A₃`
  · have h3 : D 3 = (A 3).submatrix c[1, 2] c[1, 2] := by decide
    rw [h3, addLeaf_submatrix] at h ⊢
    simp only [IsFiniteCartan.submatrix_equiv_iff, HasDynkinType.submatrix_iff] at h ⊢
    exact h.hasDynkinType_addLeaf_A hab
  obtain ⟨u, hu⟩ := u
  obtain hu1 | hu2 : u < 2 ∨ 2 ≤ u := by lia
  -- leaf at a short arm: by the symmetry swapping `0` and `1`, as for a leaf at `1`
  · have : n.AtLeastTwo := ⟨by lia⟩
    have h1 : ((1 : Fin n) : ℕ) = 1 := by rw [Fin.val_one', Nat.mod_eq_of_lt (by lia)]
    have hσ : (D n).submatrix (Equiv.swap 0 1) (Equiv.swap 0 1) = D n :=
      D_submatrix_swap n _ (Equiv.swap_apply_left _ _) (Equiv.swap_apply_right _ _)
        fun i hi ↦ Equiv.swap_apply_of_ne_of_ne (by rintro rfl; simp at hi)
          (by rintro rfl; rw [h1] at hi; lia)
    obtain rfl | rfl : u = 0 ∨ u = 1 := by lia
    · have h01 : (⟨0, hu⟩ : Fin n) = Equiv.swap 0 1 ⟨1, by lia⟩ := by
        rw [show (⟨1, by lia⟩ : Fin n) = 1 from Fin.ext h1.symm, Equiv.swap_apply_right]
        exact Fin.ext (by simp)
      rw [h01, isFiniteCartan_addLeaf_iff_of_submatrix_eq _ _ _ _ hσ] at h
      rw [h01, hasDynkinType_addLeaf_iff_of_submatrix_eq _ _ _ _ hσ]
      exact hasDynkinType_addLeaf_D_one hn rfl hab h
    · exact hasDynkinType_addLeaf_D_one hn rfl hab h
  obtain hmid | rfl : u + 2 ≤ n ∨ u = n - 1 := by lia
  -- leaf at `2 ≤ u ≤ n-2`: excluded
  · exact (not_isFiniteCartan_addLeaf_D_mid hu2 hmid hab.one_le_mul h).elim
  -- leaf at the long end `n-1`: `Dₙ₊₁` for a simple bond, excluded for a multiple bond
  · obtain ⟨rfl, rfl⟩ | hm := hab.eq_neg_one_or_two_le_mul
    · rw [addLeaf_D_last_eq (by lia)]
      exact hasDynkinType_D _
    · exact (not_isFiniteCartan_addLeaf_D_last hn hm h).elim

end Matrix
