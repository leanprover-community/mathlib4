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

In `Dₙ` (`n ≥ 4`) the nodes `0, …, n-3` form a path and `n-3` is joined to `n-2` and `n-1`.

## Main results

* `Matrix.IsFiniteCartan.hasDynkinType_addLeaf_D`: attaching a leaf to an indecomposable `Dₙ`
  gives a matrix of Dynkin type whenever it gives a finite Cartan matrix.
-/

public section

open CartanMatrix

namespace Matrix

/-! ### The leaf at `0` or at an interior node -/

/-- Leaf at `0`, simple bond: `Dₙ₊₁`, relabelled by `last ↦ 0, k ↦ k + 1`. -/
private lemma addLeaf_D_zero_eq {n : ℕ} (hn : 4 ≤ n) :
    addLeaf (D n) ⟨0, by lia⟩ (-1) (-1) = (D (n + 1)).submatrix (finRotate _) (finRotate _) := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [-Fin.castSucc_mk, D, Fin.ext_iff] <;> split_ifs <;> lia

/-- Leaf at `0`, multiple bond: the path `0, …, n-3` has bonds to the leaf, `n-2` and `n-1`. -/
private lemma not_isFiniteCartan_addLeaf_D_zero {n : ℕ} (hn : 4 ≤ n) {a b : ℤ}
    (hm : 2 ≤ a * b) : ¬ (addLeaf (D n) ⟨0, by lia⟩ a b).IsFiniteCartan := fun h ↦ by
  have := h.path_bonds_lt_four (k := n - 3) (fun t ↦ (⟨t, by lia⟩ : Fin n).castSucc)
    (fun x y hxy ↦ by simpa [Fin.ext_iff] using hxy)
    (fun i ↦ by
      simp (disch := lia) only [addLeaf_castSucc_castSucc, D, of_apply, Fin.ext_iff,
        Fin.val_castSucc, Fin.val_succ, true_and, ite_eq_right]
      lia)
    [(0, Fin.last n), (Fin.last _, (⟨n - 2, by lia⟩ : Fin n).castSucc),
      (Fin.last _, (⟨n - 1, by lia⟩ : Fin n).castSucc)]
    (by simp [Fin.ext_iff]; lia) (by simp [Fin.ext_iff]; grind)
  simp (disch := lia) only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    addLeaf_castSucc_castSucc, addLeaf_castSucc_last, addLeaf_last_castSucc, D, of_apply,
    Fin.ext_iff, Fin.val_last, Fin.val_zero, ite_eq_left, ite_eq_right] at this
  lia

/-- Leaf at `0 < u ≤ n-3`: the path `u, …, n-3` has bonds to `u-1`, the leaf, `n-2` and `n-1`. -/
private lemma not_isFiniteCartan_addLeaf_D_mid {n u : ℕ} (hu0 : 0 < u) (hu : u + 3 ≤ n)
    {a b : ℤ} (hm : 1 ≤ a * b) : ¬ (addLeaf (D n) ⟨u, by lia⟩ a b).IsFiniteCartan := fun h ↦ by
  have := h.path_bonds_lt_four (k := n - 3 - u) (fun t ↦ (⟨u + t, by lia⟩ : Fin n).castSucc)
    (fun x y hxy ↦ by simpa [Fin.ext_iff] using hxy)
    (fun i ↦ by
      simp (disch := lia) only [addLeaf_castSucc_castSucc, D, of_apply, Fin.ext_iff,
        Fin.val_castSucc, Fin.val_succ, ite_eq_right]
      lia)
    [(0, (⟨u - 1, by lia⟩ : Fin n).castSucc), (0, Fin.last n),
      (Fin.last _, (⟨n - 2, by lia⟩ : Fin n).castSucc),
      (Fin.last _, (⟨n - 1, by lia⟩ : Fin n).castSucc)]
    (by simp [Fin.ext_iff]; lia) (by simp [Fin.ext_iff]; grind)
  simp (disch := lia) only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    addLeaf_castSucc_castSucc, addLeaf_castSucc_last, addLeaf_last_castSucc, D, of_apply,
    Fin.ext_iff, Fin.val_last, Fin.val_zero, add_zero, ite_eq_left, ite_eq_right] at this
  lia

/-! ### The leaf at a short arm -/

/-- Leaf at `n-1`, multiple bond: the path `n-3, n-1` has bonds to `n-4`, `n-2` and the leaf. -/
private lemma not_isFiniteCartan_addLeaf_D_last_multiple {n : ℕ} (hn : 4 ≤ n) {a b : ℤ}
    (hm : 2 ≤ a * b) : ¬ (addLeaf (D n) ⟨n - 1, by lia⟩ a b).IsFiniteCartan := fun h ↦ by
  have := h.path_bonds_lt_four
    ![(⟨n - 3, by lia⟩ : Fin n).castSucc, (⟨n - 1, by lia⟩ : Fin n).castSucc]
    (fun x y hxy ↦ by fin_cases x <;> fin_cases y <;> simp_all [Fin.ext_iff] <;> lia)
    (fun i ↦ by fin_cases i; simp [-Fin.castSucc_mk, D, Fin.ext_iff]; lia)
    [(0, (⟨n - 4, by lia⟩ : Fin n).castSucc), (0, (⟨n - 2, by lia⟩ : Fin n).castSucc),
      (1, Fin.last n)]
    (by simp [Fin.ext_iff]; lia) (by simp [Fin.ext_iff]; lia)
  simp (disch := lia) only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    addLeaf_castSucc_castSucc, addLeaf_castSucc_last, addLeaf_last_castSucc, D, of_apply,
    cons_val_zero, cons_val_one, Fin.ext_iff, ite_eq_left, ite_eq_right] at this
  lia

/-- The nodes `n-8, …, n-1` of `Dₙ` together with a leaf at `n-1` form `D₈` with a leaf at
`7`. -/
private lemma addLeaf_D_last_submatrix_eq {n : ℕ} (hn : 8 ≤ n) (a b : ℤ) :
    (addLeaf (D n) ⟨n - 1, by lia⟩ a b).submatrix
      (Fin.lastCases (Fin.last n) fun i : Fin 8 ↦ (⟨i + (n - 8), by lia⟩ : Fin n).castSucc)
      (Fin.lastCases (Fin.last n) fun i : Fin 8 ↦ (⟨i + (n - 8), by lia⟩ : Fin n).castSucc) =
      addLeaf (D 8) 7 a b := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp only [submatrix_apply, Fin.lastCases_last, Fin.lastCases_castSucc, addLeaf_last_last,
      addLeaf_castSucc_castSucc, addLeaf_castSucc_last, addLeaf_last_castSucc] <;>
    simp [D, Fin.ext_iff] <;> split_ifs <;> lia

/-- Leaf at `n-1`, simple bond, `n ≥ 8`: the centre `n-3` with arms `n-2`; `n-1, leaf`;
`n-4, …, n-8` is affine `E₈`. -/
private lemma not_isFiniteCartan_addLeaf_D_last_simple {n : ℕ} (hn : 8 ≤ n) :
    ¬ (addLeaf (D n) ⟨n - 1, by lia⟩ (-1) (-1)).IsFiniteCartan := fun h ↦ by
  have hg : Function.Injective
      (Fin.lastCases (Fin.last n) fun i : Fin 8 ↦ (⟨i + (n - 8), by lia⟩ : Fin n).castSucc) := by
    intro i j hij
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hij <;>
      simp [Fin.ext_iff] at hij ⊢ <;> lia
  have h8 := h.submatrix hg
  rw [addLeaf_D_last_submatrix_eq hn] at h8
  exact h8.mulVec_ne_zero (f := ![5, 4, 3, 2, 1, 0, 7, 8, 6]) (by decide)
    (x := ![6, 5, 4, 3, 2, 1, 4, 2, 3]) (by decide) (by decide)

/-- Leaf at `n-1`: a multiple bond is excluded; a simple bond gives `D₅`, `E₆`, `E₇`, `E₈` for
`n = 4, 5, 6, 7` and contains affine `E₈` for `n ≥ 8`. -/
private lemma hasDynkinType_addLeaf_D_last {n : ℕ} (hn : 4 ≤ n) {u : Fin n} (hu : (u : ℕ) + 1 = n)
    {a b : ℤ} (hab : IsBond a b) (h : (addLeaf (D n) u a b).IsFiniteCartan) :
    (addLeaf (D n) u a b).HasDynkinType := by
  obtain ⟨rfl, rfl⟩ | hm := hab.eq_neg_one_or_two_le_mul
  swap
  · rw [show u = ⟨n - 1, by lia⟩ from Fin.ext (by simp; lia)] at h ⊢
    exact (not_isFiniteCartan_addLeaf_D_last_multiple hn hm h).elim
  obtain rfl | rfl | rfl | rfl | hn8 : n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ 8 ≤ n := by lia
  -- arms `(1, 1, 2)` from the centre: `D₅`
  · obtain rfl : u = 3 := Fin.ext (by simp; lia)
    exact .of_eq_submatrix (.ofBijective ![3, 2, 4, 1, 0] (by decide)) (by decide)
      (hasDynkinType_D 5)
  -- arms `(1, 2, 2)`, `(1, 2, 3)`, `(1, 2, 4)`: `E₆`, `E₇`, `E₈`
  · obtain rfl : u = 4 := Fin.ext (by simp; lia)
    exact .of_eq_submatrix (.ofBijective ![5, 4, 3, 1, 2, 0] (by decide)) (by decide)
      hasDynkinType_E_six
  · obtain rfl : u = 5 := Fin.ext (by simp; lia)
    exact .of_eq_submatrix (.ofBijective ![6, 5, 4, 3, 1, 2, 0] (by decide)) (by decide)
      hasDynkinType_E_seven
  · obtain rfl : u = 6 := Fin.ext (by simp; lia)
    exact .of_eq_submatrix (.ofBijective ![7, 6, 5, 4, 3, 1, 2, 0] (by decide)) (by decide)
      hasDynkinType_E_eight
  -- arms `(1, 2, ≥ 5)` contain affine `E₈`
  · rw [show u = ⟨n - 1, by lia⟩ from Fin.ext (by simp; lia)] at h ⊢
    exact (not_isFiniteCartan_addLeaf_D_last_simple hn8 h).elim

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
  · have h3 : D 3 = (A 3).submatrix c[0, 1] c[0, 1] := by
      rw [← D_three']; ext; simp
    rw [h3, addLeaf_submatrix] at h ⊢
    simp only [IsFiniteCartan.submatrix_equiv_iff, HasDynkinType.submatrix_iff] at h ⊢
    exact h.hasDynkinType_addLeaf_A hab
  obtain ⟨u, hu⟩ := u
  obtain rfl | hu0 := Nat.eq_zero_or_pos u
  · obtain ⟨rfl, rfl⟩ | hm := hab.eq_neg_one_or_two_le_mul
    -- leaf at `0`, simple bond: `Dₙ₊₁`
    · exact .of_eq_submatrix _ (addLeaf_D_zero_eq hn) (hasDynkinType_D _)
    -- leaf at `0`, multiple bond: excluded
    · exact (not_isFiniteCartan_addLeaf_D_zero hn hm h).elim
  obtain hu3 | rfl | rfl : u + 3 ≤ n ∨ u = n - 2 ∨ u = n - 1 := by lia
  -- leaf at an interior node `0 < u ≤ n-3`: excluded
  · exact (not_isFiniteCartan_addLeaf_D_mid hu0 hu3 hab.one_le_mul h).elim
  -- leaf at `n-2`: by the symmetry swapping `n-2` and `n-1`, as for a leaf at `n-1`
  · have hσ := D_submatrix_swap (n := n) (by lia)
    rw [← Equiv.swap_apply_right (⟨n - 2, hu⟩ : Fin n) ⟨n - 1, by lia⟩] at h ⊢
    rw [isFiniteCartan_addLeaf_iff_of_submatrix_eq _ _ _ _ hσ] at h
    rw [hasDynkinType_addLeaf_iff_of_submatrix_eq _ _ _ _ hσ]
    exact hasDynkinType_addLeaf_D_last hn (by simp; lia) hab h
  -- leaf at `n-1`
  · exact hasDynkinType_addLeaf_D_last hn (by simp; lia) hab h

end Matrix
