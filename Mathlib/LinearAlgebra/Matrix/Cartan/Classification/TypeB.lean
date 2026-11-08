/-
Copyright (c) 2026 Ambrose Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ambrose Tang
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Classification.Leaf

import Mathlib.LinearAlgebra.Matrix.Cartan.Classification.TypeA
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# The classification step for types `Bₙ` and `Cₙ`

Attaching a leaf to `Bₙ` (the path `0 — ⋯ — (n-1)` with the double bond at the end `n - 1`)
gives, if the result is a finite Cartan matrix, a matrix of Dynkin type: `A₂`, `B₂`, `C₂` or `G₂`
for `n = 1`, and otherwise `Bₙ₊₁` (leaf at `0`), `C₃` or `F₄` (leaf at `n - 1`). The case of `Cₙ`
follows by transposition.

## Main results

* `Matrix.IsFiniteCartan.hasDynkinType_addLeaf_B`: attaching a leaf to `Bₙ` gives a matrix of
  Dynkin type whenever it gives a finite Cartan matrix.
* `Matrix.IsFiniteCartan.hasDynkinType_addLeaf_C`: the same for `Cₙ`.
-/

public section

open CartanMatrix

namespace Matrix

variable {n : ℕ} {u : Fin n} {a b : ℤ}

/-! ### Entries of `Bₙ` -/

/-- An entry of `Bₙ` just above the diagonal: `-2` in the last column, `-1` elsewhere. -/
private lemma B_apply_of_val_add_one_eq {i j : Fin n} (h : i.val + 1 = j.val) :
    B n i j = if j.val + 1 = n then -2 else -1 := by
  simp only [B, of_apply, Fin.ext_iff]
  split_ifs <;> lia

/-- An entry of `Bₙ` just below the diagonal is `-1`. -/
private lemma B_apply_of_val_eq_add_one {i j : Fin n} (h : i.val = j.val + 1) : B n i j = -1 := by
  simp only [B, of_apply, Fin.ext_iff]
  split_ifs <;> lia

/-- The bond between consecutive indices of `Bₙ`: double at the end `n - 1`, simple elsewhere. -/
private lemma B_mul_of_val_add_one_eq {i j : Fin n} (h : i.val + 1 = j.val) :
    B n i j * B n j i = if j.val + 1 = n then 2 else 1 := by
  rw [B_apply_of_val_add_one_eq h, B_apply_of_val_eq_add_one h.symm]
  split_ifs <;> rfl

/-! ### The leaf at `n - 1` -/

/-- A multiple bond at `u = n - 1`: with the double bond to `n - 2`, four bonds at `u`. -/
private lemma not_isFiniteCartan_addLeaf_B_last_of_two_le_mul (hn : 2 ≤ n) (hu : u.val + 1 = n)
    (hab : 2 ≤ a * b) : ¬ (addLeaf (B n) u a b).IsFiniteCartan := fun h ↦ by
  have := h.bonds_lt_four u.castSucc [(⟨n - 2, by lia⟩ : Fin n).castSucc, Fin.last n]
    (by simp [Fin.ext_iff]; lia)
  have hB := B_mul_of_val_add_one_eq (i := ⟨n - 2, by lia⟩) (j := u) (by simp; lia)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, addLeaf_castSucc_castSucc,
    addLeaf_castSucc_last, addLeaf_last_castSucc, ↓reduceIte, add_zero] at this
  rw [mul_comm (B n u _), hB] at this
  split_ifs at this
  lia

/-- A simple bond at `u = n - 1` for `n ≥ 4`: the indices `n - 4, …, n - 1` and the leaf form
the affine diagram `F₄⁽¹⁾`, which has a null vector. -/
private lemma not_isFiniteCartan_addLeaf_B_last_of_four_le (hn : 4 ≤ n) (hu : u.val + 1 = n) :
    ¬ (addLeaf (B n) u (-1) (-1)).IsFiniteCartan := fun h ↦ by
  let f : Fin 5 → Fin (n + 1) :=
    Fin.lastCases (Fin.last n) fun k : Fin 4 ↦ (⟨n - 4 + k, by lia⟩ : Fin n).castSucc
  have hf : Function.Injective f := by
    intro x y hxy
    induction x using Fin.lastCases <;> induction y using Fin.lastCases <;>
      simp only [f, Fin.lastCases_last, Fin.lastCases_castSucc] at hxy <;>
      simp [Fin.ext_iff] at hxy ⊢ <;> lia
  have hK : (addLeaf (B n) u (-1) (-1)).submatrix f f = addLeaf (B 4) 3 (-1) (-1) := by
    ext x y
    induction x using Fin.lastCases <;> induction y using Fin.lastCases <;>
      simp only [submatrix_apply, f, Fin.lastCases_last, Fin.lastCases_castSucc,
        addLeaf_castSucc_castSucc, addLeaf_castSucc_last, addLeaf_last_castSucc,
        addLeaf_last_last] <;>
      simp [B, Fin.ext_iff] <;> split_ifs <;> lia
  refine h.mulVec_ne_zero hf (x := ![1, 2, 3, 2, 1]) (by decide) ?_
  rw [hK]; decide

/-- The leaf at `u = n - 1` attached by a simple bond. -/
private lemma hasDynkinType_addLeaf_B_last (hn : 2 ≤ n) (hu : u.val + 1 = n)
    (h : (addLeaf (B n) u (-1) (-1)).IsFiniteCartan) :
    (addLeaf (B n) u (-1) (-1)).HasDynkinType := by
  obtain rfl | rfl | hn4 : n = 2 ∨ n = 3 ∨ 4 ≤ n := by lia
  -- `n = 2`: `C₃`, relabelled by `0 ↦ 2, 1 ↦ 1, last ↦ 0`
  · obtain rfl : u = 1 := Fin.ext (by simp; lia)
    exact .of_eq_submatrix Fin.revPerm (by decide) (hasDynkinType_C 3)
  -- `n = 3`: `F₄`
  · obtain rfl : u = 2 := Fin.ext (by simp; lia)
    exact .of_eq_submatrix (.refl _) (by decide) hasDynkinType_F₄
  -- `n ≥ 4`: the indices `n - 4, …, n - 1` and the leaf form affine `F₄`
  · exact (not_isFiniteCartan_addLeaf_B_last_of_four_le hn4 hu h).elim

/-! ### The leaf at `0` or at an interior index -/

/-- For `u ≤ n - 2`, the path `u, …, n - 2` together with the leaf and the indices `u - 1` (if
`0 < u`) and `n - 1` leaving it. The bond to `n - 1` is double. -/
private lemma path_bonds_lt_four_addLeaf_B (hu : u.val + 2 ≤ n)
    (h : (addLeaf (B n) u a b).IsFiniteCartan) :
    a * b + 2 + (if u.val = 0 then 0 else 1) < 4 := by
  let f : Fin (n - 2 - u + 1) → Fin (n + 1) := fun t ↦ (⟨u + t, by lia⟩ : Fin n).castSucc
  have hf : Function.Injective f := fun s t hst ↦ by simpa [f, Fin.ext_iff] using hst
  have hadj (t : Fin (n - 2 - u)) : addLeaf (B n) u a b (f t.castSucc) (f t.succ) ≠ 0 := by
    simp only [f, addLeaf_castSucc_castSucc]
    rw [B_apply_of_val_add_one_eq (by simp; lia)]
    split_ifs <;> decide
  -- the leaf at the start `u` of the path
  have hleaf : addLeaf (B n) u a b (f 0) (Fin.last n) * addLeaf (B n) u a b (Fin.last n) (f 0) =
      a * b := by
    simp [f, -Fin.castSucc_mk]
  -- the double bond from the end `n - 2` of the path to `n - 1`
  have hend : addLeaf (B n) u a b (f (Fin.last _)) (⟨n - 1, by lia⟩ : Fin n).castSucc *
      addLeaf (B n) u a b (⟨n - 1, by lia⟩ : Fin n).castSucc (f (Fin.last _)) = 2 := by
    simp only [f, addLeaf_castSucc_castSucc]
    rw [B_mul_of_val_add_one_eq (by simp; lia)]
    simp; lia
  have hoff (j : Fin n) (hj : j.val < u ∨ n ≤ j.val + 1) : j.castSucc ∉ Set.range f := by
    rintro ⟨t, ht⟩
    simp [f, Fin.ext_iff] at ht
    lia
  have hlast : Fin.last n ∉ Set.range f := fun ⟨t, ht⟩ ↦ Fin.castSucc_ne_last _ ht
  by_cases hu0 : u.val = 0
  -- `u = 0`: the leaf and `n - 1` leave the path
  · have := h.path_bonds_lt_four f hf hadj
      [(0, Fin.last n), (Fin.last _, (⟨n - 1, by lia⟩ : Fin n).castSucc)]
      (by simp [-Fin.castSucc_mk, (Fin.castSucc_ne_last _).symm])
      (by
        simp only [List.forall_mem_cons]
        exact ⟨hlast, hoff _ (by simp; lia), nofun⟩)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hleaf, hend] at this
    simp [hu0]
    lia
  -- `0 < u`: the leaf, `u - 1` and `n - 1` leave the path
  · have hprev : addLeaf (B n) u a b (f 0) (⟨u - 1, by lia⟩ : Fin n).castSucc *
        addLeaf (B n) u a b (⟨u - 1, by lia⟩ : Fin n).castSucc (f 0) = 1 := by
      simp only [f, addLeaf_castSucc_castSucc]
      rw [mul_comm, B_mul_of_val_add_one_eq (by simp; lia)]
      simp; lia
    have := h.path_bonds_lt_four f hf hadj
      [(0, (⟨u - 1, by lia⟩ : Fin n).castSucc), (0, Fin.last n),
        (Fin.last _, (⟨n - 1, by lia⟩ : Fin n).castSucc)]
      (by simp [-Fin.castSucc_mk, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]; lia)
      (by
        simp only [List.forall_mem_cons]
        exact ⟨hoff _ (by simp; lia), hlast, hoff _ (by simp; lia), nofun⟩)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hleaf, hend,
      hprev] at this
    simp [hu0]
    lia

/-- A multiple bond at `u = 0`: the path `0, …, n - 2` has the leaf and the double bond to
`n - 1` leaving it. -/
private lemma not_isFiniteCartan_addLeaf_B_zero_of_two_le_mul (hn : 2 ≤ n) (hu : u.val = 0)
    (hab : 2 ≤ a * b) : ¬ (addLeaf (B n) u a b).IsFiniteCartan := fun h ↦ by
  have := path_bonds_lt_four_addLeaf_B (by lia) h
  simp [hu] at this
  lia

/-- A simple bond at `u = 0` gives `Bₙ₊₁`, relabelled by `last ↦ 0, k ↦ k + 1`. -/
private lemma addLeaf_B_zero_eq (hn : 2 ≤ n) (hu : u.val = 0) :
    addLeaf (B n) u (-1) (-1) = (B (n + 1)).submatrix (finRotate (n + 1)) (finRotate (n + 1)) := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [B, Fin.ext_iff] <;> split_ifs <;> lia

/-- For `0 < u ≤ n - 2`, the path `u, …, n - 2` has the leaf, `u - 1` and the double bond to
`n - 1` leaving it. -/
private lemma not_isFiniteCartan_addLeaf_B_interior (hu0 : 0 < u.val) (hu : u.val + 2 ≤ n)
    (hab : IsBond a b) : ¬ (addLeaf (B n) u a b).IsFiniteCartan := fun h ↦ by
  have hp := path_bonds_lt_four_addLeaf_B hu h
  have := hab.one_le_mul
  split_ifs at hp <;> lia

/-! ### The induction step -/

/-- Attaching a leaf to `Bₙ` gives a matrix of Dynkin type whenever it gives a finite Cartan
matrix. -/
theorem IsFiniteCartan.hasDynkinType_addLeaf_B (h : (addLeaf (B n) u a b).IsFiniteCartan)
    (hab : IsBond a b) : (addLeaf (B n) u a b).HasDynkinType := by
  -- a single index: `B₁ = A₁`
  obtain hn | hn := Nat.lt_or_ge n 2
  · obtain rfl : n = 1 := by have := u.pos; lia
    rw [B_one] at h ⊢
    exact h.hasDynkinType_addLeaf_A hab
  obtain hul | hu0 | hu : u.val + 1 = n ∨ u.val = 0 ∨ (0 < u.val ∧ u.val + 2 ≤ n) := by lia
  -- leaf at the double-bond end `n - 1`: two bonds at `u` force a simple bond
  · obtain ⟨rfl, rfl⟩ | hm := hab.eq_neg_one_or_two_le_mul
    · exact hasDynkinType_addLeaf_B_last hn hul h
    · exact (not_isFiniteCartan_addLeaf_B_last_of_two_le_mul hn hul hm h).elim
  -- leaf at the far end `0`: the path `0, …, n - 2` forces a simple bond, giving `Bₙ₊₁`
  · obtain ⟨rfl, rfl⟩ | hm := hab.eq_neg_one_or_two_le_mul
    · exact .of_eq_submatrix (finRotate (n + 1)) (addLeaf_B_zero_eq hn hu0) (hasDynkinType_B _)
    · exact (not_isFiniteCartan_addLeaf_B_zero_of_two_le_mul hn hu0 hm h).elim
  -- leaf at an interior index: four bonds leave the path from `u` to `n - 2`
  · exact (not_isFiniteCartan_addLeaf_B_interior hu.1 hu.2 hab h).elim

/-- Attaching a leaf to `Cₙ` gives a matrix of Dynkin type whenever it gives a finite Cartan
matrix. This follows from the case of `Bₙ` by transposition. -/
theorem IsFiniteCartan.hasDynkinType_addLeaf_C (h : (addLeaf (C n) u a b).IsFiniteCartan)
    (hab : IsBond a b) : (addLeaf (C n) u a b).HasDynkinType := by
  rw [← B_transpose, ← addLeaf_transpose] at h ⊢
  rw [IsFiniteCartan.transpose_iff] at h
  exact (h.hasDynkinType_addLeaf_B hab.swap).transpose

end Matrix
