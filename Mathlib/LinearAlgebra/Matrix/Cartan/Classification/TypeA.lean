/-
Copyright (c) 2026 Ambrose Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ambrose Tang
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Classification.Leaf

/-!
# The classification step for type `Aₙ`

Attaching a leaf to the path `Aₙ` gives, if the result is a finite Cartan matrix, a matrix of
Dynkin type: `Aₙ₊₁, Bₙ₊₁, Cₙ₊₁, Dₙ₊₁, E₆, E₇, E₈` or `G₂`.

Every configuration at a symbolic position of the path is reduced, by restricting to a window of
consecutive indices around the attachment point, to a leaf on a path of fixed length, where the
remaining computations are done by `decide`.

## Main results

* `Matrix.IsFiniteCartan.hasDynkinType_addLeaf_A`: attaching a leaf to `Aₙ` gives a matrix of
  Dynkin type whenever it gives a finite Cartan matrix.
-/

public section

open CartanMatrix

namespace Matrix

variable {n : ℕ}

/-! ### Restricting to a window of the path -/

/-- If a leaf is attached at `u` to `Aₙ`, the indices `s, …, s + m - 1` of the path together with
the leaf form the leaf attached at `u - s` to `Aₘ`. -/
private lemma isFiniteCartan_addLeaf_A_window {u : Fin n} {a b : ℤ} {m : ℕ} (s : ℕ) (k : Fin m)
    (hs : s + m ≤ n) (hk : s + k.val = u.val) (h : (addLeaf (A n) u a b).IsFiniteCartan) :
    (addLeaf (A m) k a b).IsFiniteCartan := by
  let g : Fin (m + 1) → Fin (n + 1) :=
    Fin.lastCases (Fin.last n) fun i ↦ (⟨s + i, by lia⟩ : Fin n).castSucc
  have hg : Function.Injective g := by
    intro i j hij
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp_all [g, Fin.ext_iff] <;> lia
  convert h.submatrix hg using 1
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [g, -Fin.castSucc_mk, A, Fin.ext_iff] <;> lia

/-! ### The leaf at an end of the path -/

/-- A single bond at the end of the path gives `Aₙ₊₁`. -/
private lemma addLeaf_A_end_eq_A (u : Fin n) (hu : u.val + 1 = n) :
    addLeaf (A n) u (-1) (-1) = A (n + 1) := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [A, Fin.ext_iff] <;> lia

/-- A double bond at the end of the path, pointing to the path, gives `Bₙ₊₁`. -/
private lemma addLeaf_A_end_eq_B (u : Fin n) (hu : u.val + 1 = n) :
    addLeaf (A n) u (-2) (-1) = B (n + 1) := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [A, B, Fin.ext_iff] <;> lia

/-- A double bond at the end of the path, pointing to the leaf, gives `Cₙ₊₁`. -/
private lemma addLeaf_A_end_eq_C (u : Fin n) (hu : u.val + 1 = n) :
    addLeaf (A n) u (-1) (-2) = C (n + 1) := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [A, C, Fin.ext_iff] <;> lia

/-- A triple bond at the end of a path of length at least two: four bonds at `u`. -/
private lemma not_isFiniteCartan_addLeaf_A_end_triple {u : Fin n} {a b : ℤ} (hu : u.val + 1 = n)
    (hn : 2 ≤ n) (hab : a * b = 3) : ¬ (addLeaf (A n) u a b).IsFiniteCartan := fun h ↦ by
  have := (isFiniteCartan_addLeaf_A_window (u.val - 1) 1 (by lia) (by simp; lia)
    h).bonds_lt_four (1 : Fin 2).castSucc [(0 : Fin 2).castSucc, Fin.last 2] (by decide)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, addLeaf_castSucc_castSucc,
    addLeaf_castSucc_last, addLeaf_last_castSucc] at this
  simp [A] at this
  lia

/-- A leaf at an end of the path: `Aₙ₊₁`, `Bₙ₊₁`, `Cₙ₊₁` or `G₂`. -/
private lemma hasDynkinType_addLeaf_A_end {u : Fin n} {a b : ℤ} (hu : u.val + 1 = n)
    (hab : IsBond a b) (h : (addLeaf (A n) u a b).IsFiniteCartan) :
    (addLeaf (A n) u a b).HasDynkinType := by
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  -- single bond: `Aₙ₊₁`
  · rw [addLeaf_A_end_eq_A u hu]; exact hasDynkinType_A _
  -- double bond pointing to the leaf: `Cₙ₊₁`
  · rw [addLeaf_A_end_eq_C u hu]; exact hasDynkinType_C _
  -- double bond pointing to the path: `Bₙ₊₁`
  · rw [addLeaf_A_end_eq_B u hu]; exact hasDynkinType_B _
  -- triple bond on two nodes: `G₂` after swapping them; on more nodes: four bonds at `u`
  · obtain hn | hn : n = 1 ∨ 2 ≤ n := by lia
    · subst hn
      obtain rfl : u = 0 := Subsingleton.elim _ _
      have : addLeaf (A 1) 0 (-1) (-3) = G₂.submatrix (Equiv.swap 0 1) (Equiv.swap 0 1) := by
        decide
      rw [this, HasDynkinType.submatrix_iff]; exact hasDynkinType_G₂
    · exact absurd h (not_isFiniteCartan_addLeaf_A_end_triple hu hn (by norm_num))
  -- triple bond on two nodes: `G₂`; on more nodes: four bonds at `u`
  · obtain hn | hn : n = 1 ∨ 2 ≤ n := by lia
    · subst hn
      obtain rfl : u = 0 := Subsingleton.elim _ _
      rw [show addLeaf (A 1) 0 (-3) (-1) = G₂ by decide]; exact hasDynkinType_G₂
    · exact absurd h (not_isFiniteCartan_addLeaf_A_end_triple hu hn (by norm_num))

/-! ### The leaf at an interior node -/

/-- An interior node with a multiple bond to the leaf: four bonds at `u`. -/
private lemma not_isFiniteCartan_addLeaf_A_interior_multiple {u : Fin n} {a b : ℤ}
    (hu0 : 0 < u.val) (hu1 : u.val + 1 < n) (hab : 2 ≤ a * b) :
    ¬ (addLeaf (A n) u a b).IsFiniteCartan := fun h ↦ by
  have := (isFiniteCartan_addLeaf_A_window (u.val - 1) 1 (by lia) (by simp; lia)
    h).bonds_lt_four (1 : Fin 3).castSucc
      [(0 : Fin 3).castSucc, (2 : Fin 3).castSucc, Fin.last 3] (by decide)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, addLeaf_castSucc_castSucc,
    addLeaf_castSucc_last, addLeaf_last_castSucc] at this
  simp [A] at this
  lia

/-- Arms `(1, 1, p)`: `Dₙ₊₁`. -/
private lemma addLeaf_A_penultimate_eq_D (u : Fin n) (hu0 : 0 < u.val) (hu : u.val + 2 = n) :
    addLeaf (A n) u (-1) (-1) = D (n + 1) := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [A, D, Fin.ext_iff] <;> lia

/-- Arms `(1, 2, 2)`: `E₆`. -/
private lemma addLeaf_A_five_eq : addLeaf (A 5) 2 (-1) (-1) =
    (E 6).submatrix (Equiv.ofBijective ![5, 4, 3, 2, 0, 1] (by decide))
      (Equiv.ofBijective ![5, 4, 3, 2, 0, 1] (by decide)) := by
  decide

/-- Arms `(1, 2, 3)`: `E₇`. -/
private lemma addLeaf_A_six_eq : addLeaf (A 6) 3 (-1) (-1) =
    (E 7).submatrix (Equiv.ofBijective ![6, 5, 4, 3, 2, 0, 1] (by decide))
      (Equiv.ofBijective ![6, 5, 4, 3, 2, 0, 1] (by decide)) := by
  decide

/-- Arms `(1, 2, 4)`: `E₈`. -/
private lemma addLeaf_A_seven_eq : addLeaf (A 7) 4 (-1) (-1) =
    (E 8).submatrix (Equiv.ofBijective ![7, 6, 5, 4, 3, 2, 0, 1] (by decide))
      (Equiv.ofBijective ![7, 6, 5, 4, 3, 2, 0, 1] (by decide)) := by
  decide

/-- Arms `(1, 2, p)` with `2 ≤ p ≤ 4`: `E₆, E₇, E₈`. -/
private lemma hasDynkinType_addLeaf_A_E (u : Fin n) (hu : u.val + 3 = n) (h2 : 2 ≤ u.val)
    (h4 : u.val ≤ 4) : (addLeaf (A n) u (-1) (-1)).HasDynkinType := by
  obtain ⟨k, hk⟩ := u
  simp only at hu h2 h4
  subst hu
  interval_cases k
  · change (addLeaf (A 5) 2 (-1) (-1)).HasDynkinType
    rw [addLeaf_A_five_eq, HasDynkinType.submatrix_iff]; exact hasDynkinType_E_six
  · change (addLeaf (A 6) 3 (-1) (-1)).HasDynkinType
    rw [addLeaf_A_six_eq, HasDynkinType.submatrix_iff]; exact hasDynkinType_E_seven
  · change (addLeaf (A 7) 4 (-1) (-1)).HasDynkinType
    rw [addLeaf_A_seven_eq, HasDynkinType.submatrix_iff]; exact hasDynkinType_E_eight

/-- Arms `(1, 2, p)` with `p ≥ 5` contain affine `E₈`, which has a null vector. -/
private lemma not_isFiniteCartan_addLeaf_A_affine_E8 {u : Fin n} (hu0 : 5 ≤ u.val)
    (hu1 : u.val + 2 < n) : ¬ (addLeaf (A n) u (-1) (-1)).IsFiniteCartan := fun h ↦ by
  refine (isFiniteCartan_addLeaf_A_window (u.val - 5) (5 : Fin 8) (by lia) (by simp; lia)
    h).mulVec_ne_zero Function.injective_id (x := ![1, 2, 3, 4, 5, 6, 4, 2, 3]) (by decide) ?_
  decide

/-- Arms `(1, q, p)` with `3 ≤ q, p` contain affine `E₇`, which has a null vector. -/
private lemma not_isFiniteCartan_addLeaf_A_affine_E7 {u : Fin n} (hu0 : 3 ≤ u.val)
    (hu1 : u.val + 3 < n) : ¬ (addLeaf (A n) u (-1) (-1)).IsFiniteCartan := fun h ↦ by
  refine (isFiniteCartan_addLeaf_A_window (u.val - 3) (3 : Fin 7) (by lia) (by simp; lia)
    h).mulVec_ne_zero Function.injective_id (x := ![1, 2, 3, 4, 3, 2, 1, 2]) (by decide) ?_
  decide

/-! ### The induction step -/

/-- Attaching a leaf to `Aₙ` gives a matrix of Dynkin type whenever it gives a finite Cartan
matrix. -/
theorem IsFiniteCartan.hasDynkinType_addLeaf_A {u : Fin n} {a b : ℤ}
    (h : (addLeaf (A n) u a b).IsFiniteCartan) (hab : IsBond a b) :
    (addLeaf (A n) u a b).HasDynkinType := by
  -- by symmetry, the arm `n - 1 - u` beyond `u` is at most the arm `u` before it
  wlog hu : n ≤ 2 * u.val + 1 generalizing u with H
  · have hrev := A_submatrix_revPerm n
    rw [← isFiniteCartan_addLeaf_iff_of_submatrix_eq _ u a b hrev] at h
    rw [← hasDynkinType_addLeaf_iff_of_submatrix_eq _ u a b hrev]
    exact H (by simpa using h) (by simp; lia)
  -- `u` is the end of the path
  obtain hend | hint : u.val + 1 = n ∨ u.val + 1 < n := by lia
  · exact hasDynkinType_addLeaf_A_end hend hab h
  obtain ⟨rfl, rfl⟩ | hm := hab.eq_neg_one_or_two_le_mul
  swap
  -- `u` is interior with a multiple bond to the leaf: four bonds at `u`
  · exact absurd h (not_isFiniteCartan_addLeaf_A_interior_multiple (by lia) hint hm)
  -- arms `(1, 1, p)`: `Dₙ₊₁`
  obtain h1 | h2 | h3 : u.val + 2 = n ∨ u.val + 3 = n ∨ u.val + 3 < n := by lia
  · rw [addLeaf_A_penultimate_eq_D u (by lia) h1]; exact hasDynkinType_D _
  -- arms `(1, 2, p)`: `E₆, E₇, E₈` for `p ≤ 4`, contains affine `E₈` for `p ≥ 5`
  · obtain h4 | h5 : u.val < 5 ∨ 5 ≤ u.val := by lia
    · exact hasDynkinType_addLeaf_A_E u h2 (by lia) (by lia)
    · exact absurd h (not_isFiniteCartan_addLeaf_A_affine_E8 h5 (by lia))
  -- arms `(1, q, p)` with `3 ≤ q ≤ p`: contains affine `E₇`
  · exact absurd h (not_isFiniteCartan_addLeaf_A_affine_E7 (by lia) h3)

end Matrix
