/-
Copyright (c) 2026 Ambrose Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ambrose Tang
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Classification.Leaf

/-!
# The classification step for type `Eₙ`

If attaching a leaf to `E₆`, `E₇` or `E₈` gives a finite Cartan matrix, the result has Dynkin
type: it is `E₇` or `E₈`.

In `E n` the node `3` is the center, with arms `1`, `2 — 0` and `4 — 5 — ⋯ — (n - 1)`.

## Main results

* `Matrix.IsFiniteCartan.hasDynkinType_addLeaf_E`: attaching a leaf to `Eₙ` (`n = 6, 7, 8`) gives
  a matrix of Dynkin type whenever it gives a finite Cartan matrix.
-/

public section

open CartanMatrix

namespace Matrix

/-! ### Multiple bonds and nodes of degree three -/

/-- `u = 3`, the center: four bonds at the center. -/
private lemma not_isFiniteCartan_addLeaf_E_three {n : ℕ} {u : Fin n} {a b : ℤ} (hn : 6 ≤ n)
    (hu : u.val = 3) (hab : IsBond a b) : ¬ (addLeaf (E n) u a b).IsFiniteCartan := fun h ↦ by
  have := h.bonds_lt_four u.castSucc [Fin.castSucc ⟨1, by lia⟩, Fin.castSucc ⟨2, by lia⟩,
    Fin.castSucc ⟨4, by lia⟩, Fin.last n] (by simp [Fin.ext_iff, List.nodup_cons]; lia)
  simp [-Fin.castSucc_mk, E, Fin.ext_iff, hu] at this
  linarith [hab.one_le_mul]

/-- `u = 2`: the path `2, 3` has four outgoing bonds (to `0`, the leaf, `1` and `4`). -/
private lemma not_isFiniteCartan_addLeaf_E_two {n : ℕ} {u : Fin n} {a b : ℤ} (hn : 6 ≤ n)
    (hu : u.val = 2) (hab : IsBond a b) : ¬ (addLeaf (E n) u a b).IsFiniteCartan := fun h ↦ by
  have := h.path_bonds_lt_four ![Fin.castSucc ⟨2, by lia⟩, Fin.castSucc ⟨3, by lia⟩]
    (fun i j hij ↦ by fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff])
    (by simp [-Fin.castSucc_mk, E])
    [(0, Fin.castSucc ⟨0, by lia⟩), (0, Fin.last n), (1, Fin.castSucc ⟨1, by lia⟩),
      (1, Fin.castSucc ⟨4, by lia⟩)]
    (by simp [Fin.ext_iff, List.nodup_cons]; lia)
    (by rintro ⟨t, _⟩ hp ⟨i, rfl⟩; fin_cases i <;> simp [-Fin.castSucc_mk] at hp)
  simp [-Fin.castSucc_mk, E, Fin.ext_iff, hu] at this
  linarith [hab.one_le_mul]

/-- `4 ≤ u ≤ n - 2`: the path `3, …, u` has four outgoing bonds (to `1`, `2`, `u + 1` and the
leaf). -/
private lemma not_isFiniteCartan_addLeaf_E_long_arm {n : ℕ} {u : Fin n} {a b : ℤ}
    (hu₁ : 4 ≤ u.val) (hu₂ : u.val + 2 ≤ n) (hab : IsBond a b) :
    ¬ (addLeaf (E n) u a b).IsFiniteCartan := fun h ↦ by
  have := h.path_bonds_lt_four (k := u - 3) (fun t ↦ Fin.castSucc ⟨3 + t, by lia⟩)
    (fun s t hst ↦ by simpa [Fin.ext_iff] using hst)
    (fun t ↦ by simp [-Fin.castSucc_mk, E, Fin.ext_iff]; lia)
    [(0, Fin.castSucc ⟨1, by lia⟩), (0, Fin.castSucc ⟨2, by lia⟩),
      (Fin.last _, Fin.castSucc ⟨u + 1, by lia⟩), (Fin.last _, Fin.last n)]
    (by simp [Fin.ext_iff, List.nodup_cons]; lia)
    (by rintro ⟨t, _⟩ hp ⟨i, rfl⟩; simp [-Fin.castSucc_mk] at hp; lia)
  simp [-Fin.castSucc_mk, E, Fin.ext_iff, show 3 + (u.val - 3) = u by lia,
    show 2 ≤ u.val by lia] at this
  linarith [hab.one_le_mul]

/-- `u = 0`, multiple bond: the path `0, 2, 3` has four outgoing bonds (to the leaf, `1` and
`4`). -/
private lemma not_isFiniteCartan_addLeaf_E_zero_of_two_le_mul {n : ℕ} {u : Fin n} {a b : ℤ}
    (hn : 6 ≤ n) (hu : u.val = 0) (hm : 2 ≤ a * b) :
    ¬ (addLeaf (E n) u a b).IsFiniteCartan := fun h ↦ by
  have := h.path_bonds_lt_four
    ![Fin.castSucc ⟨0, by lia⟩, Fin.castSucc ⟨2, by lia⟩, Fin.castSucc ⟨3, by lia⟩]
    (fun i j hij ↦ by fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff])
    (by simp [Fin.forall_fin_two, -Fin.castSucc_mk, E])
    [(0, Fin.last n), (2, Fin.castSucc ⟨1, by lia⟩), (2, Fin.castSucc ⟨4, by lia⟩)]
    (by simp [Fin.ext_iff, List.nodup_cons]; lia)
    (by rintro ⟨t, _⟩ hp ⟨i, rfl⟩; fin_cases i <;> simp [-Fin.castSucc_mk] at hp)
  simp [-Fin.castSucc_mk, E, Fin.ext_iff, hu] at this
  linarith

/-- `u = 1`, multiple bond: the path `1, 3` has four outgoing bonds (to the leaf, `2` and `4`). -/
private lemma not_isFiniteCartan_addLeaf_E_one_of_two_le_mul {n : ℕ} {u : Fin n} {a b : ℤ}
    (hn : 6 ≤ n) (hu : u.val = 1) (hm : 2 ≤ a * b) :
    ¬ (addLeaf (E n) u a b).IsFiniteCartan := fun h ↦ by
  have := h.path_bonds_lt_four ![Fin.castSucc ⟨1, by lia⟩, Fin.castSucc ⟨3, by lia⟩]
    (fun i j hij ↦ by fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff])
    (by simp [-Fin.castSucc_mk, E])
    [(0, Fin.last n), (1, Fin.castSucc ⟨2, by lia⟩), (1, Fin.castSucc ⟨4, by lia⟩)]
    (by simp [Fin.ext_iff, List.nodup_cons]; lia)
    (by rintro ⟨t, _⟩ hp ⟨i, rfl⟩; fin_cases i <;> simp [-Fin.castSucc_mk] at hp)
  simp [-Fin.castSucc_mk, E, Fin.ext_iff, hu] at this
  linarith

/-- `u = n - 1`, multiple bond: the path `3, …, n - 1` has four outgoing bonds (to `1`, `2` and the
leaf). -/
private lemma not_isFiniteCartan_addLeaf_E_last_of_two_le_mul {n : ℕ} {u : Fin n} {a b : ℤ}
    (hn : 6 ≤ n) (hu : u.val + 1 = n) (hm : 2 ≤ a * b) :
    ¬ (addLeaf (E n) u a b).IsFiniteCartan := fun h ↦ by
  have := h.path_bonds_lt_four (k := u - 3) (fun t ↦ Fin.castSucc ⟨3 + t, by lia⟩)
    (fun s t hst ↦ by simpa [Fin.ext_iff] using hst)
    (fun t ↦ by simp [-Fin.castSucc_mk, E, Fin.ext_iff]; lia)
    [(0, Fin.castSucc ⟨1, by lia⟩), (0, Fin.castSucc ⟨2, by lia⟩), (Fin.last _, Fin.last n)]
    (by simp [Fin.ext_iff, List.nodup_cons]; lia)
    (by rintro ⟨t, _⟩ hp ⟨i, rfl⟩; simp [-Fin.castSucc_mk] at hp; lia)
  simp [-Fin.castSucc_mk, E, Fin.ext_iff, show 3 + (u.val - 3) = u by lia] at this
  linarith

/-! ### Simple bonds at the ends of the arms -/

/-- `u = 0` in `E₆`, simple bond: arms `(1, 3, 2)`, which is `E₇`. -/
private lemma addLeaf_E_six_zero_eq :
    addLeaf (E 6) 0 (-1) (-1) = (E 7).submatrix (Equiv.swap 2 4 * Equiv.swap 0 5 : Equiv.Perm _)
      (Equiv.swap 2 4 * Equiv.swap 0 5 : Equiv.Perm _) := by
  decide

/-- `u = 0` in `E₇` or `E₈`, simple bond: arms `(1, 3, 3)` or `(1, 3, 4)` contain affine `E₇`. -/
private lemma not_isFiniteCartan_addLeaf_E_zero {n : ℕ} {u : Fin n} (hn : n = 7 ∨ n = 8)
    (hu : u.val = 0) : ¬ (addLeaf (E n) u (-1) (-1)).IsFiniteCartan := fun h ↦ by
  obtain rfl | rfl := hn <;> obtain rfl : u = 0 := Fin.ext hu
  · exact h.mulVec_ne_zero (f := id) Function.injective_id (x := ![2, 2, 3, 4, 3, 2, 1, 1])
      (by decide) (by decide)
  · exact h.mulVec_ne_zero (f := ![0, 1, 2, 3, 4, 5, 6, 8]) (by decide)
      (x := ![2, 2, 3, 4, 3, 2, 1, 1]) (by decide) (by decide)

/-- `u = 1`, simple bond: the nodes leaf, `1, 3, 2, 0, 4, 5` form affine `E₆` (arms
`(2, 2, 2)`). -/
private lemma not_isFiniteCartan_addLeaf_E_one {n : ℕ} {u : Fin n} (hn : n = 6 ∨ n = 7 ∨ n = 8)
    (hu : u.val = 1) : ¬ (addLeaf (E n) u (-1) (-1)).IsFiniteCartan := fun h ↦ by
  obtain rfl | rfl | rfl := hn <;> obtain rfl : u = 1 := Fin.ext hu
  · exact h.mulVec_ne_zero (f := ![6, 1, 3, 2, 0, 4, 5]) (by decide)
      (x := ![1, 2, 3, 2, 1, 2, 1]) (by decide) (by decide)
  · exact h.mulVec_ne_zero (f := ![7, 1, 3, 2, 0, 4, 5]) (by decide)
      (x := ![1, 2, 3, 2, 1, 2, 1]) (by decide) (by decide)
  · exact h.mulVec_ne_zero (f := ![8, 1, 3, 2, 0, 4, 5]) (by decide)
      (x := ![1, 2, 3, 2, 1, 2, 1]) (by decide) (by decide)

/-- `u = 5` in `E₆`, simple bond: `E₇`. -/
private lemma addLeaf_E_six_last_eq :
    addLeaf (E 6) 5 (-1) (-1) = (E 7).submatrix (Equiv.refl _) (Equiv.refl _) := by
  decide

/-- `u = 6` in `E₇`, simple bond: `E₈`. -/
private lemma addLeaf_E_seven_last_eq :
    addLeaf (E 7) 6 (-1) (-1) = (E 8).submatrix (Equiv.refl _) (Equiv.refl _) := by
  decide

/-- `u = 7` in `E₈`, simple bond: affine `E₈`. -/
private lemma not_isFiniteCartan_addLeaf_E_eight_last :
    ¬ (addLeaf (E 8) 7 (-1) (-1)).IsFiniteCartan := fun h ↦
  h.mulVec_ne_zero (f := id) Function.injective_id (x := ![2, 3, 4, 6, 5, 4, 3, 2, 1])
    (by decide) (by decide)

/-! ### The induction step -/

/-- Attaching a leaf to `E₆`, `E₇` or `E₈` gives a matrix of Dynkin type (`E₇` or `E₈`) whenever
it gives a finite Cartan matrix. -/
theorem IsFiniteCartan.hasDynkinType_addLeaf_E {n : ℕ} {u : Fin n} {a b : ℤ}
    (h : (addLeaf (E n) u a b).IsFiniteCartan) (hab : IsBond a b) (hn : n = 6 ∨ n = 7 ∨ n = 8) :
    (addLeaf (E n) u a b).HasDynkinType := by
  have hn6 : 6 ≤ n := by lia
  have := u.isLt
  obtain hu | hu | hu | hu | hu | hu : u.val = 0 ∨ u.val = 1 ∨ u.val = 2 ∨ u.val = 3 ∨
      4 ≤ u.val ∧ u.val + 2 ≤ n ∨ u.val + 1 = n := by lia
  -- `u = 0`: `E₇` for `n = 6`, affine `E₇` for `n = 7, 8`, four bonds on `0, 2, 3` if multiple
  · obtain ⟨rfl, rfl⟩ | hm := hab.eq_neg_one_or_two_le_mul
    · obtain rfl | hn := hn
      · obtain rfl : u = 0 := Fin.ext hu
        exact .of_eq_submatrix _ addLeaf_E_six_zero_eq hasDynkinType_E_seven
      · exact (not_isFiniteCartan_addLeaf_E_zero hn hu h).elim
    · exact (not_isFiniteCartan_addLeaf_E_zero_of_two_le_mul hn6 hu hm h).elim
  -- `u = 1`: affine `E₆`, or four bonds on `1, 3` if multiple
  · obtain ⟨rfl, rfl⟩ | hm := hab.eq_neg_one_or_two_le_mul
    · exact (not_isFiniteCartan_addLeaf_E_one hn hu h).elim
    · exact (not_isFiniteCartan_addLeaf_E_one_of_two_le_mul hn6 hu hm h).elim
  -- `u = 2`: four bonds on `2, 3`
  · exact (not_isFiniteCartan_addLeaf_E_two hn6 hu hab h).elim
  -- `u = 3`: four bonds at the center
  · exact (not_isFiniteCartan_addLeaf_E_three hn6 hu hab h).elim
  -- `4 ≤ u ≤ n - 2`: four bonds on `3, …, u`
  · exact (not_isFiniteCartan_addLeaf_E_long_arm hu.1 hu.2 hab h).elim
  -- `u = n - 1`: `E₇`, `E₈`, affine `E₈`, or four bonds on `3, …, n - 1` if multiple
  · obtain ⟨rfl, rfl⟩ | hm := hab.eq_neg_one_or_two_le_mul
    · obtain rfl | rfl | rfl := hn
      · obtain rfl : u = 5 := Fin.ext (by simp; lia)
        exact .of_eq_submatrix _ addLeaf_E_six_last_eq hasDynkinType_E_seven
      · obtain rfl : u = 6 := Fin.ext (by simp; lia)
        exact .of_eq_submatrix _ addLeaf_E_seven_last_eq hasDynkinType_E_eight
      · obtain rfl : u = 7 := Fin.ext (by simp; lia)
        exact (not_isFiniteCartan_addLeaf_E_eight_last h).elim
    · exact (not_isFiniteCartan_addLeaf_E_last_of_two_le_mul hn6 hu hm h).elim

end Matrix
