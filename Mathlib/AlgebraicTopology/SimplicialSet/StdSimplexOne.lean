/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# Simplices in `Δ[1]`

-/

@[expose] public section

universe u

open CategoryTheory Simplicial

namespace SSet

namespace stdSimplex

/-- Given `i : Fin (n + 2)`, this is the `n`-simplex of `Δ[1]` which corresponds
to the monotone map `Fin (n + 1) → Fin 2` which takes `i` times the value `0`. -/
def objMk₁ {n : ℕ} (i : Fin (n + 2)) : Δ[1] _⦋n⦌ :=
  objMk
    { toFun j := if j.castSucc < i then 0 else 1
      monotone' j₁ j₂ h := by
        by_cases hi : j₁.castSucc < i
        · simp [if_pos hi]
        · dsimp
          rw [if_neg hi, if_neg (fun hj' ↦ hi (lt_of_le_of_lt (by simpa using h) hj'))] }

lemma objMk₁_apply_eq_zero_iff {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    objMk₁ i j = 0 ↔ j.castSucc < i := by
  by_cases hj : j.castSucc < i
  · simpa [objMk₁, if_pos hj]
  · simpa [objMk₁, if_neg hj] using hj

lemma objMk₁_of_castSucc_lt {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : j.castSucc < i) :
    objMk₁ i j = 0 := by
  simpa [objMk₁_apply_eq_zero_iff]

lemma objMk₁_apply_eq_one_iff {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    objMk₁ i j = 1 ↔ i ≤ j.castSucc := by
  by_cases hj : j.castSucc < i
  · simpa [objMk₁, if_pos hj]
  · simpa [objMk₁, if_neg hj] using hj

lemma objMk₁_of_le_castSucc {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : i ≤ j.castSucc) :
    objMk₁ i j = 1 := by
  simpa [objMk₁_apply_eq_one_iff]

-- to be moved
lemma _root_.Fin.eq_iff_eq_zero_iff (a b : Fin 2) : a = b ↔ (a = 0 ↔ b = 0) := by
  fin_cases a <;> fin_cases b <;> tauto

lemma δ_objMk₁_of_le {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2)) (h : i ≤ j.castSucc) :
    Δ[1].δ j (objMk₁.{u} i) =
      objMk₁.{u} (i.castPred (Fin.ne_last_of_lt (lt_of_le_of_lt h j.castSucc_lt_succ))) := by
  obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last
    (Fin.ne_last_of_lt (lt_of_le_of_lt h j.castSucc_lt_succ))
  simp only [Fin.castSucc_le_castSucc_iff] at h
  rw [Fin.castPred_castSucc]
  ext k : 1
  change objMk₁.{u} i.castSucc (j.succAbove k) = _
  rw [Fin.eq_iff_eq_zero_iff]
  simp only [objMk₁_apply_eq_zero_iff, Fin.castSucc_lt_castSucc_iff]
  by_cases hk : k.castSucc < j
  · rw [Fin.succAbove_of_castSucc_lt _ _ hk]
  · simp only [not_lt] at hk
    rw [Fin.succAbove_of_le_castSucc _ _ hk]
    constructor
    · intro h'
      have := lt_of_le_of_lt ((h.trans hk).trans k.castSucc_le_succ) h'
      simp at this
    · lia

lemma δ_objMk₁_of_lt {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2)) (h : j.castSucc < i) :
    Δ[1].δ j (objMk₁.{u} i) = objMk₁.{u} (i.pred (Fin.ne_zero_of_lt h)) := by
  obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h)
  rw [Fin.pred_succ]
  ext k : 1
  change objMk₁.{u} i.succ (j.succAbove k) = _
  rw [Fin.eq_iff_eq_zero_iff]
  simp only [objMk₁_apply_eq_zero_iff]
  by_cases hk : j ≤ k.castSucc
  · rw [Fin.succAbove_of_le_castSucc _ _ hk,
      Fin.castSucc_lt_succ_iff, Fin.castSucc_lt_iff_succ_le]
  · simp only [not_le] at hk
    rw [Fin.succAbove_of_castSucc_lt _ _ hk, Fin.castSucc_lt_succ_iff]
    exact ⟨fun _ ↦ lt_of_lt_of_le hk (by simpa using h), fun h ↦ h.le⟩

lemma σ_objMk₁_of_le {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : i ≤ j.castSucc) :
    Δ[1].σ j (objMk₁.{u} i) = objMk₁ i.castSucc := by
  ext k : 1
  dsimp [SimplicialObject.σ, SimplexCategory.σ]
  change objMk₁.{u} i (j.predAbove k) = _
  by_cases hk : k < i
  · rw [Fin.predAbove_of_le_castSucc _ _ (by
      rw [Fin.le_castSucc_iff]
      exact lt_of_lt_of_le hk (h.trans j.castSucc_le_succ)),
      objMk₁_of_castSucc_lt _ _ (by simpa),
      objMk₁_of_castSucc_lt _ _ (by simpa using hk)]
  · simp at hk
    rw [objMk₁_of_le_castSucc, objMk₁_of_le_castSucc _ _ (by simpa)]
    by_cases hk' : k ≤ j.castSucc
    · rwa [Fin.predAbove_of_le_castSucc _ _ hk', Fin.castSucc_castPred]
    · simp only [not_le] at hk'
      rw [Fin.predAbove_of_castSucc_lt _ _ hk']
      refine h.trans ?_
      rwa [Fin.castSucc_le_castSucc_iff, Fin.le_pred_iff, ← Fin.castSucc_lt_iff_succ_le]

lemma σ_objMk₁_of_lt {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : j.castSucc < i) :
    Δ[1].σ j (objMk₁.{u} i) = objMk₁ i.succ := by
  ext k : 1
  dsimp [SimplicialObject.σ, SimplexCategory.σ]
  change objMk₁.{u} i (j.predAbove k) = _
  by_cases hk : i < k
  · obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hk)
    rw [Fin.predAbove_of_castSucc_lt _ _ (h.trans hk),
      objMk₁_of_le_castSucc _ _ (by simpa [Fin.le_castSucc_iff]),
      objMk₁_of_le_castSucc _ _ (by simpa [Fin.le_castSucc_iff])]
  · simp only [not_lt] at hk
    rw [objMk₁_of_castSucc_lt i.succ k (by simpa),
      objMk₁_of_castSucc_lt]
    by_cases hk' : j.castSucc < k
    · rwa [Fin.predAbove_of_castSucc_lt _ _ hk', Fin.castSucc_pred_lt_iff]
    · simp only [not_lt] at hk'
      rw [Fin.predAbove_of_le_castSucc _ _ hk']
      exact lt_of_le_of_lt (by simpa) h

lemma objMk₁_injective {n : ℕ} : Function.Injective (objMk₁ (n := n)) := by
  intro i j h
  wlog hij : i < j generalizing i j
  · simp only [not_lt] at hij
    obtain hij | rfl := hij.lt_or_eq
    · exact (this h.symm hij).symm
    · rfl
  have := DFunLike.congr_fun (objMk_bijective.1 h)
    ⟨i.1, lt_of_lt_of_le hij (by dsimp; lia)⟩
  simp [if_pos hij] at this

lemma objMk₁_surjective {n : ℕ} : Function.Surjective (objMk₁ (n := n)) := by
  intro f
  let S : Finset (Fin (n + 1)) := { i | f i = 1}
  by_cases hS : S.Nonempty
  · refine ⟨(S.min' hS).castSucc, ?_⟩
    ext i : 1
    dsimp [objMk₁]
    split_ifs with h
    · have hi : i ∉ S := fun hi ↦ by
        have := S.min'_le _ hi
        rw [Fin.le_iff_val_le_val] at this
        rw [Fin.lt_def] at h
        dsimp at h
        lia
      obtain ⟨j, hj⟩ : ∃ (j : Fin 2), f i = j := ⟨_, rfl⟩
      fin_cases j
      · exact hj.symm
      · exact (hi (by simpa [S])).elim
    · simp only [Fin.castSucc_lt_castSucc_iff, Finset.lt_min'_iff, not_forall,
        not_lt] at h
      obtain ⟨j, hj, hij⟩ := h
      replace hj : f j = 1 := by simpa [S] using hj
      have : f j ≤ f i := (objEquiv f).toOrderHom.monotone hij
      exact le_antisymm (by simpa [hj] using this) (by lia)
  · refine ⟨Fin.last _, ?_⟩
    ext i : 1
    dsimp [objMk₁]
    rw [if_pos (by simp)]
    obtain ⟨j, hj⟩ : ∃ (j : Fin 2), f i = j := ⟨_, rfl⟩
    fin_cases j
    · simp [hj]
    · exact (hS ⟨i, by simpa [S]⟩).elim

lemma objMk₁_bijective {n : ℕ} : Function.Bijective (objMk₁ (n := n)) :=
  ⟨objMk₁_injective, objMk₁_surjective⟩

end stdSimplex

end SSet
