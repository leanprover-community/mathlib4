/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Morphisms to `⦋1⦌`

We define a bijective map `SimplexCategory.toMk₁ : Fin (n + 2) → `⦋n⦌ ⟶ ⦋1⦌`.
This is used in the file `Mathlib.AlgebraicTopology.SimplicialSet.StdSimplexOne`
in the study of simplices in the simplicial set `Δ[1]`.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial

namespace SimplexCategory

/-- Given `i : Fin (n + 2)`, this is the morphism `⦋n⦌ ⟶ ⦋1⦌` in the simplex
category which corresponds to the monotone map `Fin (n + 1) → Fin 2` which
takes `i` times the value `0`. -/
def toMk₁ {n : ℕ} (i : Fin (n + 2)) : ⦋n⦌ ⟶ ⦋1⦌ :=
  Hom.mk
    { toFun j := if j.castSucc < i then 0 else 1
      monotone' j₁ j₂ h := by
        dsimp
        split_ifs <;> grind }

@[local grind =]
lemma toMk₁_apply {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
  dsimp% toMk₁ i j = if j.castSucc < i then 0 else 1 := rfl

#adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
(replacing grind's canonicalizer with a type-directed normalizer), `grind` closed the goals in
the four lemmas below. It is not yet clear whether this is due to defeq abuse in Mathlib or a
problem in the new canonicalizer; a minimization would help. The original proof was: `grind` -/

lemma toMk₁_apply_eq_zero_iff {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    dsimp% toMk₁ i j = 0 ↔ j.castSucc < i := by
  simp [toMk₁_apply]

lemma toMk₁_of_castSucc_lt {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : j.castSucc < i) :
    dsimp% toMk₁ i j = 0 := by
  simpa [toMk₁_apply]

lemma toMk₁_apply_eq_one_iff {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    dsimp% toMk₁ i j = 1 ↔ i ≤ j.castSucc := by
  simp [toMk₁_apply]

lemma toMk₁_of_le_castSucc {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : i ≤ j.castSucc) :
    dsimp% toMk₁ i j = 1 := by
  simpa [toMk₁_apply]

set_option backward.isDefEq.respectTransparency false in
lemma δ_comp_toMk₁_of_le {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2)) (h : i ≤ j.castSucc) :
    δ j ≫ toMk₁ i =
      toMk₁ (i.castPred (Fin.ne_last_of_lt (lt_of_le_of_lt h j.castSucc_lt_succ))) := by
  obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last
    (Fin.ne_last_of_lt (lt_of_le_of_lt h j.castSucc_lt_succ))
  simp only [Fin.castSucc_le_castSucc_iff] at h
  rw [Fin.castPred_castSucc]
  refine ConcreteCategory.hom_ext _ _ (fun k ↦ ?_)
  change toMk₁ i.castSucc (j.succAbove k) = _
  dsimp
  rw [Fin.eq_iff_eq_zero_iff, toMk₁_apply_eq_zero_iff, toMk₁_apply_eq_zero_iff]
  grind [Fin.succAbove]

set_option backward.isDefEq.respectTransparency false in
lemma δ_comp_toMk₁_of_lt {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2)) (h : j.castSucc < i) :
    δ j ≫ toMk₁ i = toMk₁ (i.pred (Fin.ne_zero_of_lt h)) := by
  obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h)
  rw [Fin.pred_succ]
  refine ConcreteCategory.hom_ext _ _ (fun k ↦ ?_)
  change toMk₁ i.succ (j.succAbove k) = _
  dsimp
  rw [Fin.eq_iff_eq_zero_iff, toMk₁_apply_eq_zero_iff, toMk₁_apply_eq_zero_iff]
  grind [Fin.succAbove]

set_option backward.isDefEq.respectTransparency false in
lemma σ_comp_toMk₁_of_le {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : i ≤ j.castSucc) :
    σ j ≫ toMk₁ i = toMk₁ i.castSucc := by
  refine ConcreteCategory.hom_ext _ _ (fun k ↦ ?_)
  change toMk₁ i (j.predAbove k) = _
  by_cases! hk : k < i
  · #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
    It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
    canonicalizer; a minimization would help. The original proof was:
    `grind [Fin.castPred, Fin.predAbove_of_le_castSucc, toMk₁_of_castSucc_lt]` -/
    simp; grind [Fin.castPred, Fin.predAbove_of_le_castSucc, toMk₁_of_castSucc_lt]
  · dsimp
    rw [toMk₁_of_le_castSucc, toMk₁_of_le_castSucc _ _ (by simpa)]
    by_cases hk' : k ≤ j.castSucc
    · rwa [Fin.predAbove_of_le_castSucc _ _ hk', Fin.castSucc_castPred]
    · grind [Fin.predAbove]

set_option backward.isDefEq.respectTransparency false in
lemma σ_comp_toMk₁_of_lt {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : j.castSucc < i) :
    σ j ≫ toMk₁ i = toMk₁ i.succ := by
  refine ConcreteCategory.hom_ext _ _ (fun k ↦ ?_)
  change toMk₁ i (j.predAbove k) = _
  by_cases! hk : i < k
  · #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
    It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
    canonicalizer; a minimization would help. The original proof was:
    `grind [Fin.predAbove_of_castSucc_lt, toMk₁_of_le_castSucc]` -/
    simp; grind [Fin.predAbove_of_castSucc_lt, toMk₁_of_le_castSucc]
  · dsimp
    rw [toMk₁_of_castSucc_lt i.succ k (by simpa), toMk₁_of_castSucc_lt]
    by_cases hk' : j.castSucc < k
    · rwa [Fin.predAbove_of_castSucc_lt _ _ hk', Fin.castSucc_pred_lt_iff]
    · simp only [not_lt] at hk'
      rw [Fin.predAbove_of_le_castSucc _ _ hk']
      exact lt_of_le_of_lt (by simpa) h

lemma toMk₁_injective {n : ℕ} : Function.Injective (toMk₁ (n := n)) := by
  intro i j h
  wlog hij : i < j generalizing i j
  · grind
  have := ConcreteCategory.congr_hom h ⟨i.1, lt_of_lt_of_le hij (by dsimp; lia)⟩
  simp [toMk₁_apply, if_pos hij] at this

set_option backward.isDefEq.respectTransparency false in
lemma toMk₁_surjective {n : ℕ} : Function.Surjective (toMk₁ (n := n)) := by
  intro f
  let S : Finset (Fin (n + 1)) := { i | f i = 1}
  by_cases hS : S.Nonempty
  · refine ⟨(S.min' hS).castSucc, ConcreteCategory.hom_ext _ _ (fun i ↦ ?_)⟩
    dsimp [toMk₁_apply]
    split_ifs with h
    · have hi : i ∉ S := fun hi ↦ by have := S.min'_le _ hi; grind
      #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
      (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this
      goal. It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in
      the new canonicalizer; a minimization would help. The original proof was: `grind` -/
      simp [S] at hi; grind
    · simp only [Fin.castSucc_lt_castSucc_iff, Finset.lt_min'_iff, not_forall,
        not_lt] at h
      obtain ⟨j, hj, hij⟩ := h
      have := f.toOrderHom.monotone hij
      #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
      (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this
      goal. It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in
      the new canonicalizer; a minimization would help. The original proof was:
      `grind [show f j ≤ f i from f.toOrderHom.monotone hij]` -/
      simp_all [ConcreteCategory.hom, S]
      grind
  · refine ⟨Fin.last _, ConcreteCategory.hom_ext _ _ (fun i ↦ ?_)⟩
    dsimp [toMk₁_apply]
    rw [if_pos (by simp)]
    obtain ⟨j, hj⟩ : ∃ (j : Fin 2), f i = j := ⟨_, rfl⟩
    fin_cases j
    · #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
      (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this
      goal. It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in
      the new canonicalizer; a minimization would help. The original proof was: `grind` -/
      simp_all
    · exact (hS ⟨i, by simpa [S]⟩).elim

lemma toMk₁_bijective {n : ℕ} : Function.Bijective (toMk₁ (n := n)) :=
  ⟨toMk₁_injective, toMk₁_surjective⟩

/-- The bijection `Fin (n + 2) ≃ (⦋n⦌ ⟶ ⦋1⦌)` which sends `i : Fin (n + 2)` to the
morphism `⦋n⦌ ⟶ ⦋1⦌` in the simplex category which corresponds to the monotone map
`Fin (n + 1) → Fin 2` which takes `i` times the value `0`. -/
@[simps! apply]
noncomputable def toMk₁Equiv {n : ℕ} : Fin (n + 2) ≃ (⦋n⦌ ⟶ ⦋1⦌) :=
  Equiv.ofBijective _ toMk₁_bijective

end SimplexCategory
