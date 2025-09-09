/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic

/-!
# Simplices in torsors over normed spaces.

This file defines properties of simplices in a `NormedAddTorsor`.

## Main definitions

* `Affine.Simplex.Scalene`
* `Affine.Simplex.Equilateral`
* `Affine.Simplex.Regular`

-/


namespace Affine

open Function

variable {R V P : Type*} [Ring R] [SeminormedAddCommGroup V] [PseudoMetricSpace P] [Module R V]
variable [NormedAddTorsor V P]

namespace Simplex

variable {m n : ℕ}

/-- A simplex is scalene if all the edge lengths are different. -/
def Scalene (s : Simplex R P n) : Prop :=
  Injective fun i : {x : Fin (n + 1) × Fin (n + 1) // x.1 < x.2} ↦
    dist (s.points i.val.1) (s.points i.val.2)

lemma Scalene.dist_ne {s : Simplex R P n} (hs : s.Scalene) {i₁ i₂ i₃ i₄ : Fin (n + 1)}
    (h₁₂ : i₁ ≠ i₂) (h₃₄ : i₃ ≠ i₄) (h₁₂₃₄ : ¬(i₁ = i₃ ∧ i₂ = i₄)) (h₁₂₄₃ : ¬(i₁ = i₄ ∧ i₂ = i₃)) :
    dist (s.points i₁) (s.points i₂) ≠ dist (s.points i₃) (s.points i₄) := by
  rw [Classical.not_and_iff_not_or_not] at h₁₂₃₄ h₁₂₄₃
  rcases h₁₂.lt_or_gt with h₁₂lt | h₂₁lt <;> rcases h₃₄.lt_or_gt with h₃₄lt | h₄₃lt
  · apply hs.ne (a₁ := ⟨(i₁, i₂), h₁₂lt⟩) (a₂ := ⟨(i₃, i₄), h₃₄lt⟩)
    cases h₁₂₃₄ <;> simp [*]
  · nth_rw 2 [dist_comm]
    apply hs.ne (a₁ := ⟨(i₁, i₂), h₁₂lt⟩) (a₂ := ⟨(i₄, i₃), h₄₃lt⟩)
    cases h₁₂₄₃ <;> simp [*]
  · rw [dist_comm]
    apply hs.ne (a₁ := ⟨(i₂, i₁), h₂₁lt⟩) (a₂ := ⟨(i₃, i₄), h₃₄lt⟩)
    cases h₁₂₄₃ <;> simp [*]
  · rw [dist_comm]
    nth_rw 2 [dist_comm]
    apply hs.ne (a₁ := ⟨(i₂, i₁), h₂₁lt⟩) (a₂ := ⟨(i₄, i₃), h₄₃lt⟩)
    cases h₁₂₃₄ <;> simp [*]

@[simp] lemma scalene_reindex_iff {s : Simplex R P m} (e : Fin (m + 1) ≃ Fin (n + 1)) :
    (s.reindex e).Scalene ↔ s.Scalene := by
  let f : {x : Fin (m + 1) × Fin (m + 1) // x.1 < x.2} ≃
    {y : Fin (n + 1) × Fin (n + 1) // y.1 < y.2} :=
    ⟨fun x ↦ if h : e x.val.1 < e x.val.2 then ⟨(e x.val.1, e x.val.2), h⟩ else
      ⟨(e x.val.2, e x.val.1), Ne.lt_of_le (e.injective.ne x.property.ne') (not_lt.1 h)⟩,
     fun y ↦ if h : e.symm y.val.1 < e.symm y.val.2 then ⟨(e.symm y.val.1, e.symm y.val.2), h⟩ else
      ⟨(e.symm y.val.2, e.symm y.val.1),
       Ne.lt_of_le (e.symm.injective.ne y.property.ne') (not_lt.1 h)⟩,
     by
       simp only [LeftInverse, Subtype.forall, Prod.forall]
       intro i j h
       split_ifs with h₁ h₂ h₃
       · simp
       · simp [h] at h₂
       · simp [h, lt_asymm] at h₃
       · simp,
     by
       simp only [RightInverse, LeftInverse, Subtype.forall, Prod.forall]
       intro i j h
       split_ifs with h₁ h₂ h₃
       · simp
       · simp [h] at h₂
       · simp [h, lt_asymm] at h₃
       · simp⟩
  simp_rw [Scalene]
  convert (Injective.of_comp_iff' _ (Equiv.bijective f)).symm
  simp only [reindex_points, comp_apply, Equiv.coe_fn_mk, f]
  split_ifs with h
  · simp
  · simp [dist_comm]

/-- A simplex is equilateral if all the edge lengths are equal. -/
def Equilateral (s : Simplex R P n) : Prop :=
  ∃ r : ℝ, ∀ i j, i ≠ j → dist (s.points i) (s.points j) = r

lemma Equilateral.dist_eq {s : Simplex R P n} (he : s.Equilateral) {i₁ i₂ i₃ i₄ : Fin (n + 1)}
    (h₁₂ : i₁ ≠ i₂) (h₃₄ : i₃ ≠ i₄) :
    dist (s.points i₁) (s.points i₂) = dist (s.points i₃) (s.points i₄) := by
  rcases he with ⟨r, hr⟩
  rw [hr _ _ h₁₂, hr _ _ h₃₄]

@[simp] lemma equilateral_reindex_iff {s : Simplex R P m} (e : Fin (m + 1) ≃ Fin (n + 1)) :
    (s.reindex e).Equilateral ↔ s.Equilateral := by
  refine ⟨fun ⟨r, hr⟩ ↦ ⟨r, fun i j hij ↦ ?_⟩, fun ⟨r, hr⟩ ↦ ⟨r, fun i j hij ↦ ?_⟩⟩
  · convert hr (e i) (e j) (e.injective.ne hij) using 2 <;> simp
  · convert hr (e.symm i) (e.symm j) (e.symm.injective.ne hij) using 2

/-- A simplex is regular if it is equivalent under an isometry to any reindexing. -/
def Regular (s : Simplex R P n) : Prop :=
  ∀ σ : Equiv.Perm (Fin (n + 1)), ∃ x : P ≃ᵢ P, s.points ∘ σ = x ∘ s.points

@[simp] lemma regular_reindex_iff {s : Simplex R P m} (e : Fin (m + 1) ≃ Fin (n + 1)) :
    (s.reindex e).Regular ↔ s.Regular := by
  refine ⟨fun h σ ↦ ?_, fun h σ ↦ ?_⟩
  · rcases h ((e.symm.trans σ).trans e) with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    ext i
    simpa using congrFun hx (e i)
  · rcases h ((e.trans σ).trans e.symm) with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    ext i
    simpa using congrFun hx (e.symm i)

lemma Regular.equilateral {s : Simplex R P n} (hr : s.Regular) : s.Equilateral := by
  refine ⟨dist (s.points 0) (s.points 1), fun i j hij ↦ ?_⟩
  have hn : n ≠ 0 := by omega
  by_cases hi : i = 1
  · rw [hi, dist_comm]
    rcases hr (Equiv.swap 0 j) with ⟨x, hx⟩
    nth_rw 2 [← x.dist_eq]
    simp_rw [← Function.comp_apply (f := x), ← hx]
    simp only [comp_apply, Equiv.swap_apply_left]
    convert rfl
    rw [Equiv.swap_apply_of_ne_of_ne (by simp [hn]) (by grind)]
  · rcases hr ((Equiv.swap 0 i).trans (Equiv.swap 1 j)) with ⟨x, hx⟩
    nth_rw 2 [← x.dist_eq]
    simp_rw [← Function.comp_apply (f := x), ← hx]
    simp only [Equiv.coe_trans, comp_apply, Equiv.swap_apply_left]
    convert rfl
    · exact Equiv.swap_apply_of_ne_of_ne hi hij
    · rw [Equiv.swap_apply_of_ne_of_ne (by simp [hn]) (Ne.symm hi)]
      simp

end Simplex

namespace Triangle

lemma scalene_iff_dist_ne_and_dist_ne_and_dist_ne {t : Triangle R P} :
    t.Scalene ↔ dist (t.points 0) (t.points 1) ≠ dist (t.points 0) (t.points 2) ∧
      dist (t.points 0) (t.points 1) ≠ dist (t.points 1) (t.points 2) ∧
      dist (t.points 0) (t.points 2) ≠ dist (t.points 1) (t.points 2) := by
  refine ⟨fun h ↦
    ⟨h.dist_ne (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2) (by decide) (by decide),
     h.dist_ne (by decide : (0 : Fin 3) ≠ 1) (by decide : (1 : Fin 3) ≠ 2) (by decide) (by decide),
     h.dist_ne (by decide : (0 : Fin 3) ≠ 2) (by decide : (1 : Fin 3) ≠ 2) (by decide) (by decide)⟩,
    fun ⟨h₁, h₂, h₃⟩ ↦ ?_⟩
  intro ⟨⟨x₁, x₂⟩, hx⟩ ⟨⟨y₁, y₂⟩, hy⟩ hxy
  simp only at hx hy hxy
  simp only [Subtype.mk.injEq, Prod.mk.injEq]
  fin_cases x₁ <;> fin_cases x₂ <;> simp +decide only at hx <;>
    fin_cases y₁ <;> fin_cases y₂ <;> simp +decide only at hy <;>
    simp [h₁, h₂, h₃, h₁.symm, h₂.symm, h₃.symm] at hxy ⊢

lemma equilateral_iff_dist_eq_and_dist_eq {t : Triangle R P} {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂)
    (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    t.Equilateral ↔ dist (t.points i₁) (t.points i₂) = dist (t.points i₁) (t.points i₃) ∧
      dist (t.points i₁) (t.points i₂) = dist (t.points i₂) (t.points i₃) := by
  refine ⟨fun ⟨r, hr⟩ ↦ ?_, fun h ↦ ?_⟩
  · simp [hr _ _ h₁₂, hr _ _ h₁₃, hr _ _ h₂₃]
  · refine ⟨dist (t.points i₁) (t.points i₂), ?_⟩
    intro i j hij
    have hi : (i = i₁ ∧ j = i₂) ∨ (i = i₂ ∧ j = i₁) ∨ (i = i₁ ∧ j = i₃) ∨
      (i = i₃ ∧ j = i₁) ∨ (i = i₂ ∧ j = i₃) ∨ (i = i₃ ∧ j = i₂) := by
      clear h
      decide +revert
    rcases h with ⟨h₁, h₂⟩
    rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩| ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact dist_comm _ _
    · exact h₁.symm
    · rw [h₁, dist_comm]
    · rw [h₂, dist_comm]
    · rw [h₂, dist_comm]

lemma equilateral_iff_dist_01_eq_02_and_dist_01_eq_12 {t : Triangle R P} :
    t.Equilateral ↔ dist (t.points 0) (t.points 1) = dist (t.points 0) (t.points 2) ∧
      dist (t.points 0) (t.points 1) = dist (t.points 1) (t.points 2) :=
  equilateral_iff_dist_eq_and_dist_eq (by decide) (by decide) (by decide)

end Triangle

end Affine
