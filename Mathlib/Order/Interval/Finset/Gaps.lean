/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Prod.Lex.Basic

/-!
# Gaps of disjoint closed intervals

This file defines `Finset.intervalGapsWithin` that computes the complement of the union of a
collection of pairwise disjoint subintervals of `[a, b]`.

If `LinearOrder α`, `F` is a finite subset of `α × α` such that for any `(x, y) ∈ F`,
`a ≤ x ≤ y ≤ b` and all such `[x, y]`'s are pairwise disjoint, `h` is a proof of `#F = k`,
`i` is in `Fin (k + 1)`, we order `F` from left to right as
`(x 0, y 0), ..., (x (k - 1), y (k - 1))`, then `F.intervalGapsWithin h a b i` is
- `(a, b)` if `0 = i = k`;
- `(a, x 0)` if `0 = i < k`;
- `(y (i - 1), x i)` if `0 < i < k`;
- `(y (i - 1), b)` if `0 < i = k`.

Technically, the definition `F.intervalGapsWithin a b` does not require `F` to be pairwise disjoint
or endpoints to be within `[a, b]` or even require that `a ≤ b`, but it makes the most sense if
they are actually satisfied. If they are actually satisfied, then we show that
* `Finset.intervalGapsWithin_mapsTo`, `Finset.intervalGapsWithin_injective`,
  `Finset.intervalGapsWithin_surjOn`:
  `(fun j ↦ ((F.intervalGapsWithin h a b j.castSucc).2, (F.intervalGapsWithin h a b j.succ).1))` is
  a bijection between `Set.Iio k` and `F`.
* `Finset.intervalGapsWithin_le_fst`, `Finset.intervalGapsWithin_snd_le`,
  `Finset.intervalGapsWithin_fst_le_snd`:
  `[(F.intervalGapsWithin h a b j).1, (F.intervalGapsWithin h a b j).2]` is indeed a subinterval of
  `[a, b]` when `j < k`.
* `Finset.intervalGapsWithin_pairwiseDisjoint_Ioc`: the half-closed intervals
  `[(F.intervalGapsWithin h a b j).1, (F.intervalGapsWithin h a b j).2)` are pairwise disjoint
  for `j < k + 1`.
-/

open scoped Finset

@[expose] public section

open Fin Fin.NatCast Set

section IntervalGapsWithin

namespace Finset

variable {α : Type*} [LinearOrder α] (F : Finset (α × α)) {k : ℕ} (h : #F = k) (a b : α)
  (j : ℕ)

local notation "∗" => map ofLexEquiv.symm.toEmbedding

/-- We order `F` in the lexicographic order as `(x 0, y 0), ..., (x (k - 1), y (k - 1))`.
Then `F.intervalGapsWithin h a b i` is
- `(a, b)` if `0 = i = k`;
- `(a, x 0)` if `0 = i < k`;
- `(y (i - 1), x i)` if `0 < i < k`;
- `(y (i - 1), b)` if `0 < i = k`.
-/
noncomputable def intervalGapsWithin (i : Fin (k + 1)) : α × α := (fst, snd) where
  /-- The first coordinate of `F.intervalGapsWithin h a b i` is `a` if `i = 0`,
  `y (i - 1)` otherwise. -/
  fst := if hi : i = 0 then a else (∗ F).orderEmbOfFin (by simp [h]) (i.pred hi) |>.ofLex.2
  /-- The second coordinate of `F.intervalGapsWithin h a b i` is `b` if `i = k`,
  `x i` otherwise. -/
  snd := if hi : i = last k then b else (∗ F).orderEmbOfFin (by simp [h]) (i.castPred hi) |>.ofLex.1

@[simp]
theorem intervalGapsWithin_zero_fst : (F.intervalGapsWithin h a b 0).1 = a := by
  simp [intervalGapsWithin, intervalGapsWithin.fst]

theorem intervalGapsWithin_succ_fst_of_lt (hj : j < k) :
    (F.intervalGapsWithin h a b j.succ).1 =
    ((∗ F).orderEmbOfFin (by simp [h]) ⟨j, hj⟩).ofLex.2 := by
  have : (j.succ : Fin (k + 1)) = (⟨j, hj⟩ : Fin k).succ := by ext; simp [hj]
  grind [intervalGapsWithin, intervalGapsWithin.fst]

theorem intervalGapsWithin_fst_of_lt_lt (hj₁ : 0 < j) (hj₂ : j - 1 < k) :
    (F.intervalGapsWithin h a b j).1 =
    ((∗ F).orderEmbOfFin (by simp [h]) ⟨j - 1, hj₂⟩).ofLex.2 := by
  convert F.intervalGapsWithin_succ_fst_of_lt h a b (j - 1) hj₂
  lia

@[simp]
theorem intervalGapsWithin_last_snd : (F.intervalGapsWithin h a b (last k)).2 = b := by
  simp [intervalGapsWithin, intervalGapsWithin.snd]

theorem intervalGapsWithin_snd_of_lt (hj : j < k) :
    (F.intervalGapsWithin h a b j).2 = ((∗ F).orderEmbOfFin (by simp [h]) ⟨j, hj⟩).ofLex.1 := by
  have : (j : Fin (k + 1)) ≠ last k := by grind [val_cast_of_lt]
  simp only [intervalGapsWithin, intervalGapsWithin.snd, this, ↓reduceDIte]
  congr
  ext
  simp only [coe_castPred, val_natCast, Nat.mod_succ_eq_iff_lt]
  lia

theorem intervalGapsWithin_mapsTo : (Set.Iio k).MapsTo
    (fun (j : ℕ) ↦ ((F.intervalGapsWithin h a b j).2, (F.intervalGapsWithin h a b j.succ).1))
    F := by
  intro j hj
  rw [mem_Iio] at hj
  simpa [intervalGapsWithin_snd_of_lt, intervalGapsWithin_succ_fst_of_lt, hj]
    using (∗ F).orderEmbOfFin_mem (by simp [h]) ⟨j, hj⟩

theorem intervalGapsWithin_injOn : (Set.Iio k).InjOn
    (fun (j : ℕ) ↦ ((F.intervalGapsWithin h a b j).2, (F.intervalGapsWithin h a b j.succ).1)) := by
  intro j hj j' hj' hjj'
  rw [mem_Iio] at hj hj'
  simpa [hj, hj', intervalGapsWithin_snd_of_lt, intervalGapsWithin_succ_fst_of_lt, ofLex_inj]
    using hjj'

theorem intervalGapsWithin_surjOn : (Set.Iio k).SurjOn
    (fun (j : ℕ) ↦ ((F.intervalGapsWithin h a b j).2, (F.intervalGapsWithin h a b j.succ).1))
    F := by
  intro z hz
  replace hz : Lex.toLex z ∈ (∗ F : Set _) := by simpa using hz
  rw [← (∗ F).range_orderEmbOfFin (k := k) (by simp [h])] at hz
  obtain ⟨j, hj⟩ := hz
  use j.val, j.prop
  simp [intervalGapsWithin_snd_of_lt, intervalGapsWithin_succ_fst_of_lt, j.prop, hj,
    -coe_eq_castSucc]

theorem intervalGapsWithin_le_fst {a b : α} (hFab : ∀ ⦃z⦄, z ∈ F → a ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b) :
    a ≤ (F.intervalGapsWithin h a b j).1 := by
  wlog hj : j < k + 1 generalizing j
  · grind [cast_val_eq_self]
  by_cases hj : j = 0
  · simp [hj]
  · have := F.intervalGapsWithin_mapsTo h a b (x := j - 1)
    grind

theorem intervalGapsWithin_snd_le {a b : α} (hFab : ∀ ⦃z⦄, z ∈ F → a ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b) :
    (F.intervalGapsWithin h a b j).2 ≤ b := by
  wlog hj : j < k + 1 generalizing j
  · grind [cast_val_eq_self]
  by_cases hj : j = k
  · simp [hj]
  · have := hFab (F.intervalGapsWithin_mapsTo h a b (x := j) (by grind))
    grind

theorem intervalGapsWithin_fst_le_snd {a b : α} (hab : a ≤ b)
    (hFab : ∀ ⦃z⦄, z ∈ F → a ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b)
    (hF : (SetLike.coe F).PairwiseDisjoint (fun z ↦ Set.Icc z.1 z.2)) :
    (F.intervalGapsWithin h a b j).1 ≤ (F.intervalGapsWithin h a b j).2 := by
  wlog hj : j < k + 1 generalizing j
  · convert this (j : Fin (k + 1)) (by grind) using 3 <;> grind [cast_val_eq_self]
  by_cases hj₁ : j = 0
  · simp only [hj₁]
    by_cases hk : 0 = k
    · simp only [natCast_zero, intervalGapsWithin_zero_fst]
      simp [show 0 = last k by grind, hab]
    · exact hFab (F.intervalGapsWithin_mapsTo h a b (x := 0) (by grind)) |>.left
  have hk : k - 1 + 1 = k := by lia
  by_cases hj₂ : j = k
  · simp only [hj₂, natCast_eq_last, intervalGapsWithin_last_snd, ge_iff_le]
    convert hFab (F.intervalGapsWithin_mapsTo h a b (x := j - 1) (by grind)) |>.right.right using 1
    simp [hj₂, hk]
  rw [intervalGapsWithin_fst_of_lt_lt (hj₁ := by lia) (hj₂ := by lia),
    intervalGapsWithin_snd_of_lt (hj := by lia)]
  have hj₃ : (⟨j - 1, by lia⟩ : Fin k) ≠ ⟨j, by lia⟩ := by lia
  set G : Fin k ↪o α ×ₗ α := (∗ F).orderEmbOfFin (by simp [h])
  have mG (i) : (G i).ofLex ∈ F := by simpa [G] using (∗ F).orderEmbOfFin_mem (by simp [h]) i
  have := hF (mG _) (mG _) (fun e ↦ G.injective.ne hj₃ (Lex.ext e))
  contrapose! this
  simp only [Set.not_disjoint_iff, Set.mem_Icc]
  use (G ⟨j, by lia⟩).ofLex.1
  have hG : (G ⟨j - 1, by lia⟩).ofLex.1 ≤ (G ⟨j, by lia⟩).ofLex.1 :=
    Prod.Lex.le_iff'.mp (G.monotone (by simp [le_iff_val_le_val])) |>.left
  have hFabi := hFab (mG ⟨j, by lia⟩)
  simp [hFabi, this.le, hG]

theorem intervalGapsWithin_pairwiseDisjoint_Ioc {a b : α}
    (hFab : ∀ ⦃z⦄, z ∈ F → a ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b) :
    (Set.Iio (k + 1)).PairwiseDisjoint (fun (j : ℕ) ↦
      Set.Ioc (F.intervalGapsWithin h a b j).1 (F.intervalGapsWithin h a b j).2) := by
  intro j hj j' hj' hjj'
  rw [mem_Iio] at hj hj'
  wlog hij' : j < j' generalizing j j'
  · exact (this hj' hj hjj'.symm (by lia)).symm
  rw [Function.onFun, Set.disjoint_iff_inter_eq_empty]
  suffices (F.intervalGapsWithin h a b j).2 ≤ (F.intervalGapsWithin h a b j').1 by grind
  have hj'₀ : j' - 1 + 1 = j' := by lia
  have := hFab (F.intervalGapsWithin_mapsTo h a b (x := j' - 1) (by grind)) |>.right.left
  simp only [Nat.succ_eq_add_one, hj'₀] at this
  grw [← this]
  rw [intervalGapsWithin_snd_of_lt (hj := by lia), intervalGapsWithin_snd_of_lt (hj := by lia)]
  exact Prod.Lex.le_iff'.mp ((∗ F).orderEmbOfFin (by simp [h]) |>.monotone (by grind)) |>.left

end Finset

end IntervalGapsWithin
