/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
module

public import Mathlib.Order.Interval.Lex
public import Mathlib.Data.Finset.Sort

/-!
# Gaps of disjoint closed intervals

This file defines `Finset.intervalGapsWithin` that computes the complement of the union of a
collection of pairwise disjoint subintervals of `[a, b]`.

If `LinearOrder α`, `F` is a finite subset of `α × α` such that for any `(x, y) ∈ F`,
`a ≤ x ≤ y ≤ b` and all such `[x, y]`'s are pairwise disjoint, `h` is a proof of `F.card = k`,
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
a bijection between `Fin k` and `F`.
* `Finset.intervalGapsWithin_le_fst`, `Finset.intervalGapsWithin_snd_le`,
`Finset.intervalGapsWithin_fst_le_snd`:
`[(F.intervalGapsWithin h a b i).1, (F.intervalGapsWithin h a b i).2]` is indeed a subinterval of
`[a, b]`.
* `Finset.intervalGapsWithin_pairwiseDisjoint_Ioc`: the half-closed intervals
`[(F.intervalGapsWithin h a b i).1, (F.intervalGapsWithin h a b i).2)` are pairwise disjoint.
-/

@[expose] public section

open Set

section IntervalGapsWithin

namespace Finset

variable {α : Type*} [LinearOrder α] (F : Finset (α × α)) {k : ℕ} (h : F.card = k) (a b : α)
  (i : Fin (k + 1)) (j : Fin k)

/-- We order `F` in the lexicographic order as `(x 0, y 0), ..., (x (k - 1), y (k - 1))`.
Then `F.intervalGapsWithin h a b i` is
- `(a, b)` if `0 = i = k`;
- `(a, x 0)` if `0 = i < k`;
- `(y (i - 1), x i)` if `0 < i < k`;
- `(y (i - 1), b)` if `0 < i = k`.
-/
noncomputable def intervalGapsWithin : α × α := (fst, snd) where
  /-- The first coordinate of `F.intervalGapsWithin h a b i` is `a` if `i = 0`,
  `y (i - 1)` otherwise. -/
  fst := if hi : i = 0 then a else
    F.orderEmbOfFin (α := α ×ₗ α) h (i.pred hi) |>.2
  /-- The second coordinate of `F.intervalGapsWithin h a b i` is `b` if `i = k`,
  `x i` otherwise. -/
  snd := if hi : i = Fin.last k then b else
    F.orderEmbOfFin (α := α ×ₗ α) h (i.castPred hi) |>.1

@[simp]
theorem intervalGapsWithin_zero_fst : (F.intervalGapsWithin h a b 0).1 = a := by
  simp [intervalGapsWithin, intervalGapsWithin.fst]

theorem intervalGapsWithin_succ_fst :
    (F.intervalGapsWithin h a b (j.succ)).1 = (F.orderEmbOfFin (α := α ×ₗ α) h j).2 := by
  simp [intervalGapsWithin, intervalGapsWithin.fst]

theorem intervalGapsWithin_fst_of_not_zero (hi : i ≠ 0) :
    (F.intervalGapsWithin h a b i).1 = (F.orderEmbOfFin (α := α ×ₗ α) h (i.pred hi)).2 := by
  convert intervalGapsWithin_succ_fst _ _ _ _ (i.pred hi)
  simp

@[simp]
theorem intervalGapsWithin_last_snd : (F.intervalGapsWithin h a b (Fin.last k)).2 = b := by
  simp [intervalGapsWithin, intervalGapsWithin.snd]

theorem intervalGapsWithin_castSucc_snd :
    (F.intervalGapsWithin h a b (j.castSucc)).2 = (F.orderEmbOfFin (α := α ×ₗ α) h j).1 := by
  simp [intervalGapsWithin, intervalGapsWithin.snd]

theorem intervalGapsWithin_snd_of_not_last (hi : i ≠ Fin.last k) :
    (F.intervalGapsWithin h a b i).2 = (F.orderEmbOfFin (α := α ×ₗ α) h (i.castPred hi)).1 := by
  convert intervalGapsWithin_castSucc_snd _ _ _ _ (i.castPred hi)

theorem intervalGapsWithin_mapsTo : Set.univ.MapsTo
    (fun (j : Fin k) ↦ ((F.intervalGapsWithin h a b j.castSucc).2,
      (F.intervalGapsWithin h a b j.succ).1)) F := by
  intro j _
  simp only [intervalGapsWithin_castSucc_snd, intervalGapsWithin_succ_fst, Prod.mk.eta,
    SetLike.mem_coe]
  convert F.orderEmbOfFin_mem h j using 1

theorem intervalGapsWithin_injective : Function.Injective
    (fun (j : Fin k) ↦ ((F.intervalGapsWithin h a b j.castSucc).2,
      (F.intervalGapsWithin h a b j.succ).1)) := by
  intro j j'
  simp only [intervalGapsWithin_castSucc_snd, intervalGapsWithin_succ_fst, Prod.mk.eta]
  exact fun h' ↦ F.orderEmbOfFin (α := α ×ₗ α) h |>.injective h'

theorem intervalGapsWithin_surjOn : Set.univ.SurjOn
    (fun (j : Fin k) ↦ ((F.intervalGapsWithin h a b j.castSucc).2,
      (F.intervalGapsWithin h a b j.succ).1)) F := by
  intro z hz
  rw [← F.range_orderEmbOfFin h (α := α ×ₗ α)] at hz
  obtain ⟨j, hj⟩ := hz
  use j
  simp [hj, intervalGapsWithin_succ_fst, intervalGapsWithin_castSucc_snd]

theorem intervalGapsWithin_le_fst {a b : α} (hFab : ∀ ⦃z⦄, z ∈ F → a ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b) :
    a ≤ (F.intervalGapsWithin h a b i).1 := by
  by_cases hi : i = 0
  · simp [hi]
  · have := hFab (F.intervalGapsWithin_mapsTo h a b (x := i.pred hi) trivial)
    simp only [intervalGapsWithin_castSucc_snd, Fin.succ_pred] at this
    grind

theorem intervalGapsWithin_snd_le {a b : α} (hFab : ∀ ⦃z⦄, z ∈ F → a ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b) :
    (F.intervalGapsWithin h a b i).2 ≤ b := by
  by_cases hi : i = Fin.last k
  · simp [hi]
  · have := hFab (F.intervalGapsWithin_mapsTo h a b (x := i.castPred hi) trivial)
    simp only [Fin.castSucc_castPred, intervalGapsWithin_succ_fst] at this
    grind

theorem intervalGapsWithin_fst_le_snd {a b : α} (hab : a ≤ b)
    (hFab : ∀ ⦃z⦄, z ∈ F → a ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b)
    (hF : (SetLike.coe F).PairwiseDisjoint (fun z ↦ Set.Icc z.1 z.2)) :
    (F.intervalGapsWithin h a b i).1 ≤ (F.intervalGapsWithin h a b i).2 := by
  by_cases hi₁ : i = 0
  · simp only [hi₁, intervalGapsWithin_zero_fst]
    by_cases hk : 0 = Fin.last k
    · simp [hk, hab]
    · exact hFab (F.intervalGapsWithin_mapsTo h a b (x := Fin.castPred 0 hk) trivial) |>.left
  · by_cases hi₂ : i = Fin.last k
    · simp only [hi₂, intervalGapsWithin_last_snd]
      convert hFab (F.intervalGapsWithin_mapsTo h a b (x := i.pred hi₁) (by grind)) |>.right.right
        using 1
      simp [hi₂]
    · rw [intervalGapsWithin_fst_of_not_zero (hi := hi₁),
          intervalGapsWithin_snd_of_not_last (hi := hi₂)]
      set G := F.orderEmbOfFin (α := α ×ₗ α) h
      have hi₃ : i.pred hi₁ ≠ i.castPred hi₂ := by
        simp only [← Fin.val_ne_iff, Fin.val_pred, Fin.coe_castPred, ne_eq]
        simp only [← Fin.val_ne_zero_iff] at hi₁
        omega
      have hG : (G (i.pred hi₁)).1 ≤ (G (i.castPred hi₂)).1 :=
        Prod.Lex.le_iff'.mp (G.monotone (by simp [Fin.le_iff_val_le_val])) |>.left
      have := hF (by simp [G, F.orderEmbOfFin_mem (α := α ×ₗ α)])
        (by simp [G, F.orderEmbOfFin_mem (α := α ×ₗ α)]) (G.injective.ne hi₃)
      contrapose! this
      simp only [Set.not_disjoint_iff, Set.mem_Icc]
      use (G (i.castPred hi₂)).1
      have hFabi := hFab (z := G (i.castPred hi₂)) (by simp [G, F.orderEmbOfFin_mem (α := α ×ₗ α)])
      simp [hFabi, this.le, hG]

theorem intervalGapsWithin_pairwiseDisjoint_Ioc {a b : α}
    (hFab : ∀ ⦃z⦄, z ∈ F → a ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b) :
    Set.univ.PairwiseDisjoint
      (fun i ↦ Set.Ioc (F.intervalGapsWithin h a b i).1 (F.intervalGapsWithin h a b i).2) := by
  intro i _ i' _ hii'
  wlog hij' : i < i' generalizing i i'
  · exact (this trivial trivial hii'.symm (by omega)).symm
  · rw [Function.onFun, Set.disjoint_iff_inter_eq_empty]
    suffices (F.intervalGapsWithin h a b i).2 ≤ (F.intervalGapsWithin h a b i').1 by grind
    have hi : i ≠ Fin.last k := Fin.ne_last_of_lt hij'
    have hi' : i' ≠ 0 := Fin.ne_zero_of_lt hij'
    have hij'' : i.castPred hi ≤ i'.pred hi' := Fin.mk_le_mk.mpr (by omega)
    have := hFab (F.intervalGapsWithin_mapsTo h a b (x := i'.pred hi') trivial) |>.right.left
    simp only [Fin.succ_pred] at this
    grw [← this]
    rw [intervalGapsWithin_snd_of_not_last (hi := hi), intervalGapsWithin_castSucc_snd]
    exact Prod.Lex.le_iff'.mp (F.orderEmbOfFin (α := α ×ₗ α) h |>.monotone hij'') |>.left

end Finset

end IntervalGapsWithin
