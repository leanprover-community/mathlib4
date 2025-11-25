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

If `LinearOrder α` and `F` is a finite subset of `α × α` such that for any `(x, y) ∈ F`,
`a ≤ x ≤ y ≤ b` and all such `[x, y]`'s are pairwise disjoint, we order `F` from left to right as
`(x 0, y 0), ..., (x (F.card - 1), y (F.card - 1))`, then `F.intervalGapsWithin a b i` is
- `(a, x 0)` if `0 = i < F.card`;
- `(y (i - 1), x i)` if `0 < i < F.card`;
- `(y (i - 1), b)` if `0 < i = F.card`;
- `(a, b)` otherwise.

Technically, the definition `F.intervalGapsWithin a b` does not require `F` to be pairwise disjoint
or endpoints to be within `[a, b]` or even require that `a ≤ b`, but it makes the most sense if
they are actually satisfied. If they are actually satisfied, then we show that
* `Finset.intervalGapsWithin_mapsTo`, `Finset.intervalGapsWithin_injOn`,
`Finset.intervalGapsWithin_surjOn`:
`(fun i ↦ ((F.intervalGapsWithin a b i).2, (F.intervalGapsWithin a b (i + 1)).1))` is a bijection
between `Set.Iio F.card` and `F`.
* `Finset.intervalGapsWithin_le_fst`, `Finset.intervalGapsWithin_snd_le`,
`Finset.intervalGapsWithin_fst_le_snd`:
`[(F.intervalGapsWithin a b i).1, (F.intervalGapsWithin a b i).2]` is indeed a subinterval of
`[a, b]`.
* `Finset.intervalGapsWithin_pairwiseDisjoint_Ioc`: the half-closed intervals
`[(F.intervalGapsWithin a b i).1, (F.intervalGapsWithin a b i).2)` are pairwise disjoint for
`i ≤ F.card`.
-/

@[expose] public section

open Set

section IntervalGapsWithin

namespace Finset

variable {α : Type*} [LinearOrder α] (F : Finset (α × α)) (a b : α) {i : ℕ}

/-- We order `F` in the lexicographic order as `(x 0, y 0), ..., (x (F.card - 1), y (F.card - 1))`.
Then `F.intervalGapsWithin a b i` is
- `(a, x 0)` if `0 = i < F.card`;
- `(y (i - 1), x i)` if `0 < i < F.card`;
- `(y (i - 1), b)` if `0 < i = F.card`;
- `(a, b)` otherwise.
-/
noncomputable def intervalGapsWithin (i : ℕ) : α × α := (fst, snd) where
  /-- The first coordinate of `F.intervalGapsWithin a b i` is `y (i - 1)` if `0 < i ≤ F.card`,
  `a` otherwise. -/
  fst := match i with
    | 0 => a
    | i + 1 => if hi : i < F.card then F.orderEmbOfFin (α := α ×ₗ α) rfl ⟨i, hi⟩ |>.2 else a
  /-- The second coordinate of `F.intervalGapsWithin a b i` is `x i` if `i < F.card`,
  `b` otherwise. -/
  snd := if hi : i < F.card then F.orderEmbOfFin (α := α ×ₗ α) rfl ⟨i, hi⟩ |>.1 else b

@[simp]
theorem intervalGapsWithin_zero_fst : (F.intervalGapsWithin a b 0).1 = a := by
  simp [intervalGapsWithin, intervalGapsWithin.fst]

@[simp]
theorem intervalGapsWithin_fst_of_card_lt (hi : F.card < i) :
    (F.intervalGapsWithin a b i).1 = a := by
  simp only [intervalGapsWithin, intervalGapsWithin.fst]
  grind

@[simp]
theorem intervalGapsWithin_snd_of_card_le (hi : F.card ≤ i) :
    (F.intervalGapsWithin a b i).2 = b := by
  simp only [intervalGapsWithin, intervalGapsWithin.snd]
  grind

theorem intervalGapsWithin_card_snd : (F.intervalGapsWithin a b F.card).2 = b := by
  simp

theorem intervalGapsWithin_snd_of_card_eq (hi : F.card = i) :
    (F.intervalGapsWithin a b i).2 = b :=
  intervalGapsWithin_snd_of_card_le F a b hi.le

theorem intervalGapsWithin_succ_fst_of_lt_card (hi : i < F.card) :
    (F.intervalGapsWithin a b (i + 1)).1 = (F.orderEmbOfFin (α := α ×ₗ α) rfl ⟨i, hi⟩).2 := by
  simp [intervalGapsWithin, intervalGapsWithin.fst, hi]

theorem intervalGapsWithin_fst_of_zero_lt_le_card (hi₀ : 0 < i) (hi : i ≤ F.card) :
    (F.intervalGapsWithin a b i).1 =
      (F.orderEmbOfFin (α := α ×ₗ α) rfl ⟨i - 1, Nat.sub_one_lt_of_le hi₀ hi⟩).2 := by
  convert F.intervalGapsWithin_succ_fst_of_lt_card a b (i := i - 1) (by omega)
  omega

theorem intervalGapsWithin_snd_of_lt_card (hi : i < F.card) :
    (F.intervalGapsWithin a b i).2 = (F.orderEmbOfFin (α := α ×ₗ α) rfl ⟨i, hi⟩).1 := by
  simp [intervalGapsWithin, intervalGapsWithin.snd, hi]

theorem intervalGapsWithin_mapsTo : (Set.Iio F.card).MapsTo
    (fun i ↦ ((F.intervalGapsWithin a b i).2, (F.intervalGapsWithin a b (i + 1)).1)) F := by
  intro i hi
  rw [Set.mem_Iio] at hi
  simp only [hi, intervalGapsWithin_snd_of_lt_card, intervalGapsWithin_succ_fst_of_lt_card]
  convert F.orderEmbOfFin_mem rfl ⟨i, hi⟩ using 1

theorem intervalGapsWithin_injOn : (Set.Iio F.card).InjOn
    (fun i ↦ ((F.intervalGapsWithin a b i).2, (F.intervalGapsWithin a b (i + 1)).1)) := by
  intro i hi j hj
  rw [Set.mem_Iio] at hi hj
  simp only [hi, hj, intervalGapsWithin_snd_of_lt_card, intervalGapsWithin_succ_fst_of_lt_card]
  exact fun hij ↦ Fin.ext_iff.mp (F.orderEmbOfFin (α := α ×ₗ α) rfl |>.injective hij)

theorem intervalGapsWithin_surjOn : (Set.Iio F.card).SurjOn
    (fun i ↦ ((F.intervalGapsWithin a b i).2, (F.intervalGapsWithin a b (i + 1)).1)) F := by
  intro z hz
  rw [← F.range_orderEmbOfFin rfl (α := α ×ₗ α)] at hz
  obtain ⟨i, hi⟩ := hz
  use i.val, i.prop
  simp [i.prop, intervalGapsWithin_snd_of_lt_card, intervalGapsWithin_succ_fst_of_lt_card, hi]

theorem intervalGapsWithin_le_fst {a b : α} (hFab : ∀ ⦃z⦄, z ∈ F → a ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b)
    (i : ℕ) : a ≤ (F.intervalGapsWithin a b i).1 := by
  by_cases hi : i = 0 ∨ F.card < i
  · rcases hi with hi | hi <;> simp [hi]
  · have := hFab (F.intervalGapsWithin_mapsTo a b (x := i - 1) (by grind))
    grind

theorem intervalGapsWithin_snd_le {a b : α} (hFab : ∀ ⦃z⦄, z ∈ F → a ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b)
    (i : ℕ) : (F.intervalGapsWithin a b i).2 ≤ b := by
  by_cases hi : F.card ≤ i
  · simp [hi]
  · have := hFab (F.intervalGapsWithin_mapsTo a b (x := i) (by grind))
    grind

theorem intervalGapsWithin_fst_le_snd {a b : α} (hab : a ≤ b)
    (hFab : ∀ ⦃z⦄, z ∈ F → a ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b)
    (hF : (SetLike.coe F).PairwiseDisjoint (fun z ↦ Set.Icc z.1 z.2)) (i : ℕ) :
    (F.intervalGapsWithin a b i).1 ≤ (F.intervalGapsWithin a b i).2 := by
  by_cases hi : i ≤ F.card
  swap
  · rwa [intervalGapsWithin_fst_of_card_lt _ _ _ (by omega),
      intervalGapsWithin_snd_of_card_le _ _ _ (by omega)]
  by_cases hi₁ : i = 0
  · simp only [hi₁, intervalGapsWithin_zero_fst]
    by_cases hi₂ : F.card = 0
    · simp [hi₂, hab]
    · exact hFab (F.intervalGapsWithin_mapsTo a b (by grind)) |>.left
  · by_cases hi₂ : F.card = i
    · simp only [hi₂.le, intervalGapsWithin_snd_of_card_le]
      convert hFab (F.intervalGapsWithin_mapsTo a b (x := i - 1) (by grind)) |>.right.right using 1
      simp only
      congr
      omega
    · replace hi₂ : i < F.card := by omega
      replace hi₁ : 0 < i := Nat.zero_lt_of_ne_zero hi₁
      simp only [hi₂, hi₁, hi, intervalGapsWithin_snd_of_lt_card,
        intervalGapsWithin_fst_of_zero_lt_le_card]
      set G := F.orderEmbOfFin (α := α ×ₗ α) rfl
      have hi' : (⟨i - 1, by omega⟩ : Fin F.card) < ⟨i, hi₂⟩ := Fin.mk_lt_mk.mpr (by omega)
      have hG : (G ⟨i - 1, by omega⟩).1 ≤ (G ⟨i, hi₂⟩).1 :=
        Prod.Lex.le_iff'.mp (G.monotone hi'.le) |>.left
      have := hF (by simp [G, F.orderEmbOfFin_mem (α := α ×ₗ α)])
        (by simp [G, F.orderEmbOfFin_mem (α := α ×ₗ α)]) (G.injective.ne hi'.ne)
      contrapose! this
      simp only [Set.not_disjoint_iff, Set.mem_Icc]
      use (G ⟨i, hi₂⟩).1
      have hFabi := hFab (z := G ⟨i, hi₂⟩) (by simp [G, F.orderEmbOfFin_mem (α := α ×ₗ α)])
      simp [hFabi, this.le, hG]

theorem intervalGapsWithin_pairwiseDisjoint_Ioc {a b : α}
    (hFab : ∀ ⦃z⦄, z ∈ F → a ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b) :
    (Set.Iio (F.card + 1)).PairwiseDisjoint
      (fun i ↦ Set.Ioc (F.intervalGapsWithin a b i).1 (F.intervalGapsWithin a b i).2) := by
  intro i hi j hj hij
  wlog hij' : i < j generalizing i j
  · exact (this hj hi hij.symm (by omega)).symm
  · rw [Function.onFun, Set.disjoint_iff_inter_eq_empty]
    suffices (F.intervalGapsWithin a b i).2 ≤ (F.intervalGapsWithin a b j).1 by grind
    have hi : i < F.card := by grind
    have hj : j - 1 < F.card := by grind
    have hij'' : (⟨i, hi⟩ : Fin F.card) ≤ ⟨j - 1, hj⟩ := Fin.mk_le_mk.mpr (by omega)
    trans (F.intervalGapsWithin a b (j - 1)).2
    · simp only [hi, hj, intervalGapsWithin_snd_of_lt_card]
      exact Prod.Lex.le_iff'.mp (F.orderEmbOfFin (α := α ×ₗ α) rfl |>.monotone hij'') |>.left
    · have := hFab (intervalGapsWithin_mapsTo F a b (x := j - 1) (by grind))
      grind

end Finset

end IntervalGapsWithin
