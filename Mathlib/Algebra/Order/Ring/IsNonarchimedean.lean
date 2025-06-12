/-
Copyright (c) 2025 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Fabrizio Barroero
-/

import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.Order.Hom.Basic
import Mathlib.Data.Nat.Choose.Sum

/-!
# Nonarchimedean functions

A function `f : α → R` is nonarchimedean if it satisfies the strong triangle inequality
`f (a + b) ≤ max (f a) (f b)` for all `a b : α`. This file proves basic properties of
nonarchimedean functions.
-/

namespace IsNonarchimedean

variable {R : Type*} [Semiring R] [LinearOrder R] {a b : R} {m n : ℕ}

/-- A nonnegative nonarchimedean function satisfies the triangle inequality. -/
theorem add_le [IsStrictOrderedRing R] {α : Type*} [Add α] {f : α → R} (hf : ∀ x : α, 0 ≤ f x)
    (hna : IsNonarchimedean f) {a b : α} : f (a + b) ≤ f a + f b := by
  apply le_trans (hna _ _)
  rw [max_le_iff, le_add_iff_nonneg_right, le_add_iff_nonneg_left]
  exact ⟨hf _, hf _⟩

/-- If `f` is a nonegative nonarchimedean function `α → R` such that `f 0 = 0`, then for every
  `n : ℕ` and `a : α`, we have `f (n • a) ≤ (f a)`. -/
theorem nsmul_le {F α : Type*} [AddMonoid α] [FunLike F α R] [ZeroHomClass F α R]
    [NonnegHomClass F α R] {f : F} (hna : IsNonarchimedean f) {n : ℕ} {a : α} :
    f (n • a) ≤ f a := by
  induction n with
  | zero => simp
  | succ n _ =>
    rw [add_nsmul]
    apply le_trans <| hna (n • a) (1 • a)
    simpa

/-- If `f` is a nonegative nonarchimedean function `α → R` such that `f 0 = 0`, then for every
  `n : ℕ` and `a : α`, we have `f (n * a) ≤ (f a)`. -/
theorem nmul_le {F α : Type*} [NonAssocSemiring α] [FunLike F α R] [ZeroHomClass F α R]
    [NonnegHomClass F α R] {f : F} (hna : IsNonarchimedean f) {n : ℕ} {a : α} :
    f (n * a) ≤ f a := by
  rw [← nsmul_eq_mul]
  exact nsmul_le hna

lemma apply_natCast_le_one_of_isNonarchimedean {F α : Type*} [AddMonoidWithOne α] [FunLike F α R]
    [ZeroHomClass F α R] [NonnegHomClass F α R] [OneHomClass F α R] {f : F}
    (hna : IsNonarchimedean f) {n : ℕ} : f n ≤ 1 := by
  rw [← nsmul_one n, ← map_one f]
  exact nsmul_le hna

/-- If `f` is a nonarchimedean additive group seminorm on `α` with `f 1 = 1`, then for every `n : ℤ`
  we have `f n ≤ 1`. -/
theorem apply_intCast_le_one_of_isNonarchimedean [IsStrictOrderedRing R]
    {F α : Type*} [AddGroupWithOne α] [FunLike F α R]
    [AddGroupSeminormClass F α R] [OneHomClass F α R] {f : F}
    (hna : IsNonarchimedean f) {n : ℤ} : f n ≤ 1 := by
  obtain ⟨a, rfl | rfl⟩ := Int.eq_nat_or_neg n <;>
  simp [apply_natCast_le_one_of_isNonarchimedean hna]

lemma add_eq_right_of_lt {F α : Type*} [AddGroup α] [FunLike F α R]
    [AddGroupSeminormClass F α R] {f : F} (hna : IsNonarchimedean f) {x y : α}
    (h_lt : f x < f y) : f (x + y) = f y := by
  by_contra! h
  have h1 : f (x + y) ≤ f y := (hna x y).trans_eq (max_eq_right_of_lt h_lt)
  apply lt_irrefl (f y)
  calc
    f y = f (-x + (x + y)) := by simp
    _   ≤ max (f (-x)) (f (x + y)) := hna (-x) (x + y)
    _   < max (f y) (f y) := by
      rw [max_self, map_neg_eq_map]
      exact max_lt h_lt <| lt_of_le_of_ne h1 h
    _   = f y := max_self (f y)

lemma add_eq_left_of_lt {F α : Type*} [AddGroup α] [FunLike F α R]
    [AddGroupSeminormClass F α R] {f : F} (hna : IsNonarchimedean f) {x y : α}
    (h_lt : f y < f x) : f (x + y) = f x := by
  by_contra! h
  have h1 : f (x + y) ≤ f x := (hna x y).trans_eq (max_eq_left_of_lt h_lt)
  apply lt_irrefl (f x)
  calc
    f x = f (x + y + -y) := by simp
    _   ≤ max (f (x + y)) (f (-y)) := hna (x + y) (-y)
    _   < max (f x) (f x) := by
      rw [max_self, map_neg_eq_map]
      apply max_lt (lt_of_le_of_ne h1 h) h_lt
    _   = f x := max_self (f x)

/-- If `f` is a nonarchimedean additive group seminorm on `α` and `x y : α` are such that
  `f x ≠ f y`, then `f (x + y) = max (f x) (f y)`. -/
theorem add_eq_max_of_ne {F α : Type*} [AddGroup α] [FunLike F α R]
    [AddGroupSeminormClass F α R] {f : F} (hna : IsNonarchimedean f) {x y : α} (hne : f x ≠ f y) :
    f (x + y) = max (f x) (f y) := by
  rcases hne.lt_or_gt with h_lt | h_lt
  · rw [add_eq_right_of_lt hna h_lt]
    exact (max_eq_right_of_lt h_lt).symm
  · rw [add_eq_left_of_lt hna h_lt]
    exact (max_eq_left_of_lt h_lt).symm

omit [Semiring R] in
/-- Given a nonarchimedean function `α → R`, a function `g : β → α` and a nonempty multiset
  `s : Multiset β`, we can always find `b : β` belonging to `s` such that
  `f (t.sum g) ≤ f (g b)` . -/
theorem multiset_image_add_of_nonempty {α β : Type*} [AddCommMonoid α] [Nonempty β] {f : α → R}
    (hna : IsNonarchimedean f) (g : β → α) {s : Multiset β} (hs : s ≠ 0) :
    ∃ b : β, (b ∈ s) ∧ f (Multiset.map g s).sum ≤ f (g b) := by
  induction s using Multiset.induction_on with
  | empty => contradiction
  | cons a s h =>
    simp only [Multiset.mem_cons, Multiset.map_cons, Multiset.sum_cons, exists_eq_or_imp]
    by_cases h1 : s = 0
    · simp [h1]
    · obtain ⟨w, h2, h3⟩ := h h1
      rcases le_max_iff.mp <| hna (g a) (Multiset.map g s).sum with h4 | h4
      · exact .inl h4
      · exact .inr ⟨w, h2, le_trans h4 h3⟩

omit [Semiring R] in
/-- Given a nonarchimedean function `α → R`, a function `g : β → α` and a nonempty finset
  `t : Finset β`, we can always find `b : β` belonging to `t` such that `f (t.sum g) ≤ f (g b)` . -/
theorem finset_image_add_of_nonempty {α β : Type*} [AddCommMonoid α] [Nonempty β] {f : α → R}
    (hna : IsNonarchimedean f) (g : β → α) {t : Finset β} (ht : t.Nonempty) :
    ∃ b ∈ t, f (t.sum g) ≤ f (g b) := by
  apply multiset_image_add_of_nonempty hna
  simp_all [Finset.nonempty_iff_ne_empty]

/-- Given a nonegative nonarchimedean function `α → R` such that `f 0 = 0`, a function `g : β → α`
  and a multiset `s : Multiset β`, we can always find `b : β`, belonging to `s` if `s` is nonempty,
  such that `f (s.sum g) ≤ f (g b)` . -/
theorem multiset_image_add {F α β : Type*} [AddCommMonoid α] [FunLike F α R] [ZeroHomClass F α R]
    [NonnegHomClass F α R] [Nonempty β] {f : F} (hna : IsNonarchimedean f) (g : β → α)
    (s : Multiset β) : ∃ b : β, (s ≠ 0 → b ∈ s) ∧ f (Multiset.map g s).sum ≤ f (g b) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s h =>
    obtain ⟨b, hb1, hb2⟩ := multiset_image_add_of_nonempty (s := a ::ₘ s)
      hna g Multiset.cons_ne_zero
    exact ⟨b, fun _ ↦ hb1, hb2⟩

/-- Given a nonegative nonarchimedean function `α → R` such that `f 0 = 0`, a function `g : β → α`
  and a finset `t : Finset β`, we can always find `b : β`, belonging to `t` if `t` is nonempty,
  such that `f (t.sum g) ≤ f (g b)` . -/
theorem finset_image_add {F α β : Type*} [AddCommMonoid α] [FunLike F α R]
    [ZeroHomClass F α R] [NonnegHomClass F α R] [Nonempty β] {f : F} (hna : IsNonarchimedean f)
    (g : β → α) (t : Finset β) :
    ∃ b : β, (t.Nonempty → b ∈ t) ∧ f (t.sum g) ≤ f (g b) := by
  have h1 : t.Nonempty ↔ t.val ≠ 0 := by simp [Finset.nonempty_iff_ne_empty]
  rw [h1]
  exact multiset_image_add hna g t.val

open Multiset in
theorem multiset_powerset_image_add [IsStrictOrderedRing R]
    {F α : Type*} [CommRing α] [FunLike F α R]
    [AddGroupSeminormClass F α R] {f : F} (hf_na : IsNonarchimedean f) (s : Multiset α) (m : ℕ) :
    ∃ t : Multiset α, card t = card s - m ∧ (∀ x : α, x ∈ t → x ∈ s) ∧
      f (map prod (powersetCard (card s - m) s)).sum ≤ f t.prod := by
  set g := fun t : Multiset α ↦ t.prod
  obtain ⟨b, hb_in, hb_le⟩ := hf_na.multiset_image_add g (powersetCard (card s - m) s)
  have hb : b ≤ s ∧ card b = card s - m := by
    rw [← mem_powersetCard]
    exact hb_in (card_pos.mp
      (card_powersetCard (s.card - m) s ▸ Nat.choose_pos ((card s).sub_le m)))
  exact ⟨b, hb.2, fun x hx ↦ mem_of_le hb.left hx, hb_le⟩

open Finset in
theorem finset_powerset_image_add [IsStrictOrderedRing R]
    {F α β : Type*} [CommRing α] [FunLike F α R]
    [AddGroupSeminormClass F α R] {f : F} (hf_na : IsNonarchimedean f) (s : Finset β)
    (b : β → α) (m : ℕ) :
    ∃ u : powersetCard (s.card - m) s,
      f ((powersetCard (s.card - m) s).sum fun t : Finset β ↦
        t.prod fun i : β ↦ -b i) ≤ f (u.val.prod fun i : β  ↦ -b i)  := by
  set g := fun t : Finset β ↦ t.prod fun i : β ↦ - b i
  obtain ⟨b, hb_in, hb⟩ := hf_na.finset_image_add g (powersetCard (s.card - m) s)
  exact ⟨⟨b, hb_in (powersetCard_nonempty.mpr (Nat.sub_le s.card m))⟩, hb⟩

omit [Semiring R] in
open Finset in
/-- Ultrametric inequality with `Finset.sum`. -/
lemma apply_sum_le_sup_of_isNonarchimedean {α β : Type*} [AddCommMonoid α] {f : α → R}
    (nonarch : IsNonarchimedean f) {s : Finset β} (hnonempty : s.Nonempty) {l : β → α} :
    f (∑ i ∈ s, l i) ≤ s.sup' hnonempty fun i => f (l i) := by
  induction hnonempty using Nonempty.cons_induction with
  | singleton i => simp
  | cons i s _ hs hind =>
    simp only [sum_cons, le_sup'_iff, mem_cons, exists_eq_or_imp]
    rw [← le_sup'_iff hs]
    rcases le_max_iff.mp <| nonarch (l i) (∑ i ∈ s, l i) with h₁ | h₂
    · exact .inl h₁
    · exact .inr <| le_trans h₂ hind

/-- If `f` is a nonarchimedean additive group seminorm on a commutative ring `α`, `n : ℕ`, and
  `a b : α`, then we can find `m : ℕ` such that `m ≤ n` and
  `f ((a + b) ^ n) ≤ (f (a ^ m)) * (f (b ^ (n - m)))`. -/
theorem add_pow_le {F α : Type*} [CommRing α] [FunLike F α R] [ZeroHomClass F α R]
    [NonnegHomClass F α R] [SubmultiplicativeHomClass F α R] {f : F} (hna : IsNonarchimedean f)
    (n : ℕ) (a b : α) : ∃ m < n + 1, f ((a + b) ^ n) ≤ f (a ^ m) * f (b ^ (n - m)) := by
  obtain ⟨m, hm_lt, hM⟩ := finset_image_add hna
    (fun m => a ^ m * b ^ (n - m) * ↑(n.choose m)) (Finset.range (n + 1))
  simp only [Finset.nonempty_range_iff, ne_eq, Nat.succ_ne_zero, not_false_iff, Finset.mem_range,
    if_true, forall_true_left] at hm_lt
  refine ⟨m, hm_lt, ?_⟩
  simp only [← add_pow] at hM
  rw [mul_comm] at hM
  exact le_trans hM (le_trans (nmul_le hna) (map_mul_le_mul _ _ _))

end IsNonarchimedean
