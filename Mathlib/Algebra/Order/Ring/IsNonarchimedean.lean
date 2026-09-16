/-
Copyright (c) 2025 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Fabrizio Barroero
-/
module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Nonarchimedean functions

A function `f : α → R` is nonarchimedean if it satisfies the strong triangle inequality
`f (a + b) ≤ max (f a) (f b)` for all `a b : α`. This file proves basic properties of nonarchimedean
functions. -/

public section

namespace IsNonarchimedean

variable {α β R : Type*} {a b : α} [LinearOrder R] {f : α → R} {n : ℕ}

/-- A nonnegative nonarchimedean function satisfies the triangle inequality. -/
theorem add_le [Semiring R] [IsStrictOrderedRing R] [Add α] (f_nonneg : ∀ x : α, 0 ≤ f x)
    (hna : IsNonarchimedean f) : f (a + b) ≤ f a + f b := by
  apply le_trans (hna _ _)
  rw [max_le_iff, le_add_iff_nonneg_right, le_add_iff_nonneg_left]
  exact ⟨f_nonneg _, f_nonneg _⟩

section AddMonoid

variable [AddMonoid α] (hna : IsNonarchimedean f)

include hna

/-- If `f : α → R` is nonarchimedean and `f 0 ≤ f a`, then `f (n • a) ≤ f a` for every
  `n : ℕ`. -/
theorem nsmul_le (f_zero_le : f 0 ≤ f a) : f (n • a) ≤ f a := by
  induction n with
  | zero => simpa using f_zero_le
  | succ n _ =>
    rw [add_nsmul]
    apply le_trans <| hna (n • a) (1 • a)
    simpa

/-- If `f : α → R` is nonarchimedean, then `f (n • a) ≤ f a` for every positive `n : ℕ`. -/
theorem nsmul_le_of_pos (hn : 0 < n) :
    f (n • a) ≤ f a := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n _ ih =>
    rw [succ_nsmul]
    exact (hna _ _).trans (max_le ih (by simp))

end AddMonoid

section NonAssocSemiring

variable [NonAssocSemiring α] (hna : IsNonarchimedean f)

include hna

/-- If `f : α → R` is nonarchimedean and `f 0 ≤ f a`, then `f (n * a) ≤ f a` for every
  `n : ℕ`. -/
theorem nmul_le (f_zero_le : f 0 ≤ f a) : f (n * a) ≤ f a := by
  rw [← nsmul_eq_mul]
  exact hna.nsmul_le f_zero_le

/-- If `f : α → R` is nonarchimedean, then `f (n * a) ≤ f a` for every positive `n : ℕ`. -/
theorem nmul_le_of_pos (a : α) (hn : 0 < n) : f (n * a) ≤ f a := by
  rw [← nsmul_eq_mul]
  exact hna.nsmul_le_of_pos hn

end NonAssocSemiring

section AddGroup

variable [AddGroup α] (f_neg : ∀ a, f (-a) = f a) (h_lt : f a < f b) (hna : IsNonarchimedean f)

include f_neg hna

include h_lt in
lemma add_eq_right_of_lt : f (a + b) = f b := by
  by_contra! h
  have h1 : f (a + b) ≤ f b := (hna a b).trans_eq (max_eq_right_of_lt h_lt)
  apply lt_irrefl (f b)
  calc
    f b = f (-a + (a + b)) := by simp
    _   ≤ max (f (-a)) (f (a + b)) := hna (-a) (a + b)
    _   < max (f b) (f b) := by
      rw [max_self, f_neg]
      exact max_lt h_lt <| lt_of_le_of_ne h1 h
    _   = f b := max_self (f b)

include h_lt in
lemma add_eq_left_of_lt : f (b + a) = f b := by
  by_contra! h
  have h1 : f (b + a) ≤ f b := (hna b a).trans_eq (max_eq_left_of_lt h_lt)
  apply lt_irrefl (f b)
  calc
    f b = f (b + a + -a) := by simp
    _   ≤ max (f (b + a)) (f (-a)) := hna (b + a) (-a)
    _   < max (f b) (f b) := by
      rw [max_self, f_neg]
      exact max_lt (lt_of_le_of_ne h1 h) h_lt
    _   = f b := max_self (f b)

/-- If `f : α → R` is nonarchimedean and invariant under negation, and `f a ≠ f b`, then
  `f (a + b) = max (f a) (f b)`. -/
theorem add_eq_max_of_ne (hne : f a ≠ f b) : f (a + b) = max (f a) (f b) := by
  rcases hne.lt_or_gt with h_lt | h_lt
  · rw [hna.add_eq_right_of_lt f_neg h_lt]
    exact (max_eq_right_of_lt h_lt).symm
  · rw [hna.add_eq_left_of_lt f_neg h_lt]
    exact (max_eq_left_of_lt h_lt).symm

@[deprecated (since := "2026-08-16")]
alias add_eq_max_of_ne' := add_eq_max_of_ne

end AddGroup

lemma apply_natCast_le_one [AddMonoidWithOne α] [One R] (f_zero_le : f 0 ≤ f 1) (f_one : f 1 = 1)
    (hna : IsNonarchimedean f) : f n ≤ 1 := by
  rw [← nsmul_one n, ← f_one]
  exact hna.nsmul_le f_zero_le

@[deprecated (since := "2026-04-27")]
alias apply_natCast_le_one_of_isNonarchimedean := apply_natCast_le_one

/-- If `f : α → R` is nonarchimedean, maps one to one, is invariant under negation, and
  `f 0 ≤ f 1`, then `f n ≤ 1` for every `n : ℤ`. -/
theorem apply_intCast_le_one [One R] [AddGroupWithOne α] (f_zero_le : f 0 ≤ f 1) (f_one : f 1 = 1)
    (f_neg : ∀ a, f (-a) = f a) (hna : IsNonarchimedean f) {n : ℤ} : f n ≤ 1 := by
  obtain ⟨a, rfl | rfl⟩ := Int.eq_nat_or_neg n <;>
  simp [f_neg, hna.apply_natCast_le_one f_zero_le f_one]

@[deprecated (since := "2026-04-27")]
alias apply_intCast_le_one_of_isNonarchimedean := apply_intCast_le_one

variable (g : β → α)

section AddCommMonoid

variable [AddCommMonoid α] (hna : IsNonarchimedean f)

section Multiset

open Multiset

variable {s : Multiset β}

include hna

/-- Given a nonarchimedean function `α → R`, a function `g : β → α` and a nonempty multiset
  `s : Multiset β`, we can always find `b : β` belonging to `s` such that
  `f (t.sum g) ≤ f (g b)`. -/
theorem multiset_image_add_of_nonempty (hs : s ≠ 0) : ∃ b ∈ s, f (s.map g).sum ≤ f (g b) := by
  induction s using Multiset.induction_on with
  | empty => contradiction
  | cons a s h =>
    simp only [mem_cons, map_cons, sum_cons, exists_eq_or_imp]
    by_cases h1 : s = 0
    · simp [h1]
    · obtain ⟨w, h2, h3⟩ := h h1
      rcases le_max_iff.mp <| hna (g a) (s.map g).sum with h4 | h4
      · exact .inl h4
      · exact .inr ⟨w, h2, le_trans h4 h3⟩

/-- Given a nonarchimedean function `f : α → R` such that `f 0` is a minimum of `f`, a
  function `g : β → α`, and a multiset `s : Multiset β`, we can always find `b : β`, belonging
  to `s` if `s` is nonempty, such that `f (s.map g).sum ≤ f (g b)`. -/
theorem multiset_image_add [Nonempty β] (s : Multiset β) (f_zero_le : ∀ x, f 0 ≤ f x) :
    ∃ b : β, (s ≠ 0 → b ∈ s) ∧ f (s.map g).sum ≤ f (g b) := by
  induction s using Multiset.induction_on with
  | empty =>
    exact ⟨Classical.arbitrary β, by simp, by simpa using f_zero_le _⟩
  | cons a s h =>
    obtain ⟨b, hb1, hb2⟩ := hna.multiset_image_add_of_nonempty (s := a ::ₘ s) g
      Multiset.cons_ne_zero
    exact ⟨b, fun _ ↦ hb1, hb2⟩

theorem multiset_powerset_image_add (n : ℕ) [CommMonoid α] (s : Multiset α) :
    ∃ t : Multiset α, card t = card s - n ∧ (∀ x : α, x ∈ t → x ∈ s) ∧
    f (map prod (powersetCard (card s - n) s)).sum ≤ f t.prod := by
  set g := fun t : Multiset α ↦ t.prod
  have hne : powersetCard (card s - n) s ≠ 0 := card_pos.mp
    (card_powersetCard (s.card - n) s ▸ Nat.choose_pos ((card s).sub_le n))
  obtain ⟨b, hb_in, hb_le⟩ := hna.multiset_image_add_of_nonempty g hne
  have hb : b ≤ s ∧ card b = card s - n := by
    rw [← mem_powersetCard]
    exact hb_in
  exact ⟨b, hb.2, fun x hx ↦ mem_of_le hb.left hx, hb_le⟩

end Multiset

section Finset

open Finset

variable {s : Finset β}

include hna

variable {g} in
/-- Ultrametric inequality with `Finset.sum`. -/
lemma apply_sum_le_sup (hne : s.Nonempty) : f (∑ i ∈ s, g i) ≤ s.sup' hne fun i => f (g i) := by
  induction hne using Nonempty.cons_induction with
  | singleton i => simp
  | cons i s _ hs hind =>
    simp only [sum_cons, le_sup'_iff, mem_cons, exists_eq_or_imp]
    rw [← le_sup'_iff hs]
    rcases le_max_iff.mp <| hna (g i) (∑ i ∈ s, g i) with h₁ | h₂
    · exact .inl h₁
    · exact .inr <| le_trans h₂ hind

@[deprecated (since := "2026-04-27")]
alias apply_sum_le_sup_of_isNonarchimedean := apply_sum_le_sup

/-- Given a nonarchimedean function `α → R`, a function `g : β → α` and a nonempty finset
  `s : Finset β`, we can always find `b : β` belonging to `s` such that `f (s.sum g) ≤ f (g b)`. -/
theorem finset_image_add_of_nonempty (hs : s.Nonempty) : ∃ b ∈ s, f (s.sum g) ≤ f (g b) := by
  simpa [Finset.le_sup'_iff] using hna.apply_sum_le_sup hs

variable (s)

/-- Given a nonarchimedean function `f : α → R` such that `f 0` is a minimum of `f`, a
  function `g : β → α`, and a finset `s : Finset β`, we can always find `b : β`, belonging to
  `s` if `s` is nonempty, such that `f (s.sum g) ≤ f (g b)`. -/
lemma finset_image_add [Nonempty β] (f_zero_le : ∀ x, f 0 ≤ f x) :
    ∃ i, (s.Nonempty → i ∈ s) ∧ f (s.sum g) ≤ f (g i) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · let b := Classical.choice (inferInstance : Nonempty β)
    exact ⟨b, by simp, by simpa using f_zero_le (g b)⟩
  · exact (fun ⟨i, h, h'⟩ => ⟨i, fun _ ↦ h, h'⟩) <| hna.finset_image_add_of_nonempty g hs

theorem finset_powerset_image_add [CommMonoid α] : ∃ u : s.powersetCard (s.card - n),
    f ((s.powersetCard (s.card - n)).sum fun t ↦ ∏ i ∈ t, g i) ≤ f (∏ i ∈ u.val, g i) := by
  obtain ⟨b, hb_in, hb⟩ := hna.finset_image_add_of_nonempty (fun t ↦ ∏ i ∈ t, g i)
    (powersetCard_nonempty.mpr (s.card.sub_le n))
  exact ⟨⟨b, hb_in⟩, hb⟩

end Finset

end AddCommMonoid

lemma apply_sum_eq_of_lt [AddCommGroup α] (hna : IsNonarchimedean f)
    (f_neg : ∀ a, f (-a) = f a) {s : Finset β} {k : β} (hk : k ∈ s)
    (hmax : ∀ j ∈ s, j ≠ k → f (g j) < f (g k)) : f (∑ i ∈ s, g i) = f (g k) := by
  by_cases hcard : s.card = 1
  · grind [Finset.card_eq_one.mp hcard]
  · classical
    rw [← Finset.add_sum_erase _ _ hk]
    have hNonempty : (s.erase k).Nonempty :=
      Finset.Nontrivial.erase_nonempty (Finset.one_lt_card_iff_nontrivial.mp (by grind))
    have hrest_le := hna.apply_sum_le_sup hNonempty (g := g)
    simp only [Finset.le_sup'_iff, Finset.mem_erase, ne_eq] at hrest_le
    rw [hna.add_eq_max_of_ne f_neg (by grind), max_eq_left (le_of_lt (by grind))]

variable (a b n) in
/-- If `f` is a submultiplicative, nonarchimedean function on a commutative semiring `α`, then for
  `n : ℕ` and `a b : α` we can find `m : ℕ` such that `m ≤ n` and
  `f ((a + b) ^ n) ≤ (f (a ^ m)) * (f (b ^ (n - m)))`. -/
theorem add_pow_le [Mul R] [CommSemiring α] (f_mul : ∀ x y, f (x * y) ≤ f x * f y)
    (hna : IsNonarchimedean f) : ∃ m < n + 1, f ((a + b) ^ n) ≤ f (a ^ m) * f (b ^ (n - m)) := by
  obtain ⟨m, hm_lt, hM⟩ := hna.finset_image_add_of_nonempty
    (fun m => a ^ m * b ^ (n - m) * ↑(n.choose m)) (s := Finset.range (n + 1)) (by simp)
  simp only [Finset.mem_range] at hm_lt
  refine ⟨m, hm_lt, ?_⟩
  simp only [← add_pow] at hM
  rw [mul_comm] at hM
  exact le_trans hM <| le_trans (hna.nmul_le_of_pos _ (Nat.choose_pos (Nat.lt_succ_iff.mp hm_lt)))
    (f_mul _ _)

end IsNonarchimedean
