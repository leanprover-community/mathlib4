/-
Copyright (c) 2025 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic

/-!
# Big operators on a finset in groups with zero involving order

This file contains the results concerning the interaction of finset big operators with groups with
zero, where order is involved.
-/

public section

variable {α M : Type*}

namespace Finset

section CommMonoidWithZero
variable [CommMonoidWithZero M]

section PosMulMono
variable [Preorder M] [ZeroLEOneClass M] [PosMulMono M] {f g : α → M} {s t : Finset α}

lemma prod_nonneg (h0 : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ ∏ i ∈ s, f i :=
  prod_induction f (fun i ↦ 0 ≤ i) (fun _ _ ha hb ↦ mul_nonneg ha hb) zero_le_one h0

/-- If all `f i`, `i ∈ s`, are nonneg and each `f i` is less than or equal to `g i`, then the
product of `f i` is less than or equal to the product of `g i`. See also `Finset.prod_le_prod` for
the case of an ordered commutative multiplicative monoid. -/
@[gcongr]
lemma prod_le_prod₀ (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    simp only [prod_cons, forall_mem_cons] at h0 h1 ⊢
    have := posMulMono_iff_mulPosMono.1 ‹PosMulMono M›
    gcongr
    exacts [prod_nonneg h0.2, h0.1.trans h1.1, h1.1, ih h0.2 h1.2]

theorem one_le_prod₀ (h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i :=
  prod_const_one.symm.trans_le (prod_le_prod₀ (fun _ _ ↦ zero_le_one) h)

theorem one_le_prod'₀ (h : ∀ i : α, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i :=
  one_le_prod₀ fun i _ ↦ h i

/-- If each `f i`, `i ∈ s` belongs to `[0, 1]`, then their product is less than or equal to one.
See also `Finset.prod_le_one` for the case of an ordered commutative multiplicative monoid. -/
lemma prod_le_one₀ (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ 1 := by
  convert ← prod_le_prod₀ h0 h1
  exact Finset.prod_const_one

@[to_additive (attr := gcongr) sum_le_sum_of_subset_of_nonneg]
theorem prod_le_prod_of_subset_of_one_le' [MulLeftMono N] (h : s ⊆ t)
    (hf : ∀ i ∈ t, i ∉ s → 1 ≤ f i) : ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  classical calc
      ∏ i ∈ s, f i ≤ (∏ i ∈ t \ s, f i) * ∏ i ∈ s, f i :=
        le_mul_of_one_le_left' <| one_le_prod <| by simpa only [mem_sdiff, and_imp]
      _ = ∏ i ∈ t \ s ∪ s, f i := (prod_union sdiff_disjoint).symm
      _ = ∏ i ∈ t, f i := by rw [sdiff_union_of_subset h]

@[to_additive]
theorem prod_le_prod_of_subset_of_le_one
    {ι : Type u_1} {N : Type u_5} [CommMonoid N] [Preorder N]
    {f : ι → N} {s t : Finset ι} [MulLeftMono N] (h : s ⊆ t) (hf : ∀ i ∈ t, i ∉ s → f i ≤ 1) :
    ∏ i ∈ t, f i ≤ ∏ i ∈ s, f i :=
  prod_le_prod_of_subset_of_one_le' (N := Nᵒᵈ) h hf

@[to_additive sum_mono_set_of_nonneg]
theorem prod_mono_set_of_one_le' [MulLeftMono N] (hf : ∀ x, 1 ≤ f x) :
    Monotone fun s ↦ ∏ x ∈ s, f x :=
  fun _ _ hst ↦ prod_le_prod_of_subset_of_one_le' hst fun x _ _ ↦ hf x

@[to_additive]
theorem prod_anti_set_of_le_one
    {ι : Type u_1} {N : Type u_5} [CommMonoid N] [Preorder N]
    {f : ι → N} [MulLeftMono N] (hf : ∀ (x : ι), f x ≤ 1) :
    Antitone fun (s : Finset ι) => ∏ x ∈ s, f x :=
  fun _ _ hst ↦ prod_le_prod_of_subset_of_le_one hst (by simp [hf])

@[to_additive sum_le_univ_sum_of_nonneg]
theorem prod_le_univ_prod_of_one_le' [MulLeftMono N] [Fintype ι] {s : Finset ι} (w : ∀ x, 1 ≤ f x) :
    ∏ x ∈ s, f x ≤ ∏ x, f x :=
  prod_le_prod_of_subset_of_one_le' (subset_univ s) fun a _ _ ↦ w a

@[to_additive sum_eq_zero_iff_of_nonneg]
theorem prod_eq_one_iff_of_one_le' {ι : Type u_1} {N : Type u_5} [CommMonoid N] [PartialOrder N]
    {f : ι → N} {s : Finset ι} [MulLeftMono N] :
    (∀ i ∈ s, 1 ≤ f i) → ((∏ i ∈ s, f i) = 1 ↔ ∀ i ∈ s, f i = 1) := by
  classical
    refine Finset.induction_on s
      (fun _ ↦ ⟨fun _ _ h ↦ False.elim (Finset.notMem_empty _ h), fun _ ↦ rfl⟩) ?_
    intro a s ha ih H
    have : ∀ i ∈ s, 1 ≤ f i := fun _ ↦ H _ ∘ mem_insert_of_mem
    rw [prod_insert ha, mul_eq_one_iff_of_one_le (H _ <| mem_insert_self _ _) (one_le_prod this),
      forall_mem_insert, ih this]

@[to_additive sum_pos_iff_of_nonneg]
lemma one_lt_prod_iff_of_one_le {ι : Type u_1} {N : Type u_5} [CommMonoid N] [PartialOrder N]
    {f : ι → N} {s : Finset ι} [MulLeftMono N] (hf : ∀ x ∈ s, 1 ≤ f x) :
    1 < ∏ x ∈ s, f x ↔ ∃ x ∈ s, 1 < f x := by
  have hsum : 1 ≤ ∏ x ∈ s, f x := one_le_prod hf
  rw [hsum.lt_iff_ne', Ne, prod_eq_one_iff_of_one_le' hf, not_forall]
  simp +contextual [← exists_prop, -exists_const_iff, hf _ _ |>.lt_iff_ne']

@[to_additive sum_eq_zero_iff_of_nonpos]
theorem prod_eq_one_iff_of_le_one' {ι : Type u_1} {N : Type u_5} [CommMonoid N] [PartialOrder N]
    {f : ι → N} {s : Finset ι} [MulLeftMono N] :
    (∀ i ∈ s, f i ≤ 1) → ((∏ i ∈ s, f i) = 1 ↔ ∀ i ∈ s, f i = 1) :=
  prod_eq_one_iff_of_one_le' (N := Nᵒᵈ)

@[to_additive]
lemma prod_lt_one_iff_of_le_one {ι : Type u_1} {N : Type u_5} [CommMonoid N] [PartialOrder N]
    {f : ι → N} {s : Finset ι} [MulLeftMono N] (hf : ∀ x ∈ s, f x ≤ 1) :
    ∏ x ∈ s, f x < 1 ↔ ∃ x ∈ s, f x < 1 :=
  one_lt_prod_iff_of_one_le (N := Nᵒᵈ) hf

@[to_additive single_le_sum]
theorem single_le_prod' [MulLeftMono N] (hf : ∀ i ∈ s, 1 ≤ f i) {a} (h : a ∈ s) :
    f a ≤ ∏ x ∈ s, f x :=
  calc
    f a = ∏ i ∈ {a}, f i := (prod_singleton _ _).symm
    _ ≤ ∏ i ∈ s, f i :=
      prod_le_prod_of_subset_of_one_le' (singleton_subset_iff.2 h) fun i hi _ ↦ hf i hi

@[to_additive]
lemma mul_le_prod [MulLeftMono N] {i j : ι} (hf : ∀ i ∈ s, 1 ≤ f i) (hi : i ∈ s) (hj : j ∈ s)
    (hne : i ≠ j) :
    f i * f j ≤ ∏ k ∈ s, f k :=
  calc
    f i * f j = ∏ k ∈ .cons i {j} (by simpa), f k := by rw [prod_cons, prod_singleton]
    _ ≤ ∏ k ∈ s, f k := by
      refine prod_le_prod_of_subset_of_one_le' ?_ fun k hk _ ↦ hf k hk
      simp [cons_subset, *]

@[to_additive sum_le_card_nsmul]
theorem prod_le_pow_card [MulLeftMono N] (s : Finset ι) (f : ι → N) (n : N) (h : ∀ x ∈ s, f x ≤ n) :
    s.prod f ≤ n ^ #s := by
  refine (Multiset.prod_le_pow_card (s.val.map f) n ?_).trans ?_
  · simpa using h
  · simp

@[to_additive card_nsmul_le_sum]
theorem pow_card_le_prod [MulLeftMono N] (s : Finset ι) (f : ι → N) (n : N) (h : ∀ x ∈ s, n ≤ f x) :
    n ^ #s ≤ s.prod f := Finset.prod_le_pow_card (N := Nᵒᵈ) _ _ _ h

lemma le_prod_max_one {N : Type*} [CommMonoidWithZero N] [LinearOrder N] [ZeroLEOneClass N]
    [PosMulMono N] {i : α} (hi : i ∈ s) (f : α → N) :
    f i ≤ ∏ i ∈ s, max (f i) 1 := by
  classical
  rcases lt_or_ge (f i) 0 with hf | hf
  · exact (hf.trans_le <| prod_nonneg fun _ _ ↦ le_sup_of_le_right zero_le_one).le
  have : f i = ∏ j ∈ s, if i = j then f i else 1 := by
    rw [prod_eq_single_of_mem i hi fun _ _ _ ↦ by grind]
    simp
  exact this ▸ prod_le_prod₀ (fun _ _ ↦ by grind [zero_le_one]) fun _ _ ↦ by grind

end PosMulMono

section PosMulStrictMono
variable [PartialOrder M] [ZeroLEOneClass M] [PosMulStrictMono M] [Nontrivial M]
  {f g : α → M} {s t : Finset α}

lemma prod_pos (h0 : ∀ i ∈ s, 0 < f i) : 0 < ∏ i ∈ s, f i :=
  prod_induction f (fun x ↦ 0 < x) (fun _ _ ha hb ↦ mul_pos ha hb) zero_lt_one h0

lemma prod_lt_prod (hf : ∀ i ∈ s, 0 < f i) (hfg : ∀ i ∈ s, f i ≤ g i)
    (hlt : ∃ i ∈ s, f i < g i) :
    ∏ i ∈ s, f i < ∏ i ∈ s, g i := by
  classical
  obtain ⟨i, hi, hilt⟩ := hlt
  rw [← insert_erase hi, prod_insert (notMem_erase _ _), prod_insert (notMem_erase _ _)]
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹PosMulStrictMono M›
  refine mul_lt_mul_of_pos_of_nonneg' hilt ?_ ?_ ?_
  · exact prod_le_prod₀ (fun j hj => le_of_lt (hf j (mem_of_mem_erase hj)))
      (fun _ hj ↦ hfg _ <| mem_of_mem_erase hj)
  · exact prod_pos fun j hj => hf j (mem_of_mem_erase hj)
  · exact (hf i hi).le.trans hilt.le

lemma prod_lt_prod_of_nonempty (hf : ∀ i ∈ s, 0 < f i) (hfg : ∀ i ∈ s, f i < g i)
    (h_ne : s.Nonempty) :
    ∏ i ∈ s, f i < ∏ i ∈ s, g i := by
  apply prod_lt_prod hf fun i hi => le_of_lt (hfg i hi)
  obtain ⟨i, hi⟩ := h_ne
  exact ⟨i, hi, hfg i hi⟩

end PosMulStrictMono

end CommMonoidWithZero

end Finset
