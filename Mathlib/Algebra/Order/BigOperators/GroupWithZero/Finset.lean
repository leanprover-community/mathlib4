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
