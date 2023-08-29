/-
Copyright (c) 2022 Yaël Dillies, George Shakan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, George Shakan
-/
import Mathlib.Combinatorics.DoubleCounting
import Mathlib.Data.Finset.Pointwise
import Mathlib.Data.Rat.NNRat
import Mathlib.Tactic.GCongr

#align_import combinatorics.additive.pluennecke_ruzsa from "leanprover-community/mathlib"@"4aab2abced69a9e579b1e6dc2856ed3db48e2cbd"

/-!
# The Plünnecke-Ruzsa inequality

This file proves Ruzsa's triangle inequality, the Plünnecke-Petridis lemma, and the Plünnecke-Ruzsa
inequality.

## Main declarations

* `Finset.card_sub_mul_le_card_sub_mul_card_sub`: Ruzsa's triangle inequality, difference version.
* `Finset.card_add_mul_le_card_add_mul_card_add`: Ruzsa's triangle inequality, sum version.
* `Finset.pluennecke_petridis`: The Plünnecke-Petridis lemma.
* `Finset.card_smul_div_smul_le`: The Plünnecke-Ruzsa inequality.

## References

* [Giorgis Petridis, *The Plünnecke-Ruzsa inequality: an overview*][petridis2014]
* [Terrence Tao, Van Vu, *Additive Combinatorics][tao-vu]
-/


open Nat

open NNRat Pointwise

namespace Finset

variable {α : Type*} [CommGroup α] [DecidableEq α] {A B C : Finset α}

/-- **Ruzsa's triangle inequality**. Division version. -/
@[to_additive card_sub_mul_le_card_sub_mul_card_sub
      "**Ruzsa's triangle inequality**. Subtraction version."]
theorem card_div_mul_le_card_div_mul_card_div (A B C : Finset α) :
    (A / C).card * B.card ≤ (A / B).card * (B / C).card := by
  rw [← card_product (A / B), ← mul_one ((A / B) ×ˢ (B / C)).card]
  -- ⊢ card (A / C) * card B ≤ card ((A / B) ×ˢ (B / C)) * 1
  refine' card_mul_le_card_mul (fun b ac ↦ ac.1 * ac.2 = b) (fun x hx ↦ _)
    fun x _ ↦ card_le_one_iff.2 fun hu hv ↦
      ((mem_bipartiteBelow _).1 hu).2.symm.trans ((mem_bipartiteBelow _).1 hv).2
  obtain ⟨a, c, ha, hc, rfl⟩ := mem_div.1 hx
  -- ⊢ card B ≤ card (bipartiteAbove (fun b ac => ac.fst * ac.snd = b) ((A / B) ×ˢ  …
  refine' card_le_card_of_inj_on (fun b ↦ (a / b, b / c)) (fun b hb ↦ _) fun b₁ _ b₂ _ h ↦ _
  -- ⊢ (fun b => (a / b, b / c)) b ∈ bipartiteAbove (fun b ac => ac.fst * ac.snd =  …
  · rw [mem_bipartiteAbove]
    -- ⊢ (fun b => (a / b, b / c)) b ∈ (A / B) ×ˢ (B / C) ∧ ((fun b => (a / b, b / c) …
    exact ⟨mk_mem_product (div_mem_div ha hb) (div_mem_div hb hc), div_mul_div_cancel' _ _ _⟩
    -- 🎉 no goals
  · exact div_right_injective (Prod.ext_iff.1 h).1
    -- 🎉 no goals
#align finset.card_div_mul_le_card_div_mul_card_div Finset.card_div_mul_le_card_div_mul_card_div
#align finset.card_sub_mul_le_card_sub_mul_card_sub Finset.card_sub_mul_le_card_sub_mul_card_sub

/-- **Ruzsa's triangle inequality**. Div-mul-mul version. -/
@[to_additive card_sub_mul_le_card_add_mul_card_add
      "**Ruzsa's triangle inequality**. Sub-add-add version."]
theorem card_div_mul_le_card_mul_mul_card_mul (A B C : Finset α) :
    (A / C).card * B.card ≤ (A * B).card * (B * C).card := by
  rw [← div_inv_eq_mul, ← card_inv B, ← card_inv (B * C), mul_inv, ← div_eq_mul_inv]
  -- ⊢ card (A / C) * card B⁻¹ ≤ card (A / B⁻¹) * card (B⁻¹ / C)
  exact card_div_mul_le_card_div_mul_card_div _ _ _
  -- 🎉 no goals
#align finset.card_div_mul_le_card_mul_mul_card_mul Finset.card_div_mul_le_card_mul_mul_card_mul
#align finset.card_sub_mul_le_card_add_mul_card_add Finset.card_sub_mul_le_card_add_mul_card_add

/-- **Ruzsa's triangle inequality**. Mul-div-div version. -/
@[to_additive card_add_mul_le_card_sub_mul_card_add
      "**Ruzsa's triangle inequality**. Add-sub-sub version."]
theorem card_mul_mul_le_card_div_mul_card_mul (A B C : Finset α) :
    (A * C).card * B.card ≤ (A / B).card * (B * C).card := by
  rw [← div_inv_eq_mul, ← div_inv_eq_mul B]
  -- ⊢ card (A / C⁻¹) * card B ≤ card (A / B) * card (B / C⁻¹)
  exact card_div_mul_le_card_div_mul_card_div _ _ _
  -- 🎉 no goals
#align finset.card_mul_mul_le_card_div_mul_card_mul Finset.card_mul_mul_le_card_div_mul_card_mul
#align finset.card_add_mul_le_card_sub_mul_card_add Finset.card_add_mul_le_card_sub_mul_card_add

/-- **Ruzsa's triangle inequality**. Mul-mul-div version. -/
@[to_additive card_add_mul_le_card_add_mul_card_sub
      "**Ruzsa's triangle inequality**. Add-add-sub version."]
theorem card_mul_mul_le_card_mul_mul_card_div (A B C : Finset α) :
    (A * C).card * B.card ≤ (A * B).card * (B / C).card := by
  rw [← div_inv_eq_mul, div_eq_mul_inv B]
  -- ⊢ card (A / C⁻¹) * card B ≤ card (A * B) * card (B * C⁻¹)
  exact card_div_mul_le_card_mul_mul_card_mul _ _ _
  -- 🎉 no goals
#align finset.card_mul_mul_le_card_mul_mul_card_div Finset.card_mul_mul_le_card_mul_mul_card_div
#align finset.card_add_mul_le_card_add_mul_card_sub Finset.card_add_mul_le_card_add_mul_card_sub

@[to_additive]
theorem mul_pluennecke_petridis (C : Finset α)
    (hA : ∀ (A') (_ : A' ⊆ A), (A * B).card * A'.card ≤ (A' * B).card * A.card) :
    (A * B * C).card * A.card ≤ (A * B).card * (A * C).card := by
  induction' C using Finset.induction_on with x C _ ih
  -- ⊢ card (A * B * ∅) * card A ≤ card (A * B) * card (A * ∅)
  · simp
    -- 🎉 no goals
  set A' := A ∩ (A * C / {x}) with hA'
  -- ⊢ card (A * B * insert x C) * card A ≤ card (A * B) * card (A * insert x C)
  set C' := insert x C with hC'
  -- ⊢ card (A * B * C') * card A ≤ card (A * B) * card (A * C')
  have h₀ : A' * {x} = A * {x} ∩ (A * C) := by
    rw [hA', inter_mul_singleton, (isUnit_singleton x).div_mul_cancel]
  have h₁ : A * B * C' = A * B * C ∪ (A * B * {x}) \ (A' * B * {x}) := by
    rw [hC', insert_eq, union_comm, mul_union]
    refine' (sup_sdiff_eq_sup _).symm
    rw [mul_right_comm, mul_right_comm A, h₀]
    exact mul_subset_mul_right (inter_subset_right _ _)
  have h₂ : A' * B * {x} ⊆ A * B * {x} :=
    mul_subset_mul_right (mul_subset_mul_right <| inter_subset_left _ _)
  have h₃ : (A * B * C').card ≤ (A * B * C).card + (A * B).card - (A' * B).card := by
    rw [h₁]
    refine' (card_union_le _ _).trans_eq _
    rw [card_sdiff h₂, ← add_tsub_assoc_of_le (card_le_of_subset h₂), card_mul_singleton,
      card_mul_singleton]
  refine' (mul_le_mul_right' h₃ _).trans _
  -- ⊢ (card (A * B * C) + card (A * B) - card (A' * B)) * card A ≤ card (A * B) *  …
  rw [tsub_mul, add_mul]
  -- ⊢ card (A * B * C) * card A + card (A * B) * card A - card (A' * B) * card A ≤ …
  refine' (tsub_le_tsub (add_le_add_right ih _) <| hA _ <| inter_subset_left _ _).trans_eq _
  -- ⊢ card (A * B) * card (A * C) + card (A * B) * card A - card (A * B) * card (A …
  rw [← mul_add, ← mul_tsub, ← hA', hC', insert_eq, mul_union, ← card_mul_singleton A x, ←
    card_mul_singleton A' x, add_comm (card _), h₀,
    eq_tsub_of_add_eq (card_union_add_card_inter _ _)]
#align finset.mul_pluennecke_petridis Finset.mul_pluennecke_petridis
#align finset.add_pluennecke_petridis Finset.add_pluennecke_petridis

/-! ### Sum triangle inequality -/


-- Auxiliary lemma for Ruzsa's triangle sum inequality, and the Plünnecke-Ruzsa inequality.
@[to_additive]
private theorem mul_aux (hA : A.Nonempty) (hAB : A ⊆ B)
    (h : ∀ A' ∈ B.powerset.erase ∅, ((A * C).card : ℚ≥0) / ↑A.card ≤ (A' * C).card / ↑A'.card) :
    ∀ (A') (_ : A' ⊆ A), (A * C).card * A'.card ≤ (A' * C).card * A.card := by
  rintro A' hAA'
  -- ⊢ card (A * C) * card A' ≤ card (A' * C) * card A
  obtain rfl | hA' := A'.eq_empty_or_nonempty
  -- ⊢ card (A * C) * card ∅ ≤ card (∅ * C) * card A
  · simp
    -- 🎉 no goals
  have hA₀ : (0 : ℚ≥0) < A.card := cast_pos.2 hA.card_pos
  -- ⊢ card (A * C) * card A' ≤ card (A' * C) * card A
  have hA₀' : (0 : ℚ≥0) < A'.card := cast_pos.2 hA'.card_pos
  -- ⊢ card (A * C) * card A' ≤ card (A' * C) * card A
  exact_mod_cast
    (div_le_div_iff hA₀ hA₀').1
      (h _ <| mem_erase_of_ne_of_mem hA'.ne_empty <| mem_powerset.2 <| hAA'.trans hAB)

/-- **Ruzsa's triangle inequality**. Multiplication version. -/
@[to_additive card_add_mul_card_le_card_add_mul_card_add
      "**Ruzsa's triangle inequality**. Addition version."]
theorem card_mul_mul_card_le_card_mul_mul_card_mul (A B C : Finset α) :
    (A * C).card * B.card ≤ (A * B).card * (B * C).card := by
  obtain rfl | hB := B.eq_empty_or_nonempty
  -- ⊢ card (A * C) * card ∅ ≤ card (A * ∅) * card (∅ * C)
  · simp
    -- 🎉 no goals
  have hB' : B ∈ B.powerset.erase ∅ := mem_erase_of_ne_of_mem hB.ne_empty (mem_powerset_self _)
  -- ⊢ card (A * C) * card B ≤ card (A * B) * card (B * C)
  obtain ⟨U, hU, hUA⟩ :=
    exists_min_image (B.powerset.erase ∅) (fun U ↦ (U * A).card / U.card : _ → ℚ≥0) ⟨B, hB'⟩
  rw [mem_erase, mem_powerset, ← nonempty_iff_ne_empty] at hU
  -- ⊢ card (A * C) * card B ≤ card (A * B) * card (B * C)
  refine' cast_le.1 (_ : (_ : ℚ≥0) ≤ _)
  -- ⊢ ↑(card (A * C) * card B) ≤ ↑(card (A * B) * card (B * C))
  push_cast
  -- ⊢ ↑(card (A * C)) * ↑(card B) ≤ ↑(card (A * B)) * ↑(card (B * C))
  refine' (le_div_iff <| cast_pos.2 hB.card_pos).1 _
  -- ⊢ ↑(card (A * C)) ≤ ↑(card (A * B)) * ↑(card (B * C)) / ↑(card B)
  rw [mul_div_right_comm, mul_comm _ B]
  -- ⊢ ↑(card (A * C)) ≤ ↑(card (B * A)) / ↑(card B) * ↑(card (B * C))
  refine' (cast_le.2 <| card_le_card_mul_left _ hU.1).trans _
  -- ⊢ ↑(card (U * (A * C))) ≤ ↑(card (B * A)) / ↑(card B) * ↑(card (B * C))
  refine' le_trans _
    (mul_le_mul (hUA _ hB') (cast_le.2 <| card_le_of_subset <| mul_subset_mul_right hU.2)
      (zero_le _) (zero_le _))
  rw [← mul_div_right_comm, ← mul_assoc]
  -- ⊢ ↑(card (U * A * C)) ≤ ↑(card (U * A)) * ↑(card (U * C)) / ↑(card U)
  refine' (le_div_iff <| cast_pos.2 hU.1.card_pos).2 _
  -- ⊢ ↑(card (U * A * C)) * ↑(card U) ≤ ↑(card (U * A)) * ↑(card (U * C))
  exact_mod_cast mul_pluennecke_petridis C (mul_aux hU.1 hU.2 hUA)
  -- 🎉 no goals
#align finset.card_mul_mul_card_le_card_mul_mul_card_mul Finset.card_mul_mul_card_le_card_mul_mul_card_mul
#align finset.card_add_mul_card_le_card_add_mul_card_add Finset.card_add_mul_card_le_card_add_mul_card_add

/-- **Ruzsa's triangle inequality**. Add-sub-sub version. -/
theorem card_mul_mul_le_card_div_mul_card_div (A B C : Finset α) :
    (A * C).card * B.card ≤ (A / B).card * (B / C).card := by
  rw [div_eq_mul_inv, ← card_inv B, ← card_inv (B / C), inv_div', div_inv_eq_mul]
  -- ⊢ card (A * C) * card B⁻¹ ≤ card (A * B⁻¹) * card (B⁻¹ * C)
  exact card_mul_mul_card_le_card_mul_mul_card_mul _ _ _
  -- 🎉 no goals
#align finset.card_mul_mul_le_card_div_mul_card_div Finset.card_mul_mul_le_card_div_mul_card_div

/-- **Ruzsa's triangle inequality**. Sub-add-sub version. -/
theorem card_div_mul_le_card_mul_mul_card_div (A B C : Finset α) :
    (A / C).card * B.card ≤ (A * B).card * (B / C).card := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  -- ⊢ card (A * C⁻¹) * card B ≤ card (A * B) * card (B * C⁻¹)
  exact card_mul_mul_card_le_card_mul_mul_card_mul _ _ _
  -- 🎉 no goals
#align finset.card_div_mul_le_card_mul_mul_card_div Finset.card_div_mul_le_card_mul_mul_card_div

/-- **Ruzsa's triangle inequality**. Sub-sub-add version. -/
theorem card_div_mul_le_card_div_mul_card_mul (A B C : Finset α) :
    (A / C).card * B.card ≤ (A / B).card * (B * C).card := by
  rw [← div_inv_eq_mul, div_eq_mul_inv]
  -- ⊢ card (A * C⁻¹) * card B ≤ card (A / B) * card (B / C⁻¹)
  exact card_mul_mul_le_card_div_mul_card_div _ _ _
  -- 🎉 no goals
#align finset.card_div_mul_le_card_div_mul_card_mul Finset.card_div_mul_le_card_div_mul_card_mul

theorem card_add_nsmul_le {α : Type*} [AddCommGroup α] [DecidableEq α] {A B : Finset α}
    (hAB : ∀ (A') (_ : A' ⊆ A), (A + B).card * A'.card ≤ (A' + B).card * A.card) (n : ℕ) :
    (A + n • B).card ≤ ((A + B).card / A.card : ℚ≥0) ^ n * A.card := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  -- ⊢ ↑(card (∅ + n • B)) ≤ (↑(card (∅ + B)) / ↑(card ∅)) ^ n * ↑(card ∅)
  · simp
    -- 🎉 no goals
  induction' n with n ih
  -- ⊢ ↑(card (A + zero • B)) ≤ (↑(card (A + B)) / ↑(card A)) ^ zero * ↑(card A)
  · simp
    -- 🎉 no goals
  rw [succ_nsmul, ← add_assoc, _root_.pow_succ, mul_assoc, ← mul_div_right_comm, le_div_iff,
    ← cast_mul]
  swap; exact cast_pos.2 hA.card_pos
  -- ⊢ 0 < ↑(card A)
        -- ⊢ ↑(card (A + B + n • B) * card A) ≤ ↑(card (A + B)) * ((↑(card (A + B)) / ↑(c …
  refine' (cast_le.2 <| add_pluennecke_petridis _ hAB).trans _
  -- ⊢ ↑(card (A + B) * card (A + n • B)) ≤ ↑(card (A + B)) * ((↑(card (A + B)) / ↑ …
  rw [cast_mul]
  -- ⊢ ↑(card (A + B)) * ↑(card (A + n • B)) ≤ ↑(card (A + B)) * ((↑(card (A + B))  …
  gcongr
  -- 🎉 no goals
#align finset.card_add_nsmul_le Finset.card_add_nsmul_le

@[to_additive existing]
theorem card_mul_pow_le (hAB : ∀ (A') (_ : A' ⊆ A), (A * B).card * A'.card ≤ (A' * B).card * A.card)
    (n : ℕ) : (A * B ^ n).card ≤ ((A * B).card / A.card : ℚ≥0) ^ n * A.card := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  -- ⊢ ↑(card (∅ * B ^ n)) ≤ (↑(card (∅ * B)) / ↑(card ∅)) ^ n * ↑(card ∅)
  · simp
    -- 🎉 no goals
  induction' n with n ih
  -- ⊢ ↑(card (A * B ^ zero)) ≤ (↑(card (A * B)) / ↑(card A)) ^ zero * ↑(card A)
  · simp
    -- 🎉 no goals
  rw [_root_.pow_succ, ← mul_assoc, _root_.pow_succ, @mul_assoc ℚ≥0, ← mul_div_right_comm,
    le_div_iff, ← cast_mul]
  swap; exact cast_pos.2 hA.card_pos
  -- ⊢ 0 < ↑(card A)
        -- ⊢ ↑(card (A * B * B ^ n) * card A) ≤ ↑(card (A * B)) * ((↑(card (A * B)) / ↑(c …
  refine' (cast_le.2 <| mul_pluennecke_petridis _ hAB).trans _
  -- ⊢ ↑(card (A * B) * card (A * B ^ n)) ≤ ↑(card (A * B)) * ((↑(card (A * B)) / ↑ …
  rw [cast_mul]
  -- ⊢ ↑(card (A * B)) * ↑(card (A * B ^ n)) ≤ ↑(card (A * B)) * ((↑(card (A * B))  …
  gcongr
  -- 🎉 no goals
#align finset.card_mul_pow_le Finset.card_mul_pow_le

/-- The **Plünnecke-Ruzsa inequality**. Multiplication version. Note that this is genuinely harder
than the division version because we cannot use a double counting argument. -/
@[to_additive "The **Plünnecke-Ruzsa inequality**. Addition version. Note that this is genuinely
harder than the subtraction version because we cannot use a double counting argument."]
theorem card_pow_div_pow_le (hA : A.Nonempty) (B : Finset α) (m n : ℕ) :
    ((B ^ m / B ^ n).card) ≤ ((A * B).card / A.card : ℚ≥0) ^ (m + n) * A.card := by
  have hA' : A ∈ A.powerset.erase ∅ := mem_erase_of_ne_of_mem hA.ne_empty (mem_powerset_self _)
  -- ⊢ ↑(card (B ^ m / B ^ n)) ≤ (↑(card (A * B)) / ↑(card A)) ^ (m + n) * ↑(card A)
  obtain ⟨C, hC, hCA⟩ :=
    exists_min_image (A.powerset.erase ∅) (fun C ↦ (C * B).card / C.card : _ → ℚ≥0) ⟨A, hA'⟩
  rw [mem_erase, mem_powerset, ← nonempty_iff_ne_empty] at hC
  -- ⊢ ↑(card (B ^ m / B ^ n)) ≤ (↑(card (A * B)) / ↑(card A)) ^ (m + n) * ↑(card A)
  refine' (mul_le_mul_right <| cast_pos.2 hC.1.card_pos).1 _
  -- ⊢ ↑(card (B ^ m / B ^ n)) * ↑(card C) ≤ (↑(card (A * B)) / ↑(card A)) ^ (m + n …
  norm_cast
  -- ⊢ ↑(card (B ^ m / B ^ n) * card C) ≤ (↑(card (A * B)) / ↑(card A)) ^ (m + n) * …
  refine' (cast_le.2 <| card_div_mul_le_card_mul_mul_card_mul _ _ _).trans _
  -- ⊢ ↑(card (B ^ m * C) * card (C * B ^ n)) ≤ (↑(card (A * B)) / ↑(card A)) ^ (m  …
  push_cast
  -- ⊢ ↑(card (B ^ m * C)) * ↑(card (C * B ^ n)) ≤ (↑(card (A * B)) / ↑(card A)) ^  …
  rw [mul_comm _ C]
  -- ⊢ ↑(card (C * B ^ m)) * ↑(card (C * B ^ n)) ≤ (↑(card (A * B)) / ↑(card A)) ^  …
  refine' (mul_le_mul (card_mul_pow_le (mul_aux hC.1 hC.2 hCA) _)
    (card_mul_pow_le (mul_aux hC.1 hC.2 hCA) _) (zero_le _) (zero_le _)).trans _
  rw [mul_mul_mul_comm, ← pow_add, ← mul_assoc]
  -- ⊢ (↑(card (C * B)) / ↑(card C)) ^ (m + n) * ↑(card C) * ↑(card C) ≤ (↑(card (A …
  gcongr ((?_ ^ _) * Nat.cast ?_) * _
  -- ⊢ ↑(card (C * B)) / ↑(card C) ≤ ↑(card (A * B)) / ↑(card A)
  · exact hCA _ hA'
    -- 🎉 no goals
  · exact card_le_of_subset hC.2
    -- 🎉 no goals
#align finset.card_pow_div_pow_le Finset.card_pow_div_pow_le
#align finset.card_nsmul_sub_nsmul_le Finset.card_nsmul_sub_nsmul_le

/-- The **Plünnecke-Ruzsa inequality**. Subtraction version. -/
@[to_additive "The **Plünnecke-Ruzsa inequality**. Subtraction version."]
theorem card_pow_div_pow_le' (hA : A.Nonempty) (B : Finset α) (m n : ℕ) :
    (B ^ m / B ^ n).card ≤ ((A / B).card / A.card : ℚ≥0) ^ (m + n) * A.card := by
  rw [← card_inv, inv_div', ← inv_pow, ← inv_pow, div_eq_mul_inv A]
  -- ⊢ ↑(card (B⁻¹ ^ m / B⁻¹ ^ n)) ≤ (↑(card (A * B⁻¹)) / ↑(card A)) ^ (m + n) * ↑( …
  exact card_pow_div_pow_le hA _ _ _
  -- 🎉 no goals
#align finset.card_pow_div_pow_le' Finset.card_pow_div_pow_le'
#align finset.card_nsmul_sub_nsmul_le' Finset.card_nsmul_sub_nsmul_le'

/-- Special case of the **Plünnecke-Ruzsa inequality**. Multiplication version. -/
@[to_additive "Special case of the **Plünnecke-Ruzsa inequality**. Addition version."]
theorem card_pow_le (hA : A.Nonempty) (B : Finset α) (n : ℕ) :
    (B ^ n).card ≤ ((A * B).card / A.card : ℚ≥0) ^ n * A.card := by
  simpa only [_root_.pow_zero, div_one] using card_pow_div_pow_le hA _ _ 0
  -- 🎉 no goals
#align finset.card_pow_le Finset.card_pow_le
#align finset.card_nsmul_le Finset.card_nsmul_le

/-- Special case of the **Plünnecke-Ruzsa inequality**. Division version. -/
@[to_additive "Special case of the **Plünnecke-Ruzsa inequality**. Subtraction version."]
theorem card_pow_le' (hA : A.Nonempty) (B : Finset α) (n : ℕ) :
    (B ^ n).card ≤ ((A / B).card / A.card : ℚ≥0) ^ n * A.card := by
  simpa only [_root_.pow_zero, div_one] using card_pow_div_pow_le' hA _ _ 0
  -- 🎉 no goals
#align finset.card_pow_le' Finset.card_pow_le'
#align finset.card_nsmul_le' Finset.card_nsmul_le'

end Finset
