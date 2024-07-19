/-
Copyright (c) 2022 Yaël Dillies, George Shakan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, George Shakan
-/
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Pointwise
import Mathlib.Tactic.GCongr

/-!
# The Plünnecke-Ruzsa inequality

This file proves Ruzsa's triangle inequality, the Plünnecke-Petridis lemma, and the Plünnecke-Ruzsa
inequality.

## Main declarations

* `Finset.ruzsa_triangle_inequality_sub_sub_sub`: The Ruzsa triangle inequality, difference version.
* `Finset.ruzsa_triangle_inequality_add_add_add`: The Ruzsa triangle inequality, sum version.
* `Finset.pluennecke_petridis_inequality_add`: The Plünnecke-Petridis inequality.
* `Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add`: The Plünnecke-Ruzsa inequality.

## References

* [Giorgis Petridis, *The Plünnecke-Ruzsa inequality: an overview*][petridis2014]
* [Terrence Tao, Van Vu, *Additive Combinatorics][tao-vu]
-/

open Nat
open scoped Pointwise
namespace Finset

variable {α : Type*} [CommGroup α] [DecidableEq α] {A B C : Finset α}

/-- **Ruzsa's triangle inequality**. Division version. -/
@[to_additive "**Ruzsa's triangle inequality**. Subtraction version."]
theorem ruzsa_triangle_inequality_div_div_div (A B C : Finset α) :
    (A / C).card * B.card ≤ (A / B).card * (B / C).card := by
  rw [← card_product (A / B), ← mul_one ((A / B) ×ˢ (B / C)).card]
  refine card_mul_le_card_mul (fun b ac ↦ ac.1 * ac.2 = b) (fun x hx ↦ ?_)
    fun x _ ↦ card_le_one_iff.2 fun hu hv ↦
      ((mem_bipartiteBelow _).1 hu).2.symm.trans ?_
  · obtain ⟨a, ha, c, hc, rfl⟩ := mem_div.1 hx
    refine card_le_card_of_injOn (fun b ↦ (a / b, b / c)) (fun b hb ↦ ?_) fun b₁ _ b₂ _ h ↦ ?_
    · rw [mem_bipartiteAbove]
      exact ⟨mk_mem_product (div_mem_div ha hb) (div_mem_div hb hc), div_mul_div_cancel' _ _ _⟩
    · exact div_right_injective (Prod.ext_iff.1 h).1
  · exact ((mem_bipartiteBelow _).1 hv).2

/-- **Ruzsa's triangle inequality**. Div-mul-mul version. -/
@[to_additive "**Ruzsa's triangle inequality**. Sub-add-add version."]
theorem ruzsa_triangle_inequality_div_mul_mul (A B C : Finset α) :
    (A / C).card * B.card ≤ (A * B).card * (B * C).card := by
  rw [← div_inv_eq_mul, ← card_inv B, ← card_inv (B * C), mul_inv, ← div_eq_mul_inv]
  exact ruzsa_triangle_inequality_div_div_div _ _ _

/-- **Ruzsa's triangle inequality**. Mul-div-mul version. -/
@[to_additive "**Ruzsa's triangle inequality**. Add-sub-add version."]
theorem ruzsa_triangle_inequality_mul_div_mul (A B C : Finset α) :
    (A * C).card * B.card ≤ (A / B).card * (B * C).card := by
  rw [← div_inv_eq_mul, ← div_inv_eq_mul B]
  exact ruzsa_triangle_inequality_div_div_div _ _ _

/-- **Ruzsa's triangle inequality**. Mul-mul-div version. -/
@[to_additive "**Ruzsa's triangle inequality**. Add-add-sub version."]
theorem ruzsa_triangle_inequality_mul_mul_div (A B C : Finset α) :
    (A * C).card * B.card ≤ (A * B).card * (B / C).card := by
  rw [← div_inv_eq_mul, div_eq_mul_inv B]
  exact ruzsa_triangle_inequality_div_mul_mul _ _ _

@[to_additive]
theorem pluennecke_petridis_inequality_mul (C : Finset α)
    (hA : ∀ A' ⊆ A, (A * B).card * A'.card ≤ (A' * B).card * A.card) :
    (A * B * C).card * A.card ≤ (A * B).card * (A * C).card := by
  induction' C using Finset.induction_on with x C _ ih
  · simp
  set A' := A ∩ (A * C / {x}) with hA'
  set C' := insert x C with hC'
  have h₀ : A' * {x} = A * {x} ∩ (A * C) := by
    rw [hA', inter_mul_singleton, (isUnit_singleton x).div_mul_cancel]
  have h₁ : A * B * C' = A * B * C ∪ (A * B * {x}) \ (A' * B * {x}) := by
    rw [hC', insert_eq, union_comm, mul_union]
    refine (sup_sdiff_eq_sup ?_).symm
    rw [mul_right_comm, mul_right_comm A, h₀]
    exact mul_subset_mul_right inter_subset_right
  have h₂ : A' * B * {x} ⊆ A * B * {x} :=
    mul_subset_mul_right (mul_subset_mul_right inter_subset_left)
  have h₃ : (A * B * C').card ≤ (A * B * C).card + (A * B).card - (A' * B).card := by
    rw [h₁]
    refine (card_union_le _ _).trans_eq ?_
    rw [card_sdiff h₂, ← add_tsub_assoc_of_le (card_le_card h₂), card_mul_singleton,
      card_mul_singleton]
  refine (mul_le_mul_right' h₃ _).trans ?_
  rw [tsub_mul, add_mul]
  refine (tsub_le_tsub (add_le_add_right ih _) <| hA _ inter_subset_left).trans_eq ?_
  rw [← mul_add, ← mul_tsub, ← hA', hC', insert_eq, mul_union, ← card_mul_singleton A x, ←
    card_mul_singleton A' x, add_comm (card _), h₀,
    eq_tsub_of_add_eq (card_union_add_card_inter _ _)]

/-! ### Sum triangle inequality -/


-- Auxiliary lemma for Ruzsa's triangle sum inequality, and the Plünnecke-Ruzsa inequality.
@[to_additive]
private theorem mul_aux (hA : A.Nonempty) (hAB : A ⊆ B)
    (h : ∀ A' ∈ B.powerset.erase ∅, ((A * C).card : ℚ≥0) / ↑A.card ≤ (A' * C).card / ↑A'.card) :
    ∀ A' ⊆ A, (A * C).card * A'.card ≤ (A' * C).card * A.card := by
  rintro A' hAA'
  obtain rfl | hA' := A'.eq_empty_or_nonempty
  · simp
  have hA₀ : (0 : ℚ≥0) < A.card := cast_pos.2 hA.card_pos
  have hA₀' : (0 : ℚ≥0) < A'.card := cast_pos.2 hA'.card_pos
  exact mod_cast
    (div_le_div_iff hA₀ hA₀').1
      (h _ <| mem_erase_of_ne_of_mem hA'.ne_empty <| mem_powerset.2 <| hAA'.trans hAB)

/-- **Ruzsa's triangle inequality**. Multiplication version. -/
@[to_additive "**Ruzsa's triangle inequality**. Addition version."]
theorem ruzsa_triangle_inequality_mul_mul_mul (A B C : Finset α) :
    (A * C).card * B.card ≤ (A * B).card * (B * C).card := by
  obtain rfl | hB := B.eq_empty_or_nonempty
  · simp
  have hB' : B ∈ B.powerset.erase ∅ := mem_erase_of_ne_of_mem hB.ne_empty (mem_powerset_self _)
  obtain ⟨U, hU, hUA⟩ :=
    exists_min_image (B.powerset.erase ∅) (fun U ↦ (U * A).card / U.card : _ → ℚ≥0) ⟨B, hB'⟩
  rw [mem_erase, mem_powerset, ← nonempty_iff_ne_empty] at hU
  refine cast_le.1 (?_ : (_ : ℚ≥0) ≤ _)
  push_cast
  refine (le_div_iff <| cast_pos.2 hB.card_pos).1 ?_
  rw [mul_div_right_comm, mul_comm _ B]
  refine (Nat.cast_le.2 <| card_le_card_mul_left _ hU.1).trans ?_
  refine le_trans ?_
    (mul_le_mul (hUA _ hB') (cast_le.2 <| card_le_card <| mul_subset_mul_right hU.2)
      (zero_le _) (zero_le _))
  rw [← mul_div_right_comm, ← mul_assoc]
  refine (le_div_iff <| cast_pos.2 hU.1.card_pos).2 ?_
  exact mod_cast pluennecke_petridis_inequality_mul C (mul_aux hU.1 hU.2 hUA)

/-- **Ruzsa's triangle inequality**. Mul-div-div version. -/
@[to_additive "**Ruzsa's triangle inequality**. Add-sub-sub version."]
theorem ruzsa_triangle_inequality_mul_div_div (A B C : Finset α) :
    (A * C).card * B.card ≤ (A / B).card * (B / C).card := by
  rw [div_eq_mul_inv, ← card_inv B, ← card_inv (B / C), inv_div', div_inv_eq_mul]
  exact ruzsa_triangle_inequality_mul_mul_mul _ _ _

/-- **Ruzsa's triangle inequality**. Div-mul-div version. -/
@[to_additive "**Ruzsa's triangle inequality**. Sub-add-sub version."]
theorem ruzsa_triangle_inequality_div_mul_div (A B C : Finset α) :
    (A / C).card * B.card ≤ (A * B).card * (B / C).card := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact ruzsa_triangle_inequality_mul_mul_mul _ _ _

/-- **Ruzsa's triangle inequality**. Div-div-mul version. -/
@[to_additive "**Ruzsa's triangle inequality**. Sub-sub-add version."]
theorem card_div_mul_le_card_div_mul_card_mul (A B C : Finset α) :
    (A / C).card * B.card ≤ (A / B).card * (B * C).card := by
  rw [← div_inv_eq_mul, div_eq_mul_inv]
  exact ruzsa_triangle_inequality_mul_div_div _ _ _

-- Auxiliary lemma towards the Plünnecke-Ruzsa inequality
@[to_additive]
private lemma card_mul_pow_le (hAB : ∀ A' ⊆ A, (A * B).card * A'.card ≤ (A' * B).card * A.card)
    (n : ℕ) : (A * B ^ n).card ≤ ((A * B).card / A.card : ℚ≥0) ^ n * A.card := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  induction' n with n ih
  · simp
  rw [_root_.pow_succ', ← mul_assoc, _root_.pow_succ', @mul_assoc ℚ≥0, ← mul_div_right_comm,
    le_div_iff, ← cast_mul]
  swap
  · exact cast_pos.2 hA.card_pos
  refine (Nat.cast_le.2 <| pluennecke_petridis_inequality_mul _ hAB).trans ?_
  rw [cast_mul]
  gcongr

/-- The **Plünnecke-Ruzsa inequality**. Multiplication version. Note that this is genuinely harder
than the division version because we cannot use a double counting argument. -/
@[to_additive "The **Plünnecke-Ruzsa inequality**. Addition version. Note that this is genuinely
harder than the subtraction version because we cannot use a double counting argument."]
theorem pluennecke_ruzsa_inequality_pow_div_pow_mul (hA : A.Nonempty) (B : Finset α) (m n : ℕ) :
    ((B ^ m / B ^ n).card) ≤ ((A * B).card / A.card : ℚ≥0) ^ (m + n) * A.card := by
  have hA' : A ∈ A.powerset.erase ∅ := mem_erase_of_ne_of_mem hA.ne_empty (mem_powerset_self _)
  obtain ⟨C, hC, hCA⟩ :=
    exists_min_image (A.powerset.erase ∅) (fun C ↦ (C * B).card / C.card : _ → ℚ≥0) ⟨A, hA'⟩
  rw [mem_erase, mem_powerset, ← nonempty_iff_ne_empty] at hC
  refine (mul_le_mul_right <| cast_pos.2 hC.1.card_pos).1 ?_
  norm_cast
  refine (Nat.cast_le.2 <| ruzsa_triangle_inequality_div_mul_mul _ _ _).trans ?_
  push_cast
  rw [mul_comm _ C]
  refine (mul_le_mul (card_mul_pow_le (mul_aux hC.1 hC.2 hCA) _)
    (card_mul_pow_le (mul_aux hC.1 hC.2 hCA) _) (zero_le _) (zero_le _)).trans ?_
  rw [mul_mul_mul_comm, ← pow_add, ← mul_assoc]
  gcongr ((?_ ^ _) * Nat.cast ?_) * _
  · exact hCA _ hA'
  · exact card_le_card hC.2

/-- The **Plünnecke-Ruzsa inequality**. Division version. -/
@[to_additive "The **Plünnecke-Ruzsa inequality**. Subtraction version."]
theorem pluennecke_ruzsa_inequality_pow_div_pow_div (hA : A.Nonempty) (B : Finset α) (m n : ℕ) :
    (B ^ m / B ^ n).card ≤ ((A / B).card / A.card : ℚ≥0) ^ (m + n) * A.card := by
  rw [← card_inv, inv_div', ← inv_pow, ← inv_pow, div_eq_mul_inv A]
  exact pluennecke_ruzsa_inequality_pow_div_pow_mul hA _ _ _

/-- Special case of the **Plünnecke-Ruzsa inequality**. Multiplication version. -/
@[to_additive "Special case of the **Plünnecke-Ruzsa inequality**. Addition version."]
theorem pluennecke_ruzsa_inequality_pow_mul (hA : A.Nonempty) (B : Finset α) (n : ℕ) :
    (B ^ n).card ≤ ((A * B).card / A.card : ℚ≥0) ^ n * A.card := by
  simpa only [_root_.pow_zero, div_one] using pluennecke_ruzsa_inequality_pow_div_pow_mul hA _ _ 0

/-- Special case of the **Plünnecke-Ruzsa inequality**. Division version. -/
@[to_additive "Special case of the **Plünnecke-Ruzsa inequality**. Subtraction version."]
theorem pluennecke_ruzsa_inequality_pow_div (hA : A.Nonempty) (B : Finset α) (n : ℕ) :
    (B ^ n).card ≤ ((A / B).card / A.card : ℚ≥0) ^ n * A.card := by
  simpa only [_root_.pow_zero, div_one] using pluennecke_ruzsa_inequality_pow_div_pow_div hA _ _ 0

end Finset
