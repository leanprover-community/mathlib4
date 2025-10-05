/-
Copyright (c) 2022 Yaël Dillies, George Shakan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, George Shakan
-/
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

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

## See also

In general non-abelian groups, small doubling doesn't imply small powers anymore, but small tripling
does. See `Mathlib/Combinatorics/Additive/SmallTripling.lean`.
-/

open MulOpposite Nat
open scoped Pointwise
namespace Finset
variable {G : Type*} [DecidableEq G]

section Group
variable [Group G] {A B C : Finset G}

/-! ### Noncommutative Ruzsa triangle inequality -/

/-- **Ruzsa's triangle inequality**. Division version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Subtraction version. -/]
theorem ruzsa_triangle_inequality_div_div_div (A B C : Finset G) :
    #(A / C) * #B ≤ #(A / B) * #(C / B) := by
  rw [← card_product (A / B), ← mul_one #((A / B) ×ˢ (C / B))]
  refine card_mul_le_card_mul (fun b (a, c) ↦ a / c = b) (fun x hx ↦ ?_)
    fun x _ ↦ card_le_one_iff.2 fun hu hv ↦
      ((mem_bipartiteBelow _).1 hu).2.symm.trans ?_
  · obtain ⟨a, ha, c, hc, rfl⟩ := mem_div.1 hx
    refine card_le_card_of_injOn (fun b ↦ (a / b, c / b)) (fun b hb ↦ ?_) fun b₁ _ b₂ _ h ↦ ?_
    · rw [mem_coe, mem_bipartiteAbove]
      exact ⟨mk_mem_product (div_mem_div ha hb) (div_mem_div hc hb), div_div_div_cancel_right ..⟩
    · exact div_right_injective (Prod.ext_iff.1 h).1
  · exact ((mem_bipartiteBelow _).1 hv).2

/-- **Ruzsa's triangle inequality**. Mulinv-mulinv-mulinv version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Addneg-addneg-addneg version. -/]
theorem ruzsa_triangle_inequality_mulInv_mulInv_mulInv (A B C : Finset G) :
    #(A * C⁻¹) * #B ≤ #(A * B⁻¹) * #(C * B⁻¹) := by
  simpa [div_eq_mul_inv] using ruzsa_triangle_inequality_div_div_div A B C

/-- **Ruzsa's triangle inequality**. Invmul-invmul-invmul version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Negadd-negadd-negadd version. -/]
theorem ruzsa_triangle_inequality_invMul_invMul_invMul (A B C : Finset G) :
    #B * #(A⁻¹ * C) ≤ #(B⁻¹ * A) * #(B⁻¹ * C) := by
  simpa [mul_comm, div_eq_mul_inv, ← map_op_mul, ← map_op_inv] using
    ruzsa_triangle_inequality_div_div_div (G := Gᵐᵒᵖ) (C.map opEquiv.toEmbedding)
      (B.map opEquiv.toEmbedding) (A.map opEquiv.toEmbedding)


/-- **Ruzsa's triangle inequality**. Div-mul-mul version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Sub-add-add version. -/]
theorem ruzsa_triangle_inequality_div_mul_mul (A B C : Finset G) :
    #(A / C) * #B ≤ #(A * B) * #(C * B) := by
  simpa using ruzsa_triangle_inequality_div_div_div A B⁻¹ C

/-- **Ruzsa's triangle inequality**. Mulinv-mul-mul version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Addneg-add-add version. -/]
theorem ruzsa_triangle_inequality_mulInv_mul_mul (A B C : Finset G) :
    #(A * C⁻¹) * #B ≤ #(A * B) * #(C * B) := by
  simpa using ruzsa_triangle_inequality_mulInv_mulInv_mulInv A B⁻¹ C

/-- **Ruzsa's triangle inequality**. Invmul-mul-mul version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Negadd-add-add version. -/]
theorem ruzsa_triangle_inequality_invMul_mul_mul (A B C : Finset G) :
    #B * #(A⁻¹ * C) ≤ #(B * A) * #(B * C) := by
  simpa using ruzsa_triangle_inequality_invMul_invMul_invMul A B⁻¹ C


/-- **Ruzsa's triangle inequality**. Mul-div-mul version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Add-sub-add version. -/]
theorem ruzsa_triangle_inequality_mul_div_mul (A B C : Finset G) :
    #B * #(A * C) ≤ #(B / A) * #(B * C) := by
  simpa [div_eq_mul_inv] using ruzsa_triangle_inequality_invMul_mul_mul A⁻¹ B C

/-- **Ruzsa's triangle inequality**. Mul-mulinv-mul version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Add-addneg-add version. -/]
theorem ruzsa_triangle_inequality_mul_mulInv_mul (A B C : Finset G) :
    #B * #(A * C) ≤ #(B * A⁻¹) * #(B * C) := by
  simpa [div_eq_mul_inv] using ruzsa_triangle_inequality_mul_div_mul A B C

/-- **Ruzsa's triangle inequality**. Mul-mul-invmul version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Add-add-negadd version. -/]
theorem ruzsa_triangle_inequality_mul_mul_invMul (A B C : Finset G) :
    #(A * C) * #B ≤ #(A * B) * #(C⁻¹ * B) := by
  simpa using ruzsa_triangle_inequality_mulInv_mul_mul A B C⁻¹

/-! ### Plünnecke-Petridis inequality -/

@[to_additive]
theorem pluennecke_petridis_inequality_mul (C : Finset G)
    (hA : ∀ A' ⊆ A, #(A * B) * #A' ≤ #(A' * B) * #A) :
    #(C * A * B) * #A ≤ #(A * B) * #(C * A) := by
  induction C using Finset.induction_on with
  | empty => simp
  | insert x C _ ih =>
    set A' := A ∩ ({x}⁻¹ * C * A) with hA'
    set C' := insert x C with hC'
    have h₀ : {x} * A' = {x} * A ∩ (C * A) := by
      rw [hA', mul_assoc, singleton_mul_inter, (isUnit_singleton x).mul_inv_cancel_left]
    have h₁ : C' * A * B = C * A * B ∪ ({x} * A * B) \ ({x} * A' * B) := by
      rw [hC', insert_eq, union_comm, union_mul, union_mul]
      refine (sup_sdiff_eq_sup ?_).symm
      rw [h₀]
      gcongr
      exact inter_subset_right
    have h₂ : {x} * A' * B ⊆ {x} * A * B := by gcongr; exact inter_subset_left
    have h₃ : #(C' * A * B) ≤ #(C * A * B) + #(A * B) - #(A' * B) := by
      rw [h₁]
      refine (card_union_le _ _).trans_eq ?_
      rw [card_sdiff_of_subset h₂, ← add_tsub_assoc_of_le (card_le_card h₂), mul_assoc {_},
        mul_assoc {_}, card_singleton_mul, card_singleton_mul]
    refine (mul_le_mul_left h₃ _).trans ?_
    rw [tsub_mul, add_mul]
    refine (tsub_le_tsub (add_le_add_right ih _) <| hA _ inter_subset_left).trans_eq ?_
    rw [← mul_add, ← mul_tsub, ← hA', hC', insert_eq, union_mul, ← card_singleton_mul x A, ←
      card_singleton_mul x A', add_comm #_, h₀, eq_tsub_of_add_eq (card_union_add_card_inter _ _)]

end Group

section CommGroup
variable [CommGroup G] {A B C : Finset G}

/-! ### Commutative Ruzsa triangle inequality -/

-- Auxiliary lemma for Ruzsa's triangle sum inequality, and the Plünnecke-Ruzsa inequality.
@[to_additive]
private theorem mul_aux (hA : A.Nonempty) (hAB : A ⊆ B)
    (h : ∀ A' ∈ B.powerset.erase ∅, (#(A * C) : ℚ≥0) / #A ≤ #(A' * C) / #A') :
    ∀ A' ⊆ A, #(A * C) * #A' ≤ #(A' * C) * #A := by
  rintro A' hAA'
  obtain rfl | hA' := A'.eq_empty_or_nonempty
  · simp
  have hA₀ : (0 : ℚ≥0) < #A := cast_pos.2 hA.card_pos
  have hA₀' : (0 : ℚ≥0) < #A' := cast_pos.2 hA'.card_pos
  exact mod_cast
    (div_le_div_iff₀ hA₀ hA₀').1
      (h _ <| mem_erase_of_ne_of_mem hA'.ne_empty <| mem_powerset.2 <| hAA'.trans hAB)

/-- **Ruzsa's triangle inequality**. Multiplication version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Addition version. -/]
theorem ruzsa_triangle_inequality_mul_mul_mul (A B C : Finset G) :
    #(A * C) * #B ≤ #(A * B) * #(B * C) := by
  obtain rfl | hB := B.eq_empty_or_nonempty
  · simp
  have hB' : B ∈ B.powerset.erase ∅ := mem_erase_of_ne_of_mem hB.ne_empty (mem_powerset_self _)
  obtain ⟨U, hU, hUA⟩ :=
    exists_min_image (B.powerset.erase ∅) (fun U ↦ #(U * A) / #U : _ → ℚ≥0) ⟨B, hB'⟩
  rw [mem_erase, mem_powerset, ← nonempty_iff_ne_empty] at hU
  refine cast_le.1 (?_ : (_ : ℚ≥0) ≤ _)
  push_cast
  rw [← le_div_iff₀ (cast_pos.2 hB.card_pos), mul_div_right_comm, mul_comm _ B]
  refine (Nat.cast_le.2 <| card_le_card_mul_left hU.1).trans ?_
  refine le_trans ?_
    (mul_le_mul (hUA _ hB') (cast_le.2 <| card_le_card <| mul_subset_mul_right hU.2)
      (zero_le _) (zero_le _))
  rw [← mul_div_right_comm, ← mul_assoc, le_div_iff₀ (cast_pos.2 hU.1.card_pos), mul_comm _ C,
    ← mul_assoc, mul_comm _ C]
  exact mod_cast pluennecke_petridis_inequality_mul C (mul_aux hU.1 hU.2 hUA)

/-- **Ruzsa's triangle inequality**. Mul-div-div version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Add-sub-sub version. -/]
theorem ruzsa_triangle_inequality_mul_div_div (A B C : Finset G) :
    #(A * C) * #B ≤ #(A / B) * #(B / C) := by
  rw [div_eq_mul_inv, ← card_inv B, ← card_inv (B / C), inv_div', div_inv_eq_mul]
  exact ruzsa_triangle_inequality_mul_mul_mul _ _ _

/-- **Ruzsa's triangle inequality**. Div-mul-div version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Sub-add-sub version. -/]
theorem ruzsa_triangle_inequality_div_mul_div (A B C : Finset G) :
    #(A / C) * #B ≤ #(A * B) * #(B / C) := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact ruzsa_triangle_inequality_mul_mul_mul _ _ _

/-- **Ruzsa's triangle inequality**. Div-div-mul version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Sub-sub-add version. -/]
theorem card_div_mul_le_card_div_mul_card_mul (A B C : Finset G) :
    #(A / C) * #B ≤ #(A / B) * #(B * C) := by
  rw [← div_inv_eq_mul, div_eq_mul_inv]
  exact ruzsa_triangle_inequality_mul_div_div _ _ _

-- Auxiliary lemma towards the Plünnecke-Ruzsa inequality
@[to_additive]
private lemma card_mul_pow_le (hAB : ∀ A' ⊆ A, #(A * B) * #A' ≤ #(A' * B) * #A) (n : ℕ) :
    #(A * B ^ n) ≤ (#(A * B) / #A : ℚ≥0) ^ n * #A := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  induction n with
  | zero => simp
  | succ n ih =>
    refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℚ≥0) < #A)
    calc
      ((#(A * B ^ (n + 1))) * #A : ℚ≥0)
        = #(B ^ n * A * B) * #A := by rw [pow_succ, mul_left_comm, mul_assoc]
      _ ≤ #(A * B) * #(B ^ n * A) := mod_cast pluennecke_petridis_inequality_mul _ hAB
      _ ≤ #(A * B) * ((#(A * B) / #A) ^ n * #A) := by rw [mul_comm _ A]; gcongr
      _ = (#(A * B) / #A) ^ (n + 1) * #A * #A := by simp [field, pow_add]

/-- The **Plünnecke-Ruzsa inequality**. Multiplication version. Note that this is genuinely harder
than the division version because we cannot use a double counting argument. -/
@[to_additive /-- The **Plünnecke-Ruzsa inequality**. Addition version. Note that this is genuinely
harder than the subtraction version because we cannot use a double counting argument. -/]
theorem pluennecke_ruzsa_inequality_pow_div_pow_mul (hA : A.Nonempty) (B : Finset G) (m n : ℕ) :
    #(B ^ m / B ^ n) ≤ (#(A * B) / #A : ℚ≥0) ^ (m + n) * #A := by
  have hA' : A ∈ A.powerset.erase ∅ := mem_erase_of_ne_of_mem hA.ne_empty (mem_powerset_self _)
  obtain ⟨C, hC, hCmin⟩ :=
    exists_min_image (A.powerset.erase ∅) (fun C ↦ #(C * B) / #C : _ → ℚ≥0) ⟨A, hA'⟩
  rw [mem_erase, mem_powerset, ← nonempty_iff_ne_empty] at hC
  obtain ⟨hC, hCA⟩ := hC
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℚ≥0) < #C)
  calc
    (#(B ^ m / B ^ n) * #C : ℚ≥0)
      ≤ #(B ^ m * C) * #(B ^ n * C) := mod_cast ruzsa_triangle_inequality_div_mul_mul ..
    _ = #(C * B ^ m) * #(C * B ^ n) := by simp_rw [mul_comm]
    _ ≤ ((#(C * B) / #C) ^ m * #C) * ((#(C * B) / #C : ℚ≥0) ^ n * #C) := by
      gcongr <;> exact card_mul_pow_le (mul_aux hC hCA hCmin) _
    _ = (#(C * B) / #C) ^ (m + n) * #C * #C := by ring
    _ ≤ (#(A * B) / #A) ^ (m + n) * #A * #C := by gcongr (?_ ^ _) * #?_ * _; exact hCmin _ hA'

/-- The **Plünnecke-Ruzsa inequality**. Division version. -/
@[to_additive /-- The **Plünnecke-Ruzsa inequality**. Subtraction version. -/]
theorem pluennecke_ruzsa_inequality_pow_div_pow_div (hA : A.Nonempty) (B : Finset G) (m n : ℕ) :
    #(B ^ m / B ^ n) ≤ (#(A / B) / #A : ℚ≥0) ^ (m + n) * #A := by
  rw [← card_inv, inv_div', ← inv_pow, ← inv_pow, div_eq_mul_inv A]
  exact pluennecke_ruzsa_inequality_pow_div_pow_mul hA _ _ _

/-- Special case of the **Plünnecke-Ruzsa inequality**. Multiplication version. -/
@[to_additive /-- Special case of the **Plünnecke-Ruzsa inequality**. Addition version. -/]
theorem pluennecke_ruzsa_inequality_pow_mul (hA : A.Nonempty) (B : Finset G) (n : ℕ) :
    #(B ^ n) ≤ (#(A * B) / #A : ℚ≥0) ^ n * #A := by
  simpa only [_root_.pow_zero, div_one] using pluennecke_ruzsa_inequality_pow_div_pow_mul hA _ _ 0

/-- Special case of the **Plünnecke-Ruzsa inequality**. Division version. -/
@[to_additive /-- Special case of the **Plünnecke-Ruzsa inequality**. Subtraction version. -/]
theorem pluennecke_ruzsa_inequality_pow_div (hA : A.Nonempty) (B : Finset G) (n : ℕ) :
    #(B ^ n) ≤ (#(A / B) / #A : ℚ≥0) ^ n * #A := by
  simpa only [_root_.pow_zero, div_one] using pluennecke_ruzsa_inequality_pow_div_pow_div hA _ _ 0

end CommGroup
end Finset
