/-
Copyright (c) 2025 Yaël Dillies, Strahinja Gvozdić, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Strahinja Gvozdić, Bhavik Mehta
-/
import Mathlib.Algebra.Group.Action.Pointwise.Finset

/-!
# Convolution

This file defines convolution of finite subsets `A` and `B` of group `G` as the map `A ⋆ B : G → ℕ`
that maps `x ∈ G` to the number of distinct representations of `x` in the form `x = ab` for
`a ∈ A`, `b ∈ B`. It is shown how convolution behaves under the change of order of `A` and `B`, as
well as under the left and right actions on `A`, `B`, and the function argument.
-/

open MulOpposite MulAction
open scoped Pointwise RightActions

namespace Finset
variable {G : Type*} [Group G] [DecidableEq G] {A B : Finset G} {s x y : G}

/-- Given finite subsets `A` and `B` of a group `G`, convolution of `A` and `B` is a map `G → ℕ`
that maps `x ∈ G` to the number of distinct representations of `x` in the form `x = ab`, where
`a ∈ A`, `b ∈ B`. -/
@[to_additive addConvolution /-- Given finite subsets `A` and `B` of an additive group `G`,
convolution of `A` and `B` is a map `G → ℕ` that maps `x ∈ G` to the number of distinct
representations of `x` in the form `x = a + b`, where `a ∈ A`, `b ∈ B`. -/]
def convolution (A B : Finset G) : G → ℕ := fun x => #{ab ∈ A ×ˢ B | ab.1 * ab.2 = x}

@[to_additive]
lemma card_smul_inter_smul (A B : Finset G) (x y : G) :
    #((x • A) ∩ (y • B)) = A.convolution B⁻¹ (x⁻¹ * y) :=
  card_nbij' (fun z ↦ (x⁻¹ * z, z⁻¹ * y)) (fun ab' ↦ x • ab'.1)
    (by simp +contextual [Set.MapsTo, Set.mem_smul_set_iff_inv_smul_mem, mul_assoc])
    (by simp +contextual [Set.MapsTo, Set.mem_smul_set_iff_inv_smul_mem]
        simp +contextual [← eq_mul_inv_iff_mul_eq, mul_assoc])
    (by simp [Set.LeftInvOn])
    (by simp +contextual [Set.LeftInvOn, ← eq_mul_inv_iff_mul_eq, mul_assoc])

@[to_additive]
lemma card_inter_smul (A B : Finset G) (x : G) : #(A ∩ (x • B)) = A.convolution B⁻¹ x := by
  simpa using card_smul_inter_smul _ _ 1 x

@[to_additive]
lemma card_smul_inter (A B : Finset G) (x : G) : #((x • A) ∩ B) = A.convolution B⁻¹ x⁻¹ := by
  simpa using card_smul_inter_smul _ _ x 1

@[to_additive card_add_neg_eq_addConvolution_neg]
lemma card_mul_inv_eq_convolution_inv (A B : Finset G) (x : G) :
    #{ab ∈ A ×ˢ B | ab.1 * ab.2⁻¹ = x} = A.convolution B⁻¹ x :=
  card_nbij' (fun ab => (ab.1, ab.2⁻¹)) (fun ab => (ab.1, ab.2⁻¹))
    (by simp [Set.MapsTo]) (by simp [Set.MapsTo])
    (by simp [Set.LeftInvOn]) (by simp [Set.LeftInvOn])

@[to_additive (attr := simp) addConvolution_pos]
lemma convolution_pos : 0 < A.convolution B x ↔ x ∈ A * B := by
  aesop (add simp [convolution, Finset.Nonempty, mem_mul])

@[to_additive addConvolution_ne_zero]
lemma convolution_ne_zero : A.convolution B x ≠ 0 ↔ x ∈ A * B := by
  suffices A.convolution B x ≠ 0 ↔ 0 < A.convolution B x by simp [this]
  cutsat

@[to_additive (attr := simp) addConvolution_eq_zero]
lemma convolution_eq_zero : A.convolution B x = 0 ↔ x ∉ A * B := by
  simp [← convolution_ne_zero]

@[to_additive addConvolution_le_card_left]
lemma convolution_le_card_left : A.convolution B x ≤ #A := by
  rw [← inv_inv B, ← card_inter_smul]
  exact card_le_card inter_subset_left

@[to_additive addConvolution_le_card_right]
lemma convolution_le_card_right : A.convolution B x ≤ #B := by
  rw [← inv_inv B, ← inv_inv x, ← card_smul_inter, card_inv]
  exact card_le_card inter_subset_right

@[to_additive (attr := simp) addConvolution_neg]
lemma convolution_inv (A B : Finset G) (x : G) : A.convolution B x⁻¹ = B⁻¹.convolution A⁻¹ x := by
  nth_rw 1 [← inv_inv B]
  rw [← card_smul_inter, ← card_inter_smul, inter_comm]

@[to_additive (attr := simp) op_vadd_addConvolution_eq_addConvolution_vadd]
lemma op_smul_convolution_eq_convolution_smul (A B : Finset G) (s : G) :
    (A <• s).convolution B = A.convolution (s • B) := funext fun x => by
  nth_rw 1 [← inv_inv B, ← inv_inv (s • B), inv_smul_finset_distrib s B, ← card_inter_smul,
    ← card_inter_smul, smul_comm]
  simp [← card_smul_finset (op s) (A ∩ _), smul_finset_inter]

@[to_additive (attr := simp) vadd_addConvolution_eq_addConvolution_neg_add]
lemma smul_convolution_eq_convolution_inv_mul (A B : Finset G) (s x : G) :
    (s •> A).convolution B x = A.convolution B (s⁻¹ * x) := by
  nth_rw 1 [← inv_inv x, ← inv_inv (s⁻¹ * x)]
  rw [← inv_inv B, ← card_smul_inter, ← card_smul_inter, mul_inv_rev, inv_inv, smul_smul]

@[to_additive (attr := simp) addConvolution_op_vadd_eq_addConvolution_add_neg]
lemma convolution_op_smul_eq_convolution_mul_inv (A B : Finset G) (s x : G) :
    A.convolution (B <• s) x = A.convolution B (x * s⁻¹) := by
  nth_rw 2 [← inv_inv B]
  rw [← inv_inv (B <• s), inv_op_smul_finset_distrib, ← card_inter_smul, ← card_inter_smul,
    smul_smul]

end Finset
