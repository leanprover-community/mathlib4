/-
Copyright (c) 2025 Yaël Dillies, Strahinja Gvozdić, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Strahinja Gvozdić, Bhavik Mehta
-/
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Order.Group.Nat

/-!
# Convolution

This file defines convolution of finite subsets `A` and `B` of group `G` as the map `A ⋆ B : G → ℕ`
that maps `x ∈ G` to the number of distinct representations of `x` in the form `x = ab⁻¹` for
`a ∈ A`, `b ∈ B`. It is shown how convolution behaves under the change of order of `A` and `B`, as
well as under the left and right actions on `A`, `B`, and the function argument.
-/

open MulOpposite MulAction
open scoped Pointwise RightActions

namespace Finset
variable {G : Type*} [Group G] [DecidableEq G] {A B : Finset G} {s x y : G}

lemma card_smul_inter_smul (A B : Finset G) (x y : G) :
    #((x • A) ∩ (y • B)) = #{wz ∈ A ×ˢ B | wz.1 * wz.2⁻¹ = x⁻¹ * y} :=
  card_nbij' (fun z ↦ (x⁻¹ * z, y⁻¹ * z)) (fun zw ↦ x • zw.1)
    (by simp +contextual [Set.MapsTo, Set.mem_smul_set_iff_inv_smul_mem, mul_assoc])
    (by simp +contextual [Set.MapsTo, Set.mem_smul_set_iff_inv_smul_mem]
        simp +contextual [mul_inv_eq_iff_eq_mul, mul_assoc])
    (by simp [Set.LeftInvOn])
    (by simp +contextual [Set.LeftInvOn, mul_inv_eq_iff_eq_mul, mul_assoc])

lemma card_inter_smul (A B : Finset G) (x : G) :
    #(A ∩ (x • B)) = #{yz ∈ A ×ˢ B | yz.1 * yz.2⁻¹ = x} := by
  simpa using card_smul_inter_smul _ _ 1 x

lemma card_inv_smul_inter (A B : Finset G) (x : G) :
    #((x⁻¹ • A) ∩ B) = #{yz ∈ A ×ˢ B | yz.1 * yz.2⁻¹ = x} := by
  simpa using card_smul_inter_smul _ _ x⁻¹ 1

/-- Given finite subsets `A` and `B` of a group `G`, convolution of `A` and `B` is a map `G → ℕ`
that maps `x ∈ G` to the number of distinct representations of `x` in the form `x = ab⁻¹`, where
`a ∈ A`, `b ∈ B`. -/
def convolution (A B : Finset G) : G → ℕ := fun x => #{ab ∈ A ×ˢ B | ab.1 * ab.2⁻¹ = x}

lemma convolution_eq_card_smul_inter_smul (A B : Finset G) (x y : G) :
    A.convolution B (x⁻¹ * y) = #((x • A) ∩ (y • B)) := Eq.symm <| card_smul_inter_smul ..

lemma convolution_eq_card_inter_smul (A B : Finset G) (x : G) :
    A.convolution B x = #(A ∩ (x • B)) := Eq.symm <| card_inter_smul ..

lemma convolution_eq_card_inv_smul_inter (A B : Finset G) (x : G) :
    A.convolution B x = #((x⁻¹ • A) ∩ B) := Eq.symm <| card_inv_smul_inter ..

lemma convolution_nonneg (A B : Finset G) (x : G) : 0 ≤ A.convolution B x := zero_le _

lemma convolution_pos_of_mem (hx : x ∈ A * B⁻¹) :
    0 < A.convolution B x := by
  obtain ⟨a, ha, b, hb, h⟩ := mem_mul.mp hx
  exact card_pos.mpr ⟨(a, b⁻¹),
    by simp_all only [mem_inv', mem_filter, mem_product, and_self, inv_inv]⟩

lemma convolution_le_card_left (A B : Finset G) (x : G) : A.convolution B x ≤ #A := by
  simp only [convolution_eq_card_inter_smul]
  gcongr
  exact inter_subset_left

lemma convolution_le_card_right (A B : Finset G) (x : G) : A.convolution B x ≤ #B := by
  simp only [convolution_eq_card_inv_smul_inter]
  gcongr
  exact inter_subset_right

lemma convolution_inv (A B : Finset G) (x : G) :
    A.convolution B x⁻¹ = B.convolution A x := by
  rw [convolution_eq_card_inter_smul, convolution_eq_card_inv_smul_inter, inter_comm]

lemma convolution_op_smul_eq_op_smul_inv_convolution (A B : Finset G) (s : G) :
    A.convolution (B <• s) = (A <• s⁻¹).convolution B := funext <| fun x => by
  simp only [convolution_eq_card_inter_smul, smul_comm x (op s), inv_mul_cancel, one_smul,
    ← card_smul_finset (op s⁻¹) (A ∩ x •> B <• s), op_inv, smul_finset_inter, smul_smul]

lemma op_smul_convolution_eq_convolution_op_smul_inv (A B : Finset G) (s : G) :
    (A <• s).convolution B = A.convolution (B <• s⁻¹) := by
  simpa only [inv_inv] using Eq.symm <| convolution_op_smul_eq_op_smul_inv_convolution A B s⁻¹

lemma convolution_mul_left_eq_inv_smul_convolution (A B : Finset G) (s x : G) :
    A.convolution B (s * x) = (s⁻¹ •> A).convolution B x := by
  simp only [convolution_eq_card_inter_smul, ← smul_smul, ← card_smul_finset s (s⁻¹ •> A ∩ x •> B),
    smul_finset_inter, smul_inv_smul]

lemma convolution_mul_right_eq_convolution_smul (A B : Finset G) (s x : G) :
    A.convolution B (x * s) = A.convolution (s •> B) x := by
  rw [← convolution_inv, mul_inv_rev, convolution_mul_left_eq_inv_smul_convolution,
    inv_inv, convolution_inv]

end Finset
