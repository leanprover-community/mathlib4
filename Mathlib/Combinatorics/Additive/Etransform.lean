/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Finset.Pointwise

#align_import combinatorics.additive.e_transform from "leanprover-community/mathlib"@"207c92594599a06e7c134f8d00a030a83e6c7259"

/-!
# e-transforms

e-transforms are a family of transformations of pairs of finite sets that aim to reduce the size
of the sumset while keeping some invariant the same. This file defines a few of them, to be used
as internals of other proofs.

## Main declarations

* `Finset.mulDysonEtransform`: The Dyson e-transform. Replaces `(s, t)` by
  `(s ∪ e • t, t ∩ e⁻¹ • s)`. The additive version preserves `|s ∩ [1, m]| + |t ∩ [1, m - e]|`.
* `Finset.mulEtransformLeft`/`Finset.mulEtransformRight`: Replace `(s, t)` by
  `(s ∩ s • e, t ∪ e⁻¹ • t)` and `(s ∪ s • e, t ∩ e⁻¹ • t)`. Preserve (together) the sum of
  the cardinalities (see `Finset.MulEtransform.card`). In particular, one of the two transforms
  increases the sum of the cardinalities and the other one decreases it. See
  `le_or_lt_of_add_le_add` and around.

## TODO

Prove the invariance property of the Dyson e-transform.
-/


open MulOpposite

open Pointwise

variable {α : Type*} [DecidableEq α]

namespace Finset

/-! ### Dyson e-transform -/


section CommGroup

variable [CommGroup α] (e : α) (x : Finset α × Finset α)

/-- The **Dyson e-transform**. Turns `(s, t)` into `(s ∪ e • t, t ∩ e⁻¹ • s)`. This reduces the
product of the two sets. -/
@[to_additive (attr := simps) "The **Dyson e-transform**.
Turns `(s, t)` into `(s ∪ e +ᵥ t, t ∩ -e +ᵥ s)`. This reduces the sum of the two sets."]
def mulDysonEtransform : Finset α × Finset α :=
  (x.1 ∪ e • x.2, x.2 ∩ e⁻¹ • x.1)
#align finset.mul_dyson_e_transform Finset.mulDysonEtransform
#align finset.add_dyson_e_transform Finset.addDysonEtransform

@[to_additive]
theorem mulDysonEtransform.subset :
    (mulDysonEtransform e x).1 * (mulDysonEtransform e x).2 ⊆ x.1 * x.2 := by
  refine' union_mul_inter_subset_union.trans (union_subset Subset.rfl _)
  -- ⊢ e • x.snd * e⁻¹ • x.fst ⊆ x.fst * x.snd
  rw [mul_smul_comm, smul_mul_assoc, inv_smul_smul, mul_comm]
  -- 🎉 no goals
#align finset.mul_dyson_e_transform.subset Finset.mulDysonEtransform.subset
#align finset.add_dyson_e_transform.subset Finset.addDysonEtransform.subset

@[to_additive]
theorem mulDysonEtransform.card :
    (mulDysonEtransform e x).1.card + (mulDysonEtransform e x).2.card = x.1.card + x.2.card := by
  dsimp
  -- ⊢ Finset.card (x.fst ∪ e • x.snd) + Finset.card (x.snd ∩ e⁻¹ • x.fst) = Finset …
  rw [← card_smul_finset e (_ ∩ _), smul_finset_inter, smul_inv_smul, inter_comm,
    card_union_add_card_inter, card_smul_finset]
#align finset.mul_dyson_e_transform.card Finset.mulDysonEtransform.card
#align finset.add_dyson_e_transform.card Finset.addDysonEtransform.card

@[to_additive (attr := simp)]
theorem mulDysonEtransform_idem :
    mulDysonEtransform e (mulDysonEtransform e x) = mulDysonEtransform e x := by
  ext : 1 <;> dsimp
  -- ⊢ (mulDysonEtransform e (mulDysonEtransform e x)).fst = (mulDysonEtransform e  …
              -- ⊢ x.fst ∪ e • x.snd ∪ e • (x.snd ∩ e⁻¹ • x.fst) = x.fst ∪ e • x.snd
              -- ⊢ x.snd ∩ e⁻¹ • x.fst ∩ e⁻¹ • (x.fst ∪ e • x.snd) = x.snd ∩ e⁻¹ • x.fst
  · rw [smul_finset_inter, smul_inv_smul, inter_comm, union_eq_left_iff_subset]
    -- ⊢ x.fst ∩ e • x.snd ⊆ x.fst ∪ e • x.snd
    exact inter_subset_union
    -- 🎉 no goals
  · rw [smul_finset_union, inv_smul_smul, union_comm, inter_eq_left_iff_subset]
    -- ⊢ x.snd ∩ e⁻¹ • x.fst ⊆ x.snd ∪ e⁻¹ • x.fst
    exact inter_subset_union
    -- 🎉 no goals
#align finset.mul_dyson_e_transform_idem Finset.mulDysonEtransform_idem
#align finset.add_dyson_e_transform_idem Finset.addDysonEtransform_idem

variable {e x}

@[to_additive]
theorem mulDysonEtransform.smul_finset_snd_subset_fst :
    e • (mulDysonEtransform e x).2 ⊆ (mulDysonEtransform e x).1 := by
  dsimp
  -- ⊢ e • (x.snd ∩ e⁻¹ • x.fst) ⊆ x.fst ∪ e • x.snd
  rw [smul_finset_inter, smul_inv_smul, inter_comm]
  -- ⊢ x.fst ∩ e • x.snd ⊆ x.fst ∪ e • x.snd
  exact inter_subset_union
  -- 🎉 no goals
#align finset.mul_dyson_e_transform.smul_finset_snd_subset_fst Finset.mulDysonEtransform.smul_finset_snd_subset_fst
#align finset.add_dyson_e_transform.vadd_finset_snd_subset_fst Finset.addDysonEtransform.vadd_finset_snd_subset_fst

end CommGroup

/-!
### Two unnamed e-transforms

The following two transforms both reduce the product/sum of the two sets. Further, one of them must
decrease the sum of the size of the sets (and then the other increases it).

This pair of transforms doesn't seem to be named in the literature. It is used by Sanders in his
bound on Roth numbers, and by DeVos in his proof of Cauchy-Davenport.
-/


section Group

variable [Group α] (e : α) (x : Finset α × Finset α)

/-- An **e-transform**. Turns `(s, t)` into `(s ∩ s • e, t ∪ e⁻¹ • t)`. This reduces the
product of the two sets. -/
@[to_additive (attr := simps) "An **e-transform**.
Turns `(s, t)` into `(s ∩ s +ᵥ e, t ∪ -e +ᵥ t)`. This reduces the sum of the two sets."]
def mulEtransformLeft : Finset α × Finset α :=
  (x.1 ∩ op e • x.1, x.2 ∪ e⁻¹ • x.2)
#align finset.mul_e_transform_left Finset.mulEtransformLeft
#align finset.add_e_transform_left Finset.addEtransformLeft

/-- An **e-transform**. Turns `(s, t)` into `(s ∪ s • e, t ∩ e⁻¹ • t)`. This reduces the
product of the two sets. -/
@[to_additive (attr := simps) "An **e-transform**.
Turns `(s, t)` into `(s ∪ s +ᵥ e, t ∩ -e +ᵥ t)`. This reduces the sum of the two sets."]
def mulEtransformRight : Finset α × Finset α :=
  (x.1 ∪ op e • x.1, x.2 ∩ e⁻¹ • x.2)
#align finset.mul_e_transform_right Finset.mulEtransformRight
#align finset.add_e_transform_right Finset.addEtransformRight

@[to_additive (attr := simp)]
theorem mulEtransformLeft_one : mulEtransformLeft 1 x = x := by simp [mulEtransformLeft]
                                                                -- 🎉 no goals
#align finset.mul_e_transform_left_one Finset.mulEtransformLeft_one
#align finset.add_e_transform_left_zero Finset.addEtransformLeft_zero

@[to_additive (attr := simp)]
theorem mulEtransformRight_one : mulEtransformRight 1 x = x := by simp [mulEtransformRight]
                                                                  -- 🎉 no goals
#align finset.mul_e_transform_right_one Finset.mulEtransformRight_one
#align finset.add_e_transform_right_zero Finset.addEtransformRight_zero

@[to_additive]
theorem mulEtransformLeft.fst_mul_snd_subset :
    (mulEtransformLeft e x).1 * (mulEtransformLeft e x).2 ⊆ x.1 * x.2 := by
  refine' inter_mul_union_subset_union.trans (union_subset Subset.rfl _)
  -- ⊢ op e • x.fst * e⁻¹ • x.snd ⊆ x.fst * x.snd
  rw [op_smul_finset_mul_eq_mul_smul_finset, smul_inv_smul]
  -- 🎉 no goals
#align finset.mul_e_transform_left.fst_mul_snd_subset Finset.mulEtransformLeft.fst_mul_snd_subset
#align finset.add_e_transform_left.fst_add_snd_subset Finset.addEtransformLeft.fst_add_snd_subset

@[to_additive]
theorem mulEtransformRight.fst_mul_snd_subset :
    (mulEtransformRight e x).1 * (mulEtransformRight e x).2 ⊆ x.1 * x.2 := by
  refine' union_mul_inter_subset_union.trans (union_subset Subset.rfl _)
  -- ⊢ op e • x.fst * e⁻¹ • x.snd ⊆ x.fst * x.snd
  rw [op_smul_finset_mul_eq_mul_smul_finset, smul_inv_smul]
  -- 🎉 no goals
#align finset.mul_e_transform_right.fst_mul_snd_subset Finset.mulEtransformRight.fst_mul_snd_subset
#align finset.add_e_transform_right.fst_add_snd_subset Finset.addEtransformRight.fst_add_snd_subset

@[to_additive]
theorem mulEtransformLeft.card :
    (mulEtransformLeft e x).1.card + (mulEtransformRight e x).1.card = 2 * x.1.card :=
  (card_inter_add_card_union _ _).trans <| by rw [card_smul_finset, two_mul]
                                              -- 🎉 no goals
#align finset.mul_e_transform_left.card Finset.mulEtransformLeft.card
#align finset.add_e_transform_left.card Finset.addEtransformLeft.card

@[to_additive]
theorem mulEtransformRight.card :
    (mulEtransformLeft e x).2.card + (mulEtransformRight e x).2.card = 2 * x.2.card :=
  (card_union_add_card_inter _ _).trans <| by rw [card_smul_finset, two_mul]
                                              -- 🎉 no goals
#align finset.mul_e_transform_right.card Finset.mulEtransformRight.card
#align finset.add_e_transform_right.card Finset.addEtransformRight.card

/-- This statement is meant to be combined with `le_or_lt_of_add_le_add` and similar lemmas. -/
@[to_additive AddEtransform.card "This statement is meant to be combined with
`le_or_lt_of_add_le_add` and similar lemmas."]
protected theorem MulEtransform.card :
    (mulEtransformLeft e x).1.card + (mulEtransformLeft e x).2.card +
        ((mulEtransformRight e x).1.card + (mulEtransformRight e x).2.card) =
      x.1.card + x.2.card + (x.1.card + x.2.card) := by
  rw [add_add_add_comm, mulEtransformLeft.card, mulEtransformRight.card, ← mul_add, two_mul]
  -- 🎉 no goals
#align finset.mul_e_transform.card Finset.MulEtransform.card
#align finset.add_e_transform.card Finset.AddEtransform.card

end Group

section CommGroup

variable [CommGroup α] (e : α) (x : Finset α × Finset α)

@[to_additive (attr := simp)]
theorem mulEtransformLeft_inv : mulEtransformLeft e⁻¹ x = (mulEtransformRight e x.swap).swap := by
  simp [-op_inv, op_smul_eq_smul, mulEtransformLeft, mulEtransformRight]
  -- 🎉 no goals
#align finset.mul_e_transform_left_inv Finset.mulEtransformLeft_inv
#align finset.add_e_transform_left_neg Finset.addEtransformLeft_neg

@[to_additive (attr := simp)]
theorem mulEtransformRight_inv : mulEtransformRight e⁻¹ x = (mulEtransformLeft e x.swap).swap := by
  simp [-op_inv, op_smul_eq_smul, mulEtransformLeft, mulEtransformRight]
  -- 🎉 no goals
#align finset.mul_e_transform_right_inv Finset.mulEtransformRight_inv
#align finset.add_e_transform_right_neg Finset.addEtransformRight_neg

end CommGroup

end Finset
