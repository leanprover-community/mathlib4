/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Stabilizer of a set under a pointwise action

This file characterises the stabilizer of a set/finset under the pointwise action of a group.
-/

open Function MulOpposite Set
open scoped Pointwise

namespace MulAction
variable {G H α : Type*}

/-! ### Stabilizer of a set -/

section Set
section Group
variable [Group G] [Group H] [MulAction G α] {a : G} {s t : Set α}

@[to_additive (attr := simp)]
lemma stabilizer_empty : stabilizer G (∅ : Set α) = ⊤ :=
  Subgroup.coe_eq_univ.1 <| eq_univ_of_forall fun _a ↦ smul_set_empty

@[to_additive (attr := simp)]
lemma stabilizer_univ : stabilizer G (Set.univ : Set α) = ⊤ := by
  ext
  simp

@[to_additive (attr := simp)]
lemma stabilizer_singleton (b : α) : stabilizer G ({b} : Set α) = stabilizer G b := by ext; simp

@[to_additive]
lemma mem_stabilizer_set {s : Set α} : a ∈ stabilizer G s ↔ ∀ b, a • b ∈ s ↔ b ∈ s := by
  refine mem_stabilizer_iff.trans ⟨fun h b ↦ ?_, fun h ↦ ?_⟩
  · rw [← (smul_mem_smul_set_iff : a • b ∈ _ ↔ _), h]
  simp_rw [Set.ext_iff, mem_smul_set_iff_inv_smul_mem]
  exact ((MulAction.toPerm a).forall_congr' <| by simp [Iff.comm]).1 h

@[to_additive]
lemma map_stabilizer_le (f : G →* H) (s : Set G) :
    (stabilizer G s).map f ≤ stabilizer H (f '' s) := by
  rintro a
  simp only [Subgroup.mem_map, mem_stabilizer_iff, exists_prop, forall_exists_index, and_imp]
  rintro a ha rfl
  rw [← image_smul_distrib, ha]

@[to_additive (attr := simp)]
lemma stabilizer_mul_self (s : Set G) : (stabilizer G s : Set G) * s = s := by
  ext
  refine ⟨?_, fun h ↦ ⟨_, (stabilizer G s).one_mem, _, h, one_mul _⟩⟩
  rintro ⟨a, ha, b, hb, rfl⟩
  rw [← mem_stabilizer_iff.1 ha]
  exact smul_mem_smul_set hb

@[to_additive]
lemma stabilizer_inf_stabilizer_le_stabilizer_apply₂ {f : Set α → Set α → Set α}
    (hf : ∀ a : G, a • f s t = f (a • s) (a • t)) :
    stabilizer G s ⊓ stabilizer G t ≤ stabilizer G (f s t) := by aesop (add simp [SetLike.le_def])

@[to_additive]
lemma stabilizer_inf_stabilizer_le_stabilizer_union :
    stabilizer G s ⊓ stabilizer G t ≤ stabilizer G (s ∪ t) :=
  stabilizer_inf_stabilizer_le_stabilizer_apply₂ fun _ ↦ smul_set_union

@[to_additive]
lemma stabilizer_inf_stabilizer_le_stabilizer_inter :
    stabilizer G s ⊓ stabilizer G t ≤ stabilizer G (s ∩ t) :=
  stabilizer_inf_stabilizer_le_stabilizer_apply₂ fun _ ↦ smul_set_inter

@[to_additive]
lemma stabilizer_inf_stabilizer_le_stabilizer_sdiff :
    stabilizer G s ⊓ stabilizer G t ≤ stabilizer G (s \ t) :=
  stabilizer_inf_stabilizer_le_stabilizer_apply₂ fun _ ↦ smul_set_sdiff

@[to_additive]
lemma stabilizer_union_eq_left (hdisj : Disjoint s t) (hstab : stabilizer G s ≤ stabilizer G t)
    (hstab_union : stabilizer G (s ∪ t) ≤ stabilizer G t) :
    stabilizer G (s ∪ t) = stabilizer G s := by
  refine le_antisymm ?_ ?_
  · calc
      stabilizer G (s ∪ t)
        ≤ stabilizer G (s ∪ t) ⊓ stabilizer G t := by simpa
      _ ≤ stabilizer G ((s ∪ t) \ t) := stabilizer_inf_stabilizer_le_stabilizer_sdiff
      _ = stabilizer G s := by rw [union_diff_cancel_right]; simpa [← disjoint_iff_inter_eq_empty]
  · calc
      stabilizer G s
        ≤ stabilizer G s ⊓ stabilizer G t := by simpa
      _ ≤ stabilizer G (s ∪ t) := stabilizer_inf_stabilizer_le_stabilizer_union

@[to_additive]
lemma stabilizer_union_eq_right (hdisj : Disjoint s t) (hstab : stabilizer G t ≤ stabilizer G s)
    (hstab_union : stabilizer G (s ∪ t) ≤ stabilizer G s)  :
    stabilizer G (s ∪ t) = stabilizer G t := by
  rw [union_comm, stabilizer_union_eq_left hdisj.symm hstab (union_comm .. ▸ hstab_union)]

variable {s : Set G}

open scoped RightActions in
@[to_additive]
lemma op_smul_set_stabilizer_subset (ha : a ∈ s) : (stabilizer G s : Set G) <• a ⊆ s :=
  smul_set_subset_iff.2 fun b hb ↦ by rw [← hb]; exact smul_mem_smul_set ha

@[to_additive]
lemma stabilizer_subset_div_right (ha : a ∈ s) : ↑(stabilizer G s) ⊆ s / {a} := fun b hb ↦
  ⟨_, by rwa [← smul_eq_mul, mem_stabilizer_set.1 hb], _, mem_singleton _, mul_div_cancel_right _ _⟩

@[to_additive]
lemma stabilizer_finite (hs₀ : s.Nonempty) (hs : s.Finite) : (stabilizer G s : Set G).Finite := by
  obtain ⟨a, ha⟩ := hs₀
  exact (hs.div <| finite_singleton _).subset <| stabilizer_subset_div_right ha

end Group

section CommGroup
variable [CommGroup G] {s t : Set G} {a : G}

@[to_additive]
lemma smul_set_stabilizer_subset (ha : a ∈ s) : a • (stabilizer G s : Set G) ⊆ s := by
  simpa using op_smul_set_stabilizer_subset ha

end CommGroup
end Set

variable [Group G] [Group H] [MulAction G α] {a : G}

/-! ### Stabilizer of a subgroup -/

section Subgroup

-- TODO: Is there a lemma that could unify the following three very similar lemmas?

@[to_additive (attr := simp)]
lemma stabilizer_subgroup (s : Subgroup G) : stabilizer G (s : Set G) = s := by
  simp_rw [SetLike.ext_iff, mem_stabilizer_set]
  refine fun a ↦ ⟨fun h ↦ ?_, fun ha b ↦ s.mul_mem_cancel_left ha⟩
  simpa only [smul_eq_mul, SetLike.mem_coe, mul_one] using (h 1).2 s.one_mem

@[to_additive (attr := simp)]
lemma stabilizer_op_subgroup (s : Subgroup G) : stabilizer Gᵐᵒᵖ (s : Set G) = s.op := by
  simp_rw [SetLike.ext_iff, mem_stabilizer_set]
  simp only [smul_eq_mul_unop, SetLike.mem_coe, Subgroup.mem_op, «forall», unop_op]
  refine fun a ↦ ⟨fun h ↦ ?_, fun ha b ↦ s.mul_mem_cancel_right ha⟩
  simpa only [op_smul_eq_mul, SetLike.mem_coe, one_mul] using (h 1).2 s.one_mem

@[to_additive (attr := simp)]
lemma stabilizer_subgroup_op (s : Subgroup Gᵐᵒᵖ) : stabilizer G (s : Set Gᵐᵒᵖ) = s.unop := by
  simp_rw [SetLike.ext_iff, mem_stabilizer_set]
  refine fun a ↦ ⟨fun h ↦ ?_, fun ha b ↦ s.mul_mem_cancel_right ha⟩
  have : 1 * MulOpposite.op a ∈ s := (h 1).2 s.one_mem
  simpa only [op_smul_eq_mul, SetLike.mem_coe, one_mul] using this

end Subgroup

/-! ### Stabilizer of a finset -/

section Finset
variable [DecidableEq α]

@[to_additive (attr := simp, norm_cast)]
lemma stabilizer_coe_finset (s : Finset α) : stabilizer G (s : Set α) = stabilizer G s := by
  ext; simp [← Finset.coe_inj]

@[to_additive (attr := simp)]
lemma stabilizer_finset_empty : stabilizer G (∅ : Finset α) = ⊤ :=
  Subgroup.coe_eq_univ.1 <| eq_univ_of_forall Finset.smul_finset_empty

@[to_additive (attr := simp)]
lemma stabilizer_finset_univ [Fintype α] : stabilizer G (Finset.univ : Finset α) = ⊤ := by
  ext
  simp

@[to_additive (attr := simp)]
lemma stabilizer_finset_singleton (b : α) : stabilizer G ({b} : Finset α) = stabilizer G b := by
  ext; simp

@[to_additive]
lemma mem_stabilizer_finset {s : Finset α} : a ∈ stabilizer G s ↔ ∀ b, a • b ∈ s ↔ b ∈ s := by
  simp_rw [← stabilizer_coe_finset, mem_stabilizer_set, Finset.mem_coe]

@[to_additive]
lemma mem_stabilizer_finset_iff_subset_smul_finset {s : Finset α} :
    a ∈ stabilizer G s ↔ s ⊆ a • s := by
  rw [mem_stabilizer_iff, Finset.subset_iff_eq_of_card_le (Finset.card_smul_finset _ _).le, eq_comm]

@[to_additive]
lemma mem_stabilizer_finset_iff_smul_finset_subset {s : Finset α} :
    a ∈ stabilizer G s ↔ a • s ⊆ s := by
  rw [mem_stabilizer_iff, Finset.subset_iff_eq_of_card_le (Finset.card_smul_finset _ _).ge]

@[to_additive]
lemma mem_stabilizer_finset' {s : Finset α} : a ∈ stabilizer G s ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ s := by
  rw [← Subgroup.inv_mem_iff, mem_stabilizer_finset_iff_subset_smul_finset]
  simp_rw [← Finset.mem_inv_smul_finset_iff, Finset.subset_iff]

end Finset

/-! ### Stabilizer of a finite set -/

variable {s : Set α}

@[to_additive]
lemma mem_stabilizer_set_iff_subset_smul_set {s : Set α} (hs : s.Finite) :
    a ∈ stabilizer G s ↔ s ⊆ a • s := by
  lift s to Finset α using hs
  classical
  rw [stabilizer_coe_finset, mem_stabilizer_finset_iff_subset_smul_finset, ← Finset.coe_smul_finset,
    Finset.coe_subset]

@[to_additive]
lemma mem_stabilizer_set_iff_smul_set_subset {s : Set α} (hs : s.Finite) :
    a ∈ stabilizer G s ↔ a • s ⊆ s := by
  lift s to Finset α using hs
  classical
  rw [stabilizer_coe_finset, mem_stabilizer_finset_iff_smul_finset_subset, ← Finset.coe_smul_finset,
    Finset.coe_subset]

@[deprecated (since := "2024-11-25")]
alias mem_stabilizer_of_finite_iff_smul_le := mem_stabilizer_set_iff_subset_smul_set

@[deprecated (since := "2024-11-25")]
alias mem_stabilizer_of_finite_iff_le_smul := mem_stabilizer_set_iff_smul_set_subset

@[to_additive]
lemma mem_stabilizer_set' {s : Set α} (hs : s.Finite) :
    a ∈ stabilizer G s ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ s := by
  lift s to Finset α using hs
  classical simp [-mem_stabilizer_iff, mem_stabilizer_finset']

end MulAction

/-! ### Stabilizer in a commutative group -/

namespace MulAction
variable {G : Type*} [CommGroup G] (s : Set G)

@[to_additive (attr := simp)]
lemma mul_stabilizer_self : s * stabilizer G s = s := by rw [mul_comm, stabilizer_mul_self]

local notation " Q " => G ⧸ stabilizer G s
local notation " q " => ((↑) : G → Q)

@[to_additive]
lemma stabilizer_image_coe_quotient : stabilizer Q (q '' s) = ⊥ := by
  ext a
  induction' a using QuotientGroup.induction_on with a
  simp only [mem_stabilizer_iff, Subgroup.mem_bot, QuotientGroup.eq_one_iff]
  have : q a • q '' s = q '' (a • s) :=
    (image_smul_distrib (QuotientGroup.mk' <| stabilizer G s) _ _).symm
  rw [this]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  rwa [QuotientGroup.image_coe_inj, mul_smul_comm, stabilizer_mul_self] at h

end MulAction
