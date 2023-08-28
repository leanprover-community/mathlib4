/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Powerset

#align_import data.fintype.powerset from "leanprover-community/mathlib"@"509de852e1de55e1efa8eacfa11df0823f26f226"

/-!
# fintype instance for `Set α`, when `α` is a fintype
-/


variable {α : Type*}

open Finset

instance Finset.fintype [Fintype α] : Fintype (Finset α) :=
  ⟨univ.powerset, fun _ => Finset.mem_powerset.2 (Finset.subset_univ _)⟩
#align finset.fintype Finset.fintype

@[simp]
theorem Fintype.card_finset [Fintype α] : Fintype.card (Finset α) = 2 ^ Fintype.card α :=
  Finset.card_powerset Finset.univ
#align fintype.card_finset Fintype.card_finset

@[simp]
theorem Finset.powerset_univ [Fintype α] : (univ : Finset α).powerset = univ :=
  coe_injective <| by simp [-coe_eq_univ]
#align finset.powerset_univ Finset.powerset_univ

@[simp]
theorem Finset.powerset_eq_univ [Fintype α] {s : Finset α} : s.powerset = univ ↔ s = univ := by
  rw [← Finset.powerset_univ, powerset_inj]
#align finset.powerset_eq_univ Finset.powerset_eq_univ

@[simp]
theorem Finset.mem_powerset_len_univ_iff [Fintype α] {s : Finset α} {k : ℕ} :
    s ∈ powersetLen k (univ : Finset α) ↔ card s = k :=
  mem_powersetLen.trans <| and_iff_right <| subset_univ _
#align finset.mem_powerset_len_univ_iff Finset.mem_powerset_len_univ_iff

@[simp]
theorem Finset.univ_filter_card_eq (α : Type*) [Fintype α] (k : ℕ) :
    ((Finset.univ : Finset (Finset α)).filter fun s => s.card = k) = Finset.univ.powersetLen k := by
  ext
  simp [Finset.mem_powersetLen]
#align finset.univ_filter_card_eq Finset.univ_filter_card_eq

@[simp]
theorem Fintype.card_finset_len [Fintype α] (k : ℕ) :
    Fintype.card { s : Finset α // s.card = k } = Nat.choose (Fintype.card α) k := by
  simp [Fintype.subtype_card, Finset.card_univ]
#align fintype.card_finset_len Fintype.card_finset_len

instance Set.fintype [Fintype α] : Fintype (Set α) :=
  ⟨(@Finset.univ α _).powerset.map ⟨(↑), coe_injective⟩, fun s => by
    classical
      refine' mem_map.2 ⟨Finset.univ.filter s, Finset.mem_powerset.2 (Finset.subset_univ _), _⟩
      apply (coe_filter _ _).trans
      simp
      rfl⟩
#align set.fintype Set.fintype

-- Not to be confused with `Set.Finite`, the predicate
instance Set.finite' [Finite α] : Finite (Set α) := by
  cases nonempty_fintype α
  infer_instance
#align set.finite' Set.finite'

@[simp]
theorem Fintype.card_set [Fintype α] : Fintype.card (Set α) = 2 ^ Fintype.card α :=
  (Finset.card_map _).trans (Finset.card_powerset _)
#align fintype.card_set Fintype.card_set
