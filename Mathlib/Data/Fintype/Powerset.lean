/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin

/-!
# fintype instance for `Set α`, when `α` is a fintype
-/


variable {α : Type*}

open Finset

instance Finset.fintype [Fintype α] : Fintype (Finset α) :=
  ⟨univ.powerset, fun _ => Finset.mem_powerset.2 (Finset.subset_univ _)⟩

@[simp]
theorem Fintype.card_finset [Fintype α] : Fintype.card (Finset α) = 2 ^ Fintype.card α :=
  Finset.card_powerset Finset.univ

namespace Finset
variable [Fintype α] {s : Finset α} {k : ℕ}

@[simp] lemma powerset_univ : (univ : Finset α).powerset = univ :=
  coe_injective <| by simp [-coe_eq_univ]

lemma filter_subset_univ [DecidableEq α] (s : Finset α) :
    ({t | t ⊆ s} : Finset _) = powerset s := by ext; simp

@[simp] lemma powerset_eq_univ : s.powerset = univ ↔ s = univ := by
  rw [← Finset.powerset_univ, powerset_inj]

lemma mem_powersetCard_univ : s ∈ powersetCard k (univ : Finset α) ↔ #s = k :=
  mem_powersetCard.trans <| and_iff_right <| subset_univ _

variable (α)

@[simp] lemma univ_filter_card_eq (k : ℕ) :
   ({s | #s = k} : Finset (Finset α)) = univ.powersetCard k := by ext; simp

end Finset

@[simp]
theorem Fintype.card_finset_len [Fintype α] (k : ℕ) :
    Fintype.card { s : Finset α // #s = k } = Nat.choose (Fintype.card α) k := by
  simp [Fintype.subtype_card, Finset.card_univ]

instance Set.fintype [Fintype α] : Fintype (Set α) :=
  ⟨(@Finset.univ (Finset α) _).map coeEmb.1, fun s => by
    classical
    refine mem_map.2 ⟨({a | a ∈ s} : Finset _), Finset.mem_univ _, (coe_filter _ _).trans ?_⟩
    simp⟩

-- Not to be confused with `Set.Finite`, the predicate
instance Set.instFinite [Finite α] : Finite (Set α) := by
  cases nonempty_fintype α
  infer_instance

@[simp]
theorem Fintype.card_set [Fintype α] : Fintype.card (Set α) = 2 ^ Fintype.card α :=
  (Finset.card_map _).trans (Finset.card_powerset _)
