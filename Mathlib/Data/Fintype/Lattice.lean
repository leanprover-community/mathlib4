/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic

/-!
# Lemmas relating fintypes and order/lattice structure.
-/


open Function

open Nat

universe u v

variable {ι α β : Type*}

namespace Finset

variable [Fintype α] {s : Finset α}

/-- A special case of `Finset.sup_eq_iSup` that omits the useless `x ∈ univ` binder. -/
theorem sup_univ_eq_iSup [CompleteLattice β] (f : α → β) : Finset.univ.sup f = iSup f :=
  (sup_eq_iSup _ f).trans <| congr_arg _ <| funext fun _ => iSup_pos (mem_univ _)

/-- A special case of `Finset.inf_eq_iInf` that omits the useless `x ∈ univ` binder. -/
theorem inf_univ_eq_iInf [CompleteLattice β] (f : α → β) : Finset.univ.inf f = iInf f :=
  @sup_univ_eq_iSup _ βᵒᵈ _ _ (f : α → βᵒᵈ)

@[simp]
theorem fold_inf_univ [SemilatticeInf α] [OrderBot α] (a : α) :
    (Finset.univ.fold min a fun x => x) = ⊥ :=
  eq_bot_iff.2 <|
    ((Finset.fold_op_rel_iff_and <| @le_inf_iff α _).1 le_rfl).2 ⊥ <| Finset.mem_univ _

@[simp]
theorem fold_sup_univ [SemilatticeSup α] [OrderTop α] (a : α) :
    (Finset.univ.fold max a fun x => x) = ⊤ :=
  @fold_inf_univ αᵒᵈ _ _ _ _

lemma mem_inf [DecidableEq α] {s : Finset ι} {f : ι → Finset α} {a : α} :
    a ∈ s.inf f ↔ ∀ i ∈ s, a ∈ f i := by induction' s using Finset.cons_induction <;> simp [*]

end Finset

open Finset

theorem Finite.exists_max [Finite α] [Nonempty α] [LinearOrder β] (f : α → β) :
    ∃ x₀ : α, ∀ x, f x ≤ f x₀ := by
  cases nonempty_fintype α
  simpa using exists_max_image univ f univ_nonempty

theorem Finite.exists_min [Finite α] [Nonempty α] [LinearOrder β] (f : α → β) :
    ∃ x₀ : α, ∀ x, f x₀ ≤ f x := by
  cases nonempty_fintype α
  simpa using exists_min_image univ f univ_nonempty
