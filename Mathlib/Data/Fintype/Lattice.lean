/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.fintype.lattice
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Lattice

/-!
# Lemmas relating fintypes and order/lattice structure.
-/


open Function

open Nat

universe u v

variable {α β : Type _}

namespace Finset

variable [Fintype α] {s : Finset α}

/-- A special case of `Finset.sup_eq_supᵢ` that omits the useless `x ∈ univ` binder. -/
theorem sup_univ_eq_supᵢ [CompleteLattice β] (f : α → β) : Finset.univ.sup f = supᵢ f :=
  (sup_eq_supᵢ _ f).trans <| congr_arg _ <| funext fun _ => supᵢ_pos (mem_univ _)
#align finset.sup_univ_eq_supr Finset.sup_univ_eq_supᵢ

/-- A special case of `Finset.inf_eq_infᵢ` that omits the useless `x ∈ univ` binder. -/
theorem inf_univ_eq_infᵢ [CompleteLattice β] (f : α → β) : Finset.univ.inf f = infᵢ f :=
  @sup_univ_eq_supᵢ _ βᵒᵈ _ _ (f : α → βᵒᵈ)
#align finset.inf_univ_eq_infi Finset.inf_univ_eq_infᵢ

@[simp]
theorem fold_inf_univ [SemilatticeInf α] [OrderBot α] (a : α) :
    -- Porting note: added `haveI`
    haveI : IsCommutative α (· ⊓ ·) := inferInstance
    (Finset.univ.fold (· ⊓ ·) a fun x => x) = ⊥ :=
  eq_bot_iff.2 <|
    ((Finset.fold_op_rel_iff_and <| @le_inf_iff α _).1 le_rfl).2 ⊥ <| Finset.mem_univ _
#align finset.fold_inf_univ Finset.fold_inf_univ

@[simp]
theorem fold_sup_univ [SemilatticeSup α] [OrderTop α] (a : α) :
    -- Porting note: added `haveI`
    haveI : IsCommutative α (· ⊔ ·) := inferInstance
    (Finset.univ.fold (· ⊔ ·) a fun x => x) = ⊤ :=
  @fold_inf_univ αᵒᵈ _ _ _ _
#align finset.fold_sup_univ Finset.fold_sup_univ

end Finset

open Finset Function

theorem Finite.exists_max [Finite α] [Nonempty α] [LinearOrder β] (f : α → β) :
    ∃ x₀ : α, ∀ x, f x ≤ f x₀ := by
  cases nonempty_fintype α
  simpa using exists_max_image univ f univ_nonempty
#align finite.exists_max Finite.exists_max

theorem Finite.exists_min [Finite α] [Nonempty α] [LinearOrder β] (f : α → β) :
    ∃ x₀ : α, ∀ x, f x₀ ≤ f x := by
  cases nonempty_fintype α
  simpa using exists_min_image univ f univ_nonempty
#align finite.exists_min Finite.exists_min
