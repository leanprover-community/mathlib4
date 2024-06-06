/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Set.Basic

#align_import data.nat.order.lemmas from "leanprover-community/mathlib"@"e8638a0fcaf73e4500469f368ef9494e495099b3"

/-!
# Further lemmas about the natural numbers

The distinction between this file and `Mathlib.Algebra.Order.Ring.Nat` is not particularly clear.
They are separated for now to minimize the porting requirements for tactics during the transition to
mathlib4. After `Mathlib.Algebra.Order.Ring.Rat` has been ported,
please feel free to reorganize these two files.
-/


universe u v

variable {a b m n k : ℕ}

namespace Nat

/-! ### Sets -/


instance Subtype.orderBot (s : Set ℕ) [DecidablePred (· ∈ s)] [h : Nonempty s] : OrderBot s where
  bot := ⟨Nat.find (nonempty_subtype.1 h), Nat.find_spec (nonempty_subtype.1 h)⟩
  bot_le x := Nat.find_min' _ x.2
#align nat.subtype.order_bot Nat.Subtype.orderBot

instance Subtype.semilatticeSup (s : Set ℕ) : SemilatticeSup s :=
  { Subtype.instLinearOrder s, LinearOrder.toLattice with }
#align nat.subtype.semilattice_sup Nat.Subtype.semilatticeSup

theorem Subtype.coe_bot {s : Set ℕ} [DecidablePred (· ∈ s)] [h : Nonempty s] :
    ((⊥ : s) : ℕ) = Nat.find (nonempty_subtype.1 h) :=
  rfl
#align nat.subtype.coe_bot Nat.Subtype.coe_bot

theorem set_eq_univ {S : Set ℕ} : S = Set.univ ↔ 0 ∈ S ∧ ∀ k : ℕ, k ∈ S → k + 1 ∈ S :=
  ⟨by rintro rfl; simp, fun ⟨h0, hs⟩ => Set.eq_univ_of_forall (set_induction h0 hs)⟩
#align nat.set_eq_univ Nat.set_eq_univ

lemma exists_not_and_succ_of_not_zero_of_exists {p : ℕ → Prop} (H' : ¬ p 0) (H : ∃ n, p n) :
    ∃ n, ¬ p n ∧ p (n + 1) := by
  classical
  let k := Nat.find H
  have hk : p k := Nat.find_spec H
  suffices 0 < k from
    ⟨k - 1, Nat.find_min H <| Nat.pred_lt this.ne', by rwa [Nat.sub_add_cancel this]⟩
  by_contra! contra
  rw [le_zero_eq] at contra
  exact H' (contra ▸ hk)

end Nat
