/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Data.Nat.Find
import Mathlib.Data.Set.Basic

/-!
# Further lemmas about the natural numbers

The distinction between this file and `Mathlib/Algebra/Order/Ring/Nat.lean` is not particularly
clear. They were separated for now to minimize the porting requirements for tactics
during the transition to mathlib4. Please feel free to reorganize these two files.
-/

assert_not_exists RelIso

namespace Nat

/-! ### Sets -/


instance Subtype.orderBot (s : Set ℕ) [DecidablePred (· ∈ s)] [h : Nonempty s] : OrderBot s where
  bot := ⟨Nat.find (nonempty_subtype.1 h), Nat.find_spec (nonempty_subtype.1 h)⟩
  bot_le x := Nat.find_min' _ x.2

instance Subtype.semilatticeSup (s : Set ℕ) : SemilatticeSup s :=
  { Subtype.instLinearOrder s, LinearOrder.toLattice with }

theorem Subtype.coe_bot {s : Set ℕ} [DecidablePred (· ∈ s)] [h : Nonempty s] :
    ((⊥ : s) : ℕ) = Nat.find (nonempty_subtype.1 h) :=
  rfl

theorem set_eq_univ {S : Set ℕ} : S = Set.univ ↔ 0 ∈ S ∧ ∀ k : ℕ, k ∈ S → k + 1 ∈ S :=
  ⟨by rintro rfl; simp, fun ⟨h0, hs⟩ => Set.eq_univ_of_forall (set_induction h0 hs)⟩

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
