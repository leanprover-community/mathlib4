/-
Copyright (c) 2026 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.Sym.Basic
public import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Sym.Card

/-!
# `Nat.card` versions of `Fintype.card` lemmas on `Sym`

Each of the lemmas assuming `[Fintype α]` and `Fintype.card` can be restated using `Nat.card` alone.
-/

@[expose] public section

open Nat

variable (α : Type*)

namespace Sym

instance {k : ℕ} [Infinite α] [NeZero k] : Infinite (Sym α k) :=
  .of_injective (Sym.replicate k) <| Sym.replicate_right_injective (NeZero.ne _)

/-- A version of `card_sym_eq_multichoose` that does not need finiteness. -/
theorem natCard_sym_eq_multichoose (k : ℕ) :
    Nat.card (Sym α k) = multichoose (Nat.card α) k := by
  cases finite_or_infinite α
  · obtain ⟨_⟩ := nonempty_fintype α; letI := Classical.decEq α
    simp_rw [Nat.card_eq_fintype_card]
    exact card_sym_eq_multichoose _ _
  cases k
  · simp
  simp

/-- A version of `card_sym_eq_choose` that does not need finiteness. -/
theorem natCard_sym_eq_choose (k : ℕ) :
    Nat.card (Sym α k) = (Nat.card α + k - 1).choose k := by
  rw [natCard_sym_eq_multichoose, Nat.multichoose_eq]

end Sym

namespace Sym2

instance [Infinite α] : Infinite (Sym2 α) :=
  .of_injective Sym2.diag <| Sym2.diag_injective

instance [Infinite α] : Infinite {a : Sym2 α // a.IsDiag} :=
  .of_injective (fun a : α => ⟨.diag a, rfl⟩) fun _ _ h => Sym2.diag_injective congr($h)

instance [Infinite α] : Infinite {a : Sym2 α // ¬a.IsDiag} :=
  let e := Infinite.natEmbedding α
  .of_injective (fun n => ⟨s(e 0, e (n + 1)), by simp⟩) fun _ _ => by simp

theorem natCard_subtype_diag : Nat.card { a : Sym2 α // a.IsDiag } = Nat.card α := by
  cases finite_or_infinite α
  · obtain ⟨_⟩ := nonempty_fintype α; letI := Classical.decEq α
    simp_rw [Nat.card_eq_fintype_card]
    exact card_subtype_diag
  · simp

theorem natCard_subtype_not_diag :
    Nat.card { a : Sym2 α // ¬a.IsDiag } = (Nat.card α).choose 2 := by
  cases finite_or_infinite α
  · obtain ⟨_⟩ := nonempty_fintype α; letI := Classical.decEq α
    simp_rw [Nat.card_eq_fintype_card]
    exact card_subtype_not_diag
  · simp

lemma ncard_diagSet : (diagSet : Set (Sym2 α)).ncard = Nat.card α :=
  natCard_subtype_diag _

lemma ncard_diagSet_compl : (diagSetᶜ : Set (Sym2 α)).ncard = (Nat.card α).choose 2 :=
  natCard_subtype_not_diag _

/-- Type **stars and bars** for the case `n = 2`. -/
protected theorem natCard : Nat.card (Sym2 α) = Nat.choose (Nat.card α + 1) 2 := by
  cases finite_or_infinite α
  · obtain ⟨_⟩ := nonempty_fintype α; letI := Classical.decEq α
    simp_rw [Nat.card_eq_fintype_card]
    exact Sym2.card
  · simp

end Sym2
