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

Each of the lemmas assuming `[Fintype α]` and `Fintype.card` can be restated using `[Finite α]` and
`Nat.card`.
-/

@[expose] public section

open Nat

variable (α : Type*) [Finite α]

namespace Sym

/-- For any finite type `α` of cardinality `n`, `card (Sym α k) = multichoose (card α) k`. -/
theorem natCard_sym_eq_multichoose (k : ℕ) :
    Nat.card (Sym α k) = multichoose (Nat.card α) k := by
  obtain ⟨_⟩ := nonempty_fintype α; letI := Classical.decEq α
  simp_rw [Nat.card_eq_fintype_card]
  exact card_sym_eq_multichoose _ _

/-- The *stars and bars* lemma: the cardinality of `Sym α k` is equal to
`Nat.choose (card α + k - 1) k`. -/
theorem natCard_sym_eq_choose (k : ℕ) :
    Nat.card (Sym α k) = (Nat.card α + k - 1).choose k := by
  obtain ⟨_⟩ := nonempty_fintype α; letI := Classical.decEq α
  simp_rw [Nat.card_eq_fintype_card]
  exact card_sym_eq_choose _

end Sym

namespace Sym2

theorem natCard_subtype_diag : Nat.card { a : Sym2 α // a.IsDiag } = Nat.card α := by
  obtain ⟨_⟩ := nonempty_fintype α; letI := Classical.decEq α
  simp_rw [Nat.card_eq_fintype_card]
  exact Sym2.card_subtype_diag

theorem natCard_subtype_not_diag :
    Nat.card { a : Sym2 α // ¬a.IsDiag } = (Nat.card α).choose 2 := by
  obtain ⟨_⟩ := nonempty_fintype α; letI := Classical.decEq α
  simp_rw [Nat.card_eq_fintype_card]
  exact Sym2.card_subtype_not_diag

lemma natCard_diagSet_compl : Nat.card (diagSetᶜ : Set (Sym2 α)) = (Nat.card α).choose 2 := by
  obtain ⟨_⟩ := nonempty_fintype α; letI := Classical.decEq α
  simp_rw [Nat.card_eq_fintype_card]
  exact Sym2.card_diagSet_compl

/-- Type **stars and bars** for the case `n = 2`. -/
protected theorem natCard : Nat.card (Sym2 α) = Nat.choose (Nat.card α + 1) 2 :=by
  obtain ⟨_⟩ := nonempty_fintype α; letI := Classical.decEq α
  simp_rw [Nat.card_eq_fintype_card]
  exact Sym2.card

end Sym2
