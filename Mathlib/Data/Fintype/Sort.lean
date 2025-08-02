/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic

/-!
# Sorting a finite type

This file provides two equivalences for linearly ordered fintypes:
* `monoEquivOfFin`: Order isomorphism between `α` and `Fin (card α)`.
* `finSumEquivOfFinset`: Equivalence between `α` and `Fin m ⊕ Fin n` where `m` and `n` are
  respectively the cardinalities of some `Finset α` and its complement.
-/


open Finset

/-- Given a linearly ordered fintype `α` of cardinal `k`, the order isomorphism
`monoEquivOfFin α h` is the increasing bijection between `Fin k` and `α`. Here, `h` is a proof
that the cardinality of `α` is `k`. We use this instead of an isomorphism `Fin (card α) ≃o α` to
avoid casting issues in further uses of this function. -/
def monoEquivOfFin (α : Type*) [Fintype α] [LinearOrder α] {k : ℕ} (h : Fintype.card α = k) :
    Fin k ≃o α :=
  (univ.orderIsoOfFin h).trans <| (OrderIso.setCongr _ _ coe_univ).trans OrderIso.Set.univ

variable {α : Type*} [DecidableEq α] [Fintype α] [LinearOrder α] {m n : ℕ} {s : Finset α}

/-- If `α` is a linearly ordered fintype, `s : Finset α` has cardinality `m` and its complement has
cardinality `n`, then `Fin m ⊕ Fin n ≃ α`. The equivalence sends elements of `Fin m` to
elements of `s` and elements of `Fin n` to elements of `sᶜ` while preserving order on each
"half" of `Fin m ⊕ Fin n` (using `Set.orderIsoOfFin`). -/
def finSumEquivOfFinset (hm : #s = m) (hn : #sᶜ = n) : Fin m ⊕ Fin n ≃ α :=
  calc
    Fin m ⊕ Fin n ≃ (s : Set α) ⊕ (sᶜ : Set α) :=
      Equiv.sumCongr (s.orderIsoOfFin hm).toEquiv <|
        (sᶜ.orderIsoOfFin hn).toEquiv.trans <| Equiv.setCongr s.coe_compl
    _ ≃ α := Equiv.Set.sumCompl _

@[simp]
theorem finSumEquivOfFinset_inl (hm : #s = m) (hn : #sᶜ = n) (i : Fin m) :
    finSumEquivOfFinset hm hn (Sum.inl i) = s.orderEmbOfFin hm i :=
  rfl

@[simp]
theorem finSumEquivOfFinset_inr (hm : #s = m) (hn : #sᶜ = n) (i : Fin n) :
    finSumEquivOfFinset hm hn (Sum.inr i) = sᶜ.orderEmbOfFin hn i :=
  rfl
