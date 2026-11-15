/-
Copyright (c) 2026 Robert Shlyakhtenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Shlyakhtenko
-/

module

public import Mathlib.Data.Finsupp.Weight
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.NatCard
import Mathlib.SetTheory.Cardinal.NatCard

/-!

# Cardinalities of finitely supported functions with bounded degree

Let `n` be a natural number. In this file we prove an equivalence
`Sym (Option α) n ≃ {f : α →₀ ℕ // f.degree ≤ n}` and derive as a consequence the
formula that, for a finite type `α`, the cardinality of `{f : α →₀ ℕ // f.degree ≤ n}`
is `Nat.choose (Nat.card α + n) n`.

-/

public noncomputable section


/-- Equivalence between finitely supported functions on `Option α` whose values sum to `n`
and finitely supported functions on `α` whose values sum to at most `n`. -/
def Finsupp.optionSubtypeSumEquiv (α β : Type*)
    [AddCommMonoid β] [LinearOrder β] [Sub β] [OrderedSub β] [CanonicallyOrderedAdd β]
    [AddLeftReflectLE β] (n : β) :
    {g : Option α →₀ β // g.sum (fun _ d ↦ d) = n} ≃ {f : α →₀ β // f.sum (fun _ d ↦ d) ≤ n} where
  toFun g := ⟨g.1.some, by grind [Finsupp.sum_option_index, le_add_left]⟩
  invFun f :=
    ⟨f.1.optionElim (n - f.1.sum (fun _ d ↦ d)), by
      grind [Finsupp.sum_option_index, Finsupp.optionElim_apply_none,Finsupp.some_optionElim,
      tsub_add_cancel_of_le f.2]⟩
  left_inv f := by
    grind [Finsupp.optionElim_some, Finsupp.sum_option_index, tsub_eq_of_eq_add]
  right_inv g := Subtype.ext (Finsupp.some_optionElim _ _)

/-- `Sym (Option α) n` is equivalent to the subtype of finitely supported functions `α →₀ ℕ`
with degree less than or equal to `n`. -/
def Sym.equivNatSumLE (α : Type*) [DecidableEq α] (n : ℕ) :
    Sym (Option α) n ≃ {f : α →₀ ℕ // f.degree ≤ n} :=
  (Sym.equivNatSum (Option α) n).trans (Finsupp.optionSubtypeSumEquiv α ℕ n)

/-- Stars and bars for finitely-supported functions with bounded total degree. -/
lemma Finsupp.natCard_degree_le (α : Type*) [Finite α] (n : ℕ) :
    Nat.card {f : α →₀ ℕ // f.degree ≤ n} = Nat.choose (Nat.card α + n) n := by
  classical
  rw [Nat.card_congr (Sym.equivNatSumLE α n).symm, Sym.natCard_sym_eq_choose,
    Finite.card_option]
  grind

local instance (α : Type*) [Finite α] (n : ℕ) : Fintype {f : α →₀ ℕ // f.degree ≤ n} :=
  (Finsupp.finite_of_degree_le (σ := α) n).fintype

lemma Finsupp.finCard_degree_le (α : Type*) [Fintype α] (n : ℕ) :
    Fintype.card {f : α →₀ ℕ // f.degree ≤ n} = Nat.choose (Fintype.card α + n) n := by
  simp [← Nat.card_eq_fintype_card, Finsupp.natCard_degree_le α n]

end
