/-
Copyright (c) 2026 Robert Shlyakhtenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Shlyakhtenko
-/

module

public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Sym.NatCard
public import Mathlib.SetTheory.Cardinal.NatCard

/-!

# Cardinalities of finitely supported functions with bounded degree

Let `n` be a natural number. In this file we prove an equivalence
`Sym (Option α) n ≃ {f : α →₀ ℕ // f.degree ≤ n}` and derive as a consequence the
formula that, for a finite type `α`, the cardinality of `{f : α →₀ ℕ // f.degree ≤ n}`
is `Nat.choose (Nat.card α + n) n`.

-/

public section

noncomputable section

/-- The `n`th symmetric power of a type `Option α` is equivalent to the subtype of
finitely supported maps `α →₀ ℕ` with degree less than or equal to `n`. -/
def Sym.equivNatSumLE (α : Type*) [DecidableEq α] (n : ℕ) :
    Sym (Option α) n ≃ {f : α →₀ ℕ // f.degree ≤ n} := by
  have sum_option_eq (g : Option α →₀ ℕ) :
      g.sum (fun _ d ↦ d) = g none + g.some.sum (fun _ d ↦ d) :=
    Finsupp.sum_option_index g (fun _ d ↦ d) (fun _ => rfl) (fun _ _ _ => rfl)
  let e :
      {g : Option α →₀ ℕ // g.sum (fun _ d ↦ d) = n} ≃
        {f : α →₀ ℕ // f.sum (fun _ d ↦ d) ≤ n} :=
    { toFun := fun g => ⟨g.1.some, by grind⟩
      invFun := fun f =>
        ⟨f.1.optionElim (n - f.1.sum (fun _ d ↦ d)), by
          rw [sum_option_eq, Finsupp.optionElim_apply_none, Finsupp.some_optionElim,
            Nat.sub_add_cancel f.2]⟩
      left_inv := fun f => by
        grind [Finsupp.optionElim_some]
      right_inv := fun g => Subtype.ext (Finsupp.some_optionElim _ _) }
  exact (Sym.equivNatSum (Option α) n).trans e

/-- Stars and bars for finitely-supported functions with bounded total degree. -/
lemma Finsupp.natCard_degree_le (α : Type*) [Finite α] (n : ℕ) :
    Nat.card {f : α →₀ ℕ // f.degree ≤ n} =
      Nat.choose (Nat.card α + n) n := by
  classical
  rw [Nat.card_congr (Sym.equivNatSumLE α n).symm, Sym.natCard_sym_eq_choose,
    Finite.card_option]
  grind
