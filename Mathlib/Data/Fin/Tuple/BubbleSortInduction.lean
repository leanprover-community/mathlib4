/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Order.PiLex
import Mathlib.Order.WellFounded
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# "Bubble sort" induction

We implement the following induction principle `Tuple.bubble_sort_induction`
on tuples with values in a linear order `α`.

Let `f : Fin n → α` and let `P` be a predicate on `Fin n → α`. Then we can show that
`f ∘ sort f` satisfies `P` if `f` satisfies `P`, and whenever some `g : Fin n → α`
satisfies `P` and `g i > g j` for some `i < j`, then `g ∘ swap i j` also satisfies `P`.

We deduce it from a stronger variant `Tuple.bubble_sort_induction'`, which
requires the assumption only for `g` that are permutations of `f`.

The latter is proved by well-founded induction via `WellFounded.induction_bot'`
with respect to the lexicographic ordering on the finite set of all permutations of `f`.
-/

public section


namespace Tuple

/-- *Bubble sort induction*: Prove that the sorted version of `f` has some property `P`
if `f` satisfies `P` and `P` is preserved on permutations of `f` when swapping two
antitone values. -/
theorem bubble_sort_induction' {n : ℕ} {α : Type*} [LinearOrder α] {f : Fin n → α}
    {P : (Fin n → α) → Prop} (hf : P f)
    (h : ∀ (σ : Equiv.Perm (Fin n)) (i j : Fin n),
      i < j → (f ∘ σ) j < (f ∘ σ) i → P (f ∘ σ) → P (f ∘ σ ∘ Equiv.swap i j)) :
    P (f ∘ sort f) := by
  letI := @Preorder.lift _ (Lex (Fin n → α)) _ fun σ : Equiv.Perm (Fin n) => toLex (f ∘ σ)
  refine
    @WellFounded.induction_bot' _ _ _ (IsWellFounded.wf : WellFounded (· < ·))
      (Equiv.refl _) (sort f) P (fun σ => f ∘ σ) (fun σ hσ hfσ => ?_) hf
  obtain ⟨i, j, hij₁, hij₂⟩ := antitone_pair_of_not_sorted' hσ
  exact ⟨σ * Equiv.swap i j, Pi.lex_desc hij₁.le hij₂, h σ i j hij₁ hij₂ hfσ⟩

/-- *Bubble sort induction*: Prove that the sorted version of `f` has some property `P`
if `f` satisfies `P` and `P` is preserved when swapping two antitone values. -/
theorem bubble_sort_induction {n : ℕ} {α : Type*} [LinearOrder α] {f : Fin n → α}
    {P : (Fin n → α) → Prop} (hf : P f)
    (h : ∀ (g : Fin n → α) (i j : Fin n), i < j → g j < g i → P g → P (g ∘ Equiv.swap i j)) :
    P (f ∘ sort f) :=
  bubble_sort_induction' hf fun _ => h _

end Tuple
