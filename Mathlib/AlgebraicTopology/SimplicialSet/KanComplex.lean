/-
Copyright (c) 2023 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Kan complexes

In this file, the abbreviation `KanComplex` is introduced for
fibrant objects in the category `SSet` which is equipped with
Kan fibrations.

In `Mathlib/AlgebraicTopology/Quasicategory/Basic.lean`
we show that every Kan complex is a quasicategory.

## TODO

- Show that the singular simplicial set of a topological space is a Kan complex.

-/

@[expose] public section

universe u

namespace SSet

open CategoryTheory Simplicial Limits

open modelCategoryQuillen in
/-- A simplicial set `S` is a Kan complex if it is fibrant, which means that
the projection `S ⟶ ⊤_ _` has the right lifting property with respect to horn inclusions. -/
abbrev KanComplex (S : SSet.{u}) : Prop := HomotopicalAlgebra.IsFibrant S

/-- A Kan complex `S` satisfies the following horn-filling condition:
for every nonzero `n : ℕ` and `0 ≤ i ≤ n`,
every map of simplicial sets `σ₀ : Λ[n, i] → S` can be extended to a map `σ : Δ[n] → S`. -/
lemma KanComplex.hornFilling {S : SSet.{u}} [KanComplex S]
    {n : ℕ} {i : Fin (n + 2)} (σ₀ : (Λ[n + 1, i] : SSet) ⟶ S) :
    ∃ σ : Δ[n + 1] ⟶ S, σ₀ = Λ[n + 1, i].ι ≫ σ := by
  have sq' : CommSq σ₀ Λ[n + 1, i].ι (terminal.from S) (terminal.from _) := ⟨by simp⟩
  exact ⟨sq'.lift, by simp⟩

end SSet
