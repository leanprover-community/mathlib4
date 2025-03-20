/-
Copyright (c) 2023 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Joël Riou
-/
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

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
