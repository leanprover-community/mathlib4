/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Presentable.ColimitPresentation

/-!
# Ind and pro-properties

Given an object property `P`, we define an object property `ind P` that is satisfied for
`X` if `X` is a filtered colimit of `Xᵢ` and `Xᵢ` satisfies `P`.

## Main definitions

- `CategoryTheory.ObjectProperty.ind`: `X` satisfies `ind P` if `X` is a filtered colimit of `Xᵢ`
  for `Xᵢ` in `P`.

## Main results

- `CategoryTheory.ObjectProperty.ind_ind`: If `P` implies finitely presentable, then
  `P.ind.ind = P.ind`.

## TODOs:

- Dualise to obtain `CategoryTheory.ObjectProperty.pro`.
-/

universe w v u

namespace CategoryTheory.ObjectProperty

open Limits Opposite

variable {C : Type u} [Category.{v} C] {P : ObjectProperty C}

/-- `X` satisfies `ind P` if `X` is a filtered colimit of `Xᵢ` for `Xᵢ` in `P`. -/
def ind (P : ObjectProperty C) : ObjectProperty C :=
  fun X ↦ ∃ (J : Type w) (_ : SmallCategory J) (_ : IsFiltered J)
    (pres : ColimitPresentation J X), ∀ i, P (pres.diag.obj i)

variable (P) in
lemma le_ind : P ≤ ind.{w} P := by
  intro X hX
  exact ⟨PUnit, inferInstance, inferInstance, .self X, by simpa⟩

instance : P.ind.IsClosedUnderIsomorphisms where
  of_iso {X Y} e := fun ⟨J, _, _, pres, h⟩ ↦ ⟨J, ‹_›, ‹_›, pres.ofIso e, h⟩

/-- `ind` is idempotent if `P` implies finitely presentable. -/
lemma ind_ind (h : P ≤ isFinitelyPresentable.{w} C) [LocallySmall.{w} C] :
    ind.{w} (ind.{w} P) = ind.{w} P := by
  refine le_antisymm (fun X h ↦ ?_) (le_ind P.ind)
  choose J Jc Jf pres K Kc Kf pres' hp using h
  have (j : J) (i : K j) : IsFinitelyPresentable ((pres' j).diag.obj i) := h _ (hp _ _)
  have := IsFiltered.of_equivalence (ShrinkHoms.equivalence (ColimitPresentation.Total pres'))
  exact ⟨_, inferInstance, inferInstance,
    (pres.bind pres').reindex (ShrinkHoms.equivalence _).inverse, fun k ↦ by simp [hp]⟩

end CategoryTheory.ObjectProperty
