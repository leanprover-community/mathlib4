/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Limits.Presentation

/-!
# Ind and pro-properties

Given an object property `P`, we define an object property `ind P` that is satisfied for
`X` if `X` is a filtered colimit of `Xᵢ` and `Xᵢ` satisfies `P`.

## Main definitions

- `CategoryTheory.ObjectProperty.ind`: `X` satisfies `ind P` if `X` is a filtered colimit of `Xᵢ`
  for `Xᵢ` in `P`.
- `CategoryTheory.ObjectProperty.compact`: `X` is compact if it is finitely presentable.

## Main results

- `CategoryTheory.ObjectProperty.ind_ind`: If `P` implies compact, then `P.ind.ind = P.ind`.

## TODOs:

- Dualise to obtain `CategoryTheory.ObjectProperty.pro`.
-/

universe v u

namespace CategoryTheory.ObjectProperty

open Limits Opposite

variable {C : Type u} [Category.{v} C] {P : ObjectProperty C}

/-- `X` satisfies `ind P` if `X` is a filtered colimit of `Xᵢ` for `Xᵢ` in `P`. -/
def ind (P : ObjectProperty C) : ObjectProperty C :=
  fun X ↦ ∃ (J : Type v) (_ : SmallCategory J) (_ : IsFiltered J)
    (pres : ColimitPresentation J X), ∀ i, P (pres.diag.obj i)

variable (P) in
lemma le_ind : P ≤ P.ind := by
  intro X hX
  exact ⟨PUnit, inferInstance, inferInstance, .self X, by simpa⟩

instance : P.ind.IsClosedUnderIsomorphisms where
  of_iso {X Y} e := fun ⟨J, _, _, pres, h⟩ ↦ ⟨J, ‹_›, ‹_›, pres.ofIso e, h⟩

variable (C) in
/-- The compact objects of `C` are the finitely presentable ones. -/
def compact : ObjectProperty C := fun X ↦ IsFinitelyPresentable.{v} X

/-- `ind` is idempotent if `P` implies compact. -/
lemma ind_ind (h : P ≤ compact C) : P.ind.ind = P.ind := by
  refine le_antisymm (fun X h ↦ ?_) (le_ind P.ind)
  choose J Jc Jf pres K Kc Kf pres' hp using h
  have (j : J) (i : K j) : IsFinitelyPresentable ((pres' j).diag.obj i) := h _ (hp _ _)
  exact ⟨_, inferInstance, inferInstance, pres.bind pres', fun k ↦ by simp [hp]⟩

end CategoryTheory.ObjectProperty
