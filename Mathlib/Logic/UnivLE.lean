/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Logic.Small.Basic

/-!
# UnivLE

A proposition expressing a universe inequality. `UnivLE.{u, v}` expresses that `u ≤ v`,
in the form `∀ α : Type u, Small.{v} α`.

See the doc-string for the comparison with an alternative weaker definition.
-/

set_option autoImplicit true

noncomputable section

/--
A class expressing a universe inequality. `UnivLE.{u, v}` expresses that `u ≤ v`.

There used a stronger definition `∀ α : Type max u v, Small.{v} α` that immediately implies
`Small.{v} ((α : Type u) → (β : Type v))` which is essential for proving that `Type v` has
`Type u`-indexed limits when `u ≤ v`. However the current weaker condition
`∀ α : Type u, Small.{v} α` also implies the same, so we switched to use it for
its simplicity and transitivity.

The strong definition easily implies the weaker definition (see below),
but we can not prove the reverse implication.
This is because in Lean's type theory, while `max u v` is at least at big as `u` and `v`,
it could be bigger than both!
See also `Mathlib.CategoryTheory.UnivLE` for the statement that the stronger definition is
equivalent to `EssSurj (uliftFunctor : Type v ⥤ Type max u v)`.
-/
@[pp_with_univ]
abbrev UnivLE.{u, v} : Prop := ∀ α : Type u, Small.{v} α

example : UnivLE.{u, u} := inferInstance
example : UnivLE.{u, u+1} := inferInstance
example : UnivLE.{0, u} := inferInstance
/- Why can't Lean infer the following instances? -/
instance (priority := 100) : UnivLE.{u, max u v} := fun α ↦ small_max.{v} α
instance (priority := 100) : UnivLE.{u, max v u} := fun α ↦ small_max.{v} α

theorem Small.trans_univLE.{u, v} (α : Type w) [hα : Small.{u} α] [h : UnivLE.{u, v}] :
    Small.{v} α :=
  let ⟨β, ⟨f⟩⟩ := hα.equiv_small
  let ⟨_, ⟨g⟩⟩ := (h β).equiv_small
  ⟨_, ⟨f.trans g⟩⟩

theorem UnivLE.trans [UnivLE.{u, v}] [UnivLE.{v, w}] : UnivLE.{u, w} :=
  fun α ↦ Small.trans_univLE α

/- uses small_Pi -/
example (α : Type u) (β : Type v) [UnivLE.{u, v}] : Small.{v} (α → β) := inferInstance

example : ¬ UnivLE.{u+1, u} := by
  simp only [Small_iff, not_forall, not_exists, not_nonempty_iff]
  exact ⟨Type u, fun α => ⟨fun f => Function.not_surjective_Type.{u, u} f.symm f.symm.surjective⟩⟩

example [∀ α : Type max u v, Small.{v} α] (α : Type u) : Small.{v} α :=
  ⟨Shrink.{v, max u v} (ULift.{v} α), ⟨Equiv.ulift.symm.trans (equivShrink (ULift α))⟩⟩
