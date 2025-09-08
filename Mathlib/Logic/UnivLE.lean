/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Logic.Small.Defs

/-!
# UnivLE

A proposition expressing a universe inequality. `UnivLE.{u, v}` expresses that `u ≤ v`,
in the form `∀ α : Type u, Small.{v} α`.

This API indirectly provides an instance for `Small.{u, max u v}`, which could not be declared
directly due to https://github.com/leanprover/lean4/issues/2297.

See the doc-string for the comparison with an alternative stronger definition.
-/

universe u v w

noncomputable section

/--
A class expressing a universe inequality. `UnivLE.{u, v}` expresses that `u ≤ v`.

There used to be a stronger definition `∀ α : Type max u v, Small.{v} α` that immediately implies
`Small.{v} ((α : Type u) → (β : Type v))` which is essential for proving that `Type v` has
`Type u`-indexed limits when `u ≤ v`. However the current weaker condition
`∀ α : Type u, Small.{v} α` also implies the same, so we switched to use it for
its simplicity and transitivity.

The strong definition easily implies the weaker definition (see below),
but we can not prove the reverse implication.
This is because in Lean's type theory, while `max u v` is at least at big as `u` and `v`,
it could be bigger than both!
See also `Mathlib/CategoryTheory/UnivLE.lean` for the statement that the stronger definition is
equivalent to `EssSurj (uliftFunctor : Type v ⥤ Type max u v)`.
-/
@[pp_with_univ, mk_iff]
class UnivLE : Prop where
  small (α : Type u) : Small.{v} α

attribute [instance] UnivLE.small


/- This is useless as an instance due to https://github.com/leanprover/lean4/issues/2297 -/
theorem univLE_max : UnivLE.{u, max u v} where small α := small_max.{v} α

theorem Small.trans_univLE (α : Type w) [hα : Small.{u} α] [h : UnivLE.{u, v}] :
    Small.{v} α :=
  let ⟨β, ⟨f⟩⟩ := hα.equiv_small
  let ⟨_, ⟨g⟩⟩ := (h.small β).equiv_small
  ⟨_, ⟨f.trans g⟩⟩

theorem UnivLE.trans [UnivLE.{u, v}] [UnivLE.{v, w}] : UnivLE.{u, w} where
  small α := Small.trans_univLE α

instance UnivLE.self : UnivLE.{u, u} := ⟨inferInstance⟩
instance UnivLE.zero : UnivLE.{0, u} := ⟨inferInstance⟩

/-- This is redundant as an instance given the below. -/
theorem UnivLE.succ [UnivLE.{u, v}] : UnivLE.{u, v + 1} := @UnivLE.trans _ ⟨inferInstance⟩

/- This is the crucial instance that subsumes `univLE_max`. -/
instance univLE_of_max [UnivLE.{max u v, v}] : UnivLE.{u, v} := @UnivLE.trans univLE_max ‹_›

-- order doesn't matter
example : UnivLE.{v, max v u} := inferInstance
example : UnivLE.{v, max u v} := inferInstance
example : UnivLE.{u, max v u} := inferInstance
example : UnivLE.{u, max u v} := inferInstance
-- `succ` is implied
example : UnivLE.{u, u + 1} := inferInstance
example : UnivLE.{2, 5} := inferInstance

/- When `small_Pi` from `Mathlib/Logic/Small/Basic.lean` is imported, we have : -/
-- example (α : Type u) (β : Type v) [UnivLE.{u, v}] : Small.{v} (α → β) := inferInstance

example : ¬UnivLE.{u + 1, u} := by
  simp only [univLE_iff, small_iff, not_forall, not_exists, not_nonempty_iff]
  exact ⟨Type u, fun α => ⟨fun f => Function.not_surjective_Type.{u, u} f.symm f.symm.surjective⟩⟩
