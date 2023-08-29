/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Logic.Small.Basic

/-!
# UnivLE

A proposition expressing a universe inequality. `UnivLE.{u, v}` expresses that `u ≤ v`,
in the form `∀ α : Type max u v, Small.{v} α`.

See the doc-string for the comparison with an alternative weaker definition.

See also `Mathlib.CategoryTheory.UnivLE` for the statement
`UnivLE.{u,v} ↔ EssSurj (uliftFunctor : Type v ⥤ Type max u v)`.
-/

set_option autoImplicit true

noncomputable section

/--
A class expressing a universe inequality. `UnivLE.{u, v}` expresses that `u ≤ v`.

There are (at least) two plausible definitions for `u ≤ v`:
* strong: `∀ α : Type max u v, Small.{v} α`
* weak: `∀ α : Type u, Small.{v} α`

The weak definition has the advantage of being transitive.
However only under the strong definition do we have `Small.{v} ((α : Type u) → (β : Type v))`,
which is essential for proving that `Type v` has `Type u`-indexed limits when `u ≤ v`.

The strong definition implies the weaker definition (see below),
but we can not prove the reverse implication.
This is because in Lean's type theory, while `max u v` is at least at big as `u` and `v`,
it could be bigger than both!
-/
@[pp_with_univ]
abbrev UnivLE.{u, v} : Prop := ∀ α : Type max u v, Small.{v} α

example : UnivLE.{u, u} := inferInstance
example : UnivLE.{u, u+1} := inferInstance
example : UnivLE.{0, u} := inferInstance
example : UnivLE.{u, max u v} := inferInstance

instance [UnivLE.{u, v}] (α : Type u) : Small.{v} α :=
  ⟨Shrink.{v, max u v} (ULift.{v} α),
    ⟨Equiv.ulift.symm.trans (equivShrink (ULift α))⟩⟩

example : ¬ UnivLE.{u+1, u} := by
  simp only [Small_iff, not_forall, not_exists, not_nonempty_iff]
  -- ⊢ ∃ x, ∀ (x_1 : Type u), IsEmpty (x ≃ x_1)
  exact ⟨Type u, fun α => ⟨fun f => Function.not_surjective_Type.{u, u} f.symm f.symm.surjective⟩⟩
  -- 🎉 no goals
