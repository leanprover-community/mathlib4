/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Logic.Small.Basic

/-!
# UnivLE

A class expressing a universe inequality. `UnivLE.{u, v}` expresses that `u ≤ v`,
in the form `∀ α : Type max u v, Small.{v} α`.

See the doc-string for the comparison with an alternative weaker definition.

See also `Mathlib.CategoryTheory.UnivLE` for the statement
`UnivLE.{u,v} ↔ EssSurj (uliftFunctor : Type v ⥤ Type max u v)`.
-/

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
class UnivLE.{u, v} : Prop where
  small : ∀ α : Type max u v, Small.{v} α

attribute [instance] UnivLE.small

pp_with_univ UnivLE

example : UnivLE.{u, u} where
  small _ := inferInstance

example : UnivLE.{u, u+1} where
  small _ := inferInstance

example : UnivLE.{0, u} where
  small _ := inferInstance

example : UnivLE.{u, max u v} where
  small _ := inferInstance

instance [I : UnivLE.{u, v}] (α : Type u) : Small.{v} α :=
  ⟨@Shrink.{v, max u v} (ULift.{v} α) (I.small _),
    ⟨Equiv.ulift.symm.trans (@equivShrink (ULift α) (I.small _))⟩⟩
