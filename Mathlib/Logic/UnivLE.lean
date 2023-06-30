/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Logic.Small.Basic

noncomputable section

/--
A class expressing a universe inequality. `UnivLE.{u, v}` expresses that `u ≤ v`.

You might expect this to be defined as `∀ α : Type u, Small.{v} α`.
While this is implied by the definition below, we can not prove the reverse implication.
This is because in Lean's type theory while `max u v` is at least at big as `u` and `v`,
it could be bigger than both!
-/
class UnivLE.{u, v} : Prop where
  small : ∀ α : Type max u v, Small.{v} α

attribute [instance] UnivLE.small

pp_with_univ UnivLE

instance : UnivLE.{u, u} where
  small _ := inferInstance

instance : UnivLE.{u, u+1} where
  small _ := inferInstance

instance : UnivLE.{0, u} where
  small _ := inferInstance

instance : UnivLE.{u, max u v} where
  small _ := inferInstance

instance [I : UnivLE.{u, v}] (α : Type u) : Small.{v} α :=
  ⟨@Shrink.{v, max u v} (ULift.{v} α) (I.small _),
    ⟨Equiv.ulift.symm.trans (@equivShrink (ULift α) (I.small _))⟩⟩
