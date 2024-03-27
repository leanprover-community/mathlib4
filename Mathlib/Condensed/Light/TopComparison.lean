/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.Topology.Category.Profinite.Limits
import Mathlib.Topology.Category.TopCat.Yoneda
import Mathlib.Condensed.Light.Explicit
import Mathlib.Condensed.TopComparison

/-!

# The functor from topological spaces to light condensed sets

We define the functor `topCatToLightCondensed : TopCat.{u} ⥤ CondensedSet.{u}`.

## Projects

* Prove that `topCatToLightCondensed` is faithful.
* Define sequential topological spaces.
* Prove that `topCatToLightCondensed` restricted to sequential spaces is fully faithful.
* Define the left adjoint of the restriction mentioned in the previous point.
-/

universe w w' v u

open CategoryTheory Opposite Limits regularTopology ContinuousMap

/--
Associate to a `u`-small topological space the corresponding light condensed set, given by
`yonedaPresheaf`.
-/
-- @[simps!]
noncomputable def TopCat.toLightCondensed (X : TopCat.{u}) : LightCondSet.{u} :=
  @LightCondSet.ofSheafLightProfinite (yonedaPresheaf LightProfinite.toTopCat.{u} X) _ (by
    apply equalizerCondition_yonedaPresheaf LightProfinite.toTopCat.{u} X
    intro Z B π he
    rw [LightProfinite.effectiveEpi_iff_surjective] at he
    apply QuotientMap.of_surjective_continuous he π.continuous)

/--
`TopCat.toLightCondensed` yields a functor from `TopCat.{u}` to `LightCondSet.{u}`.
-/
noncomputable def topCatToLightCondensed : TopCat.{u} ⥤ LightCondSet.{u} where
  obj X := X.toLightCondensed
  map f := ⟨⟨fun _ g ↦ f.comp g, by aesop⟩⟩
