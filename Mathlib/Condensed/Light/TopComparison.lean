/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Condensed.Light.Explicit
import Mathlib.Condensed.TopComparison

/-!

# The functor from topological spaces to light condensed sets

We define the functor `topCatToLightCondSet : TopCat.{u} ⥤ LightCondSet.{u}`.

-/

universe w w' v u

open CategoryTheory Opposite Limits regularTopology ContinuousMap

/--
Associate to a `u`-small topological space the corresponding light condensed set, given by
`yonedaPresheaf`.
-/
@[simps! val_obj val_map]
noncomputable def TopCat.toLightCondSet (X : TopCat.{u}) : LightCondSet.{u} :=
  @LightCondSet.ofSheafLightProfinite (yonedaPresheaf LightProfinite.toTopCat.{u} X) _ (by
    apply equalizerCondition_yonedaPresheaf LightProfinite.toTopCat.{u} X
    intro Z B π he
    rw [LightProfinite.effectiveEpi_iff_surjective] at he
    apply QuotientMap.of_surjective_continuous he π.continuous)

/--
`TopCat.toLightCondSet` yields a functor from `TopCat.{u}` to `LightCondSet.{u}`.
-/
@[simps]
noncomputable def topCatToLightCondSet : TopCat.{u} ⥤ LightCondSet.{u} where
  obj X := X.toLightCondSet
  map f := ⟨⟨fun _ g ↦ f.comp g, by aesop⟩⟩
