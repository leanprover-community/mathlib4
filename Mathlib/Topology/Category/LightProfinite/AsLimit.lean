/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Category.LightProfinite.Basic
/-!
# Light profinite sets as limits of finite sets.

We show that any light profinite set is isomorphic to a sequential limit of finite sets.

This is analogous to the file `Profinite.AsLimit`.

-/

noncomputable section

open CategoryTheory Limits

namespace LightProfinite

universe u

variable (X : LightProfinite.{u})

/-- The functor `ℕᵒᵖ ⥤ Fintype` whose limit is isomorphic to `X`. -/
abbrev fintypeDiagram : ℕᵒᵖ ⥤ FintypeCat := X.toLightDiagram.diagram

/-- An abbreviation for `X.fintypeDiagram ⋙ FintypeCat.toProfinite`. -/
abbrev diagram : ℕᵒᵖ ⥤ LightProfinite := X.fintypeDiagram ⋙ FintypeCat.toLightProfinite

/-- A cone over `X.diagram` whose cone point is `X`. -/
def asLimitCone : Cone X.diagram :=
  let c : Cone (X.diagram ⋙ lightToProfinite) := X.toLightDiagram.cone
  (CreatesLimit.lifts c X.toLightDiagram.isLimit).liftedCone

/-- An auxiliary isomorphism of cones used to prove that `X.asLimitCone` is a limit cone. -/
def isoMapCone : lightToProfinite.mapCone X.asLimitCone ≅ X.toLightDiagram.cone :=
  let c : Cone (X.diagram ⋙ lightToProfinite) := X.toLightDiagram.cone
  (CreatesLimit.lifts c X.toLightDiagram.isLimit).validLift

/-- `X.asLimitCone` is indeed a limit cone. -/
def asLimit : CategoryTheory.Limits.IsLimit X.asLimitCone :=
  let hc : IsLimit (lightToProfinite.mapCone X.asLimitCone) :=
    X.toLightDiagram.isLimit.ofIsoLimit X.isoMapCone.symm
  isLimitOfReflects lightToProfinite hc

/-- A bundled version of `X.asLimitCone` and `X.asLimit`. -/
def lim : Limits.LimitCone X.diagram := ⟨X.asLimitCone, X.asLimit⟩
