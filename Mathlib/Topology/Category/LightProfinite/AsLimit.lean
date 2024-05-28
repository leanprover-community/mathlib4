import Mathlib.Topology.Category.LightProfinite.Basic

noncomputable section

open CategoryTheory Limits

namespace LightProfinite

universe u

variable (X : LightProfinite.{u})

abbrev fintypeDiagram : ℕᵒᵖ ⥤ FintypeCat := X.toLightDiagram.diagram

abbrev diagram : ℕᵒᵖ ⥤ LightProfinite := X.fintypeDiagram ⋙ FintypeCat.toLightProfinite

-- move
instance : CountableCategory ℕ where
  countableObj := inferInstance
  countableHom := inferInstance

def asLimitCone : Cone X.diagram :=
  let c : Cone (X.diagram ⋙ lightToProfinite) := X.toLightDiagram.cone
  (CreatesLimit.lifts c X.toLightDiagram.isLimit).liftedCone

def isoMapCone : lightToProfinite.mapCone X.asLimitCone ≅ X.toLightDiagram.cone :=
  let c : Cone (X.diagram ⋙ lightToProfinite) := X.toLightDiagram.cone
  (CreatesLimit.lifts c X.toLightDiagram.isLimit).validLift

def asLimit : CategoryTheory.Limits.IsLimit X.asLimitCone :=
  let hc : IsLimit (lightToProfinite.mapCone X.asLimitCone) :=
    X.toLightDiagram.isLimit.ofIsoLimit X.isoMapCone.symm
  isLimitOfReflects lightToProfinite hc
