import Mathlib.AdicSpace.Spa.StructurePresheaf

universe u

open Topology CategoryTheory TopologicalSpace UniformSpace TopCat

section Valuation

def TopCat.Presheaf.forgetToRing {X : TopCat.{u}} (ℱ : X.Presheaf TopCommRingCat) :
    X.Presheaf CommRingCat :=
  ℱ ⋙ forget₂ TopCommRingCat CommRingCat

def spa.stalk_valuation (A : HuberPair) (x : of (spa A)) :
    Spv (((spa.presheaf A).forgetToRing).stalk x) :=
  sorry

end Valuation
