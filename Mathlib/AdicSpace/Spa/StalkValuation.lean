import Mathlib.AdicSpace.Spa.StructurePresheaf
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Algebra.Category.Ring.Colimits

universe u

open Topology CategoryTheory TopologicalSpace UniformSpace TopCat

section Valuation

def TopCat.Presheaf.forgetToRing {X : TopCat.{u}} (ℱ : X.Presheaf TopCommRingCat) :
    X.Presheaf CommRingCat :=
  ℱ ⋙ forget₂ TopCommRingCat CommRingCat

namespace spa

def rationalOpenData.huberPair {A : HuberPair} (r : rationalOpenData A) : HuberPair where
  plus := sorry
  carrier := Completion r.Localization
  ring := sorry
  topologicalSpace := sorry
  huber := sorry
  algebra := sorry
  int := sorry

def map {A B : HuberPair} (f : A →ₜ+* B) : spa B → spa A :=
  fun ⟨v, h⟩ ↦ ⟨v.comap f, by sorry⟩

lemma map_cts {A B : HuberPair} (f : A →ₜ+* B) : Continuous (map f) := sorry

-- TODO: promote `spa` to a contravariant functor `HuberPair → TopCat`

def canAux {A : HuberPair} (r : rationalOpenData A) : A → r.Localization :=
  fun a ↦ Localization.mk a ⟨1, by simp⟩

def can {A : HuberPair} (r : rationalOpenData A) : A →ₜ+* r.huberPair where
  toFun a := (canAux r a : Completion r.Localization)
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  continuous_toFun := sorry

-- (Part of) Wedhorn Proposition 8.2(2)
lemma map_bijective {A : HuberPair} (r : rationalOpenData A) :
    Function.Bijective (spa.map (can r) : spa r.huberPair → spa A) :=
  sorry

namespace presheaf

/-- The valuation on the stalk of the structure presheaf of the adic spectrum. -/
def stalk_valuation (A : HuberPair) (x : spa A) :
    Spv (((spa.presheaf A).forgetToRing).stalk x) :=
  -- use `map_bijective` to extend the valuation `x` to each `Completion r.Localization`,
  -- then take the colimit.
  sorry

end presheaf

end spa

end Valuation
