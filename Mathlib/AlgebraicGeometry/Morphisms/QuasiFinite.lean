import Mathlib.AlgebraicGeometry.Morphisms.Constructors
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Topology.QuasiSeparated
import Mathlib.Topology.Sheaves.CommRingCat
import Mathlib

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

open scoped AlgebraicGeometry

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

-- #check Scheme.Hom

-- example {X Y : Type} {x : X} {S : Set X} {h : x ∈ S} {T : Set Y} {f : S → T} : Prop := by
--   have t := Set.preimage f {f x}
--   sorry

#check f.fiber

-- example {x : X} : f.fiber (f.base x) := by

#check IsOpen

example {s : S} : S.fromSpecResidueField s := sorry

example {x : X} : f.base x = (S.fromSpecResidueField (f.base x)).base

#check Scheme.fromSpecResidueField

def singletonx {x} : Set (f.fiber (f.base x)) := by
  exact fun y => y = x


-- def isquasifinite (x : X) : Prop := IsOpen (X := f.fiber (f.base x)) {x}

-- @[mk_iff]
-- class QuasiFinite (f : X ⟶ S) : Prop where
--   asdf : ∀ (y : Y),  IsFiniteLength (f.fiber y)

end AlgebraicGeometry
