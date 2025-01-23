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

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

@[mk_iff]
class QuasiFinite (f : X ⟶ Y) : Prop where
  asdf : ∀ (y : Y),  IsFiniteLength (f.fiber y)

end AlgebraicGeometry
