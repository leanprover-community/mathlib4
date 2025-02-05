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

#check Type

#check Scheme.Hom
#check pullback.lift

#check re
-- set_option trace.Meta.Tactic.simp true

example {x : X} : f.fiber (f.base x) := by
  let l := X.fromSpecResidueField x
  let ll : Spec (X.residueField x) ⟶ Spec (S.residueField (f.base x)) := Spec.map <| f.residueFieldMap x
  let lll : Spec (X.residueField x) ⟶ f.fiber (f.base x) := pullback.lift l ll (by
    ext1
    · simp only [Scheme.comp_coeBase, Scheme.Hom.Spec_map_residueFieldMap_fromSpecResidueField, l, ll]
    · ext
      simp? [l, ll]
      sorry
  )

#check Scheme.Hom.app
--
-- #check IsOpen
--
-- example {s : S} : S.fromSpecResidueField s := sorry
--
-- example {x : X} : f.base x = (S.fromSpecResidueField (f.base x)).base
--
-- #check Scheme.fromSpecResidueField
--
-- def singletonx {x} : Set (f.fiber (f.base x)) := by
--   exact fun y => y = x
--
--
-- def isquasifinite (x : X) : Prop := IsOpen (X := f.fiber (f.base x)) {x}
--
-- @[mk_iff]
-- class QuasiFinite (f : X ⟶ S) : Prop where
--   asdf : ∀ (y : Y),  IsFiniteLength (f.fiber y)
--
-- end AlgebraicGeometry
