/-
Copyright (c) 2026 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.CategoryTheory.OuterEndomorphism
public import Mathlib.Topology.Homotopy.Isotopy

/-!
# Mapping class group and outer automorphism group of fundamental group
-/

@[expose] public section

variable {X : Type*} [TopologicalSpace X] [PathConnectedSpace X]

open CategoryTheory FundamentalGroupoid

namespace MappingClassMonoid

open ContinuousMap.Monoid in
/-- The natural homomorphism from the mapping class monoid of a path-connected space `X` to the
monoid of isomorphism classes in the stabilizer of any object in the fundamental groupoid of `X`.

The path-connected assumption can be removed if the domain is replaced by the submonoid of
continuous maps acting trivially on H₀. -/
noncomputable def toQuotientStabilizerCon (x : X) :
    MappingClassMonoid X →* (stabilizerCon (C := .of (FundamentalGroupoid X)) ⟨x⟩).Quotient :=
  Con.lift _ ((Con.mk' _).comp <| (((fundamentalGroupoidFunctor ⋙ Grpd.forgetToCat).mapEnd _).comp
    TopCat.continuousMapEquivEnd.toMonoidHom).codRestrict _ fun _ ↦ ⟨(Groupoid.isoEquivHom
      (C := FundamentalGroupoid X) ..).symm ⟦PathConnectedSpace.somePath ..⟧⟩)
    fun _ _ ⟨h⟩ ↦ Quotient.sound
      ⟨Cat.Hom.isoMk <| by apply asIso <| FundamentalGroupoidFunctor.homotopicMapsNatIso h⟩

/-- The canonical homomorphism from the mapping class monoid of a path-connected space to the
outer endomorphism monoid of its fundamental group. -/
noncomputable def toOuterEndFundamentalGroup (x : X) :
    MappingClassMonoid X →* Monoid.OuterEnd (FundamentalGroup X x) :=
  quotientToOuterEndEnd.comp (toQuotientStabilizerCon x)

end MappingClassMonoid

/-- The canonical homomorphism from the mapping class group of a path-connected space to the
outer automorphism group of its fundamental group. -/
noncomputable def MappingClassGroup.toOutFundamentalGroup (x : X) :
    MappingClassGroup X →* Monoid.Out (FundamentalGroup X x) :=
  Monoid.Out.equivUnitsOuterEnd.symm.toMonoidHom.comp <|
    (Units.map <| MappingClassMonoid.toOuterEndFundamentalGroup x).comp toUnitsMonoid
