/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.Ring.Sheaf.Local
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

/-!
# The structure sheaf of a locally ringed space is locally ringed

The structure sheaf of a locally ringed space satisfies the local-ring condition formulated
in terms of covering sieves on a site.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.LocallyRingedSpace

instance (X : LocallyRingedSpace) : Sheaf.IsLocallyRinged X.sheaf where
  isUnitSieve_mem {U} a := by
    change X.presheaf.obj (op U) at a
    intro x hx
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (X.presheaf.germ U x hx a) with h | h
    · obtain ⟨V, i, hxV, ha⟩ := X.toRingedSpace.isUnit_res_of_isUnit_germ U a x hx h
      exact ⟨V, i, Or.inl ha, hxV⟩
    · have h' : IsUnit (X.presheaf.germ U x hx (1 - a)) := by simpa using h
      obtain ⟨V, i, hxV, ha⟩ := X.toRingedSpace.isUnit_res_of_isUnit_germ U (1 - a) x hx h'
      exact ⟨V, i, Or.inr ha, hxV⟩

end AlgebraicGeometry.LocallyRingedSpace
