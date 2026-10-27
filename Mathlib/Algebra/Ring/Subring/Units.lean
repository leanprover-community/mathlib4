/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.Order.GroupWithZero.Submonoid
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Basic

import Mathlib.Algebra.Group.Submonoid.Units

/-!

# Unit subgroups of a ring

-/

@[expose] public section

/-- The subgroup of positive units of a linear ordered semiring. -/
def Units.posSubgroup (R : Type*) [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] :
    Subgroup Rˣ :=
  { (Submonoid.pos R).comap (Units.coeHom R) with
    carrier := { x | (0 : R) < x }
    inv_mem' := Units.inv_pos.mpr }

@[simp]
theorem Units.mem_posSubgroup {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
    (u : Rˣ) : u ∈ Units.posSubgroup R ↔ (0 : R) < u :=
  Iff.rfl

namespace RingHom

variable {R T : Type*} [Semiring T]

theorem isUnit_eqLocusS_mk_iff [Semiring R] (f g : R →+* T) {r : R} (hr : f r = g r) :
    IsUnit (⟨r, hr⟩ : f.eqLocusS g) ↔ IsUnit r :=
  MonoidHom.isUnit_eqLocusM_mk_iff ..

theorem isUnit_eqLocus_mk_iff [Ring R] (f g : R →+* T) {r : R} (hr : f r = g r) :
    IsUnit (⟨r, hr⟩ : f.eqLocus g) ↔ IsUnit r :=
  MonoidHom.isUnit_eqLocusM_mk_iff ..

instance [Semiring R] (f g : R →+* T) : IsLocalHom (f.eqLocusS g).subtype where
  map_nonunit r := f.isUnit_eqLocusS_mk_iff g r.prop |>.2

instance [Ring R] (f g : R →+* T) : IsLocalHom (f.eqLocus g).subtype where
  map_nonunit r := f.isUnit_eqLocus_mk_iff g r.prop |>.2

end RingHom
