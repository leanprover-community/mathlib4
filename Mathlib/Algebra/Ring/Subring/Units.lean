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

theorem RingHom.isUnit_eqLocus_mk_iff {R S T : Type*} [Ring R] [Ring S] [Semiring T]
    (f g : R →+* T) {r : R} (hr : f r = g r) :
    IsUnit (⟨r, hr⟩ : f.eqLocus g) ↔ IsUnit r := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp [isUnit_iff_exists, ← Subtype.val_inj] at h ⊢
    grind
  obtain ⟨s, hs⟩ := isUnit_iff_exists.mp h
  suffices ∃ a, r * a = 1 ∧ f a = g a ∧ a * r = 1 by
    simpa [isUnit_iff_exists, ← Subtype.val_inj]
  refine ⟨s, hs.left, ?_, hs.right⟩
  rw [← mul_one (f s), ← map_one g, ← hs.left, map_mul, ← mul_assoc, ← hr, ← map_mul,
    hs.right, map_one, one_mul]
