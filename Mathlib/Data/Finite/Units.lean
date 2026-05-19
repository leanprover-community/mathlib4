/-
Copyright (c) 2026 Alex Brodbelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Brodbelt and Eric Wieser
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Equiv
public import Mathlib.Data.Finite.Subtype

@[expose] public section

@[simp]
theorem Units.finite_iff₀ {G : Type*} [GroupWithZero G] : Finite Gˣ ↔ Finite G := by
  rw [unitsEquivNeZero.finite_iff, Subtype.finite_ne_iff]

@[simp]
theorem Units.infinite_iff₀ {G : Type*} [GroupWithZero G] : Infinite Gˣ ↔ Infinite G := by
  simpa only [not_finite_iff_infinite] using Units.finite_iff₀ (G := G).not

instance {G : Type*} [GroupWithZero G] [hG : Finite G] : Finite Gˣ :=
  Units.finite_iff₀.2 ‹_›

instance {G : Type*} [GroupWithZero G] [hG : Infinite G] : Infinite Gˣ :=
  Units.infinite_iff₀.2 ‹_›
