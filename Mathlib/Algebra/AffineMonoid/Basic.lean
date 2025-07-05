/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.GroupTheory.Finiteness

/-!
# Affine monoids

This file defines affine monoids as finitely generated cancellative torsion-free commutative
monoids.
-/

/-- An affine monoid is a finitely generated cancellative torsion-free commutative monoid. -/
class abbrev IsAffineAddMonoid (M : Type*) [AddCommMonoid M] :=
  IsCancelAdd M, AddMonoid.FG M, IsAddTorsionFree M

/-- An affine monoid is a finitely generated cancellative torsion-free commutative monoid. -/
@[to_additive]
class abbrev IsAffineMonoid (M : Type*) [CommMonoid M] :=
  IsCancelMul M, Monoid.FG M, IsMulTorsionFree M
