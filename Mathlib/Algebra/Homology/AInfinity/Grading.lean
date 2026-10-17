/-
Copyright (c) 2026 Justin Mu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Mu, Annie Yao, Niels Voss, Marco David
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.Data.ZMod.Basic

/-! # Grading indices for A-infinity categories

This file introduces the grading data used for the first definitions of graded hom
spaces in `R`-linear A-infinity categories.

The parity map records the degree modulo `2`, which is needed for signs in the
A-infinity identities.
-/

namespace AInfinityTheory

universe u v w

/-- A grading index is an additive commutative group with a distinguished unit element,
together with a parity map to `ZMod 2`.

The distinguished unit is used to realize integer degree shifts via the canonical map
`ℤ →+ β`. -/
public class GradingIndex (β : Type*) extends AddCommGroupWithOne β where
  /-- The parity of a degree. -/
  protected parity : β →+ ZMod 2
  /-- The distinguished unit has odd parity. -/
  protected parity_one : parity 1 = 1

/-- The parity homomorphism attached to a grading index. -/
public def parity {β : Type*} [GradingIndex β] : β →+ ZMod 2 :=
  GradingIndex.parity

/-- The canonical additive homomorphism from `ℤ` into a grading index. -/
@[expose]
public def GradingIndex.ofInt {β : Type*} [GradingIndex β] : ℤ →+ β :=
  Int.castAddHom β

/-- The parity of the distinguished unit is odd. -/
@[simp]
public theorem parity_one {β : Type*} [GradingIndex β] : parity (1 : β) = 1 :=
  GradingIndex.parity_one

/-- The parity map agrees with integer casts modulo `2`. -/
@[simp]
public theorem parity_intCast {β : Type*} [GradingIndex β] (n : ℤ) :
    parity (n : β) = (n : ZMod 2) := by
  rw [← zsmul_one n, map_zsmul, parity_one, zsmul_one]

/-- The canonical degree shift by an integer.

Keeping this wrapper makes degree formulas read naturally throughout the project. -/
@[expose]
public def shiftOfInt {β : Type*} [GradingIndex β] (n : ℤ) : β :=
  GradingIndex.ofInt n

/-- A graded `R`-module indexed by `β`. -/
public abbrev GradedRModule (β : Type v) [GradingIndex β] (R : Type u) [CommRing R] :
    Type (max v (u + 1)) :=
  CategoryTheory.GradedObject β (ModuleCat.{u} R)

/-- An `R`-linear graded quiver. -/
public class RLinearGradedQuiver (β : Type v) [GradingIndex β] (R : Type u) [CommRing R]
    (Obj : Type w) where
  /-- The graded `R`-module of morphisms from `X` to `Y`. -/
  protected gradedHom' : Obj → Obj → GradedRModule β R

/-- The graded `R`-module of morphisms between two objects. -/
@[expose]
public def gradedHom (β : Type v) [GradingIndex β] (R : Type u) [CommRing R]
    {Obj : Type w} [RLinearGradedQuiver β R Obj] (X Y : Obj) : GradedRModule β R :=
  RLinearGradedQuiver.gradedHom' X Y

end AInfinityTheory
