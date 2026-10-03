/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Hom
public import Mathlib.CategoryTheory.Category.Basic

/-!
# The category of root pairings

This file defines the category of root pairings, following the definition of category of root data
given in SGA III Exp. 21 Section 6.

## Main definitions:
* `RootPairingCat`: Objects are root pairings.

## TODO

* Forgetful functors
* Functions passing between module maps and root pairing homs

## Implementation details

This is mostly copied from `ModuleCat`.

-/

public section

open CategoryTheory

noncomputable section

universe v u

variable {R : Type u} [Ring R] [IsMulCommutative R]

/-- Objects in the category of root pairings. -/
structure RootPairingCat (R : Type u) [Ring R] [IsMulCommutative R] where
  /-- The weight space of a root pairing. -/
  weight : Type v
  [weightIsAddCommGroup : AddGroup weight] [IsAddCommutative weight]
  [weightIsModule : Module R weight]
  /-- The coweight space of a root pairing. -/
  coweight : Type v
  [coweightIsAddCommGroup : AddGroup coweight] [IsAddCommutative coweight]
  [coweightIsModule : Module R coweight]
  /-- The set that indexes roots and coroots. -/
  index : Type v
  /-- The root pairing structure. -/
  pairing : RootPairing index R weight coweight

attribute [instance] RootPairingCat.weightIsAddCommGroup RootPairingCat.weightIsModule
attribute [instance] RootPairingCat.coweightIsAddCommGroup RootPairingCat.coweightIsModule

namespace RootPairingCat

instance category : Category.{v, max (v + 1) u} (RootPairingCat.{v} R) where
  Hom P Q := RootPairing.Hom P.pairing Q.pairing
  id P := RootPairing.Hom.id P.pairing
  comp f g := RootPairing.Hom.comp g f

end RootPairingCat
