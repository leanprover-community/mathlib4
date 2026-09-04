/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Serre's condition `(Rₙ)`

A scheme `X` satisfies Serre's condition `(Rₙ)`, spelled `IsRegularInCodimensionLE n X`, if every
local ring of `X` of dimension at most `n` is regular. The dimension of the local ring at `x` is the
codimension of the closure of `x`, which is `Order.coheight x` (see
`AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`), so this says exactly that `X` is regular in
codimension `≤ n`.

## Main definitions

* `AlgebraicGeometry.IsRegularInCodimensionLE`: Serre's condition `(Rₙ)`.

## Main results

* `AlgebraicGeometry.IsRegularInCodimensionLE.isDiscreteValuationRing_stalk`: on a scheme satisfying
  `(R₁)`, the local ring at a point of codimension one is a discrete valuation ring, provided that
  local ring is a domain. This holds automatically on an integral scheme.

## TODO

Once Mathlib knows that a regular local ring is a domain (mathlib4#28683), the `IsDomain`
assumption on `IsRegularInCodimensionLE.isDiscreteValuationRing_stalk` becomes redundant and should
be removed, so that the result applies to every scheme satisfying `(R₁)` rather than only to
integral ones.
-/

@[expose] public section

universe u

open Order

namespace AlgebraicGeometry

/--
Serre's condition `(Rₙ)`: a scheme is regular in codimension `≤ n` if all of its local rings of
dimension at most `n` are regular local rings.

This condition is normally only considered for locally Noetherian schemes. Note that
`IsRegularLocalRing` already requires the local rings in question to be Noetherian, so no such
assumption appears here.
-/
@[stacks 033Q]
class IsRegularInCodimensionLE (n : ℕ) (X : Scheme.{u}) : Prop where
  isRegularLocalRing_stalk (x : X) (hx : coheight x ≤ n) :
    IsRegularLocalRing (X.presheaf.stalk x)

variable {n : ℕ} {X : Scheme.{u}}

lemma isRegularInCodimensionLE_iff :
    IsRegularInCodimensionLE n X ↔
      ∀ x : X, coheight x ≤ n → IsRegularLocalRing (X.presheaf.stalk x) :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

/--
Serre's condition is stated in terms of the dimension of the local rings of `X`; this is the
same as the condition on codimensions of points used to define `IsRegularInCodimensionLE`.
-/
lemma isRegularInCodimensionLE_iff_ringKrullDim :
    IsRegularInCodimensionLE n X ↔
      ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ n →
        IsRegularLocalRing (X.presheaf.stalk x) := by
  rw [isRegularInCodimensionLE_iff]
  refine forall_congr' fun x ↦ ?_
  rw [ringKrullDim_stalk_eq_coheight]
  norm_cast

lemma IsRegularInCodimensionLE.mono {m n : ℕ} (h : m ≤ n) (X : Scheme.{u})
    [IsRegularInCodimensionLE n X] : IsRegularInCodimensionLE m X :=
  ⟨fun x hx ↦ isRegularLocalRing_stalk x <| hx.trans (by exact_mod_cast h)⟩

/--
TODO: Remove the `IsDomain (X.presheaf.stalk x)` hypothesis once Mathlib knows that regular local
rings are domains.
-/
lemma IsRegularInCodimensionLE.isDiscreteValuationRing_stalk [IsRegularInCodimensionLE 1 X] {x : X}
    [IsDomain (X.presheaf.stalk x)] (hx : coheight x = 1) :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  have hreg := isRegularLocalRing_stalk (n := 1) x hx.le
  rw [← IsLocalRing.finrank_CotangentSpace_eq_one_iff]
  have hdim : ringKrullDim (X.presheaf.stalk x) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight x, hx]; rfl
  have := (IsRegularLocalRing.iff_finrank_cotangentSpace (X.presheaf.stalk x)).mp hreg
  rw [hdim] at this
  exact_mod_cast this

end AlgebraicGeometry
