/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.GroupTheory.Commensurable
public import Mathlib.GroupTheory.DoubleCoset

/-!
# Hecke rings: definitions

The abstract Hecke ring of a *Hecke pair* `(H, Δ)`, following Shimura, *Introduction to the
Arithmetic Theory of Automorphic Functions*, Chapter 3. This file sets up the underlying types: the
Hecke pair, the double-coset quotient that indexes the ring, and the Hecke ring itself as formal
finitely-supported linear combinations of double cosets. The convolution product and the ring
structure are developed in later files.

## Main definitions

* `HeckePair G`: an arithmetic pair, a subgroup `H` together with a submonoid `Δ` of `G`
  satisfying `H ≤ Δ ≤ commensurator H`.
* `HeckeCoset P`: the quotient of `Δ` by the relation `HgH = HhH`, i.e. the double cosets
  forming the basis of the Hecke ring.
* `HeckeRing P Z`, notation `𝕋 P Z`: the Hecke ring with coefficients in `Z`, the
  finitely-supported `Z`-linear combinations of double cosets.
-/

@[expose] public section

open Subgroup.Commensurable

variable {G : Type*} [Group G]

/-- An arithmetic pair `(H, Δ)`: a subgroup `H` and a submonoid `Δ` of a group `G` satisfying
`H ≤ Δ ≤ commensurator H`. -/
@[ext]
structure HeckePair (G : Type*) [Group G] where
  /-- The subgroup `H` of the pair. -/
  H : Subgroup G
  /-- The submonoid `Δ` of elements commensurating `H`. -/
  Δ : Submonoid G
  /-- The subgroup `H` is contained in `Δ`. -/
  h₀ : H.toSubmonoid ≤ Δ
  /-- The submonoid `Δ` lies in the commensurator of `H`. -/
  h₁ : Δ ≤ (commensurator H).toSubmonoid

/-- The setoid on `Δ` identifying elements with the same double coset `HgH = HhH`, pulled back
from `DoubleCoset.setoid` along the inclusion `Δ ↪ G`.

This is a `def` rather than a global instance to avoid a `Setoid` diamond on `↥Δ` (the left-coset
setoid is another). Files that form `HeckeCoset`s opt in with `attribute [local instance]`; it is
marked `@[reducible]` so that opt-in is warning-free. -/
@[reducible] def doubleCosetSetoid (P : HeckePair G) : Setoid P.Δ :=
  (DoubleCoset.setoid (P.H : Set G) P.H).comap Subtype.val

/-- A Hecke double coset: an equivalence class of `Δ`-elements under `HgH = HhH`. This is the basis
type for the Hecke ring. -/
def HeckeCoset (P : HeckePair G) := Quotient (doubleCosetSetoid P)

noncomputable instance (P : HeckePair G) : DecidableEq (HeckeCoset P) :=
  Classical.decEq _

/-- The Hecke ring with coefficients in `Z`, denoted `𝕋 P Z`: the finitely-supported `Z`-linear
combinations of double cosets. The coefficients `Z` need only carry a `Zero` for the type to make
sense; algebraic structure is added by the instances below at the weakest level each requires. -/
def HeckeRing (P : HeckePair G) (Z : Type*) [Zero Z] := Finsupp (HeckeCoset P) Z

namespace HeckeRing

@[inherit_doc]
scoped notation "𝕋" => HeckeRing

/-- Elements of `𝕋 P Z` are functions `HeckeCoset P → Z` (finitely supported). -/
instance (P : HeckePair G) (Z : Type*) [Zero Z] :
    FunLike (𝕋 P Z) (HeckeCoset P) Z :=
  inferInstanceAs (FunLike (HeckeCoset P →₀ Z) (HeckeCoset P) Z)

/-- The additive commutative monoid structure on the Hecke ring, for any `AddCommMonoid` of
coefficients. -/
noncomputable instance (P : HeckePair G) (Z : Type*) [AddCommMonoid Z] :
    AddCommMonoid (𝕋 P Z) :=
  inferInstanceAs (AddCommMonoid ((HeckeCoset P) →₀ Z))

/-- The additive commutative group structure on the Hecke ring, when the coefficients form an
`AddCommGroup`. -/
noncomputable instance (P : HeckePair G) (Z : Type*) [AddCommGroup Z] :
    AddCommGroup (𝕋 P Z) :=
  inferInstanceAs (AddCommGroup ((HeckeCoset P) →₀ Z))

end HeckeRing
